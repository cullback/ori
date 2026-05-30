//! Call lowering: function calls, method calls, qualified calls,
//! built-in arithmetic dispatch. The list-builtin dispatch lives
//! here too, plus the compare-via-tag-union machinery for `<`/`<=`
//! /`>`/`>=` on numeric types.

use crate::ast::{Expr, ExprKind};
use crate::passes::lambda::SingletonTarget;
use crate::ssa::Value;
use crate::ssa::instruction::{BinaryOp, ScalarType};
use crate::symbol::SymbolId;
use crate::types::engine::Type;

use super::LowerCtx;
use super::numeric;
use super::walk::{classify_walk, walk_apply_name};

/// The `T` of a `List(T)` type. Returns a fallback `Type::Con("__none")`
/// when the receiver isn't actually a `List(T)` shape.
fn list_element_type(ty: &Type) -> Type {
    match ty {
        Type::App(name, args) if name == "List" => args
            .first()
            .cloned()
            .unwrap_or_else(|| Type::Con("__none".to_owned())),
        _ => Type::Con("__none".to_owned()),
    }
}

impl<'a, 'src> LowerCtx<'a, 'src> {
    /// Lower a closure expression destined for a walk's step
    /// parameter, returning the captures-as-slots when possible.
    ///
    /// Returns `(step_vals, step_slot_tys)`:
    ///
    /// - **Direct dispatch + captures known**: the closure expr is a
    ///   `Call(tag_sym, captures...)` and `tag_sym` is a known
    ///   closure constructor. We lower each capture arg *directly*
    ///   (via `lower_expr_lv` and `to_slots`) and never materialize
    ///   the closure value — Phase E for closures. The captures'
    ///   flattened slots are returned. Walk lowering threads them as
    ///   parallel block params; `emit_walk_step_call` passes them
    ///   straight to the lifted function.
    /// - **Multi-variant fallback**: the closure expr lowers to a
    ///   single heap pointer (the D2 shell). Returns `[closure_ptr]`
    ///   with one slot type. Walk lowering threads one block param;
    ///   `emit_walk_step_call` calls `__apply_K(closure_ptr, ...)`.
    /// - **Direct dispatch + zero captures**: returns `(vec![], vec![])`.
    ///   Walk lowering threads no extra block params.
    fn lower_closure_step(
        &mut self,
        closure_expr: &Expr<'src>,
        direct: Option<&'a SingletonTarget>,
    ) -> (Vec<Value>, Vec<ScalarType>) {
        if let Some(st) = direct {
            if st.num_captures == 0 {
                return (Vec::new(), Vec::new());
            }
            if let ExprKind::Call { args: ctor_args, .. } = &closure_expr.kind {
                let mut vals = Vec::new();
                let mut tys = Vec::new();
                for arg in ctor_args {
                    let lv = self.lower_expr_lv(arg);
                    let slot_tys = self.expand_slots(&arg.ty);
                    let slots = self.to_slots(lv, &arg.ty, &slot_tys);
                    vals.extend(slots);
                    tys.extend(slot_tys);
                }
                return (vals, tys);
            }
            // direct.is_some() but closure_expr isn't a tag-constructor
            // Call (e.g. a Name reference to a closure-typed local).
            // Fall through to the materialize path; walk's
            // `emit_walk_step_call` will load captures the old way.
        }
        let v = self.lower_expr(closure_expr);
        let ty = v.ty;
        (vec![v], vec![ty])
    }

    pub(super) fn lower_call_by_sym(
        &mut self,
        target: SymbolId,
        args: &[Expr<'src>],
        result_ty: &Type,
    ) -> Value {
        let name = self.symbols.display(target).to_owned();
        self.lower_call(&name, args, result_ty)
    }

    pub(super) fn lower_qualified_call(
        &mut self,
        segments: &[&'src str],
        args: &[Expr<'src>],
        outer: &Expr<'src>,
    ) -> Value {
        let ExprKind::QualifiedCall { resolved, .. } = &outer.kind else {
            unreachable!("lower_qualified_call called on non-QualifiedCall");
        };
        // `__builtin.<op>` dispatch: the call came out of either the
        // numeric method-call resolution (`x.add(y)` where x : I64)
        // or the eta-expansion of a numeric method reference (`I64.add`
        // used as a first-class function). Both shapes share this
        // path — the difference is only in whether `segments[0]` is
        // a local binding or the type name.
        if let Some(resolved_name) = resolved
            && let Some(op_name) = resolved_name.strip_prefix("__builtin.")
        {
            // Numeric builtin intrinsic. `segments[0]` is either a
            // local binding (receiver for `x.add(y)`) or a type name
            // (`I64` for eta-expanded `I64.add(a, b)`).
            let local_lv = self
                .vars
                .iter()
                .find(|(sym, _)| self.symbols.display(**sym) == segments[0])
                .map(|(_, v)| v.clone());
            let local_val = local_lv.map(|lv| self.materialize(lv));
            if op_name == "to_bits" {
                let arg = local_val.unwrap_or_else(|| self.lower_expr(&args[0]));
                let dest_ty = numeric::bits_dest_ty(segments[0]);
                return self.builder.bitcast(arg, dest_ty);
            }
            if op_name == "from_bits" {
                let arg = local_val.unwrap_or_else(|| self.lower_expr(&args[0]));
                return self.builder.bitcast(arg, ScalarType::F64);
            }
            if op_name == "from_u8" {
                let arg = local_val.unwrap_or_else(|| self.lower_expr(&args[0]));
                let dest_ty = match segments[0] {
                    "U32" => ScalarType::U32,
                    _ => ScalarType::U64,
                };
                return self.builder.cast(arg, dest_ty);
            }
            if op_name == "to_u8" {
                let arg = local_val.unwrap_or_else(|| self.lower_expr(&args[0]));
                return self.builder.cast(arg, ScalarType::U8);
            }
            if op_name == "to_u64" {
                let arg = local_val.unwrap_or_else(|| self.lower_expr(&args[0]));
                return self.builder.cast(arg, ScalarType::U64);
            }
            if op_name == "to_i64" {
                let arg = local_val.unwrap_or_else(|| self.lower_expr(&args[0]));
                return self.builder.cast(arg, ScalarType::I64);
            }
            // Binary arithmetic op
            let (lhs, rhs) = if let Some(local_val) = local_val {
                (local_val, self.lower_expr(&args[0]))
            } else {
                (self.lower_expr(&args[0]), self.lower_expr(&args[1]))
            };
            let ty = self.expr_scalar_type(&args[0]);
            return self.lower_builtin_op(op_name, lhs, rhs, ty);
        }
        if let Some(resolved_name) = resolved {
            // Non-builtin method dispatch on a local receiver (the
            // qualified-call form of `receiver.method(args)`).
            let receiver_name = segments[0];
            let receiver_lv = self
                .vars
                .iter()
                .find(|(sym, _)| self.symbols.display(**sym) == receiver_name)
                .map(|(_, v)| v.clone());
            let receiver_val = match receiver_lv {
                Some(lv) => self.materialize(lv),
                None => {
                    // Receiver is a declared nullary constructor
                    // being used as a method target (e.g. `True.not()`).
                    // Structural constructors don't flow through this
                    // path — they go through `ExprKind::Call` instead.
                    self.lower_constructor_call(receiver_name, &[], None)
                }
            };
            let mut arg_vals = vec![receiver_val];
            for a in args {
                arg_vals.push(self.lower_expr(a));
            }
            let ret_ty = self.func_ret_type(resolved_name);
            return self.builder.call(resolved_name, arg_vals, ret_ty);
        }
        // Plain static qualified call: prefer the mono'd `resolved`
        // name so apply-function dispatch and walk classification see
        // the per-monomorphization callable name (e.g.
        // `List.walk__I64_I64`). Falling back to segments keeps pre-
        // mono shapes working.
        let mangled = resolved.clone().unwrap_or_else(|| segments.join("."));
        self.lower_call(&mangled, args, &outer.ty)
    }

    /// LV-returning variant for QualifiedCall. The only path with
    /// possible multi-shape output is the fallthrough to
    /// `lower_call_lv`; everything else is single-Value and gets
    /// wrapped.
    pub(super) fn lower_qualified_call_lv(
        &mut self,
        _mangled: &str,
        segments: &[&'src str],
        args: &[Expr<'src>],
        outer: &Expr<'src>,
    ) -> super::lowered_value::LoweredValue {
        let ExprKind::QualifiedCall { resolved, .. } = &outer.kind else {
            unreachable!("lower_qualified_call_lv called on non-QualifiedCall");
        };
        // Numeric builtin and local-receiver method paths produce
        // single values; reuse the legacy single-value dispatch.
        if let Some(name) = resolved
            && (name.starts_with("__builtin.") || self.is_local_receiver(segments.first().copied()))
        {
            return super::lowered_value::LoweredValue::single(
                self.lower_qualified_call(segments, args, outer),
            );
        }
        let mangled = resolved.clone().unwrap_or_else(|| segments.join("."));
        self.lower_call_lv(&mangled, args, &outer.ty)
    }

    /// True if `name` resolves to a local binding in `self.vars`.
    fn is_local_receiver(&self, name: Option<&'src str>) -> bool {
        let Some(name) = name else { return false };
        self.vars.iter().any(|(sym, _)| self.symbols.display(*sym) == name)
    }

    pub(super) fn lower_method_call(
        &mut self,
        receiver: &Expr<'src>,
        method: &'src str,
        args: &[Expr<'src>],
        outer: &Expr<'src>,
    ) -> Value {
        let lv = self.lower_method_call_lv(receiver, method, args, outer);
        self.materialize_lv(lv, &outer.ty)
    }

    /// LV-returning variant. Used by `lower_expr_lv` to keep list
    /// builtins / user-call results flowing as `Multi` into immediate
    /// consumers without a heap roundtrip.
    pub(super) fn lower_method_call_lv(
        &mut self,
        receiver: &Expr<'src>,
        method: &'src str,
        args: &[Expr<'src>],
        outer: &Expr<'src>,
    ) -> super::lowered_value::LoweredValue {
        let ExprKind::MethodCall { resolved, .. } = &outer.kind else {
            unreachable!("lower_method_call called on non-MethodCall");
        };
        let mangled = if let Some(r) = resolved.clone() {
            r
        } else {
            self.resolve_method_at_lower_time(method, &receiver.ty)
        };
        if let Some(v) = self.try_fuse_list_get_unwrap(method, receiver, args, outer) {
            return super::lowered_value::LoweredValue::single(v);
        }
        if let Some(walk) = classify_walk(&mangled) {
            if let Some((start, end)) = self.as_range_call(receiver) {
                assert!(args.len() == 2, "List.walk* method form takes 2 args");
                let init_lv = self.lower_expr_lv(&args[0]);
                let acc_slots = self.expand_slots(&args[0].ty);
                let init_vals = self.to_slots(init_lv, &args[0].ty, &acc_slots);
                let direct = self.resolve_closure_target(&args[1]);
                let (step_vals, step_slot_tys) =
                    self.lower_closure_step(&args[1], direct);
                let apply_name = walk_apply_name(&mangled, &args[1].ty, args[1].span);
                return self.lower_range_walk(
                    start, end, init_vals, step_vals, step_slot_tys,
                    &apply_name, walk.until, acc_slots, &args[0].ty, direct,
                );
            }
        }
        if is_list_builtin(&mangled) {
            let recv_lv = self.lower_expr_lv(receiver);
            if let Some(lv) = self.try_emit_list_builtin_method_lv(&mangled, recv_lv, &receiver.ty, args) {
                return lv;
            }
        }
        let recv_val = self.lower_expr(receiver);
        // Below: handlers that all naturally return a single Value.
        // Wrap with LoweredValue::single at each `return`.
        if mangled == "__record_equals" || mangled == "__tuple_equals" {
            let rhs = self.lower_expr(&args[0]);
            let resolved = self.resolve_transparent(&receiver.ty);
            let eq_name = self.ensure_eq_func(&resolved);
            let result = self.builder.call(&eq_name, vec![recv_val, rhs], ScalarType::U8);
            return super::lowered_value::LoweredValue::single(self.lower_bool_from_cmp(result));
        }
        if mangled == "__record_to_str" {
            return super::lowered_value::LoweredValue::single(self.lower_record_to_str(recv_val, &receiver.ty));
        }
        if mangled == "__record_hash" {
            return super::lowered_value::LoweredValue::single(self.lower_record_hash(recv_val, &receiver.ty));
        }
        if mangled == "__tuple_hash" {
            return super::lowered_value::LoweredValue::single(self.lower_tuple_hash(recv_val, &receiver.ty));
        }
        if mangled == "__tag_hash" {
            return super::lowered_value::LoweredValue::single(self.lower_tag_hash(recv_val, &receiver.ty));
        }
        if let Some(op_name) = mangled.strip_prefix("__builtin.") {
            if op_name == "to_bits" {
                let dest_ty = numeric::bits_dest_ty_for_ty(&receiver.ty);
                return super::lowered_value::LoweredValue::single(self.builder.bitcast(recv_val, dest_ty));
            }
            if op_name == "from_bits" {
                return super::lowered_value::LoweredValue::single(self.builder.bitcast(recv_val, ScalarType::F64));
            }
            if op_name == "from_u8" {
                let dest_ty = self.expr_scalar_type(outer);
                return super::lowered_value::LoweredValue::single(self.builder.cast(recv_val, dest_ty));
            }
            if op_name == "to_u8" {
                return super::lowered_value::LoweredValue::single(self.builder.cast(recv_val, ScalarType::U8));
            }
            if op_name == "to_u64" {
                return super::lowered_value::LoweredValue::single(self.builder.cast(recv_val, ScalarType::U64));
            }
            if op_name == "to_i64" {
                return super::lowered_value::LoweredValue::single(self.builder.cast(recv_val, ScalarType::I64));
            }
            let rhs = self.lower_expr(&args[0]);
            let ty = self.expr_scalar_type(receiver);
            return super::lowered_value::LoweredValue::single(self.lower_builtin_op(op_name, recv_val, rhs, ty));
        }
        if let Some(walk) = classify_walk(&mangled) {
            assert!(args.len() == 2, "List.walk* method form takes 2 args");
            let init_lv = self.lower_expr_lv(&args[0]);
            let acc_slots = self.expand_slots(&args[0].ty);
            let init_vals = self.to_slots(init_lv, &args[0].ty, &acc_slots);
            let direct = self.resolve_closure_target(&args[1]);
            let (step_vals, step_slot_tys) =
                self.lower_closure_step(&args[1], direct);
            let apply_name = walk_apply_name(&mangled, &args[1].ty, args[1].span);
            let elem_ty = list_element_type(&receiver.ty);
            return self.lower_list_walk(
                recv_val,
                init_vals,
                step_vals,
                step_slot_tys,
                &apply_name,
                walk.until,
                acc_slots,
                &args[0].ty,
                &elem_ty,
                direct,
            );
        }
        // Plain user-defined method call.
        if self.decls.funcs.contains(&mangled) {
            let per_param_slots = self.callee_param_slots(&mangled, args.len() + 1);
            let recv_lv = super::lowered_value::LoweredValue::single(recv_val);
            let mut arg_vals = self.to_slots(recv_lv, &receiver.ty, &per_param_slots[0]);
            for (a, slots) in args.iter().zip(per_param_slots.iter().skip(1)) {
                let lv = self.lower_expr_lv(a);
                arg_vals.extend(self.to_slots(lv, &a.ty, slots));
            }
            let ret_slots = self.callee_return_slots(&mangled);
            return if ret_slots.len() == 1 {
                super::lowered_value::LoweredValue::single(
                    self.builder.call(&mangled, arg_vals, ret_slots[0]),
                )
            } else {
                super::lowered_value::LoweredValue::from_slots(
                    self.builder.call_multi(&mangled, arg_vals, &ret_slots),
                )
            };
        }
        // Intrinsic fallback (numeric to_str etc.).
        let mut arg_vals = Vec::with_capacity(args.len() + 1);
        arg_vals.push(recv_val);
        for a in args {
            arg_vals.push(self.lower_expr(a));
        }
        let ret_ty = self.func_ret_type(&mangled);
        super::lowered_value::LoweredValue::single(self.builder.call(&mangled, arg_vals, ret_ty))
    }

    /// Central dispatch for direct and static qualified calls: list
    /// walks (which need the walk loop emitted inline), list
    /// builtins, num-to-str, constructors, and plain function calls.
    ///
    /// `result_ty` is the type of the enclosing expression, used to
    /// compute layout for structural constructor calls.
    pub(super) fn lower_call(
        &mut self,
        func: &str,
        args: &[Expr<'src>],
        result_ty: &Type,
    ) -> Value {
        let lv = self.lower_call_lv(func, args, result_ty);
        self.materialize_lv(lv, result_ty)
    }

    /// LV-returning variant of `lower_call`. Used by `lower_expr_lv`
    /// so that list-builtin and user-call results can flow as `Multi`
    /// into the next decomposed consumer without a heap roundtrip.
    pub(super) fn lower_call_lv(
        &mut self,
        func: &str,
        args: &[Expr<'src>],
        result_ty: &Type,
    ) -> super::lowered_value::LoweredValue {
        if let Some(walk) = classify_walk(func) {
            assert!(args.len() >= 3, "List.walk* takes 3 arguments");
            let init_lv = self.lower_expr_lv(&args[1]);
            let acc_slots = self.expand_slots(&args[1].ty);
            let init_vals = self.to_slots(init_lv, &args[1].ty, &acc_slots);
            let direct = self.resolve_closure_target(&args[2]);
            let (step_vals, step_slot_tys) =
                self.lower_closure_step(&args[2], direct);
            let apply_name = walk_apply_name(func, &args[2].ty, args[2].span);
            if let Some((start, end)) = self.as_range_call(&args[0]) {
                return self.lower_range_walk(
                    start, end, init_vals, step_vals, step_slot_tys,
                    &apply_name, walk.until, acc_slots, &args[1].ty, direct,
                );
            }
            let list_val = self.lower_expr(&args[0]);
            let elem_ty = list_element_type(&args[0].ty);
            return self.lower_list_walk(
                list_val,
                init_vals,
                step_vals,
                step_slot_tys,
                &apply_name,
                walk.until,
                acc_slots,
                &args[1].ty,
                &elem_ty,
                direct,
            );
        }
        if func == "crash" {
            let msg_val = self.lower_expr(&args[0]);
            let ret_ty = self.scalar_type(result_ty);
            return super::lowered_value::LoweredValue::single(
                self.builder.call("__crash", vec![msg_val], ret_ty),
            );
        }
        if is_list_builtin(func) {
            if let Some(lv) = self.try_emit_list_builtin_lv(func, args) {
                return lv;
            }
        }
        if self.decls.funcs.contains(func) {
            return self.lower_user_call(func, args, result_ty);
        }
        let arg_vals: Vec<Value> = args.iter().map(|a| self.lower_expr(a)).collect();
        if self.decls.constructors.contains_key(func) {
            return self.lower_constructor_call_lv(func, &arg_vals, Some(result_ty));
        }
        if func.starts_with(|c: char| c.is_ascii_uppercase()) {
            return self.lower_constructor_call_lv(func, &arg_vals, Some(result_ty));
        }
        panic!("undefined function or constructor: {func}")
    }

    /// Expansion-aware list builtin dispatch. Lists are consumed as
    /// `(len, cap, data)` directly — no header materialization at
    /// the call boundary. Returns `None` when `name` isn't a list
    /// builtin; the caller falls through to user-call dispatch.
    pub(super) fn try_emit_list_builtin_lv(
        &mut self,
        name: &str,
        args: &[Expr<'src>],
    ) -> Option<super::lowered_value::LoweredValue> {
        let base = strip_mono_suffix(name);
        match base {
            "List.len" => {
                let slots = self.list_slots(&args[0]);
                Some(super::lowered_value::LoweredValue::single(slots[0]))
            }
            "List.get" => {
                let slots = self.list_slots(&args[0]);
                let elem_ty = list_element_type(&args[0].ty);
                let idx = self.lower_expr(&args[1]);
                Some(self.emit_list_get_expanded(slots[0], slots[2], idx, &elem_ty))
            }
            "List.append" => {
                let slots = self.list_slots(&args[0]);
                let elem_ty = list_element_type(&args[0].ty);
                let val_lv = self.lower_expr_lv(&args[1]);
                let new_slots = self.emit_list_append_expanded(
                    slots[0], slots[1], slots[2], val_lv, &elem_ty,
                );
                Some(super::lowered_value::LoweredValue::Multi(new_slots))
            }
            "List.set" => {
                let slots = self.list_slots(&args[0]);
                let elem_ty = list_element_type(&args[0].ty);
                let idx = self.lower_expr(&args[1]);
                let val_lv = self.lower_expr_lv(&args[2]);
                let new_slots = self.emit_list_set_expanded(
                    slots[0], slots[1], slots[2], idx, val_lv, &elem_ty,
                );
                Some(super::lowered_value::LoweredValue::Multi(new_slots))
            }
            "List.range" => {
                let start = self.lower_expr(&args[0]);
                let end = self.lower_expr(&args[1]);
                let new_slots = self.emit_list_range_expanded(start, end);
                Some(super::lowered_value::LoweredValue::Multi(new_slots))
            }
            _ => None,
        }
    }

    /// Method-call variant: receiver and args are already lowered as
    /// LoweredValues, possibly Multi for the list receiver.
    pub(super) fn try_emit_list_builtin_method_lv(
        &mut self,
        name: &str,
        receiver_lv: super::lowered_value::LoweredValue,
        receiver_ty: &Type,
        args: &[Expr<'src>],
    ) -> Option<super::lowered_value::LoweredValue> {
        let base = strip_mono_suffix(name);
        let list_trio: [ScalarType; 3] =
            [ScalarType::U64, ScalarType::U64, ScalarType::RcPtr];
        match base {
            "List.len" => {
                let slots = self.to_slots(receiver_lv, receiver_ty, &list_trio);
                Some(super::lowered_value::LoweredValue::single(slots[0]))
            }
            "List.get" => {
                let slots = self.to_slots(receiver_lv, receiver_ty, &list_trio);
                let elem_ty = list_element_type(receiver_ty);
                let idx = self.lower_expr(&args[0]);
                Some(self.emit_list_get_expanded(slots[0], slots[2], idx, &elem_ty))
            }
            "List.append" => {
                let slots = self.to_slots(receiver_lv, receiver_ty, &list_trio);
                let elem_ty = list_element_type(receiver_ty);
                let val_lv = self.lower_expr_lv(&args[0]);
                let new_slots = self.emit_list_append_expanded(
                    slots[0], slots[1], slots[2], val_lv, &elem_ty,
                );
                Some(super::lowered_value::LoweredValue::Multi(new_slots))
            }
            "List.set" => {
                let slots = self.to_slots(receiver_lv, receiver_ty, &list_trio);
                let elem_ty = list_element_type(receiver_ty);
                let idx = self.lower_expr(&args[0]);
                let val_lv = self.lower_expr_lv(&args[1]);
                let new_slots = self.emit_list_set_expanded(
                    slots[0], slots[1], slots[2], idx, val_lv, &elem_ty,
                );
                Some(super::lowered_value::LoweredValue::Multi(new_slots))
            }
            _ => None,
        }
    }

    /// Lower a list expression, returning its (len, cap, data) slots.
    fn list_slots(&mut self, expr: &Expr<'src>) -> Vec<Value> {
        let lv = self.lower_expr_lv(expr);
        let trio: [ScalarType; 3] =
            [ScalarType::U64, ScalarType::U64, ScalarType::RcPtr];
        self.to_slots(lv, &expr.ty, &trio)
    }

    /// `List.get` on expanded slots: bounds-check len, load data at
    /// idx. Returns `Multi(tag, payload)` per D2's tag-union shape —
    /// `Ok(elem)` payload heap object holds the element at offset 0;
    /// `Err(OutOfBounds)` payload holds the OOB discriminant at 0.
    ///
    /// Note: this helper passes elements as a single 8-byte slot
    /// (matching the `Ok(elem)` payload heap layout). For aggregate
    /// element types under D1 inline layouts, the caller is
    /// responsible for materializing into the payload's 8-byte slot.
    fn emit_list_get_expanded(&mut self, len: Value, data: Value, idx: Value, elem_ty: &Type) -> super::lowered_value::LoweredValue {
        let in_bounds = self.builder.binop(BinaryOp::Lt, idx, len, ScalarType::U8);
        let ok_block = self.builder.create_block();
        let err_block = self.builder.create_block();
        let merge = self.builder.create_block();
        let merge_tag = self.builder.add_block_param(merge, ScalarType::U64);
        let merge_payload = self.builder.add_block_param(merge, ScalarType::RcPtr);
        self.builder.branch(in_bounds, ok_block, vec![], err_block, vec![]);

        self.builder.switch_to(ok_block);
        // For inlined elements, load all slots from the data buffer
        // and re-materialize into a single payload-friendly aggregate
        // ptr. For scalar / heap-pointer elements, a single load
        // suffices.
        let elem = if self.element_is_inlined(elem_ty) {
            let stride_units = self.element_stride(elem_ty) / 8;
            let stride_units_const = self.builder.const_u64(stride_units as u64);
            let unit_base = self.builder.binop(BinaryOp::Mul, idx, stride_units_const, ScalarType::U64);
            let slot_tys = self.expand_slots(elem_ty);
            let slot_vals: Vec<Value> = slot_tys.iter().enumerate().map(|(j, &ty)| {
                let j_const = self.builder.const_u64(j as u64);
                let unit_idx = self.builder.binop(BinaryOp::Add, unit_base, j_const, ScalarType::U64);
                self.builder.load_dyn(data, unit_idx, ty)
            }).collect();
            self.materialize_lv(super::lowered_value::LoweredValue::Multi(slot_vals), elem_ty)
        } else {
            self.builder.load_dyn(data, idx, ScalarType::RcPtr)
        };
        let ok_tag = self.builder.const_u64(0);
        let ok_payload = self.builder.alloc(8);
        self.builder.store(ok_payload, 0, elem);
        self.builder.jump(merge, vec![ok_tag, ok_payload]);

        self.builder.switch_to(err_block);
        let err_tag = self.builder.const_u64(1);
        let err_payload = self.builder.alloc(8);
        let oob_tag = self.builder.const_u8(0);
        self.builder.store(err_payload, 0, oob_tag);
        self.builder.jump(merge, vec![err_tag, err_payload]);

        self.builder.switch_to(merge);
        super::lowered_value::LoweredValue::Multi(vec![merge_tag, merge_payload])
    }

    /// `List.append` on expanded slots: FBIP on the data buffer
    /// directly. Honors D1's inline-element layout — aggregate
    /// elements are stored as N slots back-to-back at the new tail.
    fn emit_list_append_expanded(
        &mut self,
        len: Value,
        _cap: Value,
        data: Value,
        val_lv: super::lowered_value::LoweredValue,
        elem_ty: &Type,
    ) -> Vec<Value> {
        let stride = self.element_stride(elem_ty);
        let stride_units = stride / 8;
        let one = self.builder.const_u64(1);
        let new_len = self.builder.binop(BinaryOp::Add, len, one, ScalarType::U64);
        let stride_bytes_const = self.builder.const_u64(stride as u64);
        let new_byte_len = self.builder.binop(BinaryOp::Mul, new_len, stride_bytes_const, ScalarType::U64);
        let new_data = self.builder.cow_resize_dyn(data, new_byte_len);

        // Byte-offset-in-8-byte-units of element `len` (the tail).
        let stride_units_const = self.builder.const_u64(stride_units as u64);
        let elem_unit_base = self.builder.binop(BinaryOp::Mul, len, stride_units_const, ScalarType::U64);

        if self.element_is_inlined(elem_ty) {
            let slot_tys = self.expand_slots(elem_ty);
            let slot_vals = self.to_slots(val_lv, elem_ty, &slot_tys);
            for (j, slot_val) in slot_vals.into_iter().enumerate() {
                let j_const = self.builder.const_u64(j as u64);
                let idx = self.builder.binop(BinaryOp::Add, elem_unit_base, j_const, ScalarType::U64);
                self.builder.store_dyn(new_data, idx, slot_val);
            }
        } else {
            let val = self.materialize_lv(val_lv, elem_ty);
            self.builder.store_dyn(new_data, elem_unit_base, val);
        }
        vec![new_len, new_len, new_data]
    }

    /// `List.set` on expanded slots: cow on the data buffer, writing
    /// per-element slots for inlined aggregate elements.
    fn emit_list_set_expanded(
        &mut self,
        len: Value,
        cap: Value,
        data: Value,
        idx: Value,
        val_lv: super::lowered_value::LoweredValue,
        elem_ty: &Type,
    ) -> Vec<Value> {
        let stride_units = self.element_stride(elem_ty) / 8;
        let stride_units_const = self.builder.const_u64(stride_units as u64);
        let elem_unit_base = self.builder.binop(BinaryOp::Mul, idx, stride_units_const, ScalarType::U64);

        if self.element_is_inlined(elem_ty) {
            let slot_tys = self.expand_slots(elem_ty);
            let slot_vals = self.to_slots(val_lv, elem_ty, &slot_tys);
            // cow_store_dyn each slot in turn. The first call
            // cow-preps the buffer; subsequent calls operate on the
            // (now-unique) clone.
            let mut current_data = data;
            for (j, slot_val) in slot_vals.into_iter().enumerate() {
                let j_const = self.builder.const_u64(j as u64);
                let unit_idx = self.builder.binop(BinaryOp::Add, elem_unit_base, j_const, ScalarType::U64);
                current_data = self.builder.cow_store_dyn(current_data, unit_idx, slot_val);
            }
            vec![len, cap, current_data]
        } else {
            let val = self.materialize_lv(val_lv, elem_ty);
            let new_data = self.builder.cow_store_dyn(data, elem_unit_base, val);
            vec![len, cap, new_data]
        }
    }

    /// `List.range(start, end)` on expanded slots: build a fresh
    /// counter-driven list. Returns the new `(len, cap, data)` trio.
    fn emit_list_range_expanded(&mut self, start: Value, end: Value) -> Vec<Value> {
        let nonempty = self.builder.binop(BinaryOp::Gt, end, start, ScalarType::U8);
        let then_block = self.builder.create_block();
        let else_block = self.builder.create_block();
        let count_merge = self.builder.create_block();
        let count = self.builder.add_block_param(count_merge, ScalarType::U64);
        self.builder.branch(nonempty, then_block, vec![], else_block, vec![]);

        self.builder.switch_to(then_block);
        let diff = self.builder.binop(BinaryOp::Sub, end, start, ScalarType::U64);
        self.builder.jump(count_merge, vec![diff]);

        self.builder.switch_to(else_block);
        let zero = self.builder.const_u64(0);
        self.builder.jump(count_merge, vec![zero]);

        self.builder.switch_to(count_merge);
        let eight = self.builder.const_u64(8);
        let byte_len = self.builder.binop(BinaryOp::Mul, count, eight, ScalarType::U64);
        let data = self.builder.alloc_dyn(byte_len);

        let header = self.builder.create_block();
        let body = self.builder.create_block();
        let exit = self.builder.create_block();
        let header_i = self.builder.add_block_param(header, ScalarType::U64);
        let body_i = self.builder.add_block_param(body, ScalarType::U64);

        let zero2 = self.builder.const_u64(0);
        self.builder.jump(header, vec![zero2]);

        self.builder.switch_to(header);
        let cond = self.builder.binop(BinaryOp::Lt, header_i, count, ScalarType::U8);
        self.builder.branch(cond, body, vec![header_i], exit, vec![]);

        self.builder.switch_to(body);
        let val = self.builder.binop(BinaryOp::Add, start, body_i, ScalarType::U64);
        self.builder.store_dyn(data, body_i, val);
        let one = self.builder.const_u64(1);
        let next_i = self.builder.binop(BinaryOp::Add, body_i, one, ScalarType::U64);
        self.builder.jump(header, vec![next_i]);

        self.builder.switch_to(exit);
        vec![count, count, data]
    }

    /// Lower a call to a known user-defined function, respecting its
    /// expanded sig from the inferred scheme. Returns LoweredValue so
    /// callers that can consume Multi (destructure, immediate field
    /// access) avoid heap materialization on the return.
    pub(super) fn lower_user_call(
        &mut self,
        func: &str,
        args: &[Expr<'src>],
        _result_ty: &Type,
    ) -> super::lowered_value::LoweredValue {
        let per_param_slots = self.callee_param_slots(func, args.len());
        let mut arg_vals: Vec<Value> = Vec::new();
        for (a, slots) in args.iter().zip(&per_param_slots) {
            let lv = self.lower_expr_lv(a);
            arg_vals.extend(self.to_slots(lv, &a.ty, slots));
        }
        let ret_slots = self.callee_return_slots(func);
        if ret_slots.len() == 1 {
            let v = self.builder.call(func, arg_vals, ret_slots[0]);
            super::lowered_value::LoweredValue::single(v)
        } else {
            let vs = self.builder.call_multi(func, arg_vals, &ret_slots);
            super::lowered_value::LoweredValue::from_slots(vs)
        }
    }

    // ---- Builtin arithmetic dispatch ----

    pub(super) fn lower_builtin_op(&mut self, name: &str, lhs: Value, rhs: Value, ty: ScalarType) -> Value {
        match name {
            "add" => self.builder.binop(BinaryOp::Add, lhs, rhs, ty),
            "sub" => self.builder.binop(BinaryOp::Sub, lhs, rhs, ty),
            "mul" => self.builder.binop(BinaryOp::Mul, lhs, rhs, ty),
            "div" => self.builder.binop(BinaryOp::Div, lhs, rhs, ty),
            "mod" => self.builder.binop(BinaryOp::Rem, lhs, rhs, ty),
            "bit_and" => self.builder.binop(BinaryOp::And, lhs, rhs, ty),
            "bit_or" => self.builder.binop(BinaryOp::Or, lhs, rhs, ty),
            "bit_xor" => self.builder.binop(BinaryOp::Xor, lhs, rhs, ty),
            "shl" => self.builder.binop(BinaryOp::Shl, lhs, rhs, ty),
            "shr" => self.builder.binop(BinaryOp::Shr, lhs, rhs, ty),
            "equals" => self.lower_eq(lhs, rhs, false),
            "compare" => self.lower_compare(lhs, rhs, ty),
            _ => panic!("unknown builtin: {name}"),
        }
    }

    /// Emit a compare operation returning an Order tag union (Lt/Eq/Gt).
    pub(super) fn lower_compare(&mut self, lhs: Value, rhs: Value, _ty: ScalarType) -> Value {
        let lt_meta = &self.decls.constructors["Lt"];
        let eq_meta = &self.decls.constructors["Eq"];
        let gt_meta = &self.decls.constructors["Gt"];
        let alloc_size = 8; // Order tags have no payload, one U64 tag discriminant

        let lt_tag_idx = lt_meta.tag_index;
        let eq_tag_idx = eq_meta.tag_index;
        let gt_tag_idx = gt_meta.tag_index;

        let is_lt = self.builder.binop(BinaryOp::Lt, lhs, rhs, ScalarType::U8);
        let is_eq = self.builder.binop(BinaryOp::Eq, lhs, rhs, ScalarType::U8);

        let lt_block = self.builder.create_block();
        let not_lt_block = self.builder.create_block();
        let is_eq_param = self.builder.add_block_param(not_lt_block, ScalarType::U8);
        let eq_block = self.builder.create_block();
        let gt_block = self.builder.create_block();
        let merge = self.builder.create_block();
        let merge_param = self.builder.add_block_param(merge, ScalarType::RcPtr);

        self.builder.branch(is_lt, lt_block, vec![], not_lt_block, vec![is_eq]);

        self.builder.switch_to(lt_block);
        let lt_ptr = self.builder.alloc(alloc_size);
        let lt_tag = self.builder.const_u64(lt_tag_idx);
        self.builder.store(lt_ptr, 0, lt_tag);
        self.builder.jump(merge, vec![lt_ptr]);

        self.builder.switch_to(not_lt_block);
        self.builder.branch(is_eq_param, eq_block, vec![], gt_block, vec![]);

        self.builder.switch_to(eq_block);
        let eq_ptr = self.builder.alloc(alloc_size);
        let eq_tag = self.builder.const_u64(eq_tag_idx);
        self.builder.store(eq_ptr, 0, eq_tag);
        self.builder.jump(merge, vec![eq_ptr]);

        self.builder.switch_to(gt_block);
        let gt_ptr = self.builder.alloc(alloc_size);
        let gt_tag = self.builder.const_u64(gt_tag_idx);
        self.builder.store(gt_ptr, 0, gt_tag);
        self.builder.jump(merge, vec![gt_ptr]);

        self.builder.switch_to(merge);
        merge_param
    }
}

// ---- List built-in lowering ----
//
// `List.len`, `List.get`, `List.set`, `List.append`, `List.range` are
// emitted as inline SSA directly on the expanded `(len, cap, data)`
// slot trio. Method emitters live in the LowerCtx impl above; the
// helpers here just classify names.

/// Strip the `__<mono-suffix>` from a callable name so list builtin
/// dispatch can recognize specialized variants. `List.append__I64` →
/// `List.append`.
fn strip_mono_suffix(name: &str) -> &str {
    name.split("__").next().unwrap_or(name)
}

/// True if `name` (with any mono suffix stripped) is one of the
/// expansion-aware list builtins.
fn is_list_builtin(name: &str) -> bool {
    matches!(
        strip_mono_suffix(name),
        "List.len" | "List.get" | "List.append" | "List.range" | "List.set"
    )
}

impl<'a, 'src> LowerCtx<'a, 'src> {
    /// Match the AST `<list>.get(idx).unwrap()` and emit it as a fused
    /// bounds-check + indexed load with crash-on-out-of-bounds. Returns
    /// `None` and leaves emission untouched if the shape doesn't match,
    /// so the caller can fall through to the normal lowering.
    fn try_fuse_list_get_unwrap(
        &mut self,
        method: &str,
        receiver: &Expr<'src>,
        args: &[Expr<'src>],
        outer: &Expr<'src>,
    ) -> Option<Value> {
        if method != "unwrap" || !args.is_empty() {
            return None;
        }
        let ExprKind::MethodCall {
            receiver: inner_recv,
            method: inner_method,
            args: get_args,
            ..
        } = &receiver.kind
        else {
            return None;
        };
        if *inner_method != "get" || get_args.len() != 1 {
            return None;
        }
        let is_list = matches!(&inner_recv.ty, Type::App(name, _) if name == "List");
        if !is_list {
            return None;
        }
        // For inlined aggregate elements, the data buffer's stride
        // is no longer 8 bytes — the simple `load_dyn(data, idx, ty)`
        // peephole below would step into wrong slots. Bail out and
        // let the regular `List.get` + `unwrap` path handle this.
        let source_elem_ty = list_element_type(&inner_recv.ty);
        if self.element_is_inlined(&source_elem_ty) {
            return None;
        }

        let elem_ty = self.expr_scalar_type(outer);
        let list = self.lower_expr(inner_recv);
        let idx = self.lower_expr(&get_args[0]);

        let len = self.builder.load(list, 0, ScalarType::U64);
        let in_bounds = self.builder.binop(BinaryOp::Lt, idx, len, ScalarType::U8);

        let ok_block = self.builder.create_block();
        let err_block = self.builder.create_block();
        let merge = self.builder.create_block();
        let merge_param = self.builder.add_block_param(merge, elem_ty);

        self.builder
            .branch(in_bounds, ok_block, vec![], err_block, vec![]);

        self.builder.switch_to(ok_block);
        let data = self.builder.load(list, 16, ScalarType::RcPtr);
        let elem = self.builder.load_dyn(data, idx, elem_ty);
        self.builder.jump(merge, vec![elem]);

        self.builder.switch_to(err_block);
        let msg = self.lower_str_literal(b"called unwrap on Err");
        let crash_val = self.builder.call("__crash", vec![msg], elem_ty);
        self.builder.jump(merge, vec![crash_val]);

        self.builder.switch_to(merge);
        Some(merge_param)
    }
}
