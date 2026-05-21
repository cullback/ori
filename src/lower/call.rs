//! Call lowering: function calls, method calls, qualified calls,
//! built-in arithmetic dispatch. The list-builtin dispatch lives
//! here too, plus the compare-via-tag-union machinery for `<`/`<=`
//! /`>`/`>=` on numeric types.

use crate::ast::{Expr, ExprKind};
use crate::ssa::Value;
use crate::ssa::instruction::{BinaryOp, ScalarType};
use crate::symbol::SymbolId;
use crate::types::engine::Type;

use super::LowerCtx;
use super::numeric;
use super::walk::{classify_walk, walk_apply_name};
use super::list_ops;

impl<'a, 'src> LowerCtx<'a, 'src> {
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
            let local_val = self
                .vars
                .iter()
                .find(|(sym, _)| self.symbols.display(**sym) == segments[0])
                .map(|(_, v)| *v);
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
            let receiver_val = self
                .vars
                .iter()
                .find(|(sym, _)| self.symbols.display(**sym) == receiver_name)
                .map(|(_, v)| *v)
                .unwrap_or_else(|| {
                    // Receiver is a declared nullary constructor
                    // being used as a method target (e.g. `True.not()`).
                    // Structural constructors don't flow through this
                    // path — they go through `ExprKind::Call` instead.
                    self.lower_constructor_call(receiver_name, &[], None)
                });
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

    pub(super) fn lower_method_call(
        &mut self,
        receiver: &Expr<'src>,
        method: &'src str,
        args: &[Expr<'src>],
        outer: &Expr<'src>,
    ) -> Value {
        let ExprKind::MethodCall { resolved, .. } = &outer.kind else {
            unreachable!("lower_method_call called on non-MethodCall");
        };
        let mangled = if let Some(r) = resolved.clone() {
            r
        } else {
            // No resolution from inference — resolve based on the
            // concrete receiver type (happens for polymorphic methods
            // after monomorphization).
            self.resolve_method_at_lower_time(method, &receiver.ty)
        };
        // Deforestation: check for List.range(a,b).walk(...) BEFORE
        // lowering the receiver to avoid materializing the range list.
        if let Some(walk) = classify_walk(&mangled) {
            if let Some((start, end)) = self.as_range_call(receiver) {
                assert!(args.len() == 2, "List.walk* method form takes 2 args");
                let init_val = self.lower_expr(&args[0]);
                let acc_ty = self.expr_scalar_type(&args[0]);
                let direct = self.resolve_closure_target(&args[1]);
                let closure_val = self.lower_expr(&args[1]);
                let apply_name = walk_apply_name(&mangled, &args[1].ty);
                return self.lower_range_walk(
                    start, end, init_val, closure_val, &apply_name,
                    walk.until, acc_ty, direct,
                );
            }
        }
        let recv_val = self.lower_expr(receiver);
        if mangled == "__record_equals" || mangled == "__tuple_equals" {
            let rhs = self.lower_expr(&args[0]);
            let resolved = self.resolve_transparent(&receiver.ty);
            let eq_name = self.ensure_eq_func(&resolved);
            let result = self.builder.call(&eq_name, vec![recv_val, rhs], ScalarType::U8);
            return self.lower_bool_from_cmp(result);
        }
        if mangled == "__record_to_str" {
            return self.lower_record_to_str(recv_val, &receiver.ty);
        }
        if mangled == "__record_hash" {
            return self.lower_record_hash(recv_val, &receiver.ty);
        }
        if mangled == "__tuple_hash" {
            return self.lower_tuple_hash(recv_val, &receiver.ty);
        }
        if mangled == "__tag_hash" {
            return self.lower_tag_hash(recv_val, &receiver.ty);
        }
        if let Some(op_name) = mangled.strip_prefix("__builtin.") {
            if op_name == "to_bits" {
                let dest_ty = numeric::bits_dest_ty_for_ty(&receiver.ty);
                return self.builder.bitcast(recv_val, dest_ty);
            }
            if op_name == "from_bits" {
                return self.builder.bitcast(recv_val, ScalarType::F64);
            }
            if op_name == "from_u8" {
                let dest_ty = self.expr_scalar_type(outer);
                return self.builder.cast(recv_val, dest_ty);
            }
            if op_name == "to_u8" {
                return self.builder.cast(recv_val, ScalarType::U8);
            }
            if op_name == "to_u64" {
                return self.builder.cast(recv_val, ScalarType::U64);
            }
            if op_name == "to_i64" {
                return self.builder.cast(recv_val, ScalarType::I64);
            }
            let rhs = self.lower_expr(&args[0]);
            let ty = self.expr_scalar_type(receiver);
            return self.lower_builtin_op(op_name, recv_val, rhs, ty);
        }
        // List walks: the walk loop needs untyped Values, so build
        // them positionally.
        if let Some(walk) = classify_walk(&mangled) {
            assert!(args.len() == 2, "List.walk* method form takes 2 args");
            let init_val = self.lower_expr(&args[0]);
            let acc_ty = self.expr_scalar_type(&args[0]);
            let direct = self.resolve_closure_target(&args[1]);
            let closure_val = self.lower_expr(&args[1]);
            let apply_name = walk_apply_name(&mangled, &args[1].ty);
            return self.lower_list_walk(
                recv_val,
                init_val,
                closure_val,
                &apply_name,
                walk.until,
                acc_ty,
                direct,
            );
        }
        let mut arg_vals = Vec::with_capacity(args.len() + 1);
        arg_vals.push(recv_val);
        for a in args {
            arg_vals.push(self.lower_expr(a));
        }
        if Self::is_list_builtin(&mangled) {
            // Receiver is `List(T)`; element type drives in-copy RC.
            let elem_ty = self.list_elem_scalar_type(&receiver.ty)
                .unwrap_or(ScalarType::I64);
            return list_ops::emit_list_builtin_call(&mut self.builder, &mangled, arg_vals, elem_ty);
        }
        let ret_ty = self.func_ret_type(&mangled);
        self.builder.call(&mangled, arg_vals, ret_ty)
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
        if let Some(walk) = classify_walk(func) {
            assert!(args.len() >= 3, "List.walk* takes 3 arguments");
            let init_val = self.lower_expr(&args[1]);
            let acc_ty = self.expr_scalar_type(&args[1]);
            let direct = self.resolve_closure_target(&args[2]);
            let closure_val = self.lower_expr(&args[2]);
            let apply_name = walk_apply_name(func, &args[2].ty);
            // Deforestation: List.walk(List.range(a, b), init, f) → counter loop.
            if let Some((start, end)) = self.as_range_call(&args[0]) {
                return self.lower_range_walk(
                    start, end, init_val, closure_val, &apply_name,
                    walk.until, acc_ty, direct,
                );
            }
            let list_val = self.lower_expr(&args[0]);
            return self.lower_list_walk(
                list_val,
                init_val,
                closure_val,
                &apply_name,
                walk.until,
                acc_ty,
                direct,
            );
        }
        if func == "crash" {
            // Crash diverges, so its return is never observed at
            // runtime. Typing it as the caller's expected result type
            // keeps merge/return type agreement honest in the IR.
            let msg_val = self.lower_expr(&args[0]);
            let ret_ty = self.scalar_type(result_ty);
            return self.builder.call("__crash", vec![msg_val], ret_ty);
        }
        if Self::is_list_builtin(func) {
            let arg_vals: Vec<Value> = args.iter().map(|a| self.lower_expr(a)).collect();
            // Static-form list builtins (`List.range`, `List.repeat`,
            // etc.) return a list — their result type carries the
            // element. Method-form ones (`xs.set(i, v)`) have a list
            // as their first arg. Try result type first, fall back.
            let elem_ty = self.list_elem_scalar_type(result_ty)
                .or_else(|| self.list_elem_scalar_type(&args[0].ty))
                .unwrap_or(ScalarType::I64);
            return list_ops::emit_list_builtin_call(&mut self.builder, func, arg_vals, elem_ty);
        }
        if self.decls.constructors.contains_key(func) {
            let arg_vals: Vec<Value> = args.iter().map(|a| self.lower_expr(a)).collect();
            return self.lower_constructor_call(func, &arg_vals, Some(result_ty));
        }
        if self.decls.funcs.contains(func) {
            let ret_ty = self.func_ret_type(func);
            let arg_vals: Vec<Value> = args.iter().map(|a| self.lower_expr(a)).collect();
            return self.builder.call(func, arg_vals, ret_ty);
        }
        // Structural constructor (not in decl_info). Layout is
        // derived from `result_ty` which inference closed to a
        // concrete `Type::TagUnion`.
        if func.starts_with(|c: char| c.is_ascii_uppercase()) {
            let arg_vals: Vec<Value> = args.iter().map(|a| self.lower_expr(a)).collect();
            return self.lower_constructor_call(func, &arg_vals, Some(result_ty));
        }
        panic!("undefined function or constructor: {func}")
    }

    pub(super) fn is_list_builtin(name: &str) -> bool {
        matches!(
            name,
            "List.len"
                | "List.get"
                | "List.set"
                | "List.append"
                | "List.reverse"
                | "List.sublist"
                | "List.repeat"
                | "List.range"
        )
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
