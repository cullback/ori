//! Lowering for `List.walk` / `List.walk_until` / `List.range` style
//! reductions. Each emits an explicit SSA loop (header / body / done
//! blocks) with the accumulator threaded through block params — no
//! intermediate list allocation needed for `range`-driven walks.

use crate::ast::{Expr, ExprKind, Span};
use crate::passes::lambda_specialize::SingletonTarget;
use crate::ssa::Value;
use crate::ssa::instruction::{BinaryOp, ScalarType};
use crate::types::engine::Type;

use super::LowerCtx;
use super::lowered_value::LoweredValue;

pub struct WalkKind {
    pub until: bool,
}

/// Classify a function name as a `walk` or `walk_until` call. Strips
/// the mono suffix (`__<sig>`) so specialized walks (e.g.
/// `List.walk__I64_I64`) still classify.
pub fn classify_walk(name: &str) -> Option<WalkKind> {
    let core = name.split("__").next().unwrap_or(name);
    let base = core
        .strip_prefix("List.")
        .or_else(|| core.rsplit_once(".List.").map(|(_, rest)| rest))?;
    match base {
        "walk" => Some(WalkKind { until: false }),
        "walk_until" => Some(WalkKind { until: true }),
        _ => None,
    }
}

/// Build the apply-function name for a walk call. Mirrors the
/// `walk_call_key` logic in `lambda_solve`: appends the step
/// function's full `Arrow` type AND the closure-arg's source span
/// so each walk call site gets its own lambda set. `List.walk` is
/// an intrinsic with no body to monomorphize; per-call-site keying
/// is what lets the single closure flowing into each walk-site land
/// in a singleton set, which Phase E lowering collapses into a
/// direct call (no `__apply_K` dispatch, no payload heap object).
pub fn walk_apply_name(callee: &str, step_ty: &Type, closure_span: Span) -> String {
    use std::fmt::Write;
    let mut key = callee.to_owned();
    key.push_str("__");
    crate::passes::mono::append_type_mangling(&mut key, step_ty);
    write!(
        &mut key,
        "__cs{}_{}_{}",
        closure_span.file.0, closure_span.start, closure_span.end
    ).unwrap();
    format!("__apply_{key}_2")
}

impl<'a, 'src> LowerCtx<'a, 'src> {
    /// If `expr` is `List.range(start, end)`, return the lowered
    /// `start` / `end` values. Used by walk lowering to elide the
    /// intermediate list allocation when the source is a range.
    pub(super) fn as_range_call(&mut self, expr: &Expr<'src>) -> Option<(Value, Value)> {
        let is_range = |r: &str| r == "List.range" || r.ends_with(".range");
        match &expr.kind {
            ExprKind::QualifiedCall { resolved, segments, args, .. } => {
                let full = resolved.clone()
                    .unwrap_or_else(|| segments.join("."));
                if is_range(&full) && args.len() == 2 {
                    let start = self.lower_expr(&args[0]);
                    let end = self.lower_expr(&args[1]);
                    Some((start, end))
                } else {
                    None
                }
            }
            ExprKind::Call { target, args } if args.len() == 2 => {
                let name = self.symbols.display(*target);
                if is_range(name) {
                    let start = self.lower_expr(&args[0]);
                    let end = self.lower_expr(&args[1]);
                    Some((start, end))
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    /// Emit a range-walk loop: counter from start to end, no list
    /// allocation. Accumulator threaded through `acc_slots`-many
    /// parallel block params.
    pub(super) fn lower_range_walk(
        &mut self,
        start: Value,
        end: Value,
        init_vals: Vec<Value>,
        step_val: Value,
        apply_name: &str,
        until: bool,
        acc_slots: Vec<ScalarType>,
        acc_ty: &Type,
        direct: Option<&SingletonTarget>,
    ) -> LoweredValue {
        let step_ty = step_val.ty;
        // Range-walk's element is the counter itself, always U64.
        let elem_ty = Type::Con("U64".to_string());

        let header = self.builder.create_block();
        let i_param = self.builder.add_block_param(header, ScalarType::U64);
        let acc_params: Vec<Value> = acc_slots.iter()
            .map(|&ty| self.builder.add_block_param(header, ty))
            .collect();
        let end_param = self.builder.add_block_param(header, ScalarType::U64);
        let step_param = self.builder.add_block_param(header, step_ty);
        let body_block = self.builder.create_block();
        let body_i = self.builder.add_block_param(body_block, ScalarType::U64);
        let body_acc: Vec<Value> = acc_slots.iter()
            .map(|&ty| self.builder.add_block_param(body_block, ty))
            .collect();
        let body_end = self.builder.add_block_param(body_block, ScalarType::U64);
        let body_step = self.builder.add_block_param(body_block, step_ty);
        let done = self.builder.create_block();
        let done_params: Vec<Value> = acc_slots.iter()
            .map(|&ty| self.builder.add_block_param(done, ty))
            .collect();
        // Thread `step` into `done` as an unused block param so rc_emit
        // releases the closure env on loop exit. Without this, callers
        // whose closure captures something would leak the env when the
        // loop terminates.
        let _done_step = self.builder.add_block_param(done, step_ty);

        let mut entry_args = Vec::with_capacity(2 + acc_slots.len() + 2);
        entry_args.push(start);
        entry_args.extend(init_vals.iter().copied());
        entry_args.push(end);
        entry_args.push(step_val);
        self.builder.jump(header, entry_args);

        self.builder.switch_to(header);
        let cmp = self.builder.binop(BinaryOp::Eq, i_param, end_param, ScalarType::U8);
        let mut done_args = acc_params.clone();
        done_args.push(step_param);
        let mut body_args = Vec::with_capacity(2 + acc_slots.len() + 2);
        body_args.push(i_param);
        body_args.extend(acc_params.iter().copied());
        body_args.push(end_param);
        body_args.push(step_param);
        self.builder.branch(cmp, done, done_args, body_block, body_args);

        self.builder.switch_to(body_block);
        let elem_vals = vec![body_i]; // element IS the counter for range-walk
        let result = self.emit_walk_step_call(direct, apply_name, body_step, &body_acc, elem_vals, &elem_ty, &acc_slots);

        let one = self.builder.const_u64(1);
        let next_i = self.builder.binop(BinaryOp::Add, body_i, one, ScalarType::U64);

        if until {
            // result is a Continue/Break tag union (single RcPtr,
            // since tag unions don't decompose in this phase). The
            // payload IS the acc (multi-slot) stored after the tag.
            self.emit_walk_until_branch(
                result,
                next_i,
                &body_acc,
                body_end,
                body_step,
                done,
                header,
                &acc_slots,
                acc_ty,
            );
        } else {
            let mut jump_args = Vec::with_capacity(2 + result.len() + 2);
            jump_args.push(next_i);
            jump_args.extend(result.iter().copied());
            jump_args.push(body_end);
            jump_args.push(body_step);
            self.builder.jump(header, jump_args);
        }

        self.builder.switch_to(done);
        LoweredValue::from_slots(done_params)
    }

    pub(super) fn lower_list_walk(
        &mut self,
        list_val: Value,
        init_vals: Vec<Value>,
        step_val: Value,
        apply_name: &str,
        until: bool,
        acc_slots: Vec<ScalarType>,
        acc_ty: &Type,
        elem_ty: &Type,
        direct: Option<&SingletonTarget>,
    ) -> LoweredValue {
        let len_val = self.builder.load(list_val, 0, ScalarType::U64);
        let data_ptr = self.builder.load(list_val, 16, ScalarType::RcPtr);
        let step_ty = step_val.ty;

        let header = self.builder.create_block();
        let i_param = self.builder.add_block_param(header, ScalarType::U64);
        let acc_params: Vec<Value> = acc_slots.iter()
            .map(|&ty| self.builder.add_block_param(header, ty))
            .collect();
        let len_param = self.builder.add_block_param(header, ScalarType::U64);
        let data_param = self.builder.add_block_param(header, ScalarType::RcPtr);
        let step_param = self.builder.add_block_param(header, step_ty);
        let body_block = self.builder.create_block();
        let body_i = self.builder.add_block_param(body_block, ScalarType::U64);
        let body_acc: Vec<Value> = acc_slots.iter()
            .map(|&ty| self.builder.add_block_param(body_block, ty))
            .collect();
        let body_len = self.builder.add_block_param(body_block, ScalarType::U64);
        let body_data = self.builder.add_block_param(body_block, ScalarType::RcPtr);
        let body_step = self.builder.add_block_param(body_block, step_ty);
        let done = self.builder.create_block();
        let done_params: Vec<Value> = acc_slots.iter()
            .map(|&ty| self.builder.add_block_param(done, ty))
            .collect();
        let _done_data = self.builder.add_block_param(done, ScalarType::RcPtr);
        let _done_step = self.builder.add_block_param(done, step_ty);

        let zero = self.builder.const_u64(0);
        let mut entry_args = Vec::with_capacity(2 + acc_slots.len() + 3);
        entry_args.push(zero);
        entry_args.extend(init_vals.iter().copied());
        entry_args.push(len_val);
        entry_args.push(data_ptr);
        entry_args.push(step_val);
        self.builder.jump(header, entry_args);

        self.builder.switch_to(header);
        let cmp = self.builder.binop(BinaryOp::Eq, i_param, len_param, ScalarType::U8);
        let mut done_args = acc_params.clone();
        done_args.push(data_param);
        done_args.push(step_param);
        let mut body_args = Vec::with_capacity(2 + acc_slots.len() + 3);
        body_args.push(i_param);
        body_args.extend(acc_params.iter().copied());
        body_args.push(len_param);
        body_args.push(data_param);
        body_args.push(step_param);
        self.builder.branch(cmp, done, done_args, body_block, body_args);

        self.builder.switch_to(body_block);
        // Load element slots from the data buffer. For aggregate
        // elements under D1, the buffer stores N slots back-to-back
        // per element; we emit explicit byte-math to pick each slot.
        // For scalar / heap-pointer elements, the legacy 8-byte
        // stride applies — single load.
        let elem_vals = if self.element_is_inlined(elem_ty) {
            let stride = self.element_stride(elem_ty);
            let stride_units = (stride / 8) as u64;
            let stride_const = self.builder.const_u64(stride_units);
            let unit_base = self.builder.binop(BinaryOp::Mul, body_i, stride_const, ScalarType::U64);
            let slot_tys = self.expand_slots(elem_ty);
            slot_tys.iter().enumerate().map(|(j, &ty)| {
                let off_const = self.builder.const_u64(j as u64);
                let idx = self.builder.binop(BinaryOp::Add, unit_base, off_const, ScalarType::U64);
                self.builder.load_dyn(body_data, idx, ty)
            }).collect::<Vec<_>>()
        } else {
            vec![self.builder.load_dyn(body_data, body_i, ScalarType::RcPtr)]
        };
        let result = self.emit_walk_step_call(direct, apply_name, body_step, &body_acc, elem_vals, elem_ty, &acc_slots);

        let one = self.builder.const_u64(1);
        let next_i = self.builder.binop(BinaryOp::Add, body_i, one, ScalarType::U64);

        if until {
            self.emit_walk_until_branch_with_data(
                result,
                next_i,
                &body_acc,
                body_len,
                body_data,
                body_step,
                done,
                header,
                &acc_slots,
                acc_ty,
            );
        } else {
            let mut jump_args = Vec::with_capacity(2 + result.len() + 3);
            jump_args.push(next_i);
            jump_args.extend(result.iter().copied());
            jump_args.push(body_len);
            jump_args.push(body_data);
            jump_args.push(body_step);
            self.builder.jump(header, jump_args);
        }

        self.builder.switch_to(done);
        LoweredValue::from_slots(done_params)
    }

    /// Emit the apply call inside a walk's body block. Caller is
    /// responsible for loading the element's slots (D1 inline
    /// layouts mean a multi-slot load per aggregate element).
    fn emit_walk_step_call(
        &mut self,
        direct: Option<&SingletonTarget>,
        apply_name: &str,
        body_step: Value,
        body_acc: &[Value],
        elem_vals: Vec<Value>,
        _elem_ty: &Type,
        _acc_slots: &[ScalarType],
    ) -> Vec<Value> {

        let resolved = direct.or_else(|| self.singletons.get(apply_name));
        if let Some(st) = resolved {
            let target_param_slots = self.callee_param_slots(&st.target_func, body_acc.len() + elem_vals.len() + st.num_captures);
            let target_param_types = self.callee_param_types(&st.target_func);
            let mut call_args = Vec::with_capacity(st.num_captures + body_acc.len() + elem_vals.len());
            // A closure with N source-level captures is a non-
            // fieldless tag union with one variant whose payload
            // heap object stores the N captures at offsets 0, 8,
            // 16, ... The materialized closure record is the tag
            // union shell: `tag@0`, `payload_ptr@8`. Fieldless
            // closures (0 captures) are bare discriminant
            // integers — no payload to load.
            if st.num_captures > 0 {
                let payload_ptr = self.builder.load(body_step, 8, ScalarType::RcPtr);
                for i in 0..st.num_captures {
                    let slots: &[ScalarType] = target_param_slots
                        .get(i)
                        .map(|v| v.as_slice())
                        .unwrap_or(&[ScalarType::RcPtr]);
                    let single_load_ty = if slots.len() == 1 { slots[0] } else { ScalarType::RcPtr };
                    let v = self.builder.load(payload_ptr, i * 8, single_load_ty);
                    if slots.len() > 1 {
                        let cap_ty = target_param_types
                            .get(i)
                            .cloned()
                            .unwrap_or_else(|| Type::Con("__none".to_owned()));
                        let expanded = self.to_slots(
                            super::lowered_value::LoweredValue::single(v),
                            &cap_ty,
                            slots,
                        );
                        call_args.extend(expanded);
                    } else {
                        call_args.push(v);
                    }
                }
            }
            call_args.extend(body_acc.iter().copied());
            call_args.extend(elem_vals);
            let ret_slots = self.callee_return_slots(&st.target_func);
            if ret_slots.len() == 1 {
                vec![self.builder.call(&st.target_func, call_args, ret_slots[0])]
            } else {
                self.builder.call_multi(&st.target_func, call_args, &ret_slots)
            }
        } else {
            let mut call_args = Vec::with_capacity(body_acc.len() + 1 + elem_vals.len());
            call_args.push(body_step);
            call_args.extend(body_acc.iter().copied());
            call_args.extend(elem_vals);
            let ret_slots = self.callee_return_slots(apply_name);
            if ret_slots.len() == 1 {
                vec![self.builder.call(apply_name, call_args, ret_slots[0])]
            } else {
                self.builder.call_multi(apply_name, call_args, &ret_slots)
            }
        }
    }

    /// Extract `(tag, payload_ptr)` from a walk-step apply's result.
    /// With D2, apply returns 2 parallel slots directly; if the
    /// upstream apply hasn't been expanded yet (legacy path) we
    /// load the tag/payload pair from the materialized 16-byte shell.
    fn split_walk_result(&mut self, result: &[Value]) -> (Value, Value) {
        if result.len() == 2 {
            return (result[0], result[1]);
        }
        debug_assert_eq!(
            result.len(),
            1,
            "walk_until apply result has unexpected slot count {}",
            result.len()
        );
        let r = result[0];
        let tag = self.builder.load(r, 0, ScalarType::U64);
        let payload_ptr = self.builder.load(r, 8, ScalarType::RcPtr);
        (tag, payload_ptr)
    }

    /// Load the acc out of a Continue/Break tag-union's payload heap
    /// object. The payload's first field is the source-level acc; if
    /// the acc is multi-slot, that field stores the materialized acc
    /// ptr which we then unmaterialize.
    fn load_walk_acc_payload(&mut self, payload_ptr: Value, acc_slots: &[ScalarType], acc_ty: &Type) -> Vec<Value> {
        if acc_slots.len() == 1 {
            return vec![self.builder.load(payload_ptr, 0, acc_slots[0])];
        }
        let materialized_acc = self.builder.load(payload_ptr, 0, ScalarType::RcPtr);
        self.to_slots(
            super::lowered_value::LoweredValue::single(materialized_acc),
            acc_ty,
            acc_slots,
        )
    }

    /// walk_until branch (range version). `result` is a single RcPtr
    /// pointing at a Continue/Break tag union whose payload is the
    /// (multi-slot) acc.
    #[allow(clippy::too_many_arguments)]
    fn emit_walk_until_branch(
        &mut self,
        result: Vec<Value>,
        next_i: Value,
        body_acc: &[Value],
        body_end: Value,
        body_step: Value,
        done: crate::ssa::instruction::BlockId,
        header: crate::ssa::instruction::BlockId,
        acc_slots: &[ScalarType],
        acc_ty: &Type,
    ) {
        // D2: apply's tag-union return is `Multi(tag, payload_ptr)`
        // — 2 slots. Older single-slot return falls back to loading
        // tag/payload from the materialized 16-byte shell.
        let (tag, payload_ptr) = self.split_walk_result(&result);
        let payload = self.load_walk_acc_payload(payload_ptr, acc_slots, acc_ty);
        let _ = body_acc;
        let break_tag = self.decls.constructors["Break"].tag_index;
        let break_val = self.builder.const_u64(break_tag);
        let is_break = self.builder.binop(BinaryOp::Eq, tag, break_val, ScalarType::U8);
        let mut done_args = payload.clone();
        done_args.push(body_step);
        let mut header_args = Vec::with_capacity(2 + payload.len() + 2);
        header_args.push(next_i);
        header_args.extend(payload.iter().copied());
        header_args.push(body_end);
        header_args.push(body_step);
        self.builder.branch(is_break, done, done_args, header, header_args);
    }

    /// walk_until branch (list version) — same as range except the
    /// header threads `data` as well.
    #[allow(clippy::too_many_arguments)]
    fn emit_walk_until_branch_with_data(
        &mut self,
        result: Vec<Value>,
        next_i: Value,
        body_acc: &[Value],
        body_len: Value,
        body_data: Value,
        body_step: Value,
        done: crate::ssa::instruction::BlockId,
        header: crate::ssa::instruction::BlockId,
        acc_slots: &[ScalarType],
        acc_ty: &Type,
    ) {
        let (tag, payload_ptr) = self.split_walk_result(&result);
        let payload = self.load_walk_acc_payload(payload_ptr, acc_slots, acc_ty);
        let _ = body_acc;
        let break_tag = self.decls.constructors["Break"].tag_index;
        let break_val = self.builder.const_u64(break_tag);
        let is_break = self.builder.binop(BinaryOp::Eq, tag, break_val, ScalarType::U8);
        let mut done_args = payload.clone();
        done_args.push(body_data);
        done_args.push(body_step);
        let mut header_args = Vec::with_capacity(2 + payload.len() + 3);
        header_args.push(next_i);
        header_args.extend(payload.iter().copied());
        header_args.push(body_len);
        header_args.push(body_data);
        header_args.push(body_step);
        self.builder.branch(is_break, done, done_args, header, header_args);
    }
}
