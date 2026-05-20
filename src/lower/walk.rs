//! Lowering for `List.walk` / `List.walk_until` / `List.range` style
//! reductions. Each emits an explicit SSA loop (header / body / done
//! blocks) with the accumulator threaded through block params — no
//! intermediate list allocation needed for `range`-driven walks.

use crate::ast::{Expr, ExprKind};
use crate::passes::lambda_specialize::SingletonTarget;
use crate::ssa::Value;
use crate::ssa::instruction::{BinaryOp, ScalarType};
use crate::types::engine::Type;

use super::LowerCtx;

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
/// function's full `Arrow` type so specialized walks get their own
/// per-type apply dispatchers. `List.walk` is an intrinsic (no body
/// to monomorphize), so without this all walks would share a single
/// apply with type-incoherent arm returns.
pub fn walk_apply_name(callee: &str, step_ty: &Type) -> String {
    let mut key = callee.to_owned();
    key.push_str("__");
    crate::passes::mono::append_type_mangling(&mut key, step_ty);
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

    /// Emit a range-walk loop: counter from start to end, no list allocation.
    pub(super) fn lower_range_walk(
        &mut self,
        start: Value,
        end: Value,
        init_val: Value,
        step_val: Value,
        apply_name: &str,
        until: bool,
        acc_ty: ScalarType,
        direct: Option<&SingletonTarget>,
    ) -> Value {
        let step_ty = step_val.ty;

        let header = self.builder.create_block();
        let i_param = self.builder.add_block_param(header, ScalarType::U64);
        let acc_param = self.builder.add_block_param(header, acc_ty);
        let end_param = self.builder.add_block_param(header, ScalarType::U64);
        let step_param = self.builder.add_block_param(header, step_ty);
        let body_block = self.builder.create_block();
        let body_i = self.builder.add_block_param(body_block, ScalarType::U64);
        let body_acc = self.builder.add_block_param(body_block, acc_ty);
        let body_end = self.builder.add_block_param(body_block, ScalarType::U64);
        let body_step = self.builder.add_block_param(body_block, step_ty);
        let done = self.builder.create_block();
        let done_param = self.builder.add_block_param(done, acc_ty);

        self.builder.jump(header, vec![start, init_val, end, step_val]);

        self.builder.switch_to(header);
        let cmp = self.builder.binop(BinaryOp::Eq, i_param, end_param, ScalarType::U8);
        self.builder.branch(cmp, done, vec![acc_param], body_block, vec![i_param, acc_param, end_param, step_param]);

        self.builder.switch_to(body_block);
        // The element IS the counter — no list load needed.
        let elem = body_i;
        let resolved = direct.or_else(|| self.singletons.get(apply_name));
        let result = if let Some(st) = resolved {
            let mut call_args = Vec::with_capacity(st.num_captures + 2);
            for i in 0..st.num_captures {
                call_args.push(self.builder.load(body_step, (i + 1) * 8, ScalarType::RcPtr));
            }
            call_args.push(body_acc);
            call_args.push(elem);
            let ret_ty = self.func_ret_type(&st.target_func);
            self.builder.call(&st.target_func, call_args, ret_ty)
        } else {
            let ret_ty = self.func_ret_type(apply_name);
            self.builder.call(apply_name, vec![body_step, body_acc, elem], ret_ty)
        };

        let one = self.builder.const_u64(1);
        let next_i = self.builder.binop(BinaryOp::Add, body_i, one, ScalarType::U64);

        if until {
            let tag = self.builder.load(result, 0, ScalarType::U64);
            let payload_load_ty = acc_ty;
            let payload = self.builder.load(result, 8, payload_load_ty);
            let break_tag = self.decls.constructors["Break"].tag_index;
            let break_val = self.builder.const_u64(break_tag);
            let is_break = self.builder.binop(BinaryOp::Eq, tag, break_val, ScalarType::U8);
            self.builder.branch(is_break, done, vec![payload], header, vec![next_i, payload, body_end, body_step]);
        } else {
            self.builder.jump(header, vec![next_i, result, body_end, body_step]);
        }

        self.builder.switch_to(done);
        done_param
    }

    pub(super) fn lower_list_walk(
        &mut self,
        list_val: Value,
        init_val: Value,
        step_val: Value,
        apply_name: &str,
        until: bool,
        acc_ty: ScalarType,
        direct: Option<&SingletonTarget>,
    ) -> Value {
        let len_val = self.builder.load(list_val, 0, ScalarType::U64);
        let data_ptr = self.builder.load(list_val, 16, ScalarType::RcPtr);
        let step_ty = step_val.ty;

        let header = self.builder.create_block();
        let i_param = self.builder.add_block_param(header, ScalarType::U64);
        let acc_param = self.builder.add_block_param(header, acc_ty);
        let len_param = self.builder.add_block_param(header, ScalarType::U64);
        let data_param = self.builder.add_block_param(header, ScalarType::RcPtr);
        let step_param = self.builder.add_block_param(header, step_ty);
        let body_block = self.builder.create_block();
        let body_i = self.builder.add_block_param(body_block, ScalarType::U64);
        let body_acc = self.builder.add_block_param(body_block, acc_ty);
        let body_len = self.builder.add_block_param(body_block, ScalarType::U64);
        let body_data = self.builder.add_block_param(body_block, ScalarType::RcPtr);
        let body_step = self.builder.add_block_param(body_block, step_ty);
        let done = self.builder.create_block();
        let done_param = self.builder.add_block_param(done, acc_ty);

        let zero = self.builder.const_u64(0);
        self.builder.jump(header, vec![zero, init_val, len_val, data_ptr, step_val]);

        self.builder.switch_to(header);
        let cmp = self
            .builder
            .binop(BinaryOp::Eq, i_param, len_param, ScalarType::U8);
        self.builder
            .branch(cmp, done, vec![acc_param], body_block, vec![i_param, acc_param, len_param, data_param, step_param]);

        self.builder.switch_to(body_block);
        let elem = self.builder.load_dyn(body_data, body_i, ScalarType::RcPtr);
        let resolved = direct.or_else(|| self.singletons.get(apply_name));
        let result = if let Some(st) = resolved {
            let mut call_args = Vec::with_capacity(st.num_captures + 2);
            for i in 0..st.num_captures {
                call_args.push(self.builder.load(body_step, (i + 1) * 8, ScalarType::RcPtr));
            }
            call_args.push(body_acc);
            call_args.push(elem);
            let ret_ty = self.func_ret_type(&st.target_func);
            self.builder.call(&st.target_func, call_args, ret_ty)
        } else {
            let ret_ty = self.func_ret_type(apply_name);
            self.builder.call(apply_name, vec![body_step, body_acc, elem], ret_ty)
        };

        let one = self.builder.const_u64(1);
        let next_i = self
            .builder
            .binop(BinaryOp::Add, body_i, one, ScalarType::U64);

        if until {
            let tag = self.builder.load(result, 0, ScalarType::U64);
            let payload_load_ty = acc_ty;
            let payload = self.builder.load(result, 8, payload_load_ty);
            let break_tag = self.decls.constructors["Break"].tag_index;
            let break_val = self.builder.const_u64(break_tag);
            let is_break = self
                .builder
                .binop(BinaryOp::Eq, tag, break_val, ScalarType::U8);
            self.builder
                .branch(is_break, done, vec![payload], header, vec![next_i, payload, body_len, body_data, body_step]);
        } else {
            self.builder.jump(header, vec![next_i, result, body_len, body_data, body_step]);
        }

        self.builder.switch_to(done);
        done_param
    }
}
