//! Pattern lowering: match expressions, destructure bindings,
//! literal-match dispatch, and the boolean-if-with-Is special case.
//!
//! `lower_match` is the workhorse — compiles a sequence of arms
//! with possible guards into a switch on the tag plus per-arm
//! branches. The literal-match path (`lower_literal_match`) is a
//! specialization for `match n { 0 -> ..., 1 -> ..., else -> ... }`
//! that emits a SwitchInt directly.
//!
//! `lower_destructure` handles `let (a, b) = pair` and
//! `let { x, y } = record` bindings.

use crate::ast::{self, Expr, ExprKind};
use crate::ssa::Value;
use crate::ssa::instruction::{BinaryOp, BlockId, ScalarType};
use crate::types::engine::Type;

use super::LowerCtx;

impl<'a, 'src> LowerCtx<'a, 'src> {
    // ---- Boolean if-then-else with Is binding flow ----

    /// Check if this is a boolean if-then-else (True/False arms) where the
    /// scrutinee contains Is expressions that need binding flow.
    pub(super) fn is_bool_if_with_is(scrutinee: &Expr<'src>, arms: &[ast::MatchArm<'src>]) -> bool {
        if arms.len() != 2 {
            return false;
        }
        let is_true_false = matches!(
            (&arms[0].pattern, &arms[1].pattern),
            (
                ast::Pattern::Constructor { name: "True", .. },
                ast::Pattern::Constructor { name: "False", .. }
            )
        );
        if !is_true_false {
            return false;
        }
        Self::expr_contains_is(scrutinee)
    }

    /// Check if an expression tree contains any Is expression.
    pub(super) fn expr_contains_is(expr: &Expr<'src>) -> bool {
        match &expr.kind {
            ExprKind::Is { .. } => true,
            ExprKind::BinOp { lhs, rhs, .. } => {
                Self::expr_contains_is(lhs) || Self::expr_contains_is(rhs)
            }
            _ => false,
        }
    }

    /// Lower a boolean if-then-else where the scrutinee contains Is expressions,
    /// flowing bindings from the scrutinee into the True arm body.
    pub(super) fn lower_bool_if_with_is(
        &mut self,
        scrutinee: &Expr<'src>,
        arms: &[ast::MatchArm<'src>],
        result_ty: ScalarType,
    ) -> Value {
        let merge = self.builder.create_block();
        let merge_param = self.builder.add_block_param(merge, result_ty);
        let false_block = self.builder.create_block();

        let saved_vars = self.vars.clone();

        // Use and-chain lowering for the scrutinee — bindings flow into self.vars
        self.lower_and_chain(scrutinee, false_block, &[]);

        // True arm: bindings from Is are in scope
        let true_result = self.lower_expr(&arms[0].body);
        if arms[0].is_return {
            self.builder.ret(true_result);
        } else {
            self.builder.jump(merge, vec![true_result]);
        }

        // False arm
        self.builder.switch_to(false_block);
        self.vars = saved_vars;
        let false_result = self.lower_expr(&arms[1].body);
        if arms[1].is_return {
            self.builder.ret(false_result);
        } else {
            self.builder.jump(merge, vec![false_result]);
        }

        self.builder.switch_to(merge);
        merge_param
    }

    // ---- Match/fold shared helpers ----

    /// Group match arms by the tag index of their top-level
    /// constructor pattern. `scrutinee_ty` provides the context
    /// needed to compute tag indices for structural constructors
    /// (which aren't in `decl_info.constructors`).
    pub(super) fn group_arms_by_tag(
        &self,
        arms: &[ast::MatchArm<'src>],
        scrutinee_ty: &Type,
    ) -> Vec<(u64, Vec<usize>)> {
        let mut groups: Vec<(u64, Vec<usize>)> = Vec::new();
        for (i, arm) in arms.iter().enumerate() {
            let ast::Pattern::Constructor { name: con_name, .. } = &arm.pattern else {
                panic!("arms must use constructor patterns");
            };
            let (tag_idx, _, _) = self.con_layout(con_name, Some(scrutinee_ty));
            if let Some(group) = groups.iter_mut().find(|(t, _)| *t == tag_idx) {
                group.1.push(i);
            } else {
                groups.push((tag_idx, vec![i]));
            }
        }
        groups
    }

    pub(super) fn lower_guards(
        &mut self,
        guards: &[Expr<'src>],
        arm_idx: usize,
        tag_idx: u64,
        tag_groups: &[(u64, Vec<usize>)],
        arm_blocks: &[BlockId],
        default_fail: BlockId,
        fail_args: &[Value],
    ) {
        let group = &tag_groups.iter().find(|(t, _)| *t == tag_idx).unwrap().1;
        let pos_in_group = group.iter().position(|&idx| idx == arm_idx).unwrap();
        let (fail_target, target_args) = if pos_in_group + 1 < group.len() {
            (arm_blocks[group[pos_in_group + 1]], fail_args.to_vec())
        } else {
            (default_fail, vec![])
        };

        // Route every guard through `lower_and_chain` so that any `is`
        // expressions embedded in the guard (e.g. from
        // `flatten_patterns` hoisting nested constructor fields) bind
        // their fields into `self.vars` before the arm body lowers.
        // Plain boolean guards fall through to the chain's generic
        // branch-on-True path. Fall-through to the next arm in the
        // same tag group is wired via `fail_target`.
        for guard_expr in guards {
            self.lower_and_chain(guard_expr, fail_target, &target_args);
        }
    }

    // ---- Literal match lowering ----

    /// True if every arm's pattern is `IntLit` or `StrLit`.
    pub(super) fn is_literal_match(arms: &[ast::MatchArm<'_>]) -> bool {
        arms.iter().all(|arm| {
            matches!(
                arm.pattern,
                ast::Pattern::IntLit(_) | ast::Pattern::StrLit(_)
            )
        })
    }

    /// Lower a match on literal patterns as a chain of equality checks.
    /// Each arm becomes `if scrutinee == literal then body else next_arm`.
    pub(super) fn lower_literal_match(
        &mut self,
        scrutinee_expr: &Expr<'src>,
        arms: &[ast::MatchArm<'src>],
        else_body: Option<&Expr<'src>>,
        result_ty: ScalarType,
    ) -> Value {
        let scr_val = self.lower_expr(scrutinee_expr);
        let scr_ty = self.expr_scalar_type(scrutinee_expr);
        let scr_is_func_param = self.builder.func.params.contains(&scr_val);
        let merge = self.builder.create_block();
        let merge_param = self.builder.add_block_param(merge, result_ty);

        // Cache `__eq__Str` once if any arm is a string-literal —
        // generating the same recursive equality helper per arm
        // would be redundant.
        let str_eq_fn: Option<String> = if arms
            .iter()
            .any(|a| matches!(a.pattern, ast::Pattern::StrLit(_)))
        {
            Some(self.ensure_eq_func(&scrutinee_expr.ty))
        } else {
            None
        };

        let mut current_scr = scr_val;
        for arm in arms {
            let next_block = self.builder.create_block();
            let next_scr_param = if scr_is_func_param {
                scr_val // function params don't need threading
            } else {
                self.builder.add_block_param(next_block, scr_ty)
            };
            let body_block = self.builder.create_block();
            let eq = match &arm.pattern {
                ast::Pattern::IntLit(n) => {
                    let lit_val = match scr_ty {
                        ScalarType::I8 => self.builder.const_i8(*n as i8),
                        ScalarType::U8 => self.builder.const_u8(*n as u8),
                        ScalarType::I16 => self.builder.const_i16(*n as i16),
                        ScalarType::U16 => self.builder.const_u16(*n as u16),
                        ScalarType::I32 => self.builder.const_i32(*n as i32),
                        ScalarType::U32 => self.builder.const_u32(*n as u32),
                        ScalarType::U64 => self.builder.const_u64(*n as u64),
                        _ => self.builder.const_i64(*n),
                    };
                    self.builder
                        .binop(BinaryOp::Eq, current_scr, lit_val, ScalarType::U8)
                }
                ast::Pattern::StrLit(bytes) => {
                    // Str is List(U8) — pointer-equality (BinOp::Eq)
                    // would compare List header addresses. Use the
                    // generic structural equality helper instead.
                    let lit_val = self.lower_str_literal(bytes);
                    let eq_name = str_eq_fn.as_ref().expect("str eq fn cached above");
                    self.builder
                        .call(eq_name, vec![current_scr, lit_val], ScalarType::U8)
                }
                _ => unreachable!(),
            };
            let next_args = if scr_is_func_param { vec![] } else { vec![current_scr] };
            self.builder.branch(eq, body_block, vec![], next_block, next_args);

            self.builder.switch_to(body_block);
            let body_val = self.lower_expr(&arm.body);
            self.builder.jump(merge, vec![body_val]);

            self.builder.switch_to(next_block);
            current_scr = next_scr_param;
        }

        // Else / unreachable fallthrough
        if let Some(eb) = else_body {
            let else_val = self.lower_expr(eb);
            self.builder.jump(merge, vec![else_val]);
        } else {
            // No else — unreachable. Jump with a dummy value of the
            // right type so the merge param types stay honest.
            let dummy = self.dummy_of(result_ty);
            self.builder.jump(merge, vec![dummy]);
        }

        self.builder.switch_to(merge);
        merge_param
    }

    // ---- Match lowering ----

    pub(super) fn lower_match(
        &mut self,
        scrutinee_expr: &Expr<'src>,
        arms: &[ast::MatchArm<'src>],
        else_body: Option<&Expr<'src>>,
        result_ty: ScalarType,
    ) -> Value {
        let scrutinee_ty = scrutinee_expr.ty.clone();
        let scr_val = self.lower_expr(scrutinee_expr);
        // Determine fieldless from the first constructor's layout — more
        // reliable than `is_fieldless_type` since synthesized expressions
        // (apply functions) may have placeholder types.
        let first_con_name = match &arms[0].pattern {
            ast::Pattern::Constructor { name, .. } => *name,
            _ => panic!("match arms must use constructor patterns"),
        };
        let (_, first_max, _) = self.con_layout(first_con_name, Some(&scrutinee_ty));
        let fieldless = first_max == 0;
        let tag = if fieldless {
            scr_val // already the discriminant
        } else {
            self.builder.load(scr_val, 0, ScalarType::U64)
        };
        let tag_block = self.builder.current_block.unwrap();

        // Thread scr_val through block params only when it's NOT a
        // function param (function params are always accessible).
        let scr_is_func_param = self.builder.func.params.contains(&scr_val);
        let scr_val_ty = scr_val.ty;
        let merge = self.builder.create_block();
        let merge_param = self.builder.add_block_param(merge, result_ty);
        let else_block = else_body.map(|_| self.builder.create_block());
        let arm_blocks: Vec<_> = arms.iter().map(|_| self.builder.create_block()).collect();
        let arm_scr_params: Vec<_> = if scr_is_func_param {
            vec![]
        } else {
            arm_blocks.iter().map(|&b| self.builder.add_block_param(b, scr_val_ty)).collect()
        };
        let tag_groups = self.group_arms_by_tag(arms, &scrutinee_ty);

        let switch_args = if scr_is_func_param { vec![] } else { vec![scr_val] };
        let switch_arms: Vec<_> = tag_groups
            .iter()
            .map(|(tag_idx, arm_indices)| (*tag_idx, arm_blocks[arm_indices[0]], switch_args.clone()))
            .collect();
        self.builder.switch_to(tag_block);
        self.builder
            .switch_int(tag, switch_arms, else_block.map(|b| (b, vec![])));

        // Dead-fallthrough sink: when there's no `else` body but some
        // arm has guards, the last guard-chain needs a well-typed
        // target to fall through to. That target is statically
        // unreachable (the match is exhaustive), but the IR still
        // needs a valid block with the right arg count to merge.
        // Created lazily since matches without guards don't need it.
        let mut unreachable_sink: Option<BlockId> = None;

        for (i, arm) in arms.iter().enumerate() {
            let ast::Pattern::Constructor {
                name: con_name,
                fields,
            } = &arm.pattern
            else {
                panic!("match arms must use constructor patterns");
            };
            self.builder.switch_to(arm_blocks[i]);
            let arm_scr = if scr_is_func_param {
                scr_val
            } else {
                arm_scr_params[i]
            };

            let (arm_tag_idx, _, field_types) =
                self.con_layout(con_name, Some(&scrutinee_ty));
            let saved_vars = self.vars.clone();

            if !fieldless {
                for (fi, field_pat) in fields.iter().enumerate() {
                    let field_ty = field_types.get(fi).copied().unwrap_or(ScalarType::RcPtr);
                    let field_val = self.builder.load(arm_scr, (fi + 1) * 8, field_ty);
                    self.bind_pattern_field(field_pat, field_val);
                }
            }

            if !arm.guards.is_empty() {
                let default_fail = if let Some(eb) = else_block {
                    eb
                } else {
                    *unreachable_sink.get_or_insert_with(|| {
                        let saved = self.builder.current_block;
                        let sink = self.builder.create_block();
                        self.builder.switch_to(sink);
                        let dummy = self.dummy_of(result_ty);
                        self.builder.jump(merge, vec![dummy]);
                        self.builder.current_block = saved;
                        sink
                    })
                };
                let guard_fail_args = if scr_is_func_param { vec![] } else { vec![arm_scr] };
                self.lower_guards(
                    &arm.guards,
                    i,
                    arm_tag_idx,
                    &tag_groups,
                    &arm_blocks,
                    default_fail,
                    &guard_fail_args,
                );
            }

            let result = self.lower_expr(&arm.body);
            if arm.is_return {
                self.builder.ret(result);
            } else {
                self.builder.jump(merge, vec![result]);
            }

            self.vars = saved_vars;
        }

        if let (Some(else_block_id), Some(else_expr)) = (else_block, else_body) {
            self.builder.switch_to(else_block_id);
            let else_val = self.lower_expr(else_expr);
            self.builder.jump(merge, vec![else_val]);
        }

        self.builder.switch_to(merge);
        merge_param
    }

    pub(super) fn bind_pattern_field(&mut self, pat: &ast::Pattern<'src>, val: Value) {
        match pat {
            ast::Pattern::Binding(sym) => {
                self.vars.insert(*sym, super::lowered_value::LoweredValue::single(val));
            }
            ast::Pattern::Wildcard | ast::Pattern::IntLit(_) | ast::Pattern::StrLit(_) => {}
            _ => panic!("unsupported nested pattern in match arm field"),
        }
    }

    /// Detect `List.range(a, b)` as the receiver/list expression.
    /// Returns lowered (start, end) Values if matched.
    /// Detect `List.range(a, b)` as the list expression in a walk.

    // ---- Destructure lowering ----

    /// Decomposed-aware destructure: when the source is `Multi`, bind
    /// each pattern field directly to the slot Value without going
    /// through Load. When the source is `Single` (heap ptr), fall back
    /// to the existing Load-based path.
    pub(super) fn lower_destructure_lv(
        &mut self,
        pattern: &ast::Pattern<'src>,
        val: super::lowered_value::LoweredValue,
        val_ty: &Type,
    ) {
        if let super::lowered_value::LoweredValue::Multi(vs) = val {
            self.bind_decomposed(pattern, &vs, val_ty);
            return;
        }
        let v = self.materialize(val);
        self.lower_destructure(pattern, v, val_ty);
    }

    /// Bind a tuple/record pattern's elements directly to the
    /// already-decomposed slot Values. Mirrors `lower_destructure`'s
    /// shape but with no Load instructions.
    pub(super) fn bind_decomposed(
        &mut self,
        pattern: &ast::Pattern<'src>,
        slot_vals: &[Value],
        val_ty: &Type,
    ) {
        match pattern {
            ast::Pattern::Tuple(elems) => {
                for (i, elem) in elems.iter().enumerate() {
                    let v = slot_vals[i];
                    self.lower_destructure_elem(elem, v);
                }
            }
            ast::Pattern::Record { fields, .. } => {
                let all_names: Vec<&str> = match val_ty {
                    Type::Record { fields: type_fields, .. } => {
                        let mut names: Vec<&str> =
                            type_fields.iter().map(|(n, _)| n.as_str()).collect();
                        names.sort_unstable();
                        names
                    }
                    _ => {
                        let mut names: Vec<&str> = fields
                            .iter()
                            .map(|(sym, _)| self.fields.get(*sym))
                            .collect();
                        names.sort_unstable();
                        names
                    }
                };
                for (field_sym, elem) in fields {
                    let name = self.fields.get(*field_sym);
                    let slot = all_names.iter().position(|n| *n == name).unwrap();
                    let v = slot_vals[slot];
                    self.lower_destructure_elem(elem, v);
                }
            }
            _ => panic!("expected tuple or record pattern in decomposed destructure"),
        }
    }

    pub(super) fn lower_destructure(
        &mut self,
        pattern: &ast::Pattern<'src>,
        val: Value,
        val_ty: &Type,
    ) {
        match pattern {
            ast::Pattern::Tuple(elems) => {
                let elem_types = match val_ty {
                    Type::Tuple(tys) => tys.as_slice(),
                    other => {
                        eprintln!("BUG: tuple destructure got val_ty={other:?} (fn={})",
                            self.current_fn_name);
                        &[]
                    }
                };
                for (i, elem) in elems.iter().enumerate() {
                    let ty = elem_types
                        .get(i)
                        .map(|t| self.scalar_type(t))
                        .unwrap_or(ScalarType::RcPtr);
                    let field_val = self.builder.load(val, i * 8, ty);
                    self.lower_destructure_elem(elem, field_val);
                }
            }
            ast::Pattern::Record { fields, .. } => {
                // Get ALL field names from the record TYPE (not just the
                // pattern fields) to compute correct slot indices. The
                // pattern may use `..` to ignore some fields.
                let all_names: Vec<&str> = match val_ty {
                    Type::Record {
                        fields: type_fields,
                        ..
                    } => {
                        let mut names: Vec<&str> =
                            type_fields.iter().map(|(n, _)| n.as_str()).collect();
                        names.sort_unstable();
                        names
                    }
                    _ => {
                        // Fallback: use pattern field names (old behavior).
                        let mut names: Vec<&str> = fields
                            .iter()
                            .map(|(sym, _)| self.fields.get(*sym))
                            .collect();
                        names.sort_unstable();
                        names
                    }
                };
                let type_fields: Vec<(&str, &Type)> = match val_ty {
                    Type::Record { fields: tf, .. } => {
                        let mut sorted: Vec<(&str, &Type)> =
                            tf.iter().map(|(n, t)| (n.as_str(), t)).collect();
                        sorted.sort_unstable_by_key(|(n, _)| *n);
                        sorted
                    }
                    _ => vec![],
                };
                for (field_sym, elem) in fields {
                    let name = self.fields.get(*field_sym);
                    let slot = all_names.iter().position(|n| *n == name).unwrap();
                    let ty = type_fields
                        .get(slot)
                        .map(|(_, t)| self.scalar_type(t))
                        .unwrap_or(ScalarType::RcPtr);
                    let field_val = self.builder.load(val, slot * 8, ty);
                    self.lower_destructure_elem(elem, field_val);
                }
            }
            _ => panic!("expected tuple or record pattern in destructure"),
        }
    }

    pub(super) fn lower_destructure_elem(&mut self, elem: &ast::Pattern<'src>, val: Value) {
        match elem {
            ast::Pattern::Binding(sym) => {
                self.vars.insert(*sym, super::lowered_value::LoweredValue::single(val));
            }
            ast::Pattern::Tuple(_) | ast::Pattern::Record { .. } => {
                // Nested destructure: use a dummy type (falls back to
                // pattern-field-only slot computation, which is correct
                // when the pattern names all fields).
                let dummy_ty = Type::Var(crate::types::engine::TypeVar(0));
                self.lower_destructure(elem, val, &dummy_ty);
            }
            ast::Pattern::Wildcard => {}
            _ => panic!("unsupported pattern in destructure"),
        }
    }
}
