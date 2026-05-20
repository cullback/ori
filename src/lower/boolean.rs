//! Boolean lowering: numeric comparisons (`<`, `>=`, etc.) coerce
//! to a `Bool` tagged-union value, `is` expressions destructure
//! and yield a bool, and `&&`/`||` short-circuit through control
//! flow.

use crate::ast::{self, BinOp, Expr, ExprKind};
use crate::ssa::Value;
use crate::ssa::instruction::{BinaryOp, BlockId, ScalarType};

use super::LowerCtx;

impl<'a, 'src> LowerCtx<'a, 'src> {
    pub(super) fn lower_cmp(&mut self, lhs: Value, rhs: Value, op: BinaryOp) -> Value {
        let cmp = self.builder.binop(op, lhs, rhs, ScalarType::U8);
        self.lower_bool_from_cmp(cmp)
    }

    pub(super) fn lower_bool_from_cmp(&mut self, cmp: Value) -> Value {
        self.lower_bool_from_cmp_neg(cmp, false)
    }

    pub(super) fn lower_bool_from_cmp_neg(&mut self, cmp: Value, negate: bool) -> Value {
        // Comparisons produce U8(0/1). Bool := [False, True] has
        // False=0, True=1. They're bit-identical — no conversion.
        debug_assert_eq!(self.decls.constructors["False"].tag_index, 0);
        debug_assert_eq!(self.decls.constructors["True"].tag_index, 1);
        if negate {
            let one = self.builder.const_u8(1);
            self.builder.binop(BinaryOp::Xor, cmp, one, ScalarType::U8)
        } else {
            cmp
        }
    }

    /// Lower a standalone `x is Pattern` expression (produces Bool, no binding flow).
    pub(super) fn lower_is_expr(&mut self, inner: &Expr<'src>, pattern: &ast::Pattern<'src>) -> Value {
        let inner_ty = inner.ty.clone();
        let scr = self.lower_expr(inner);
        match pattern {
            ast::Pattern::Constructor { name, .. } => {
                let (tag_index, max_fields, _) = self.con_layout(name, Some(&inner_ty));
                let fieldless = max_fields == 0;
                let tag = if fieldless {
                    scr
                } else {
                    self.builder.load(scr, 0, ScalarType::U64)
                };
                let disc_ty = if fieldless {
                    self.scalar_type(&inner_ty)
                } else {
                    ScalarType::U64
                };
                let expected_tag = self.const_tag(tag_index, disc_ty);
                let matches = self
                    .builder
                    .binop(BinaryOp::Eq, tag, expected_tag, ScalarType::U8);
                self.lower_bool_from_cmp(matches)
            }
            ast::Pattern::IntLit(n) => {
                let scr_ty = self.expr_scalar_type(inner);
                let lit_val = self.builder.const_i64(*n);
                let eq = self
                    .builder
                    .binop(BinaryOp::Eq, scr, lit_val, scr_ty);
                self.lower_bool_from_cmp(eq)
            }
            ast::Pattern::Wildcard | ast::Pattern::Binding(_) => {
                // Always matches — emit a declared Bool::True.
                self.lower_constructor_call("True", &[], None)
            }
            _ => panic!("unsupported pattern in `is` expression"),
        }
    }

    /// Lower `lhs and rhs` with fused Is-chain support (bindings flow from lhs into rhs).
    pub(super) fn lower_and_expr(&mut self, lhs: &Expr<'src>, rhs: &Expr<'src>) -> Value {
        let disc_ty = self.decls.fieldless_tags.get("Bool").copied().unwrap_or(ScalarType::U8);
        let merge = self.builder.create_block();
        let merge_param = self.builder.add_block_param(merge, disc_ty);
        let false_block = self.builder.create_block();

        let saved_vars = self.vars.clone();

        // Lower LHS chain — may emit branches to false_block, accumulating bindings
        self.lower_and_chain(lhs, false_block, &[]);

        // We're in the success path — all Is bindings from lhs are in scope
        let rhs_val = self.lower_expr(rhs);
        self.builder.jump(merge, vec![rhs_val]);

        // False block: produce False tag and jump to merge
        self.builder.switch_to(false_block);
        let false_tag_idx = self.decls.constructors["False"].tag_index;
        let false_val = self.const_tag(false_tag_idx, disc_ty);
        self.builder.jump(merge, vec![false_val]);

        self.vars = saved_vars;
        self.builder.switch_to(merge);
        merge_param
    }

    /// Recursively process an And chain, branching to `false_block` on failure
    /// and accumulating Is bindings in `self.vars` on success.
    pub(super) fn lower_and_chain(&mut self, expr: &Expr<'src>, false_block: BlockId, false_args: &[Value]) {
        match &expr.kind {
            ExprKind::Is {
                expr: inner,
                pattern,
            } => {
                let inner_ty = inner.ty.clone();
                let scr = self.lower_expr(inner);
                match pattern {
                    ast::Pattern::Constructor { name, fields } => {
                        let (tag_index, max_fields, field_types) =
                            self.con_layout(name, Some(&inner_ty));
                        let fieldless = max_fields == 0;
                        let tag = if fieldless {
                            scr // already the discriminant
                        } else {
                            self.builder.load(scr, 0, ScalarType::U64)
                        };
                        let disc_ty = if fieldless {
                            self.scalar_type(&inner_ty)
                        } else {
                            ScalarType::U64
                        };
                        let expected_tag = self.const_tag(tag_index, disc_ty);
                        let matches =
                            self.builder
                                .binop(BinaryOp::Eq, tag, expected_tag, ScalarType::U8);
                        let match_block = self.builder.create_block();
                        let scr_is_func_param = self.builder.func.params.contains(&scr);
                        let scr_in_match = if scr_is_func_param {
                            self.builder
                                .branch(matches, match_block, vec![], false_block, false_args.to_vec());
                            scr
                        } else {
                            let scr_ty = scr.ty;
                            let scr_param = self.builder.add_block_param(match_block, scr_ty);
                            self.builder
                                .branch(matches, match_block, vec![scr], false_block, false_args.to_vec());
                            scr_param
                        };
                        self.builder.switch_to(match_block);
                        // Bind pattern fields (empty for fieldless tags)
                        for (fi, field_pat) in fields.iter().enumerate() {
                            let field_ty =
                                field_types.get(fi).copied().unwrap_or(ScalarType::Ptr);
                            let field_val =
                                self.builder.load(scr_in_match, (fi + 1) * 8, field_ty);
                            self.bind_pattern_field(field_pat, field_val);
                        }
                    }
                    ast::Pattern::Binding(sym) => {
                        // Always matches, bind value
                        self.vars.insert(*sym, scr);
                    }
                    ast::Pattern::Wildcard => {
                        // Always matches, no binding
                    }
                    _ => panic!("unsupported pattern in `is` chain"),
                }
            }
            ExprKind::BinOp {
                op: BinOp::And,
                lhs,
                rhs,
            } => {
                // Process LHS first (may branch, accumulating bindings)
                self.lower_and_chain(lhs, false_block, false_args);
                // Then process RHS (we're in the LHS success path)
                self.lower_and_chain(rhs, false_block, false_args);
            }
            _ => {
                // Regular boolean expression — evaluate, compare unboxed tag, branch
                let val = self.lower_expr(expr);
                let disc_ty = self.decls.fieldless_tags.get("Bool").copied().unwrap_or(ScalarType::U8);
                let true_tag = self.decls.constructors["True"].tag_index;
                let true_val = self.const_tag(true_tag, disc_ty);
                let is_true = self
                    .builder
                    .binop(BinaryOp::Eq, val, true_val, ScalarType::U8);
                let continue_block = self.builder.create_block();
                self.builder
                    .branch(is_true, continue_block, vec![], false_block, false_args.to_vec());
                self.builder.switch_to(continue_block);
            }
        }
    }

    /// Lower `lhs or rhs` with short-circuit evaluation.
    pub(super) fn lower_or_expr(&mut self, lhs: &Expr<'src>, rhs: &Expr<'src>) -> Value {
        let disc_ty = self.decls.fieldless_tags.get("Bool").copied().unwrap_or(ScalarType::U8);
        let merge = self.builder.create_block();
        let merge_param = self.builder.add_block_param(merge, disc_ty);

        let lhs_val = self.lower_expr(lhs);
        let true_tag = self.decls.constructors["True"].tag_index;
        let true_val = self.const_tag(true_tag, disc_ty);
        let is_true = self
            .builder
            .binop(BinaryOp::Eq, lhs_val, true_val, ScalarType::U8);
        let rhs_block = self.builder.create_block();
        // If LHS is True, short-circuit to merge with LHS value
        self.builder
            .branch(is_true, merge, vec![lhs_val], rhs_block, vec![]);

        self.builder.switch_to(rhs_block);
        let rhs_val = self.lower_expr(rhs);
        self.builder.jump(merge, vec![rhs_val]);

        self.builder.switch_to(merge);
        merge_param
    }
}
