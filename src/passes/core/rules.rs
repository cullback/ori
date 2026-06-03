//! Algebraic rewrite rules for Core IR.
//!
//! Each rule is a Core → Core transformation that preserves semantics.
//! `simplify` walks an expression bottom-up: simplify children first,
//! then apply rules at the current node. Rules are local pattern
//! matches; complex multi-node rewrites would land here too as the
//! rule set grows.
//!
//! ## Soundness
//!
//! Every rule must preserve semantics unconditionally in Ori. The
//! language properties (total + pure + strict + no aggregate identity)
//! make most algebraic laws hold without side conditions — see
//! `notes/language-properties.md`. If a rule has a side condition,
//! document it explicitly and prove it locally.
//!
//! ## Today's rules
//!
//! - Additive identity: `x + 0 → x`, `0 + x → x`
//! - Multiplicative identity: `x * 1 → x`, `1 * x → x`
//!
//! These are trivially obvious but exist primarily to **establish the
//! rule-writing pattern**. Bigger wins (fusion, beta reduction,
//! case-of-case, free theorems) land as we grow the set.

use crate::ast::BinOp as AstBinOp;

use super::expr::{Expr, Literal, MatchArm, Pattern};

/// Walk an expression bottom-up, simplifying children first then
/// applying local rules at each node. Type-preserving by
/// construction — every rewrite produces an expression of the same
/// type as its input.
pub fn simplify(expr: Expr) -> Expr {
    let expr = recurse(expr);
    apply_local_rules(expr)
}

/// Apply each variant's children recursively. Each Expr variant's
/// fields are mapped through `simplify` in turn.
fn recurse(expr: Expr) -> Expr {
    match expr {
        Expr::Var { .. } | Expr::Lit { .. } => expr,

        Expr::BinOp { op, lhs, rhs, ty } => Expr::BinOp {
            op,
            lhs: Box::new(simplify(*lhs)),
            rhs: Box::new(simplify(*rhs)),
            ty,
        },

        Expr::App { target, args, ty } => Expr::App {
            target,
            args: args.into_iter().map(simplify).collect(),
            ty,
        },

        Expr::Let { binders, value, body, ty } => Expr::Let {
            binders,
            value: Box::new(simplify(*value)),
            body: Box::new(simplify(*body)),
            ty,
        },

        Expr::Match { scrutinee_slots, scrutinee_ty, arms, ty } => Expr::Match {
            scrutinee_slots: scrutinee_slots.into_iter().map(simplify).collect(),
            scrutinee_ty,
            arms: arms
                .into_iter()
                .map(|a| MatchArm {
                    pattern: a.pattern,
                    body: simplify(a.body),
                })
                .collect(),
            ty,
        },

        Expr::Cata { alg, init, target, ty } => Expr::Cata {
            alg,
            init: Box::new(simplify(*init)),
            target: Box::new(simplify(*target)),
            ty,
        },

        Expr::Con { tag, args, ty } => Expr::Con {
            tag,
            args: args.into_iter().map(simplify).collect(),
            ty,
        },

        Expr::ListLit { elements, elem_ty, ty } => Expr::ListLit {
            elements: elements.into_iter().map(simplify).collect(),
            elem_ty,
            ty,
        },
    }
}

/// Apply rewrite rules at a single node. Returns the rewritten
/// expression (or the original if no rule applies).
fn apply_local_rules(expr: Expr) -> Expr {
    match expr {
        // Additive identity: x + 0 → x, 0 + x → x.
        Expr::BinOp { op: AstBinOp::Add, lhs, rhs, ty } => {
            if is_int_zero(&rhs) {
                *lhs
            } else if is_int_zero(&lhs) {
                *rhs
            } else {
                Expr::BinOp { op: AstBinOp::Add, lhs, rhs, ty }
            }
        }

        // Multiplicative identity: x * 1 → x, 1 * x → x.
        Expr::BinOp { op: AstBinOp::Mul, lhs, rhs, ty } => {
            if is_int_one(&rhs) {
                *lhs
            } else if is_int_one(&lhs) {
                *rhs
            } else {
                Expr::BinOp { op: AstBinOp::Mul, lhs, rhs, ty }
            }
        }

        other => other,
    }
}

fn is_int_zero(expr: &Expr) -> bool {
    matches!(expr, Expr::Lit { value: Literal::Int(0), .. })
}

fn is_int_one(expr: &Expr) -> bool {
    matches!(expr, Expr::Lit { value: Literal::Int(1), .. })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::symbol::SymbolId;
    use crate::types::engine::Type;

    fn i64_ty() -> Type {
        Type::Con("I64".to_string())
    }

    fn lit_int(n: i64) -> Expr {
        Expr::Lit { value: Literal::Int(n), ty: i64_ty() }
    }

    fn var(id: u32) -> Expr {
        Expr::Var { sym: SymbolId(id), ty: i64_ty() }
    }

    #[test]
    fn add_zero_collapses() {
        let e = Expr::BinOp {
            op: AstBinOp::Add,
            lhs: Box::new(var(1)),
            rhs: Box::new(lit_int(0)),
            ty: i64_ty(),
        };
        let simplified = simplify(e);
        match simplified {
            Expr::Var { sym, .. } => assert_eq!(sym, SymbolId(1)),
            other => panic!("expected Var, got {other:?}"),
        }
    }

    #[test]
    fn mul_one_collapses() {
        let e = Expr::BinOp {
            op: AstBinOp::Mul,
            lhs: Box::new(lit_int(1)),
            rhs: Box::new(var(2)),
            ty: i64_ty(),
        };
        let simplified = simplify(e);
        match simplified {
            Expr::Var { sym, .. } => assert_eq!(sym, SymbolId(2)),
            other => panic!("expected Var, got {other:?}"),
        }
    }

    #[test]
    fn rule_recurses_into_children() {
        // (x + 0) + (y * 1) → x + y
        let e = Expr::BinOp {
            op: AstBinOp::Add,
            lhs: Box::new(Expr::BinOp {
                op: AstBinOp::Add,
                lhs: Box::new(var(1)),
                rhs: Box::new(lit_int(0)),
                ty: i64_ty(),
            }),
            rhs: Box::new(Expr::BinOp {
                op: AstBinOp::Mul,
                lhs: Box::new(var(2)),
                rhs: Box::new(lit_int(1)),
                ty: i64_ty(),
            }),
            ty: i64_ty(),
        };
        let simplified = simplify(e);
        let Expr::BinOp { op, lhs, rhs, .. } = simplified else {
            panic!("expected BinOp");
        };
        assert_eq!(op, AstBinOp::Add);
        assert!(matches!(*lhs, Expr::Var { sym: SymbolId(1), .. }));
        assert!(matches!(*rhs, Expr::Var { sym: SymbolId(2), .. }));
    }

    #[test]
    fn unrelated_expressions_pass_through() {
        let e = Expr::BinOp {
            op: AstBinOp::Add,
            lhs: Box::new(var(1)),
            rhs: Box::new(var(2)),
            ty: i64_ty(),
        };
        let simplified = simplify(e);
        // Unchanged
        let Expr::BinOp { op, .. } = simplified else { panic!("expected BinOp"); };
        assert_eq!(op, AstBinOp::Add);
    }
}
