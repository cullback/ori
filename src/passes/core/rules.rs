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

use crate::ssa::BinaryOp as SsaBinaryOp;
use crate::symbol::SymbolId;

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
                    guards: a.guards.into_iter().map(simplify).collect(),
                    body: a.body.into_iter().map(simplify).collect(),
                    is_return: a.is_return,
                })
                .collect(),
            ty,
        },

        Expr::Cata { fold_fn, target_slots, target_ty, init, captures, elem_ty, early_exit, ty } => Expr::Cata {
            fold_fn,
            target_slots: target_slots.into_iter().map(simplify).collect(),
            target_ty,
            init: init.into_iter().map(simplify).collect(),
            captures: captures.into_iter().map(simplify).collect(),
            elem_ty,
            early_exit,
            ty,
        },

        Expr::Con { tag, args, field_slot_counts, ty } => Expr::Con {
            tag,
            args: args.into_iter().map(simplify).collect(),
            field_slot_counts,
            ty,
        },

        Expr::BufLit { elements, elem_ty, ty } => Expr::BufLit {
            elements: elements.into_iter().map(simplify).collect(),
            elem_ty,
            ty,
        },

        Expr::BufLoad { buf, idx, ty } => Expr::BufLoad {
            buf: Box::new(simplify(*buf)),
            idx: Box::new(simplify(*idx)),
            ty,
        },

        Expr::Range { start, end, ty } => Expr::Range {
            start: Box::new(simplify(*start)),
            end: Box::new(simplify(*end)),
            ty,
        },

        Expr::BufAppend { buf_slots, val_slots, elem_ty, ty } => Expr::BufAppend {
            buf_slots: buf_slots.into_iter().map(simplify).collect(),
            val_slots: val_slots.into_iter().map(simplify).collect(),
            elem_ty,
            ty,
        },

        Expr::BufSet { buf_slots, idx, val_slots, elem_ty, ty } => Expr::BufSet {
            buf_slots: buf_slots.into_iter().map(simplify).collect(),
            idx: Box::new(simplify(*idx)),
            val_slots: val_slots.into_iter().map(simplify).collect(),
            elem_ty,
            ty,
        },

        Expr::Cast { src, dest_ty, bitcast, ty } => Expr::Cast {
            src: Box::new(simplify(*src)),
            dest_ty,
            bitcast,
            ty,
        },
    }
}

/// Apply rewrite rules at a single node. Returns the rewritten
/// expression (or the original if no rule applies).
fn apply_local_rules(expr: Expr) -> Expr {
    match expr {
        // Additive identity: x + 0 → x, 0 + x → x.
        Expr::BinOp { op: SsaBinaryOp::Add, lhs, rhs, ty } => {
            if is_int_zero(&rhs) {
                *lhs
            } else if is_int_zero(&lhs) {
                *rhs
            } else {
                Expr::BinOp { op: SsaBinaryOp::Add, lhs, rhs, ty }
            }
        }

        // Multiplicative identity: x * 1 → x, 1 * x → x.
        Expr::BinOp { op: SsaBinaryOp::Mul, lhs, rhs, ty } => {
            if is_int_one(&rhs) {
                *lhs
            } else if is_int_one(&lhs) {
                *rhs
            } else {
                Expr::BinOp { op: SsaBinaryOp::Mul, lhs, rhs, ty }
            }
        }

        // Dead-binding elimination: `let x = e in body` where body
        // doesn't reference any of the binders → `body`. Sound in Ori
        // because the language is total and pure: `e` can't observe-
        // ably escape, and `e`'s evaluation has no effect we need to
        // preserve. The equivalent SSA-level pass needs alias analy-
        // sis (would `e`'s value escape via some store?) and DCE; in
        // Core it's a single shape check.
        Expr::Let { binders, value, body, ty } => {
            if binders.iter().all(|s| !body_uses(&body, *s)) {
                *body
            } else {
                Expr::Let { binders, value, body, ty }
            }
        }

        other => other,
    }
}

/// Does `expr` reference `target` anywhere in its tree?
fn body_uses(expr: &Expr, target: SymbolId) -> bool {
    match expr {
        Expr::Var { sym, .. } => *sym == target,
        Expr::Lit { .. } => false,
        Expr::BinOp { lhs, rhs, .. } => body_uses(lhs, target) || body_uses(rhs, target),
        Expr::App { args, .. } => args.iter().any(|a| body_uses(a, target)),
        Expr::Let { value, body, .. } => body_uses(value, target) || body_uses(body, target),
        Expr::Match { scrutinee_slots, arms, .. } => {
            scrutinee_slots.iter().any(|e| body_uses(e, target))
                || arms.iter().any(|a| {
                    a.guards.iter().any(|g| body_uses(g, target))
                        || a.body.iter().any(|b| body_uses(b, target))
                })
        }
        Expr::Cata { target_slots, init, captures, .. } => {
            target_slots.iter().any(|e| body_uses(e, target))
                || init.iter().any(|e| body_uses(e, target))
                || captures.iter().any(|e| body_uses(e, target))
        }
        Expr::Con { args, .. } => args.iter().any(|a| body_uses(a, target)),
        Expr::BufLit { elements, .. } => elements.iter().any(|e| body_uses(e, target)),
        Expr::BufLoad { buf, idx, .. } => body_uses(buf, target) || body_uses(idx, target),
        Expr::Range { start, end, .. } => body_uses(start, target) || body_uses(end, target),
        Expr::BufAppend { buf_slots, val_slots, .. } => {
            buf_slots.iter().any(|e| body_uses(e, target))
                || val_slots.iter().any(|e| body_uses(e, target))
        }
        Expr::BufSet { buf_slots, idx, val_slots, .. } => {
            buf_slots.iter().any(|e| body_uses(e, target))
                || body_uses(idx, target)
                || val_slots.iter().any(|e| body_uses(e, target))
        }
        Expr::Cast { src, .. } => body_uses(src, target),
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
            op: SsaBinaryOp::Add,
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
            op: SsaBinaryOp::Mul,
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
            op: SsaBinaryOp::Add,
            lhs: Box::new(Expr::BinOp {
                op: SsaBinaryOp::Add,
                lhs: Box::new(var(1)),
                rhs: Box::new(lit_int(0)),
                ty: i64_ty(),
            }),
            rhs: Box::new(Expr::BinOp {
                op: SsaBinaryOp::Mul,
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
        assert_eq!(op, SsaBinaryOp::Add);
        assert!(matches!(*lhs, Expr::Var { sym: SymbolId(1), .. }));
        assert!(matches!(*rhs, Expr::Var { sym: SymbolId(2), .. }));
    }

    #[test]
    fn dead_let_drops_binding() {
        // `let x = 7 in 42` → `42`  (binding never used)
        let e = Expr::Let {
            binders: vec![SymbolId(1)],
            value: Box::new(lit_int(7)),
            body: Box::new(lit_int(42)),
            ty: i64_ty(),
        };
        let simplified = simplify(e);
        match simplified {
            Expr::Lit { value: Literal::Int(42), .. } => {}
            other => panic!("expected Lit(42), got {other:?}"),
        }
    }

    #[test]
    fn live_let_is_preserved() {
        // `let x = 7 in x + 1` → unchanged (x is used)
        let e = Expr::Let {
            binders: vec![SymbolId(1)],
            value: Box::new(lit_int(7)),
            body: Box::new(Expr::BinOp {
                op: SsaBinaryOp::Add,
                lhs: Box::new(var(1)),
                rhs: Box::new(lit_int(1)),
                ty: i64_ty(),
            }),
            ty: i64_ty(),
        };
        let simplified = simplify(e);
        // Must still be a Let — the binder is live.
        assert!(matches!(simplified, Expr::Let { .. }));
    }

    #[test]
    fn dead_let_inside_let_drops() {
        // `let x = 1 in (let y = 2 in x + x)` — y is dead, x is live.
        // After simplify: `let x = 1 in x + x` (inner Let dropped).
        let inner_let = Expr::Let {
            binders: vec![SymbolId(2)],
            value: Box::new(lit_int(2)),
            body: Box::new(Expr::BinOp {
                op: SsaBinaryOp::Add,
                lhs: Box::new(var(1)),
                rhs: Box::new(var(1)),
                ty: i64_ty(),
            }),
            ty: i64_ty(),
        };
        let outer = Expr::Let {
            binders: vec![SymbolId(1)],
            value: Box::new(lit_int(1)),
            body: Box::new(inner_let),
            ty: i64_ty(),
        };
        let simplified = simplify(outer);
        let Expr::Let { binders, body, .. } = simplified else {
            panic!("expected outer Let");
        };
        assert_eq!(binders, vec![SymbolId(1)]);
        // body should be the BinOp directly (inner Let collapsed)
        assert!(matches!(*body, Expr::BinOp { .. }));
    }

    #[test]
    fn unrelated_expressions_pass_through() {
        let e = Expr::BinOp {
            op: SsaBinaryOp::Add,
            lhs: Box::new(var(1)),
            rhs: Box::new(var(2)),
            ty: i64_ty(),
        };
        let simplified = simplify(e);
        // Unchanged
        let Expr::BinOp { op, .. } = simplified else { panic!("expected BinOp"); };
        assert_eq!(op, SsaBinaryOp::Add);
    }
}
