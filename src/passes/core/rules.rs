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
//!
//! Arithmetic / comparison primitives are `Expr::App` whose `target`
//! is a builtin `SymbolId`. The identity rules match against
//! `BuiltinRegistry::classify` rather than a closed `BinOp` enum.

use crate::symbol::{BuiltinKind, BuiltinRegistry, SymbolId};

use super::expr::{Expr, Literal, MatchArm, Pattern};

/// Walk an expression bottom-up, simplifying children first then
/// applying local rules at each node. Type-preserving by
/// construction — every rewrite produces an expression of the same
/// type as its input.
pub fn simplify(expr: Expr, builtins: &BuiltinRegistry) -> Expr {
    let expr = recurse(expr, builtins);
    apply_local_rules(expr, builtins)
}

/// Apply each variant's children recursively. Each Expr variant's
/// fields are mapped through `simplify` in turn.
fn recurse(expr: Expr, builtins: &BuiltinRegistry) -> Expr {
    match expr {
        Expr::Var { .. } | Expr::Lit { .. } => expr,

        Expr::App { target, args, ty } => Expr::App {
            target,
            args: args.into_iter().map(|e| simplify(e, builtins)).collect(),
            ty,
        },

        Expr::Let { binders, value, body, ty } => Expr::Let {
            binders,
            value: Box::new(simplify(*value, builtins)),
            body: Box::new(simplify(*body, builtins)),
            ty,
        },

        Expr::Match { scrutinee_slots, scrutinee_ty, arms, ty } => Expr::Match {
            scrutinee_slots: scrutinee_slots.into_iter().map(|e| simplify(e, builtins)).collect(),
            scrutinee_ty,
            arms: arms
                .into_iter()
                .map(|a| MatchArm {
                    pattern: a.pattern,
                    guards: a.guards.into_iter().map(|e| simplify(e, builtins)).collect(),
                    body: a.body.into_iter().map(|e| simplify(e, builtins)).collect(),
                    is_return: a.is_return,
                })
                .collect(),
            ty,
        },

        Expr::Cata { fold_fn, target_slots, target_ty, init, captures, elem_ty, early_exit, ty } => Expr::Cata {
            fold_fn,
            target_slots: target_slots.into_iter().map(|e| simplify(e, builtins)).collect(),
            target_ty,
            init: init.into_iter().map(|e| simplify(e, builtins)).collect(),
            captures: captures.into_iter().map(|e| simplify(e, builtins)).collect(),
            elem_ty,
            early_exit,
            ty,
        },

        Expr::Con { tag, args, field_slot_counts, ty } => Expr::Con {
            tag,
            args: args.into_iter().map(|e| simplify(e, builtins)).collect(),
            field_slot_counts,
            ty,
        },

        Expr::BufLit { elements, elem_ty, ty } => Expr::BufLit {
            elements: elements.into_iter().map(|e| simplify(e, builtins)).collect(),
            elem_ty,
            ty,
        },

        Expr::BufLoad { buf, idx, ty } => Expr::BufLoad {
            buf: Box::new(simplify(*buf, builtins)),
            idx: Box::new(simplify(*idx, builtins)),
            ty,
        },

        Expr::BufAppend { buf_slots, val_slots, elem_ty, ty } => Expr::BufAppend {
            buf_slots: buf_slots.into_iter().map(|e| simplify(e, builtins)).collect(),
            val_slots: val_slots.into_iter().map(|e| simplify(e, builtins)).collect(),
            elem_ty,
            ty,
        },

        Expr::BufSet { buf_slots, idx, val_slots, elem_ty, ty } => Expr::BufSet {
            buf_slots: buf_slots.into_iter().map(|e| simplify(e, builtins)).collect(),
            idx: Box::new(simplify(*idx, builtins)),
            val_slots: val_slots.into_iter().map(|e| simplify(e, builtins)).collect(),
            elem_ty,
            ty,
        },
    }
}

/// Apply rewrite rules at a single node. Returns the rewritten
/// expression (or the original if no rule applies).
fn apply_local_rules(expr: Expr, builtins: &BuiltinRegistry) -> Expr {
    use crate::ssa::BinaryOp;
    match expr {
        // Additive identity (`x + 0 → x`, `0 + x → x`) and
        // multiplicative identity (`x * 1 → x`, `1 * x → x`) on
        // builtin binary App targets. Other App targets (regular
        // function calls) pass through.
        Expr::App { target, args, ty } => match builtins.classify(target) {
            Some(BuiltinKind::Binary(BinaryOp::Add)) if args.len() == 2 => {
                if is_int_zero(&args[1]) {
                    args.into_iter().next().unwrap()
                } else if is_int_zero(&args[0]) {
                    args.into_iter().nth(1).unwrap()
                } else {
                    Expr::App { target, args, ty }
                }
            }
            Some(BuiltinKind::Binary(BinaryOp::Mul)) if args.len() == 2 => {
                if is_int_one(&args[1]) {
                    args.into_iter().next().unwrap()
                } else if is_int_one(&args[0]) {
                    args.into_iter().nth(1).unwrap()
                } else {
                    Expr::App { target, args, ty }
                }
            }
            _ => Expr::App { target, args, ty },
        },

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
        Expr::BufAppend { buf_slots, val_slots, .. } => {
            buf_slots.iter().any(|e| body_uses(e, target))
                || val_slots.iter().any(|e| body_uses(e, target))
        }
        Expr::BufSet { buf_slots, idx, val_slots, .. } => {
            buf_slots.iter().any(|e| body_uses(e, target))
                || body_uses(idx, target)
                || val_slots.iter().any(|e| body_uses(e, target))
        }
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
    use crate::symbol::{BuiltinRegistry, SymbolId, SymbolTable};
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

    fn registry() -> BuiltinRegistry {
        let mut symbols = SymbolTable::new();
        BuiltinRegistry::bootstrap(&mut symbols)
    }

    fn binop(builtins: &BuiltinRegistry, op: crate::ssa::BinaryOp, lhs: Expr, rhs: Expr) -> Expr {
        let target = match op {
            crate::ssa::BinaryOp::Add => builtins.add,
            crate::ssa::BinaryOp::Mul => builtins.mul,
            _ => panic!("test helper supports Add/Mul only"),
        };
        Expr::App { target, args: vec![lhs, rhs], ty: i64_ty() }
    }

    #[test]
    fn add_zero_collapses() {
        let b = registry();
        let e = binop(&b, crate::ssa::BinaryOp::Add, var(1), lit_int(0));
        let simplified = simplify(e, &b);
        match simplified {
            Expr::Var { sym, .. } => assert_eq!(sym, SymbolId(1)),
            other => panic!("expected Var, got {other:?}"),
        }
    }

    #[test]
    fn mul_one_collapses() {
        let b = registry();
        let e = binop(&b, crate::ssa::BinaryOp::Mul, lit_int(1), var(2));
        let simplified = simplify(e, &b);
        match simplified {
            Expr::Var { sym, .. } => assert_eq!(sym, SymbolId(2)),
            other => panic!("expected Var, got {other:?}"),
        }
    }

    #[test]
    fn rule_recurses_into_children() {
        // (x + 0) + (y * 1) → x + y
        let b = registry();
        let inner_l = binop(&b, crate::ssa::BinaryOp::Add, var(1), lit_int(0));
        let inner_r = binop(&b, crate::ssa::BinaryOp::Mul, var(2), lit_int(1));
        let e = binop(&b, crate::ssa::BinaryOp::Add, inner_l, inner_r);
        let simplified = simplify(e, &b);
        let Expr::App { target, args, .. } = simplified else {
            panic!("expected App");
        };
        assert_eq!(target, b.add);
        assert!(matches!(args[0], Expr::Var { sym: SymbolId(1), .. }));
        assert!(matches!(args[1], Expr::Var { sym: SymbolId(2), .. }));
    }

    #[test]
    fn dead_let_drops_binding() {
        // `let x = 7 in 42` → `42`  (binding never used)
        let b = registry();
        let e = Expr::Let {
            binders: vec![SymbolId(1)],
            value: Box::new(lit_int(7)),
            body: Box::new(lit_int(42)),
            ty: i64_ty(),
        };
        let simplified = simplify(e, &b);
        match simplified {
            Expr::Lit { value: Literal::Int(42), .. } => {}
            other => panic!("expected Lit(42), got {other:?}"),
        }
    }

    #[test]
    fn live_let_is_preserved() {
        // `let x = 7 in x + 1` → unchanged (x is used)
        let b = registry();
        let e = Expr::Let {
            binders: vec![SymbolId(1)],
            value: Box::new(lit_int(7)),
            body: Box::new(binop(&b, crate::ssa::BinaryOp::Add, var(1), lit_int(1))),
            ty: i64_ty(),
        };
        let simplified = simplify(e, &b);
        // Must still be a Let — the binder is live.
        assert!(matches!(simplified, Expr::Let { .. }));
    }

    #[test]
    fn dead_let_inside_let_drops() {
        // `let x = 1 in (let y = 2 in x + x)` — y is dead, x is live.
        let b = registry();
        let inner_let = Expr::Let {
            binders: vec![SymbolId(2)],
            value: Box::new(lit_int(2)),
            body: Box::new(binop(&b, crate::ssa::BinaryOp::Add, var(1), var(1))),
            ty: i64_ty(),
        };
        let outer = Expr::Let {
            binders: vec![SymbolId(1)],
            value: Box::new(lit_int(1)),
            body: Box::new(inner_let),
            ty: i64_ty(),
        };
        let simplified = simplify(outer, &b);
        let Expr::Let { binders, body, .. } = simplified else {
            panic!("expected outer Let");
        };
        assert_eq!(binders, vec![SymbolId(1)]);
        // body should be the App directly (inner Let collapsed)
        assert!(matches!(*body, Expr::App { .. }));
    }

    #[test]
    fn unrelated_expressions_pass_through() {
        let b = registry();
        let e = binop(&b, crate::ssa::BinaryOp::Add, var(1), var(2));
        let simplified = simplify(e, &b);
        // Unchanged
        let Expr::App { target, .. } = simplified else { panic!("expected App"); };
        assert_eq!(target, b.add);
    }
}
