//! Rewrite layer.
//!
//! `simplify(expr, fns)` walks an expression bottom-up, applying
//! local rewrite rules at each node. The traversal is type-
//! preserving by construction — every rewrite produces an expression
//! of the same type as its input.
//!
//! Today's rules:
//!
//! - **Dead-binding elimination.** `let x = e in body` where `body`
//!   doesn't reference `x` and `e` is total → `body`. Soundness
//!   requires `e` to be crash-free; we use the totality calculator
//!   to check.
//!
//! Each rule documents which language guarantee it relies on for
//! soundness; the spec's *Soundness* section catalogs which subtree
//! shapes admit which rewrites.

use std::collections::HashSet;

use crate::expr::{Expr, MatchArm};
use crate::pattern::Pattern;
use crate::sym::LocalId;
use crate::totality::{is_total, FnTotality};

/// Walk an expression bottom-up, simplifying children first and
/// applying local rules at each node.
#[must_use]
pub fn simplify(expr: Expr, fns: &FnTotality) -> Expr {
    let expr = recurse(expr, fns);
    apply_local_rules(expr, fns)
}

fn recurse(expr: Expr, fns: &FnTotality) -> Expr {
    match expr {
        Expr::Var { .. } | Expr::Lit { .. } | Expr::Crash { .. } => expr,
        Expr::App { target, args, ty } => Expr::App {
            target,
            args: args.into_iter().map(|a| simplify(a, fns)).collect(),
            ty,
        },
        Expr::Let { binder, value, body, ty } => Expr::Let {
            binder,
            value: Box::new(simplify(*value, fns)),
            body: Box::new(simplify(*body, fns)),
            ty,
        },
        Expr::Match { scrutinee, arms, ty } => Expr::Match {
            scrutinee: Box::new(simplify(*scrutinee, fns)),
            arms: arms
                .into_iter()
                .map(|a| MatchArm {
                    pattern: a.pattern,
                    guards: a.guards.into_iter().map(|g| simplify(g, fns)).collect(),
                    body: Box::new(simplify(*a.body, fns)),
                    is_return: a.is_return,
                })
                .collect(),
            ty,
        },
        Expr::Con { tag, args, ty } => Expr::Con {
            tag,
            args: args.into_iter().map(|a| simplify(a, fns)).collect(),
            ty,
        },
        Expr::Fold { kind, fold_fn, target, init, captures, shape, ty } => Expr::Fold {
            kind,
            fold_fn,
            target: Box::new(simplify(*target, fns)),
            init: init.into_iter().map(|e| simplify(e, fns)).collect(),
            captures: captures.into_iter().map(|e| simplify(e, fns)).collect(),
            shape,
            ty,
        },
        Expr::Gen { bound, step_fn, init, captures, elem_ty, ty } => Expr::Gen {
            bound: Box::new(simplify(*bound, fns)),
            step_fn,
            init: init.into_iter().map(|e| simplify(e, fns)).collect(),
            captures: captures.into_iter().map(|e| simplify(e, fns)).collect(),
            elem_ty,
            ty,
        },
        Expr::BufLit { elements, elem_ty, ty } => Expr::BufLit {
            elements: elements.into_iter().map(|e| simplify(e, fns)).collect(),
            elem_ty,
            ty,
        },
        Expr::BufLoad { buf, idx, ty } => Expr::BufLoad {
            buf: Box::new(simplify(*buf, fns)),
            idx: Box::new(simplify(*idx, fns)),
            ty,
        },
        Expr::BufLoadUnchecked { buf, idx, ty } => Expr::BufLoadUnchecked {
            buf: Box::new(simplify(*buf, fns)),
            idx: Box::new(simplify(*idx, fns)),
            ty,
        },
        Expr::BufAppend { buf, val, ty } => Expr::BufAppend {
            buf: Box::new(simplify(*buf, fns)),
            val: Box::new(simplify(*val, fns)),
            ty,
        },
        Expr::BufSet { buf, idx, val, ty } => Expr::BufSet {
            buf: Box::new(simplify(*buf, fns)),
            idx: Box::new(simplify(*idx, fns)),
            val: Box::new(simplify(*val, fns)),
            ty,
        },
    }
}

fn apply_local_rules(expr: Expr, fns: &FnTotality) -> Expr {
    match expr {
        // **Dead-binding elimination.**
        //
        // `let x = e in body` where:
        // - `body` does not reference `x` (binding is dead), and
        // - `e` is total (no `Crash`, only calls to total fns),
        //
        // rewrites to `body`. Soundness: purity makes the eliminated
        // evaluation unobservable; totality ensures we don't skip a
        // crash. In a non-total language this rewrite would need a
        // crash-freedom side condition; in Ori the totality bit is
        // the check.
        Expr::Let { binder, value, body, ty } => {
            if !free_vars(&body).contains(&binder) && is_total(&value, fns) {
                *body
            } else {
                Expr::Let { binder, value, body, ty }
            }
        }
        other => other,
    }
}

/// Compute the set of `LocalId`s referenced free in `expr`.
///
/// "Free" means not bound by an enclosing `Let` or `Pattern` binder
/// *within* `expr`. Function-table identifiers (`FnId`, `TagId`,
/// `TypeId`) aren't local bindings; they aren't tracked.
#[must_use]
pub fn free_vars(expr: &Expr) -> HashSet<LocalId> {
    let mut out = HashSet::new();
    collect_free(expr, &mut HashSet::new(), &mut out);
    out
}

fn collect_free(expr: &Expr, bound: &mut HashSet<LocalId>, out: &mut HashSet<LocalId>) {
    match expr {
        Expr::Var { sym, .. } => {
            if !bound.contains(sym) {
                out.insert(*sym);
            }
        }
        Expr::Lit { .. } | Expr::Crash { .. } => {}
        Expr::App { args, .. } => {
            for a in args {
                collect_free(a, bound, out);
            }
        }
        Expr::Let { binder, value, body, .. } => {
            collect_free(value, bound, out);
            let was_new = bound.insert(*binder);
            collect_free(body, bound, out);
            if was_new {
                bound.remove(binder);
            }
        }
        Expr::Match { scrutinee, arms, .. } => {
            collect_free(scrutinee, bound, out);
            for arm in arms {
                let pattern_binders = pattern_binders(&arm.pattern);
                let was_new: Vec<bool> =
                    pattern_binders.iter().map(|s| bound.insert(*s)).collect();
                for g in &arm.guards {
                    collect_free(g, bound, out);
                }
                collect_free(&arm.body, bound, out);
                for (sym, new) in pattern_binders.iter().zip(was_new) {
                    if new {
                        bound.remove(sym);
                    }
                }
            }
        }
        Expr::Con { args, .. } => {
            for a in args {
                collect_free(a, bound, out);
            }
        }
        Expr::Fold { target, init, captures, .. } => {
            collect_free(target, bound, out);
            for e in init {
                collect_free(e, bound, out);
            }
            for e in captures {
                collect_free(e, bound, out);
            }
        }
        Expr::Gen { bound: gen_bound, init, captures, .. } => {
            collect_free(gen_bound, bound, out);
            for e in init {
                collect_free(e, bound, out);
            }
            for e in captures {
                collect_free(e, bound, out);
            }
        }
        Expr::BufLit { elements, .. } => {
            for e in elements {
                collect_free(e, bound, out);
            }
        }
        Expr::BufLoad { buf, idx, .. } | Expr::BufLoadUnchecked { buf, idx, .. } => {
            collect_free(buf, bound, out);
            collect_free(idx, bound, out);
        }
        Expr::BufAppend { buf, val, .. } => {
            collect_free(buf, bound, out);
            collect_free(val, bound, out);
        }
        Expr::BufSet { buf, idx, val, .. } => {
            collect_free(buf, bound, out);
            collect_free(idx, bound, out);
            collect_free(val, bound, out);
        }
    }
}

fn pattern_binders(pat: &Pattern) -> Vec<LocalId> {
    match pat {
        Pattern::Wildcard => Vec::new(),
        Pattern::Binding(s) => vec![*s],
        Pattern::Constructor { binders, .. } => {
            binders.iter().filter_map(|b| b.as_sym()).collect()
        }
    }
}
