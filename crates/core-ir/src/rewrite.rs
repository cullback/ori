//! Rewrite layer.
//!
//! `simplify(expr, fns)` walks an expression bottom-up, applying
//! local rewrite rules at each node. Each rule documents the
//! soundness condition it depends on.
//!
//! Today's rules:
//!
//! - **Dead-binding elimination.** `let x = e in body` where
//!   `body` doesn't reference `x` and `e` is total → `body`.
//! - **Beta reduction** (let-of-literal / let-of-var).
//!   `let x = lit in body` → `body[x → lit]`. Sound
//!   unconditionally — literals and vars can't crash and are
//!   trivially cheap to duplicate.
//! - **Case-of-known-constructor.** `Match(Con(tag, args), arms)`
//!   rewrites to the matching arm's body with field binders
//!   substituted by `args`. The flagship syntactic rewrite the
//!   `Con` + `Match` variant split exists to enable.

use std::collections::HashSet;

use crate::expr::{Expr, MatchArm};
use crate::pattern::Pattern;
use crate::sym::LocalId;
use crate::totality::{is_total, FnTotality};

/// Walk an expression bottom-up. After simplifying children, apply
/// the local rules at the current node. If any rule fires, the
/// result is re-simplified — rules can compose without the caller
/// running `simplify` multiple times.
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
        // **Beta reduction** (let-of-literal / let-of-var) and
        // **dead-let elimination**, in that order. Beta is unconditional
        // for literal/var values; dead-let needs totality.
        Expr::Let { binder, value, body, ty } => {
            // Beta: if value is a literal or a Var, substitute in body.
            // Both kinds are cheap to duplicate and trivially total.
            if matches!(*value, Expr::Lit { .. } | Expr::Var { .. }) {
                let substituted = substitute_one(*body, binder, &value);
                return simplify(substituted, fns);
            }
            // Dead-let: if body doesn't reference binder and value
            // is total, drop the Let.
            if !free_vars(&body).contains(&binder) && is_total(&value, fns) {
                return simplify(*body, fns);
            }
            Expr::Let { binder, value, body, ty }
        }

        // **Case-of-known-constructor.** If the scrutinee is a `Con`,
        // find the matching arm and substitute its binders with the
        // constructor's args. Sound unconditionally — we're just
        // evaluating the match at compile time. The `Con` is gone
        // along with the entire `Match`.
        Expr::Match { scrutinee, arms, ty } => {
            if matches!(scrutinee.as_ref(), Expr::Con { .. }) {
                if let Some(reduced) = case_of_known_con(&scrutinee, &arms) {
                    return simplify(reduced, fns);
                }
                // No matching arm: a non-exhaustive match. Leave it
                // alone — the runtime will crash, which is what the
                // user wrote.
            }
            Expr::Match { scrutinee, arms, ty }
        }

        other => other,
    }
}

/// Try case-of-known-constructor. Returns `Some(body_after_subst)`
/// if a matching arm was found.
fn case_of_known_con(scrutinee: &Expr, arms: &[MatchArm]) -> Option<Expr> {
    let Expr::Con { tag: con_tag, args: con_args, .. } = scrutinee else {
        return None;
    };
    for arm in arms {
        // Guards make match outcome run-time dependent; skip the
        // rewrite (a smarter version could pattern-match on
        // syntactically-true guards).
        if !arm.guards.is_empty() {
            return None;
        }
        match &arm.pattern {
            Pattern::Wildcard => return Some((*arm.body).clone()),
            Pattern::Binding(b) => {
                return Some(substitute_one(
                    (*arm.body).clone(),
                    *b,
                    scrutinee,
                ));
            }
            Pattern::Constructor { tag: arm_tag, binders } => {
                if con_tag != arm_tag {
                    continue;
                }
                if binders.len() != con_args.len() {
                    return None;
                }
                let sub: Vec<(LocalId, Expr)> = binders
                    .iter()
                    .zip(con_args.iter())
                    .filter_map(|(b, arg)| b.as_sym().map(|s| (s, arg.clone())))
                    .collect();
                return Some(substitute_many((*arm.body).clone(), &sub));
            }
        }
    }
    None
}

// ---- Substitution ----

/// Substitute `target` → `replacement` in `expr`, respecting lexical
/// scope. `replacement` is cloned at each use site.
#[must_use]
pub fn substitute_one(expr: Expr, target: LocalId, replacement: &Expr) -> Expr {
    substitute_many(expr, &[(target, replacement.clone())])
}

/// Apply many substitutions simultaneously. Each `(LocalId, Expr)`
/// pair: any `Var` referencing the `LocalId` is replaced with the
/// `Expr` (clone). Scope-aware: shadowing binders mask the outer
/// substitution within their scope.
#[must_use]
pub fn substitute_many(expr: Expr, subs: &[(LocalId, Expr)]) -> Expr {
    fn find<'a>(subs: &'a [(LocalId, Expr)], sym: LocalId) -> Option<&'a Expr> {
        subs.iter().find_map(|(s, e)| if *s == sym { Some(e) } else { None })
    }
    fn shadowed(subs: &[(LocalId, Expr)], sym: LocalId) -> Vec<(LocalId, Expr)> {
        subs.iter()
            .filter(|(s, _)| *s != sym)
            .cloned()
            .collect()
    }
    fn go(expr: Expr, subs: &[(LocalId, Expr)]) -> Expr {
        if subs.is_empty() {
            return expr;
        }
        match expr {
            Expr::Var { sym, ty } => {
                if let Some(r) = find(subs, sym) {
                    r.clone()
                } else {
                    Expr::Var { sym, ty }
                }
            }
            Expr::Lit { .. } | Expr::Crash { .. } => expr,
            Expr::App { target, args, ty } => Expr::App {
                target,
                args: args.into_iter().map(|a| go(a, subs)).collect(),
                ty,
            },
            Expr::Let { binder, value, body, ty } => {
                let value = go(*value, subs);
                let body = if find(subs, binder).is_some() {
                    let shadowed_subs = shadowed(subs, binder);
                    go(*body, &shadowed_subs)
                } else {
                    go(*body, subs)
                };
                Expr::Let { binder, value: Box::new(value), body: Box::new(body), ty }
            }
            Expr::Match { scrutinee, arms, ty } => Expr::Match {
                scrutinee: Box::new(go(*scrutinee, subs)),
                arms: arms
                    .into_iter()
                    .map(|arm| go_arm(arm, subs))
                    .collect(),
                ty,
            },
            Expr::Con { tag, args, ty } => Expr::Con {
                tag,
                args: args.into_iter().map(|a| go(a, subs)).collect(),
                ty,
            },
            Expr::Fold { kind, fold_fn, target, init, captures, shape, ty } => Expr::Fold {
                kind,
                fold_fn,
                target: Box::new(go(*target, subs)),
                init: init.into_iter().map(|e| go(e, subs)).collect(),
                captures: captures.into_iter().map(|e| go(e, subs)).collect(),
                shape,
                ty,
            },
            Expr::Gen { bound, step_fn, init, captures, elem_ty, ty } => Expr::Gen {
                bound: Box::new(go(*bound, subs)),
                step_fn,
                init: init.into_iter().map(|e| go(e, subs)).collect(),
                captures: captures.into_iter().map(|e| go(e, subs)).collect(),
                elem_ty,
                ty,
            },
            Expr::BufLit { elements, elem_ty, ty } => Expr::BufLit {
                elements: elements.into_iter().map(|e| go(e, subs)).collect(),
                elem_ty,
                ty,
            },
            Expr::BufLoad { buf, idx, ty } => Expr::BufLoad {
                buf: Box::new(go(*buf, subs)),
                idx: Box::new(go(*idx, subs)),
                ty,
            },
            Expr::BufLoadUnchecked { buf, idx, ty } => Expr::BufLoadUnchecked {
                buf: Box::new(go(*buf, subs)),
                idx: Box::new(go(*idx, subs)),
                ty,
            },
            Expr::BufAppend { buf, val, ty } => Expr::BufAppend {
                buf: Box::new(go(*buf, subs)),
                val: Box::new(go(*val, subs)),
                ty,
            },
            Expr::BufSet { buf, idx, val, ty } => Expr::BufSet {
                buf: Box::new(go(*buf, subs)),
                idx: Box::new(go(*idx, subs)),
                val: Box::new(go(*val, subs)),
                ty,
            },
        }
    }

    fn go_arm(arm: MatchArm, subs: &[(LocalId, Expr)]) -> MatchArm {
        let pattern_binders = pattern_binders(&arm.pattern);
        let arm_subs: Vec<(LocalId, Expr)> = if pattern_binders.is_empty() {
            subs.to_vec()
        } else {
            subs.iter()
                .filter(|(s, _)| !pattern_binders.contains(s))
                .cloned()
                .collect()
        };
        MatchArm {
            pattern: arm.pattern,
            guards: arm.guards.into_iter().map(|g| go(g, &arm_subs)).collect(),
            body: Box::new(go(*arm.body, &arm_subs)),
            is_return: arm.is_return,
        }
    }

    go(expr, subs)
}

// ---- Free vars ----

/// Compute the set of `LocalId`s referenced free in `expr`.
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
                let pbs = pattern_binders(&arm.pattern);
                let was_new: Vec<bool> = pbs.iter().map(|s| bound.insert(*s)).collect();
                for g in &arm.guards {
                    collect_free(g, bound, out);
                }
                collect_free(&arm.body, bound, out);
                for (sym, new) in pbs.iter().zip(was_new) {
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
