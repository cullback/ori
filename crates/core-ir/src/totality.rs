//! Totality analysis.
//!
//! A subtree is total iff it contains no `Crash` and every `App`
//! / `Fold` / `Gen` references a callable known total. This bit
//! is the contract that lets algebraic rewrites fire unconditionally
//! — see the *Refcounting / Soundness* sections of the spec.
//!
//! Per the spec, totality propagates over the DAG call graph in
//! one bottom-up walk: callees-first guarantees every `App.target`
//! has its totality known by the time we ask.
//!
//! `FnTotality` is the result of that walk — a map from `FnId` to
//! whether the function's body is total. Pass it to `is_total` to
//! decide whether a subtree is total.

use std::collections::HashMap;

use crate::expr::Expr;
use crate::sym::FnId;

/// Totality of each known top-level callable.
///
/// `get(fn_id)` returns `Some(true)` if the function is total,
/// `Some(false)` if it isn't, and `None` if the function isn't
/// registered (treat as opaque — conservatively non-total for
/// rewrites that need a positive answer).
#[derive(Debug, Default, Clone)]
pub struct FnTotality(HashMap<FnId, bool>);

impl FnTotality {
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    pub fn insert(&mut self, f: FnId, total: bool) {
        self.0.insert(f, total);
    }

    #[must_use]
    pub fn get(&self, f: FnId) -> Option<bool> {
        self.0.get(&f).copied()
    }

    /// Convenience for tests / DAG walks: mark every function in
    /// the iterator as total.
    pub fn mark_total(&mut self, fns: impl IntoIterator<Item = FnId>) {
        for f in fns {
            self.0.insert(f, true);
        }
    }
}

/// Compute totality bits over a set of function bodies in
/// topological (callee-first) order.
///
/// The spec guarantees the call graph is a DAG modulo self-loops,
/// so this terminates in one pass: for each function in the input
/// order, check if its body is total assuming the previously-
/// processed functions' bits.
///
/// **Caller is responsible for passing the functions in topo order.**
/// Self-loops are handled — `App(f, ...)` inside `f`'s body queries
/// the in-progress map; the conservative default for self is `false`
/// (a function with self-recursion isn't proven total without
/// structural-recursion analysis, which is upstream's job via the
/// fold-lift convention).
#[must_use]
pub fn compute_fn_totality<'a>(
    functions: impl IntoIterator<Item = (FnId, &'a Expr)>,
) -> FnTotality {
    let mut out = FnTotality::new();
    for (id, body) in functions {
        let total = is_total(body, &out);
        out.insert(id, total);
    }
    out
}

/// Is `expr` total?
///
/// A subtree is total iff it contains no `Crash` and every `App` /
/// `Fold` / `Gen` references a function whose totality is `Some(true)`
/// in `fns`. Unknown callables are treated as non-total — this is
/// conservative for elimination rewrites, which is the safe default.
#[must_use]
pub fn is_total(expr: &Expr, fns: &FnTotality) -> bool {
    match expr {
        Expr::Crash { .. } => false,
        Expr::Var { .. } | Expr::Lit { .. } => true,
        Expr::App { target, args, .. } => {
            fns.get(*target).unwrap_or(false) && args.iter().all(|a| is_total(a, fns))
        }
        Expr::Let { value, body, .. } => is_total(value, fns) && is_total(body, fns),
        Expr::Match { scrutinee, arms, .. } => {
            is_total(scrutinee, fns)
                && arms.iter().all(|arm| {
                    arm.guards.iter().all(|g| is_total(g, fns)) && is_total(&arm.body, fns)
                })
        }
        Expr::Con { args, .. } => args.iter().all(|a| is_total(a, fns)),
        Expr::Fold { fold_fn, target, init, captures, .. } => {
            fns.get(*fold_fn).unwrap_or(false)
                && is_total(target, fns)
                && init.iter().all(|e| is_total(e, fns))
                && captures.iter().all(|e| is_total(e, fns))
        }
        Expr::Gen { step_fn, bound, init, captures, .. } => {
            fns.get(*step_fn).unwrap_or(false)
                && is_total(bound, fns)
                && init.iter().all(|e| is_total(e, fns))
                && captures.iter().all(|e| is_total(e, fns))
        }
        Expr::BufLit { elements, .. } => elements.iter().all(|e| is_total(e, fns)),
        Expr::BufLoad { buf, idx, .. } | Expr::BufLoadUnchecked { buf, idx, .. } => {
            is_total(buf, fns) && is_total(idx, fns)
        }
        Expr::BufAppend { buf, val, .. } => is_total(buf, fns) && is_total(val, fns),
        Expr::BufSet { buf, idx, val, .. } => {
            is_total(buf, fns) && is_total(idx, fns) && is_total(val, fns)
        }
    }
}
