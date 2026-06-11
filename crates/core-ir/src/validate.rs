//! Core IR validator.
//!
//! Checks the invariants the spec's "carried but not statically
//! checked" table lists. The redesign eliminates several invariants
//! by construction (no `Type::Var` in `CoreType`, single-binder
//! `Let`, single-Expr scrutinees and bodies, wildcard-vs-binder via
//! `Binder` enum), so the validator's job is smaller than in the
//! existing implementation.
//!
//! Today's checks:
//!
//! 1. **Scope correctness.** Every `Var.sym` is in scope —
//!    function parameters, `Let` binders, and `Pattern::Constructor`
//!    field binders.
//! 2. **DAG call graph.** Across a set of `(FnId, body)` pairs, no
//!    cycles in the call graph (self-recursion permitted as the
//!    structural-fold pattern; mutual recursion is the violation).

use std::collections::{HashMap, HashSet};

use crate::expr::{Expr, MatchArm};
use crate::pattern::Pattern;
use crate::sym::{FnId, LocalId};

#[derive(Debug)]
pub enum ValidationError {
    /// A `Var` references an identifier that isn't in scope.
    UnboundVar(LocalId),
    /// The call graph contains a cycle that isn't a self-loop.
    /// The cycle's node sequence is recorded for diagnostics.
    CallGraphCycle(Vec<FnId>),
}

/// Verify scope correctness for a single function body.
pub fn validate_scope(params: &[LocalId], body: &Expr) -> Result<(), ValidationError> {
    let mut scope: HashSet<LocalId> = params.iter().copied().collect();
    check_scope(body, &mut scope)
}

/// Verify the call graph across a set of functions is acyclic
/// modulo self-loops.
pub fn validate_call_graph(
    functions: &HashMap<FnId, Expr>,
) -> Result<(), ValidationError> {
    let mut edges: HashMap<FnId, HashSet<FnId>> = HashMap::new();
    for (caller, body) in functions {
        let mut callees: HashSet<FnId> = HashSet::new();
        collect_callees(body, &mut callees);
        callees.remove(caller);
        edges.insert(*caller, callees);
    }
    let mut visiting: HashSet<FnId> = HashSet::new();
    let mut visited: HashSet<FnId> = HashSet::new();
    for caller in functions.keys() {
        if !visited.contains(caller) {
            let mut path: Vec<FnId> = Vec::new();
            if let Some(cycle) = dfs_cycle(*caller, &edges, &mut visiting, &mut visited, &mut path)
            {
                return Err(ValidationError::CallGraphCycle(cycle));
            }
        }
    }
    Ok(())
}

// ---- scope check ----

fn check_scope(expr: &Expr, scope: &mut HashSet<LocalId>) -> Result<(), ValidationError> {
    match expr {
        Expr::Var { sym, .. } => {
            if scope.contains(sym) {
                Ok(())
            } else {
                Err(ValidationError::UnboundVar(*sym))
            }
        }
        Expr::Lit { .. } | Expr::Crash { .. } => Ok(()),
        Expr::App { args, .. } => {
            for a in args {
                check_scope(a, scope)?;
            }
            Ok(())
        }
        Expr::Let { binder, value, body, .. } => {
            check_scope(value, scope)?;
            let inserted = scope.insert(*binder);
            let result = check_scope(body, scope);
            if inserted {
                scope.remove(binder);
            }
            result
        }
        Expr::Match { scrutinee, arms, .. } => {
            check_scope(scrutinee, scope)?;
            for arm in arms {
                check_arm_scope(arm, scope)?;
            }
            Ok(())
        }
        Expr::Con { args, .. } => {
            for a in args {
                check_scope(a, scope)?;
            }
            Ok(())
        }
        Expr::Fold { target, init, captures, .. } => {
            check_scope(target, scope)?;
            for e in init {
                check_scope(e, scope)?;
            }
            for e in captures {
                check_scope(e, scope)?;
            }
            Ok(())
        }
        Expr::Gen { bound, init, captures, .. } => {
            check_scope(bound, scope)?;
            for e in init {
                check_scope(e, scope)?;
            }
            for e in captures {
                check_scope(e, scope)?;
            }
            Ok(())
        }
        Expr::BufLit { elements, .. } => {
            for e in elements {
                check_scope(e, scope)?;
            }
            Ok(())
        }
        Expr::BufLoad { buf, idx, .. } | Expr::BufLoadUnchecked { buf, idx, .. } => {
            check_scope(buf, scope)?;
            check_scope(idx, scope)
        }
        Expr::BufAppend { buf, val, .. } => {
            check_scope(buf, scope)?;
            check_scope(val, scope)
        }
        Expr::BufSet { buf, idx, val, .. } => {
            check_scope(buf, scope)?;
            check_scope(idx, scope)?;
            check_scope(val, scope)
        }
    }
}

fn check_arm_scope(arm: &MatchArm, scope: &mut HashSet<LocalId>) -> Result<(), ValidationError> {
    let bound_here = collect_pattern_binders(&arm.pattern);
    let was_new: Vec<bool> = bound_here.iter().map(|s| scope.insert(*s)).collect();
    let mut result = Ok(());
    for g in &arm.guards {
        if let Err(e) = check_scope(g, scope) {
            result = Err(e);
            break;
        }
    }
    if result.is_ok()
        && let Err(e) = check_scope(&arm.body, scope)
    {
        result = Err(e);
    }
    for (sym, new) in bound_here.iter().zip(was_new) {
        if new {
            scope.remove(sym);
        }
    }
    result
}

fn collect_pattern_binders(pat: &Pattern) -> Vec<LocalId> {
    match pat {
        Pattern::Wildcard => Vec::new(),
        Pattern::Binding(s) => vec![*s],
        Pattern::Constructor { binders, .. } => {
            binders.iter().filter_map(|b| b.as_sym()).collect()
        }
    }
}

// ---- DAG check ----

fn collect_callees(expr: &Expr, callees: &mut HashSet<FnId>) {
    match expr {
        Expr::Var { .. } | Expr::Lit { .. } | Expr::Crash { .. } => {}
        Expr::App { target, args, .. } => {
            callees.insert(*target);
            for a in args {
                collect_callees(a, callees);
            }
        }
        Expr::Let { value, body, .. } => {
            collect_callees(value, callees);
            collect_callees(body, callees);
        }
        Expr::Match { scrutinee, arms, .. } => {
            collect_callees(scrutinee, callees);
            for arm in arms {
                for g in &arm.guards {
                    collect_callees(g, callees);
                }
                collect_callees(&arm.body, callees);
            }
        }
        Expr::Con { args, .. } => {
            for a in args {
                collect_callees(a, callees);
            }
        }
        Expr::Fold { fold_fn, target, init, captures, .. } => {
            callees.insert(*fold_fn);
            collect_callees(target, callees);
            for e in init {
                collect_callees(e, callees);
            }
            for e in captures {
                collect_callees(e, callees);
            }
        }
        Expr::Gen { step_fn, bound, init, captures, .. } => {
            callees.insert(*step_fn);
            collect_callees(bound, callees);
            for e in init {
                collect_callees(e, callees);
            }
            for e in captures {
                collect_callees(e, callees);
            }
        }
        Expr::BufLit { elements, .. } => {
            for e in elements {
                collect_callees(e, callees);
            }
        }
        Expr::BufLoad { buf, idx, .. } | Expr::BufLoadUnchecked { buf, idx, .. } => {
            collect_callees(buf, callees);
            collect_callees(idx, callees);
        }
        Expr::BufAppend { buf, val, .. } => {
            collect_callees(buf, callees);
            collect_callees(val, callees);
        }
        Expr::BufSet { buf, idx, val, .. } => {
            collect_callees(buf, callees);
            collect_callees(idx, callees);
            collect_callees(val, callees);
        }
    }
}

fn dfs_cycle(
    node: FnId,
    edges: &HashMap<FnId, HashSet<FnId>>,
    visiting: &mut HashSet<FnId>,
    visited: &mut HashSet<FnId>,
    path: &mut Vec<FnId>,
) -> Option<Vec<FnId>> {
    visiting.insert(node);
    path.push(node);
    if let Some(succs) = edges.get(&node) {
        for &next in succs {
            if visiting.contains(&next) {
                let start = path.iter().position(|n| *n == next).unwrap_or(0);
                return Some(path[start..].to_vec());
            }
            if !visited.contains(&next)
                && let Some(cycle) = dfs_cycle(next, edges, visiting, visited, path)
            {
                return Some(cycle);
            }
        }
    }
    visiting.remove(&node);
    visited.insert(node);
    path.pop();
    None
}
