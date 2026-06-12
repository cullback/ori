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
//! 3. **Type consistency.** Three sub-checks:
//!    - `Var.ty` matches the type of the binding it references.
//!    - All `MatchArm.body.ty()` agree with `Match.ty`.
//!    - `BufLit.elements[i].ty()` matches `BufLit.elem_ty`.
//!    - Buffer mutation/load operations agree with element types.
//! 4. **Totality consistency.** Given an `FnTotality` map, verify
//!    that every function marked `Total` is actually total
//!    (contains no `Crash`, calls no non-total callees).

use std::collections::{HashMap, HashSet};

use crate::expr::{Expr, MatchArm};
use crate::pattern::Pattern;
use crate::sym::{FnId, LocalId};
use crate::totality::{is_total, FnTotality};
use crate::ty::CoreType;

#[derive(Debug)]
pub enum ValidationError {
    /// A `Var` references an identifier that isn't in scope.
    UnboundVar(LocalId),
    /// The call graph contains a cycle that isn't a self-loop.
    /// The cycle's node sequence is recorded for diagnostics.
    CallGraphCycle(Vec<FnId>),
    /// A `Var.ty` disagrees with the type stamped on the binding.
    VarTypeMismatch {
        sym: LocalId,
        bound_as: CoreType,
        used_as: CoreType,
    },
    /// A `MatchArm.body.ty()` disagrees with the enclosing `Match.ty`.
    ArmTypeMismatch {
        expected: CoreType,
        found: CoreType,
    },
    /// A `BufLit` element's type disagrees with the declared
    /// `elem_ty`.
    BufLitElemMismatch {
        expected: CoreType,
        found: CoreType,
    },
    /// A `BufAppend.val` or `BufSet.val` type disagrees with the
    /// buffer's element type. Also fires for `BufLoad.ty`.
    BufElementMismatch {
        op: &'static str,
        expected: CoreType,
        found: CoreType,
    },
    /// A `Fold.target.ty()` isn't a `List(_)` shape.
    FoldTargetNotList(CoreType),
    /// A function marked `Total` in the totality table contains a
    /// `Crash` or calls a non-total callee.
    TotalFunctionNotActuallyTotal(FnId),
}

/// Verify scope correctness for a single function body.
pub fn validate_scope(params: &[LocalId], body: &Expr) -> Result<(), ValidationError> {
    let mut scope: HashSet<LocalId> = params.iter().copied().collect();
    check_scope(body, &mut scope)
}

/// Verify type consistency across the tree:
///
/// - Every `Var.ty` matches the type of the binding it references.
/// - Every `MatchArm.body` has the same type as the enclosing `Match`.
/// - Every `BufLit` element has the declared `elem_ty`.
/// - Buffer mutation / load operations agree with element types.
/// - `Fold.target` is a `List(_)`.
///
/// `param_types` maps each function parameter's `LocalId` to its
/// declared type.
pub fn validate_types(
    param_types: &HashMap<LocalId, CoreType>,
    body: &Expr,
) -> Result<(), ValidationError> {
    let mut scope = param_types.clone();
    check_types(body, &mut scope)
}

/// Verify totality consistency: every function marked `Total` in
/// `fns` has a body that's actually total.
///
/// `functions` is the source of bodies; `fns` is the totality
/// table to validate. Any mismatch returns the offending `FnId`.
pub fn validate_totality(
    functions: &HashMap<FnId, Expr>,
    fns: &FnTotality,
) -> Result<(), ValidationError> {
    for (id, body) in functions {
        if fns.get(*id) == Some(true) && !is_total(body, fns) {
            return Err(ValidationError::TotalFunctionNotActuallyTotal(*id));
        }
    }
    Ok(())
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

// ---- type check ----

/// `List(T)` decomposition. We adopt the convention that a `List(_)`
/// is any `CoreType::Adt(_, [elem])` — same shape the builder's
/// `list_of` produces.
fn list_elem_ty(ty: &CoreType) -> Option<CoreType> {
    if let CoreType::Adt(_, args) = ty
        && args.len() == 1
    {
        return Some(args[0].clone());
    }
    None
}

fn check_types(
    expr: &Expr,
    scope: &mut HashMap<LocalId, CoreType>,
) -> Result<(), ValidationError> {
    match expr {
        Expr::Var { sym, ty } => {
            if let Some(bound_ty) = scope.get(sym)
                && bound_ty != ty
            {
                return Err(ValidationError::VarTypeMismatch {
                    sym: *sym,
                    bound_as: bound_ty.clone(),
                    used_as: ty.clone(),
                });
            }
            Ok(())
        }
        Expr::Lit { .. } | Expr::Crash { .. } => Ok(()),
        Expr::App { args, .. } => {
            for a in args {
                check_types(a, scope)?;
            }
            Ok(())
        }
        Expr::Let { binder, value, body, .. } => {
            check_types(value, scope)?;
            let value_ty = value.ty().clone();
            let prev = scope.insert(*binder, value_ty);
            let result = check_types(body, scope);
            match prev {
                Some(p) => { scope.insert(*binder, p); }
                None => { scope.remove(binder); }
            }
            result
        }
        Expr::Match { scrutinee, arms, ty } => {
            check_types(scrutinee, scope)?;
            for arm in arms {
                if !arm.is_return && arm.body.ty() != ty {
                    return Err(ValidationError::ArmTypeMismatch {
                        expected: ty.clone(),
                        found: arm.body.ty().clone(),
                    });
                }
                check_arm_types(arm, scope)?;
            }
            Ok(())
        }
        Expr::Con { args, .. } => {
            for a in args {
                check_types(a, scope)?;
            }
            Ok(())
        }
        Expr::Fold { target, init, captures, .. } => {
            check_types(target, scope)?;
            if list_elem_ty(target.ty()).is_none() {
                return Err(ValidationError::FoldTargetNotList(target.ty().clone()));
            }
            for e in init {
                check_types(e, scope)?;
            }
            for e in captures {
                check_types(e, scope)?;
            }
            Ok(())
        }
        Expr::Gen { bound, init, captures, .. } => {
            check_types(bound, scope)?;
            for e in init {
                check_types(e, scope)?;
            }
            for e in captures {
                check_types(e, scope)?;
            }
            Ok(())
        }
        Expr::BufLit { elements, elem_ty, .. } => {
            for e in elements {
                check_types(e, scope)?;
                if e.ty() != elem_ty {
                    return Err(ValidationError::BufLitElemMismatch {
                        expected: elem_ty.clone(),
                        found: e.ty().clone(),
                    });
                }
            }
            Ok(())
        }
        Expr::BufLoad { buf, idx, ty } | Expr::BufLoadUnchecked { buf, idx, ty } => {
            check_types(buf, scope)?;
            check_types(idx, scope)?;
            if let Some(elem) = list_elem_ty(buf.ty())
                && &elem != ty
            {
                return Err(ValidationError::BufElementMismatch {
                    op: "BufLoad",
                    expected: elem,
                    found: ty.clone(),
                });
            }
            Ok(())
        }
        Expr::BufAppend { buf, val, .. } => {
            check_types(buf, scope)?;
            check_types(val, scope)?;
            if let Some(elem) = list_elem_ty(buf.ty())
                && &elem != val.ty()
            {
                return Err(ValidationError::BufElementMismatch {
                    op: "BufAppend",
                    expected: elem,
                    found: val.ty().clone(),
                });
            }
            Ok(())
        }
        Expr::BufSet { buf, idx, val, .. } => {
            check_types(buf, scope)?;
            check_types(idx, scope)?;
            check_types(val, scope)?;
            if let Some(elem) = list_elem_ty(buf.ty())
                && &elem != val.ty()
            {
                return Err(ValidationError::BufElementMismatch {
                    op: "BufSet",
                    expected: elem,
                    found: val.ty().clone(),
                });
            }
            Ok(())
        }
    }
}

fn check_arm_types(
    arm: &MatchArm,
    scope: &mut HashMap<LocalId, CoreType>,
) -> Result<(), ValidationError> {
    // Pattern binders enter scope but we don't know their types
    // from the pattern alone (constructor field types would require
    // a tag table). For now: skip them in the type-scope; they're
    // tracked separately by scope correctness. Re-validate the
    // body's *internal* type consistency by entering with the same
    // scope (binders' Var.ty will simply be unchecked against their
    // binding because we have no source-of-truth for them).
    for g in &arm.guards {
        check_types(g, scope)?;
    }
    check_types(&arm.body, scope)
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
