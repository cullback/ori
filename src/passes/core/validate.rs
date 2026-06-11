//! Core IR validator.
//!
//! Runs after AST→Core to catch malformed Core programs before
//! they hit `to_ssa`. Checks invariants the spec relies on but
//! the Rust type system can't enforce. Validation is *not*
//! load-bearing for correctness (a well-formed AST→Core produces
//! well-formed Core by construction); it's a tripwire that
//! converts silent-wrong failure modes into loud ones.
//!
//! Today's checks:
//!
//! 1. **Scope correctness.** Every `Var.sym` references an
//!    in-scope binding: a function parameter, a `Let.binders`
//!    entry, or a `Pattern::Constructor` binder.
//!
//!    **Known limitation**: today's AST→Core uses a runtime
//!    `ctx.locals` table to alias an original AST `SymbolId` to a
//!    list of minted slot syms for multi-slot bindings. The
//!    `Pattern::Constructor` binders carry the slot syms but the
//!    body references the original AST sym via `Var(ast_sym)`.
//!    This validator sees the body's reference as unbound. The
//!    structural fix is making multi-slot binding minting visible
//!    in the IR shape (e.g., the redesign's single-binder `Let`);
//!    until then the scope check has false positives on
//!    multi-slot destructuring matches.
//!
//! 2. **DAG call graph.** No cycles among `App.target`s (the
//!    upstream `topo` pass enforces this, but checking again at
//!    Core boundary catches the case where a rewrite would have
//!    introduced one).
//!
//! 3. **No `Type::Var` in expression positions.** The polymorphic-
//!    `Con.ty` workaround means `Type::Var` *can* appear stored on
//!    `Con` nodes; this is the keystone footgun and we exempt the
//!    `Con.ty` field today. Type vars appearing anywhere else are
//!    a real silent-wrong bug — this check surfaces them loud.
//!
//! Default off; run with `ORI_VALIDATE_CORE=1` to enable. Opt-in
//! because the scope check has known false positives until the
//! multi-slot binding shape is fixed at the IR level.

use std::collections::{HashMap, HashSet};

use super::expr::{Expr, MatchArm, Pattern};
use crate::symbol::SymbolId;
use crate::types::engine::Type;

/// Run all validators over a single Core function body.
///
/// `params` are the function's parameter symbols (they form the
/// outermost scope). `callers_seen` is the bottom-up call stack
/// used by the DAG check; pass an empty set for the root.
pub fn validate_function(
    name: &str,
    params: &[SymbolId],
    body: &Expr,
) -> Result<(), ValidationError> {
    let mut scope: HashSet<SymbolId> = params.iter().copied().collect();
    check_scope(body, &mut scope)
        .map_err(|err| ValidationError::Scope { function: name.to_owned(), err })?;
    check_no_type_var_in_exprs(body)
        .map_err(|err| ValidationError::TypeVar { function: name.to_owned(), err })?;
    Ok(())
}

/// Verify the inter-function call graph is acyclic. Walk every
/// function's body collecting `App.target` edges, then run a
/// standard DFS cycle detector. Self-recursion is the one allowed
/// exception (structural recursion via `__fold_N` self-calls is
/// the only iteration primitive at Core).
pub fn validate_call_graph(
    functions: &HashMap<SymbolId, Expr>,
) -> Result<(), ValidationError> {
    let mut edges: HashMap<SymbolId, HashSet<SymbolId>> = HashMap::new();
    for (caller, body) in functions {
        let mut callees: HashSet<SymbolId> = HashSet::new();
        collect_callees(body, &mut callees);
        callees.remove(caller); // self-recursion allowed
        edges.insert(*caller, callees);
    }
    let mut visiting: HashSet<SymbolId> = HashSet::new();
    let mut visited: HashSet<SymbolId> = HashSet::new();
    for caller in functions.keys() {
        if !visited.contains(caller) {
            let mut path: Vec<SymbolId> = Vec::new();
            if let Some(cycle) = dfs_cycle(*caller, &edges, &mut visiting, &mut visited, &mut path)
            {
                return Err(ValidationError::CallGraphCycle(cycle));
            }
        }
    }
    Ok(())
}

#[derive(Debug)]
pub enum ValidationError {
    Scope { function: String, err: ScopeError },
    TypeVar { function: String, err: TypeVarError },
    CallGraphCycle(Vec<SymbolId>),
}

#[derive(Debug)]
pub struct ScopeError {
    pub unbound_sym: SymbolId,
}

#[derive(Debug)]
pub struct TypeVarError {
    pub where_seen: &'static str,
}

// ---------- scope check ----------

fn check_scope(expr: &Expr, scope: &mut HashSet<SymbolId>) -> Result<(), ScopeError> {
    match expr {
        Expr::Var { sym, .. } => {
            if scope.contains(sym) {
                Ok(())
            } else {
                Err(ScopeError { unbound_sym: *sym })
            }
        }
        Expr::Lit { .. } => Ok(()),
        Expr::App { args, .. } => {
            // App.target resolves through the symbol table, not the
            // local scope — don't check it here.
            for a in args {
                check_scope(a, scope)?;
            }
            Ok(())
        }
        Expr::Let { binders, value, body, .. } => {
            check_scope(value, scope)?;
            let prev: Vec<bool> = binders.iter().map(|s| scope.insert(*s)).collect();
            let result = check_scope(body, scope);
            for (sym, was_new) in binders.iter().zip(prev) {
                if was_new {
                    scope.remove(sym);
                }
            }
            result
        }
        Expr::Match { scrutinee_slots, arms, .. } => {
            for s in scrutinee_slots {
                check_scope(s, scope)?;
            }
            for arm in arms {
                check_arm_scope(arm, scope)?;
            }
            Ok(())
        }
        Expr::Cata { target_slots, init, captures, .. } => {
            for s in target_slots {
                check_scope(s, scope)?;
            }
            for e in init {
                check_scope(e, scope)?;
            }
            for e in captures {
                check_scope(e, scope)?;
            }
            Ok(())
        }
        Expr::Con { args, .. } => {
            for a in args {
                check_scope(a, scope)?;
            }
            Ok(())
        }
        Expr::BufLit { elements, .. } => {
            for e in elements {
                check_scope(e, scope)?;
            }
            Ok(())
        }
        Expr::BufLoad { buf, idx, .. } => {
            check_scope(buf, scope)?;
            check_scope(idx, scope)
        }
        Expr::BufAppend { buf_slots, val_slots, .. } => {
            for e in buf_slots {
                check_scope(e, scope)?;
            }
            for e in val_slots {
                check_scope(e, scope)?;
            }
            Ok(())
        }
        Expr::BufSet { buf_slots, idx, val_slots, .. } => {
            for e in buf_slots {
                check_scope(e, scope)?;
            }
            check_scope(idx, scope)?;
            for e in val_slots {
                check_scope(e, scope)?;
            }
            Ok(())
        }
    }
}

fn check_arm_scope(arm: &MatchArm, scope: &mut HashSet<SymbolId>) -> Result<(), ScopeError> {
    let bound_here = collect_pattern_binders(&arm.pattern);
    let prev: Vec<bool> = bound_here.iter().map(|s| scope.insert(*s)).collect();
    let mut result = Ok(());
    for g in &arm.guards {
        if let Err(e) = check_scope(g, scope) {
            result = Err(e);
            break;
        }
    }
    if result.is_ok() {
        for b in &arm.body {
            if let Err(e) = check_scope(b, scope) {
                result = Err(e);
                break;
            }
        }
    }
    for (sym, was_new) in bound_here.iter().zip(prev) {
        if was_new {
            scope.remove(sym);
        }
    }
    result
}

fn collect_pattern_binders(pat: &Pattern) -> Vec<SymbolId> {
    match pat {
        Pattern::Wildcard => Vec::new(),
        Pattern::Binding(s) => vec![*s],
        Pattern::Constructor { binders, .. } => binders
            .iter()
            .flat_map(|field| field.iter().filter_map(|b| b.as_sym()))
            .collect(),
    }
}

// ---------- DAG check ----------

fn collect_callees(expr: &Expr, callees: &mut HashSet<SymbolId>) {
    match expr {
        Expr::Var { .. } | Expr::Lit { .. } => {}
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
        Expr::Match { scrutinee_slots, arms, .. } => {
            for s in scrutinee_slots {
                collect_callees(s, callees);
            }
            for arm in arms {
                for g in &arm.guards {
                    collect_callees(g, callees);
                }
                for b in &arm.body {
                    collect_callees(b, callees);
                }
            }
        }
        Expr::Cata { fold_fn, target_slots, init, captures, .. } => {
            callees.insert(*fold_fn);
            for s in target_slots {
                collect_callees(s, callees);
            }
            for e in init {
                collect_callees(e, callees);
            }
            for e in captures {
                collect_callees(e, callees);
            }
        }
        Expr::Con { args, .. } => {
            for a in args {
                collect_callees(a, callees);
            }
        }
        Expr::BufLit { elements, .. } => {
            for e in elements {
                collect_callees(e, callees);
            }
        }
        Expr::BufLoad { buf, idx, .. } => {
            collect_callees(buf, callees);
            collect_callees(idx, callees);
        }
        Expr::BufAppend { buf_slots, val_slots, .. } => {
            for e in buf_slots {
                collect_callees(e, callees);
            }
            for e in val_slots {
                collect_callees(e, callees);
            }
        }
        Expr::BufSet { buf_slots, idx, val_slots, .. } => {
            for e in buf_slots {
                collect_callees(e, callees);
            }
            collect_callees(idx, callees);
            for e in val_slots {
                collect_callees(e, callees);
            }
        }
    }
}

fn dfs_cycle(
    node: SymbolId,
    edges: &HashMap<SymbolId, HashSet<SymbolId>>,
    visiting: &mut HashSet<SymbolId>,
    visited: &mut HashSet<SymbolId>,
    path: &mut Vec<SymbolId>,
) -> Option<Vec<SymbolId>> {
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

// ---------- Type::Var check ----------

fn check_no_type_var_in_exprs(expr: &Expr) -> Result<(), TypeVarError> {
    let check_ty = |ty: &Type, where_seen: &'static str| -> Result<(), TypeVarError> {
        if has_type_var(ty) {
            Err(TypeVarError { where_seen })
        } else {
            Ok(())
        }
    };
    match expr {
        Expr::Var { ty, .. } => check_ty(ty, "Var.ty")?,
        Expr::Lit { ty, .. } => check_ty(ty, "Lit.ty")?,
        Expr::App { ty, args, .. } => {
            check_ty(ty, "App.ty")?;
            for a in args {
                check_no_type_var_in_exprs(a)?;
            }
        }
        Expr::Let { ty, value, body, .. } => {
            check_ty(ty, "Let.ty")?;
            check_no_type_var_in_exprs(value)?;
            check_no_type_var_in_exprs(body)?;
        }
        Expr::Match { ty, scrutinee_slots, arms, .. } => {
            check_ty(ty, "Match.ty")?;
            for s in scrutinee_slots {
                check_no_type_var_in_exprs(s)?;
            }
            for arm in arms {
                for g in &arm.guards {
                    check_no_type_var_in_exprs(g)?;
                }
                for b in &arm.body {
                    check_no_type_var_in_exprs(b)?;
                }
            }
        }
        Expr::Cata { ty, target_slots, init, captures, .. } => {
            check_ty(ty, "Cata.ty")?;
            for s in target_slots {
                check_no_type_var_in_exprs(s)?;
            }
            for e in init {
                check_no_type_var_in_exprs(e)?;
            }
            for e in captures {
                check_no_type_var_in_exprs(e)?;
            }
        }
        // Con.ty is the polymorphic-stamping workaround target —
        // exempt from this check until the upstream fix lands.
        Expr::Con { args, .. } => {
            for a in args {
                check_no_type_var_in_exprs(a)?;
            }
        }
        Expr::BufLit { ty, elements, .. } => {
            check_ty(ty, "BufLit.ty")?;
            for e in elements {
                check_no_type_var_in_exprs(e)?;
            }
        }
        Expr::BufLoad { ty, buf, idx, .. } => {
            check_ty(ty, "BufLoad.ty")?;
            check_no_type_var_in_exprs(buf)?;
            check_no_type_var_in_exprs(idx)?;
        }
        Expr::BufAppend { ty, buf_slots, val_slots, .. } => {
            check_ty(ty, "BufAppend.ty")?;
            for e in buf_slots {
                check_no_type_var_in_exprs(e)?;
            }
            for e in val_slots {
                check_no_type_var_in_exprs(e)?;
            }
        }
        Expr::BufSet { ty, buf_slots, idx, val_slots, .. } => {
            check_ty(ty, "BufSet.ty")?;
            for e in buf_slots {
                check_no_type_var_in_exprs(e)?;
            }
            check_no_type_var_in_exprs(idx)?;
            for e in val_slots {
                check_no_type_var_in_exprs(e)?;
            }
        }
    }
    Ok(())
}

fn has_type_var(ty: &Type) -> bool {
    match ty {
        Type::Var(_) => true,
        Type::Con(_) => false,
        Type::App(_, args) => args.iter().any(has_type_var),
        Type::Arrow(params, ret, _) => params.iter().any(has_type_var) || has_type_var(ret),
        Type::Tuple(elems) => elems.iter().any(has_type_var),
        Type::Record { fields, .. } => fields.iter().any(|(_, t)| has_type_var(t)),
        Type::TagUnion { tags, .. } => tags
            .iter()
            .any(|(_, fields)| fields.iter().any(has_type_var)),
    }
}
