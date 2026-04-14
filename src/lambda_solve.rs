#![allow(
    clippy::too_many_lines,
    clippy::collapsible_if,
    clippy::needless_range_loop,
    clippy::match_same_arms,
    clippy::if_not_else,
    clippy::missing_docs_in_private_items,
    clippy::else_if_without_else,
    clippy::doc_markdown,
    clippy::iter_over_hash_type,
    clippy::explicit_iter_loop,
    clippy::needless_lifetimes,
    unused_imports,
    reason = "lambda solve is a multi-phase AST walker"
)]

//! Lambda set analysis (0-CFA) — determine which lifted functions
//! can flow into each higher-order parameter position.
//!
//! Runs after `lambda_lift` (all Lambdas are now `Closure` nodes).
//! Produces a `LambdaSolution` consumed by `lambda_specialize`.

use std::collections::{HashMap, HashSet};

use crate::ast::{Decl, Expr, ExprKind, Module, Stmt};
use crate::decl_info::{self, method_key};
use crate::reachable;
use crate::resolve::ModuleScope;
use crate::source::SourceArena;
use crate::symbol::{SymbolId, SymbolKind, SymbolTable};
use crate::types::infer::InferResult;

/// A single entry in a lambda set: one possible closure value.
#[derive(Clone)]
pub struct LambdaEntry {
    /// Tag name for this closure variant (e.g. `__lambda_0`).
    pub tag_name: String,
    /// The lifted function's SymbolId.
    pub lifted_func: SymbolId,
    /// Capture SymbolIds (from the Closure node).
    pub captures: Vec<SymbolId>,
    /// If this entry is a named function ref (not a lambda), the
    /// function's display name. The apply arm dispatches via Call.
    pub func_ref: Option<String>,
}

/// A lambda set: the collection of closures that can flow into one
/// higher-order parameter position.
#[derive(Clone)]
pub struct LambdaSet {
    /// Apply function name (e.g. `__apply_List.walk_2`).
    pub apply_name: String,
    /// Closure type name (e.g. `__Closure_List.walk_2`).
    pub closure_type_name: String,
    /// Entries: one per possible closure value.
    pub entries: Vec<LambdaEntry>,
    /// Call-site arity (arguments to the closure, NOT counting the
    /// closure itself).
    pub arity: usize,
}

/// Output of the solve pass.
pub struct LambdaSolution {
    pub sets: Vec<LambdaSet>,
    /// Maps (func_display_name, param_index) → lambda set index.
    pub param_to_set: HashMap<(String, usize), usize>,
    /// Local variables that hold closure values and are called as
    /// functions. Maps SymbolId → lambda set index.
    pub local_ho_vars: HashMap<SymbolId, usize>,
}

/// Analyze the post-lambda_lift module to build lambda sets.
pub fn solve(
    module: &Module<'_>,
    arena: &SourceArena,
    scope: &ModuleScope,
    infer_result: &InferResult,
    symbols: &SymbolTable,
) -> LambdaSolution {
    let decls = decl_info::build(arena, module, scope, infer_result, symbols);
    let reachable_set = reachable::compute(&decls, module, symbols);

    let mut ctx = SolveCtx {
        funcs: &decls.funcs,
        func_arities: &decls.func_arities,
        constructors_keys: decls.constructors.keys().cloned().collect(),
        symbols,
        sets: Vec::new(),
        param_to_set: HashMap::new(),
        ho_vars: HashMap::new(),
        lambda_counter: 0,
        current_func: None,
        current_params: HashMap::new(),
        ho_func_params: HashSet::new(),
        return_closures: HashMap::new(),
        local_closures: HashMap::new(),
        local_ho_vars: HashMap::new(),
    };

    // Iterate to fixpoint: each pass may discover new HO positions
    // as closures propagate through the call graph. The propagation
    // step traces HO status through lambda captures: if __lifted_N's
    // param i is HO, then wherever Closure { func: __lifted_N,
    // captures } appears, captures[i] is also HO.
    loop {
        let before = snapshot_size(&ctx);
        solve_free_functions(&mut ctx, &module.decls, &reachable_set);
        solve_methods(&mut ctx, &module.decls, &reachable_set);
        propagate_captures(&mut ctx, &module.decls, &reachable_set);
        let after = snapshot_size(&ctx);
        if after == before {
            break;
        }
    }

    // Completion: ensure every Closure in the module has its func in
    // at least one lambda set. Closures the flow analysis missed (deep
    // method-return chains, etc.) get singleton fallback sets so the
    // specialize pass can rewrite them to constructor calls.
    ensure_all_closures_registered(&mut ctx, &module.decls);

    LambdaSolution {
        sets: ctx.sets,
        param_to_set: ctx.param_to_set,
        local_ho_vars: ctx.local_ho_vars,
    }
}

struct SolveCtx<'a> {
    funcs: &'a HashSet<String>,
    func_arities: &'a HashMap<String, usize>,
    constructors_keys: HashSet<String>,
    symbols: &'a SymbolTable,
    sets: Vec<LambdaSet>,
    param_to_set: HashMap<(String, usize), usize>,
    ho_vars: HashMap<SymbolId, usize>,
    lambda_counter: usize,
    current_func: Option<String>,
    current_params: HashMap<SymbolId, (String, usize)>,
    /// Tracks which (lifted_func_name, param_index) are HO call targets.
    /// Used to propagate HO status through captures.
    ho_func_params: HashSet<(String, usize)>,
    /// Per function: which (lifted_func, captures) can be returned.
    return_closures: HashMap<String, Vec<(SymbolId, Vec<SymbolId>)>>,
    /// Per local variable: which (lifted_func, captures) it can hold.
    local_closures: HashMap<SymbolId, Vec<(SymbolId, Vec<SymbolId>)>>,
    /// Local variables (let-bound) that are called as functions.
    /// Collected during solve, included in the output.
    local_ho_vars: HashMap<SymbolId, usize>,
}

fn snapshot_size(ctx: &SolveCtx<'_>) -> usize {
    ctx.param_to_set.len()
        + ctx.local_closures.values().map(Vec::len).sum::<usize>()
        + ctx.return_closures.values().map(Vec::len).sum::<usize>()
        + ctx.sets.iter().map(|s| s.entries.len()).sum::<usize>()
        + ctx.ho_vars.len()
        + ctx.local_ho_vars.len()
}

impl SolveCtx<'_> {
    fn is_known_func(&self, sym: SymbolId) -> bool {
        self.funcs.contains(self.symbols.display(sym))
    }

    fn is_constructor(&self, sym: SymbolId) -> bool {
        self.constructors_keys.contains(self.symbols.display(sym))
    }

    fn func_arity(&self, sym: SymbolId) -> usize {
        self.func_arities
            .get(self.symbols.display(sym))
            .copied()
            .unwrap_or(0)
    }
}

fn solve_free_functions(
    ctx: &mut SolveCtx<'_>,
    decls: &[Decl<'_>],
    reachable_set: &HashSet<String>,
) {
    for decl in decls {
        if let Decl::FuncDef {
            name, params, body, ..
        } = decl
        {
            let name_str = ctx.symbols.display(*name).to_owned();
            if reachable_set.contains(&name_str) {
                ctx.current_func = Some(name_str.clone());
                ctx.current_params.clear();
                for (i, p) in params.iter().enumerate() {
                    ctx.current_params.insert(*p, (name_str.clone(), i));
                    let key = (name_str.clone(), i);
                    if let Some(&ls_idx) = ctx.param_to_set.get(&key) {
                        ctx.ho_vars.insert(*p, ls_idx);
                    }
                }
                solve_expr(ctx, body);
                let ret = expr_closures(ctx, body);
                if !ret.is_empty() {
                    ctx.return_closures.insert(name_str.clone(), ret);
                }
                for p in params {
                    ctx.ho_vars.remove(p);
                }
                ctx.current_func = None;
                ctx.current_params.clear();
            }
        }
    }
}

fn solve_methods(
    ctx: &mut SolveCtx<'_>,
    decls: &[Decl<'_>],
    reachable_set: &HashSet<String>,
) {
    for decl in decls {
        if let Decl::TypeAnno {
            name: type_name,
            methods,
            ..
        } = decl
        {
            let type_name_str = ctx.symbols.display(*type_name).to_owned();
            for method in methods {
                if let Decl::FuncDef {
                    name: method_name,
                    params,
                    body,
                    ..
                } = method
                {
                    let method_str = ctx.symbols.display(*method_name);
                    let mangled = method_key(&type_name_str, method_str);
                    if reachable_set.contains(&mangled) {
                        ctx.current_func = Some(mangled.clone());
                        ctx.current_params.clear();
                        for (i, p) in params.iter().enumerate() {
                            ctx.current_params.insert(*p, (mangled.clone(), i));
                            let key = (mangled.clone(), i);
                            if let Some(&ls_idx) = ctx.param_to_set.get(&key) {
                                ctx.ho_vars.insert(*p, ls_idx);
                            }
                        }
                        solve_expr(ctx, body);
                        let ret = expr_closures(ctx, body);
                        if !ret.is_empty() {
                            ctx.return_closures.insert(mangled, ret);
                        }
                        for p in params {
                            ctx.ho_vars.remove(p);
                        }
                        ctx.current_func = None;
                        ctx.current_params.clear();
                    }
                }
            }
        }
    }
}

/// Propagate HO status through Closure captures. If __lifted_N has
/// a capture parameter at index i that is HO (called as a function),
/// then wherever Closure { func: __lifted_N, captures } appears, the
/// capture expression at index i must also be marked HO.
fn propagate_captures(
    ctx: &mut SolveCtx<'_>,
    decls: &[Decl<'_>],
    _reachable_set: &HashSet<String>,
) {
    // Collect: for each lifted func name, which capture indices are HO?
    let mut ho_captures: HashMap<String, Vec<usize>> = HashMap::new();
    for (func_name, param_idx) in &ctx.ho_func_params {
        ho_captures
            .entry(func_name.clone())
            .or_default()
            .push(*param_idx);
    }
    if ho_captures.is_empty() {
        return;
    }

    // Walk all expressions looking for Closure nodes whose func has
    // HO captures. When found, propagate to the enclosing function's
    // param (which the capture expression references).
    for decl in decls {
        propagate_in_decl(ctx, decl, &ho_captures);
    }
}

fn propagate_in_decl(
    ctx: &mut SolveCtx<'_>,
    decl: &Decl<'_>,
    ho_captures: &HashMap<String, Vec<usize>>,
) {
    match decl {
        Decl::FuncDef {
            name, params, body, ..
        } => {
            let name_str = ctx.symbols.display(*name).to_owned();
            let mut local_params: HashMap<SymbolId, (String, usize)> = HashMap::new();
            for (i, p) in params.iter().enumerate() {
                local_params.insert(*p, (name_str.clone(), i));
            }
            propagate_in_expr(ctx, body, &local_params, ho_captures);
        }
        Decl::TypeAnno { methods, name, .. } => {
            let type_name = ctx.symbols.display(*name).to_owned();
            for method in methods {
                if let Decl::FuncDef {
                    name: method_name,
                    params,
                    body,
                    ..
                } = method
                {
                    let method_str = ctx.symbols.display(*method_name);
                    let mangled = method_key(&type_name, method_str);
                    let mut local_params: HashMap<SymbolId, (String, usize)> = HashMap::new();
                    for (i, p) in params.iter().enumerate() {
                        local_params.insert(*p, (mangled.clone(), i));
                    }
                    propagate_in_expr(ctx, body, &local_params, ho_captures);
                }
            }
        }
    }
}

fn propagate_in_expr(
    ctx: &mut SolveCtx<'_>,
    expr: &Expr<'_>,
    local_params: &HashMap<SymbolId, (String, usize)>,
    ho_captures: &HashMap<String, Vec<usize>>,
) {
    match &expr.kind {
        ExprKind::Closure { func, captures } => {
            let func_name = ctx.symbols.display(*func).to_owned();
            if let Some(ho_indices) = ho_captures.get(&func_name) {
                for &cap_idx in ho_indices {
                    if cap_idx < captures.len() {
                        if let ExprKind::Name(sym) = &captures[cap_idx].kind {
                            if let Some((enclosing_func, param_idx)) = local_params.get(sym) {
                                let key = (enclosing_func.clone(), *param_idx);
                                let lifted_key = (func_name.clone(), cap_idx);
                                if let Some(&lifted_ls) = ctx.param_to_set.get(&lifted_key) {
                                    if let Some(&existing_ls) = ctx.param_to_set.get(&key) {
                                        // Both positions have lambda sets — merge entries.
                                        if existing_ls != lifted_ls {
                                            let entries_to_add: Vec<_> =
                                                ctx.sets[existing_ls].entries.clone();
                                            for entry in entries_to_add {
                                                let already = ctx.sets[lifted_ls]
                                                    .entries
                                                    .iter()
                                                    .any(|e| e.lifted_func == entry.lifted_func);
                                                if !already {
                                                    ctx.sets[lifted_ls].entries.push(entry);
                                                }
                                            }
                                            // Redirect the existing key to the lifted set.
                                            ctx.param_to_set.insert(key, lifted_ls);
                                        }
                                    } else {
                                        ctx.param_to_set.insert(key, lifted_ls);
                                    }
                                }
                            }
                        }
                    }
                }
            }
            for c in captures {
                propagate_in_expr(ctx, c, local_params, ho_captures);
            }
        }
        // Recurse into all other expressions.
        ExprKind::Call { args, .. } | ExprKind::QualifiedCall { args, .. } => {
            for a in args { propagate_in_expr(ctx, a, local_params, ho_captures); }
        }
        ExprKind::MethodCall { receiver, args, .. } => {
            propagate_in_expr(ctx, receiver, local_params, ho_captures);
            for a in args { propagate_in_expr(ctx, a, local_params, ho_captures); }
        }
        ExprKind::BinOp { lhs, rhs, .. } => {
            propagate_in_expr(ctx, lhs, local_params, ho_captures);
            propagate_in_expr(ctx, rhs, local_params, ho_captures);
        }
        ExprKind::Block(stmts, result) => {
            for s in stmts {
                match s {
                    Stmt::Let { val, .. } | Stmt::Destructure { val, .. } => {
                        propagate_in_expr(ctx, val, local_params, ho_captures);
                    }
                    Stmt::Guard { condition, return_val } => {
                        propagate_in_expr(ctx, condition, local_params, ho_captures);
                        propagate_in_expr(ctx, return_val, local_params, ho_captures);
                    }
                    Stmt::TypeHint { .. } => {}
                }
            }
            propagate_in_expr(ctx, result, local_params, ho_captures);
        }
        ExprKind::If { expr: scrutinee, arms, else_body } => {
            propagate_in_expr(ctx, scrutinee, local_params, ho_captures);
            for arm in arms {
                for g in &arm.guards { propagate_in_expr(ctx, g, local_params, ho_captures); }
                propagate_in_expr(ctx, &arm.body, local_params, ho_captures);
            }
            if let Some(eb) = else_body { propagate_in_expr(ctx, eb, local_params, ho_captures); }
        }
        ExprKind::Fold { expr: scrutinee, arms } => {
            propagate_in_expr(ctx, scrutinee, local_params, ho_captures);
            for arm in arms {
                for g in &arm.guards { propagate_in_expr(ctx, g, local_params, ho_captures); }
                propagate_in_expr(ctx, &arm.body, local_params, ho_captures);
            }
        }
        ExprKind::Record { fields } => {
            for (_, e) in fields { propagate_in_expr(ctx, e, local_params, ho_captures); }
        }
        ExprKind::RecordUpdate { base, updates } => {
            propagate_in_expr(ctx, base, local_params, ho_captures);
            for (_, e) in updates { propagate_in_expr(ctx, e, local_params, ho_captures); }
        }
        ExprKind::FieldAccess { record, .. } => {
            propagate_in_expr(ctx, record, local_params, ho_captures);
        }
        ExprKind::Tuple(elems) | ExprKind::ListLit(elems) => {
            for e in elems { propagate_in_expr(ctx, e, local_params, ho_captures); }
        }
        ExprKind::Lambda { body, .. } => {
            propagate_in_expr(ctx, body, local_params, ho_captures);
        }
        ExprKind::Is { expr: inner, .. } => {
            propagate_in_expr(ctx, inner, local_params, ho_captures);
        }
        ExprKind::IntLit(_) | ExprKind::FloatLit(_) | ExprKind::StrLit(_) | ExprKind::Name(_) => {}
    }
}

/// What (lifted_func, captures) can this expression evaluate to?
fn expr_closures(ctx: &SolveCtx<'_>, expr: &Expr<'_>) -> Vec<(SymbolId, Vec<SymbolId>)> {
    match &expr.kind {
        ExprKind::Closure { func, captures } => {
            vec![(*func, collect_capture_syms(captures))]
        }
        ExprKind::Name(sym) => {
            if let Some(closures) = ctx.local_closures.get(sym) {
                return closures.clone();
            }
            // Check if sym is a function parameter with a known lambda set.
            if let Some((func_name, param_idx)) = ctx.current_params.get(sym) {
                let key = (func_name.clone(), *param_idx);
                if let Some(&ls_idx) = ctx.param_to_set.get(&key) {
                    return ctx.sets[ls_idx].entries.iter()
                        .map(|e| (e.lifted_func, e.captures.clone()))
                        .collect();
                }
            }
            Vec::new()
        }
        ExprKind::Call { target, .. } => {
            let name = ctx.symbols.display(*target).to_owned();
            ctx.return_closures.get(&name).cloned().unwrap_or_default()
        }
        ExprKind::QualifiedCall { segments, .. } => {
            let name = segments.join(".");
            ctx.return_closures.get(&name).cloned().unwrap_or_default()
        }
        ExprKind::MethodCall { resolved, .. } => {
            if let Some(name) = resolved {
                ctx.return_closures.get(name).cloned().unwrap_or_default()
            } else {
                Vec::new()
            }
        }
        ExprKind::Block(_, result) => expr_closures(ctx, result),
        ExprKind::If { arms, else_body, .. } => {
            let mut all = Vec::new();
            for arm in arms {
                all.extend(expr_closures(ctx, &arm.body));
            }
            if let Some(eb) = else_body {
                all.extend(expr_closures(ctx, eb));
            }
            all
        }
        _ => Vec::new(),
    }
}

fn solve_expr(ctx: &mut SolveCtx<'_>, expr: &Expr<'_>) {
    match &expr.kind {
        // Call to a known function: check args for closures/HO values.
        ExprKind::Call { target, args, .. } if ctx.is_known_func(*target) => {
            let name = ctx.symbols.display(*target).to_owned();
            solve_call_args(ctx, &name, args, 0);
        }
        // Call to a local variable: this is an HO call site.
        ExprKind::Call { target, args, .. } => {
            if !ctx.is_constructor(*target) {
                // Check if target is a function parameter.
                if let Some((func_name, param_idx)) = ctx.current_params.get(target).cloned() {
                    let key = (func_name.clone(), param_idx);
                    ctx.ho_func_params.insert(key.clone());
                    if !ctx.param_to_set.contains_key(&key) {
                        let arity = args.len();
                        let ls_idx = new_lambda_set(ctx, &func_name, param_idx, arity);
                        ctx.ho_vars.insert(*target, ls_idx);
                    } else if !ctx.ho_vars.contains_key(target) {
                        let idx = ctx.param_to_set[&key];
                        ctx.ho_vars.insert(*target, idx);
                    }
                }
                // Check if target is a local variable holding closures.
                if let Some(closures) = ctx.local_closures.get(target).cloned() {
                    if !ctx.ho_vars.contains_key(target) {
                        let arity = args.len();
                        let caller = ctx.current_func.clone().unwrap_or_default().replace('.', "_");
                        let local_name = ctx.symbols.display(*target);
                        let key_name = format!("{caller}__local_{local_name}");
                        let ls_idx = new_lambda_set(ctx, &key_name, 0, arity);
                        for (func_sym, captures) in &closures {
                            register_closure(ctx, ls_idx, *func_sym, captures.clone());
                        }
                        ctx.ho_vars.insert(*target, ls_idx);
                        ctx.local_ho_vars.insert(*target, ls_idx);
                    }
                }
            }
            for arg in args {
                solve_expr(ctx, arg);
            }
        }
        ExprKind::QualifiedCall { segments, args, .. } => {
            let mangled = segments.join(".");
            if is_list_walk(&mangled) || ctx.funcs.contains(&mangled) {
                solve_call_args(ctx, &mangled, args, 0);
            } else {
                for arg in args {
                    solve_expr(ctx, arg);
                }
            }
        }
        ExprKind::MethodCall {
            receiver,
            args,
            resolved,
            ..
        } => {
            solve_expr(ctx, receiver);
            if let Some(target) = resolved.as_deref() {
                if is_list_walk(target) || ctx.funcs.contains(target) {
                    // Check receiver at position 0 for closures.
                    let recv_as_slice = std::slice::from_ref(receiver.as_ref());
                    solve_call_args(ctx, target, recv_as_slice, 0);
                    solve_call_args(ctx, target, args, 1);
                } else {
                    for a in args {
                        solve_expr(ctx, a);
                    }
                }
            } else {
                for a in args {
                    solve_expr(ctx, a);
                }
            }
        }
        ExprKind::BinOp { lhs, rhs, .. } => {
            solve_expr(ctx, lhs);
            solve_expr(ctx, rhs);
        }
        ExprKind::Block(stmts, result) => {
            for stmt in stmts {
                solve_stmt(ctx, stmt);
            }
            solve_expr(ctx, result);
        }
        ExprKind::If {
            expr: scrutinee,
            arms,
            else_body,
        } => {
            solve_expr(ctx, scrutinee);
            for arm in arms {
                for g in &arm.guards {
                    solve_expr(ctx, g);
                }
                solve_expr(ctx, &arm.body);
            }
            if let Some(eb) = else_body {
                solve_expr(ctx, eb);
            }
        }
        ExprKind::Fold {
            expr: scrutinee,
            arms,
        } => {
            solve_expr(ctx, scrutinee);
            for arm in arms {
                for g in &arm.guards {
                    solve_expr(ctx, g);
                }
                solve_expr(ctx, &arm.body);
            }
        }
        ExprKind::Closure { captures, .. } => {
            for c in captures {
                solve_expr(ctx, c);
            }
        }
        ExprKind::Record { fields } => {
            for (_, e) in fields {
                solve_expr(ctx, e);
            }
        }
        ExprKind::RecordUpdate { base, updates } => {
            solve_expr(ctx, base);
            for (_, e) in updates {
                solve_expr(ctx, e);
            }
        }
        ExprKind::FieldAccess { record, .. } => solve_expr(ctx, record),
        ExprKind::Tuple(elems) | ExprKind::ListLit(elems) => {
            for e in elems {
                solve_expr(ctx, e);
            }
        }
        ExprKind::Is { expr: inner, .. } => solve_expr(ctx, inner),
        ExprKind::Lambda { body, .. } => solve_expr(ctx, body),
        ExprKind::IntLit(_) | ExprKind::FloatLit(_) | ExprKind::StrLit(_) | ExprKind::Name(_) => {}
    }
}

fn solve_stmt(ctx: &mut SolveCtx<'_>, stmt: &Stmt<'_>) {
    match stmt {
        Stmt::Let { name, val } => {
            solve_expr(ctx, val);
            let closures = expr_closures(ctx, val);
            if !closures.is_empty() {
                ctx.local_closures.insert(*name, closures);
            }
        }
        Stmt::Destructure { val, .. } => solve_expr(ctx, val),
        Stmt::Guard {
            condition,
            return_val,
        } => {
            solve_expr(ctx, condition);
            solve_expr(ctx, return_val);
        }
        Stmt::TypeHint { .. } => {}
    }
}

/// Check each argument of a call. Closures and HO variables at known
/// function argument positions are registered in the lambda set for
/// that (callee, index).
fn solve_call_args(ctx: &mut SolveCtx<'_>, callee: &str, args: &[Expr<'_>], offset: usize) {
    for (i, arg) in args.iter().enumerate() {
        let idx = i + offset;
        match &arg.kind {
            ExprKind::Closure { func, captures } => {
                let ls_idx = ensure_lambda_set(ctx, callee, idx);
                let captures_syms = collect_capture_syms(captures);
                register_closure(ctx, ls_idx, *func, captures_syms);
            }
            ExprKind::Name(sym) => {
                if ctx.is_known_func(*sym) && !ctx.is_constructor(*sym) {
                    let display = ctx.symbols.display(*sym).to_owned();
                    // Check if this function returns closures. If so,
                    // register the returned closures (not a func_ref).
                    if let Some(ret_closures) = ctx.return_closures.get(&display).cloned() {
                        let ls_idx = ensure_lambda_set(ctx, callee, idx);
                        for (func_sym, captures) in ret_closures {
                            register_closure(ctx, ls_idx, func_sym, captures);
                        }
                    } else {
                        // Only register as func_ref if the function
                        // genuinely IS a callable value (not a factory
                        // that returns closures — those get caught on
                        // a later fixpoint iteration).
                        let arity = ctx.func_arity(*sym);
                        if arity > 0 {
                            let ls_idx = ensure_lambda_set_with_arity(ctx, callee, idx, arity);
                            register_func_ref(ctx, ls_idx, *sym, display);
                        }
                    }
                } else if let Some(&ls_idx) = ctx.ho_vars.get(sym) {
                    // Pass-through: HO var flows into this position.
                    let key = (callee.to_owned(), idx);
                    ctx.param_to_set.entry(key).or_insert(ls_idx);
                } else if let Some(closures) = ctx.local_closures.get(sym).cloned() {
                    // Local variable holding closures passed to HO position.
                    let ls_idx = ensure_lambda_set(ctx, callee, idx);
                    for (func_sym, captures) in closures {
                        register_closure(ctx, ls_idx, func_sym, captures);
                    }
                }
                // If this arg position is HO, and sym is a parameter
                // of the current function, propagate: the current
                // function's param is also HO (it flows into an HO
                // callee position).
                let callee_key = (callee.to_owned(), idx);
                if let Some(&callee_ls) = ctx.param_to_set.get(&callee_key) {
                    if let Some((func_name, param_idx)) = ctx.current_params.get(sym).cloned() {
                        let my_key = (func_name, param_idx);
                        if let Some(&my_ls) = ctx.param_to_set.get(&my_key) {
                            // Both exist — merge entries from my_ls into callee_ls.
                            if my_ls != callee_ls {
                                let to_add: Vec<_> = ctx.sets[my_ls].entries.clone();
                                for entry in to_add {
                                    let already = ctx.sets[callee_ls]
                                        .entries.iter()
                                        .any(|e| e.lifted_func == entry.lifted_func);
                                    if !already {
                                        ctx.sets[callee_ls].entries.push(entry);
                                    }
                                }
                                // Redirect my_key to callee_ls.
                                ctx.param_to_set.insert(my_key.clone(), callee_ls);
                            }
                        } else {
                            ctx.param_to_set.insert(my_key.clone(), callee_ls);
                        }
                        ctx.ho_func_params.insert(my_key);
                        ctx.ho_vars.insert(*sym, callee_ls);
                    }
                }
            }
            _ => {
                // Any other expression (Call, MethodCall, Block, etc.)
                // might evaluate to a closure via return_closures.
                let closures = expr_closures(ctx, arg);
                if !closures.is_empty() {
                    let ls_idx = ensure_lambda_set(ctx, callee, idx);
                    for (func_sym, captures) in closures {
                        register_closure(ctx, ls_idx, func_sym, captures);
                    }
                }
            }
        }
        solve_expr(ctx, arg);
    }
}

fn collect_capture_syms(captures: &[Expr<'_>]) -> Vec<SymbolId> {
    captures
        .iter()
        .map(|c| match &c.kind {
            ExprKind::Name(sym) => *sym,
            _ => panic!("expected Name in Closure captures"),
        })
        .collect()
}

fn ensure_lambda_set(ctx: &mut SolveCtx<'_>, callee: &str, idx: usize) -> usize {
    let key = (callee.to_owned(), idx);
    if let Some(&ls_idx) = ctx.param_to_set.get(&key) {
        return ls_idx;
    }
    new_lambda_set(ctx, callee, idx, 0) // arity filled by register_closure
}

fn ensure_lambda_set_with_arity(ctx: &mut SolveCtx<'_>, callee: &str, idx: usize, arity: usize) -> usize {
    let key = (callee.to_owned(), idx);
    if let Some(&ls_idx) = ctx.param_to_set.get(&key) {
        return ls_idx;
    }
    new_lambda_set(ctx, callee, idx, arity)
}

fn new_lambda_set(ctx: &mut SolveCtx<'_>, callee: &str, idx: usize, arity: usize) -> usize {
    let apply_name = format!("__apply_{callee}_{idx}");
    let closure_type_name = format!("__Closure_{callee}_{idx}");
    let ls_idx = ctx.sets.len();
    ctx.sets.push(LambdaSet {
        apply_name,
        closure_type_name,
        entries: Vec::new(),
        arity,
    });
    ctx.param_to_set.insert((callee.to_owned(), idx), ls_idx);
    ls_idx
}

fn register_closure(
    ctx: &mut SolveCtx<'_>,
    ls_idx: usize,
    lifted_func: SymbolId,
    captures: Vec<SymbolId>,
) {
    // Check for duplicate (same lifted func already in this set).
    let already = ctx.sets[ls_idx]
        .entries
        .iter()
        .any(|e| e.lifted_func == lifted_func);
    if already {
        return;
    }
    let tag_name = format!("__lambda_{}", ctx.lambda_counter);
    ctx.lambda_counter += 1;

    // Update arity if not yet set: look up lifted func's total params,
    // subtract captures.
    if ctx.sets[ls_idx].arity == 0 {
        if let Some(&total) = ctx.func_arities.get(ctx.symbols.display(lifted_func)) {
            ctx.sets[ls_idx].arity = total.saturating_sub(captures.len());
        }
    }

    ctx.sets[ls_idx].entries.push(LambdaEntry {
        tag_name,
        lifted_func,
        captures,
        func_ref: None,
    });
}

fn register_func_ref(
    ctx: &mut SolveCtx<'_>,
    ls_idx: usize,
    sym: SymbolId,
    display: String,
) {
    let already = ctx.sets[ls_idx]
        .entries
        .iter()
        .any(|e| e.func_ref.as_deref() == Some(&display));
    if already {
        return;
    }
    let tag_name = format!("__lambda_{}", ctx.lambda_counter);
    ctx.lambda_counter += 1;

    // func_ref entries have no captures, arity = the function's arity.
    if ctx.sets[ls_idx].arity == 0 {
        let arity = ctx.func_arities.get(&display).copied().unwrap_or(0);
        ctx.sets[ls_idx].arity = arity;
    }

    ctx.sets[ls_idx].entries.push(LambdaEntry {
        tag_name,
        lifted_func: sym,
        captures: Vec::new(),
        func_ref: Some(display),
    });
}

/// Ensure every Closure node's func is registered in at least one
/// lambda set. Creates singleton fallback sets for any missed.
fn ensure_all_closures_registered(ctx: &mut SolveCtx<'_>, decls: &[Decl<'_>]) {
    let mut missing: Vec<(SymbolId, Vec<SymbolId>)> = Vec::new();
    collect_missing_closures(ctx, decls, &mut missing);
    for (func_sym, captures) in missing {
        let func_name = ctx.symbols.display(func_sym).to_owned();
        let total_params = ctx.func_arities.get(&func_name).copied().unwrap_or(0);
        let arity = total_params.saturating_sub(captures.len());
        let key_name = format!("__fallback_{func_name}");
        let ls_idx = new_lambda_set(ctx, &key_name, 0, arity);
        register_closure(ctx, ls_idx, func_sym, captures);
    }
}

fn collect_missing_closures(
    ctx: &SolveCtx<'_>,
    decls: &[Decl<'_>],
    out: &mut Vec<(SymbolId, Vec<SymbolId>)>,
) {
    for decl in decls {
        match decl {
            Decl::FuncDef { body, .. } => collect_missing_in_expr(ctx, body, out),
            Decl::TypeAnno { methods, .. } => {
                for m in methods {
                    if let Decl::FuncDef { body, .. } = m {
                        collect_missing_in_expr(ctx, body, out);
                    }
                }
            }
        }
    }
}

fn collect_missing_in_expr(
    ctx: &SolveCtx<'_>,
    expr: &Expr<'_>,
    out: &mut Vec<(SymbolId, Vec<SymbolId>)>,
) {
    match &expr.kind {
        ExprKind::Closure { func, captures } => {
            let in_any_set = ctx.sets.iter()
                .any(|s| s.entries.iter().any(|e| e.lifted_func == *func));
            if !in_any_set {
                out.push((*func, collect_capture_syms(captures)));
            }
            for c in captures {
                collect_missing_in_expr(ctx, c, out);
            }
        }
        ExprKind::Call { args, .. } | ExprKind::QualifiedCall { args, .. } => {
            for a in args { collect_missing_in_expr(ctx, a, out); }
        }
        ExprKind::MethodCall { receiver, args, .. } => {
            collect_missing_in_expr(ctx, receiver, out);
            for a in args { collect_missing_in_expr(ctx, a, out); }
        }
        ExprKind::BinOp { lhs, rhs, .. } => {
            collect_missing_in_expr(ctx, lhs, out);
            collect_missing_in_expr(ctx, rhs, out);
        }
        ExprKind::Block(stmts, result) => {
            for s in stmts {
                match s {
                    Stmt::Let { val, .. } | Stmt::Destructure { val, .. } => {
                        collect_missing_in_expr(ctx, val, out);
                    }
                    Stmt::Guard { condition, return_val } => {
                        collect_missing_in_expr(ctx, condition, out);
                        collect_missing_in_expr(ctx, return_val, out);
                    }
                    Stmt::TypeHint { .. } => {}
                }
            }
            collect_missing_in_expr(ctx, result, out);
        }
        ExprKind::If { expr: s, arms, else_body } => {
            collect_missing_in_expr(ctx, s, out);
            for arm in arms {
                for g in &arm.guards { collect_missing_in_expr(ctx, g, out); }
                collect_missing_in_expr(ctx, &arm.body, out);
            }
            if let Some(eb) = else_body { collect_missing_in_expr(ctx, eb, out); }
        }
        ExprKind::Fold { expr: s, arms } => {
            collect_missing_in_expr(ctx, s, out);
            for arm in arms {
                for g in &arm.guards { collect_missing_in_expr(ctx, g, out); }
                collect_missing_in_expr(ctx, &arm.body, out);
            }
        }
        ExprKind::Lambda { body, .. } => collect_missing_in_expr(ctx, body, out),
        ExprKind::Record { fields } => {
            for (_, e) in fields { collect_missing_in_expr(ctx, e, out); }
        }
        ExprKind::RecordUpdate { base, updates } => {
            collect_missing_in_expr(ctx, base, out);
            for (_, e) in updates { collect_missing_in_expr(ctx, e, out); }
        }
        ExprKind::FieldAccess { record, .. } => collect_missing_in_expr(ctx, record, out),
        ExprKind::Tuple(elems) | ExprKind::ListLit(elems) => {
            for e in elems { collect_missing_in_expr(ctx, e, out); }
        }
        ExprKind::Is { expr: inner, .. } => collect_missing_in_expr(ctx, inner, out),
        ExprKind::IntLit(_) | ExprKind::FloatLit(_) | ExprKind::StrLit(_) | ExprKind::Name(_) => {}
    }
}

fn is_list_walk(name: &str) -> bool {
    let base = name
        .strip_prefix("List.")
        .or_else(|| name.rsplit_once(".List.").map(|(_, rest)| rest));
    matches!(base, Some("walk" | "walk_until"))
}
