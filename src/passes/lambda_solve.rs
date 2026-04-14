#![allow(
    clippy::too_many_lines,
    clippy::collapsible_if,
    clippy::match_same_arms,
    clippy::if_not_else,
    clippy::doc_markdown,
    clippy::iter_over_hash_type,
    clippy::explicit_iter_loop,
    reason = "lambda solve is an AST walker"
)]

//! Lambda set analysis (0-CFA) — single-pass flow analysis.
//!
//! Runs after `lambda_lift`. Lifted functions are in topo order
//! (inner before outer, all before the function that contains their
//! Closure nodes). This ordering means a single pass suffices: when
//! we encounter a `Closure { func }`, `func` has already been
//! analyzed and we know which of its parameters are higher-order.

use std::collections::{HashMap, HashSet};

use crate::ast::{Decl, Expr, ExprKind, Module, Stmt};
use crate::passes::decl_info::{self, method_key};
use crate::passes::reachable;
use crate::symbol::{SymbolId, SymbolTable};
use crate::types::infer::InferResult;

// ---- Public types ----

/// A single entry in a lambda set: one possible closure value.
#[derive(Clone)]
pub struct LambdaEntry {
    pub tag_name: String,
    pub lifted_func: SymbolId,
    pub captures: Vec<SymbolId>,
    pub func_ref: Option<String>,
}

/// A lambda set: closures that can flow into one HO position.
#[derive(Clone)]
pub struct LambdaSet {
    pub apply_name: String,
    pub closure_type_name: String,
    pub entries: Vec<LambdaEntry>,
    pub arity: usize,
}

/// Output of the solve pass.
pub struct LambdaSolution {
    pub sets: Vec<LambdaSet>,
    pub param_to_set: HashMap<(String, usize), usize>,
    pub local_ho_vars: HashMap<SymbolId, usize>,
}

// ---- Solve context ----

struct Ctx<'a> {
    funcs: HashSet<String>,
    func_arities: HashMap<String, usize>,
    constructor_names: HashSet<String>,
    symbols: &'a SymbolTable,
    reachable: HashSet<String>,

    sets: Vec<LambdaSet>,
    param_to_set: HashMap<(String, usize), usize>,
    local_ho_vars: HashMap<SymbolId, usize>,
    lambda_counter: usize,

    /// Per function: which params are HO (called as a function).
    /// Persists across functions so Closure nodes can look up their
    /// lifted func's HO params.
    ho_params: HashSet<(String, usize)>,

    /// Per function: which closures can be returned.
    return_closures: HashMap<String, Vec<(SymbolId, Vec<SymbolId>)>>,

    // -- Per-function scan state (reset for each function) --
    /// Current function name.
    current_func: String,
    /// Params of current function: sym → (func_name, param_index).
    current_params: HashMap<SymbolId, (String, usize)>,
    /// HO variables in scope: sym → lambda set index.
    ho_vars: HashMap<SymbolId, usize>,
    /// Local variables holding closures: sym → [(lifted_func, captures)].
    local_closures: HashMap<SymbolId, Vec<(SymbolId, Vec<SymbolId>)>>,
}

impl Ctx<'_> {
    fn is_known_func(&self, sym: SymbolId) -> bool {
        self.funcs.contains(self.symbols.display(sym))
    }
    fn is_constructor(&self, sym: SymbolId) -> bool {
        self.constructor_names.contains(self.symbols.display(sym))
    }
    fn func_arity(&self, sym: SymbolId) -> usize {
        self.func_arities.get(self.symbols.display(sym)).copied().unwrap_or(0)
    }

    fn get_or_create_set(&mut self, key: &str, idx: usize, arity: usize) -> usize {
        let k = (key.to_owned(), idx);
        if let Some(&ls) = self.param_to_set.get(&k) {
            return ls;
        }
        let ls = self.sets.len();
        self.sets.push(LambdaSet {
            apply_name: format!("__apply_{key}_{idx}"),
            closure_type_name: format!("__Closure_{key}_{idx}"),
            entries: Vec::new(),
            arity,
        });
        self.param_to_set.insert(k, ls);
        ls
    }

    fn add_entry(&mut self, ls: usize, func: SymbolId, captures: Vec<SymbolId>, func_ref: Option<String>) {
        let already = self.sets[ls].entries.iter().any(|e| e.lifted_func == func);
        if already { return; }
        let tag_name = format!("__lambda_{}", self.lambda_counter);
        self.lambda_counter += 1;
        // Update arity from the lifted function if not yet set.
        if self.sets[ls].arity == 0 {
            if let Some(&total) = self.func_arities.get(self.symbols.display(func)) {
                self.sets[ls].arity = total.saturating_sub(captures.len());
            }
        }
        self.sets[ls].entries.push(LambdaEntry {
            tag_name, lifted_func: func, captures, func_ref,
        });
    }

    /// Merge entries from set `from` into set `into` (bidirectional).
    fn merge_sets(&mut self, a: usize, b: usize) {
        if a == b { return; }
        let a_entries: Vec<_> = self.sets[a].entries.clone();
        let b_entries: Vec<_> = self.sets[b].entries.clone();
        for e in &b_entries {
            if !self.sets[a].entries.iter().any(|x| x.lifted_func == e.lifted_func) {
                self.sets[a].entries.push(e.clone());
            }
        }
        for e in &a_entries {
            if !self.sets[b].entries.iter().any(|x| x.lifted_func == e.lifted_func) {
                self.sets[b].entries.push(e.clone());
            }
        }
        if self.sets[a].arity == 0 { self.sets[a].arity = self.sets[b].arity; }
        if self.sets[b].arity == 0 { self.sets[b].arity = self.sets[a].arity; }
    }
}

fn snapshot(ctx: &Ctx<'_>) -> usize {
    ctx.param_to_set.len()
        + ctx.sets.iter().map(|s| s.entries.len()).sum::<usize>()
        + ctx.local_closures.values().map(Vec::len).sum::<usize>()
        + ctx.return_closures.values().map(Vec::len).sum::<usize>()
        + ctx.ho_vars.len()
        + ctx.local_ho_vars.len()
}

// ---- Entry point ----

pub fn solve(
    module: &Module<'_>,
    infer_result: &InferResult,
    symbols: &SymbolTable,
) -> LambdaSolution {
    let decls = decl_info::build(module, infer_result, symbols);
    let reachable = reachable::compute(&decls, module, symbols);

    let mut ctx = Ctx {
        funcs: decls.funcs,
        func_arities: decls.func_arities,
        constructor_names: decls.constructors.keys().cloned().collect(),
        symbols,
        reachable,
        sets: Vec::new(),
        param_to_set: HashMap::new(),
        local_ho_vars: HashMap::new(),
        lambda_counter: 0,
        ho_params: HashSet::new(),
        return_closures: HashMap::new(),
        current_func: String::new(),
        current_params: HashMap::new(),
        ho_vars: HashMap::new(),
        local_closures: HashMap::new(),
    };

    // Iterate to fixpoint: each pass discovers new HO positions
    // and closure flows. Converges quickly (2-3 passes typically).
    loop {
        let before = snapshot(&ctx);
        for decl in &module.decls {
            solve_decl(&mut ctx, decl);
        }
        if snapshot(&ctx) == before {
            break;
        }
    }

    // Completion: any Closure whose func isn't in any set gets a
    // fallback singleton set.
    ensure_all_closures(&mut ctx, &module.decls);

    LambdaSolution {
        sets: ctx.sets,
        param_to_set: ctx.param_to_set,
        local_ho_vars: ctx.local_ho_vars,
    }
}

fn solve_decl(ctx: &mut Ctx<'_>, decl: &Decl<'_>) {
    match decl {
        Decl::FuncDef { name, params, body, .. } => {
            let name_str = ctx.symbols.display(*name).to_owned();
            if !ctx.reachable.contains(&name_str) && !name_str.starts_with("__lifted") {
                return;
            }
            enter_func(ctx, &name_str, params);
            scan_expr(ctx, body);
            let ret = expr_closures(ctx, body);
            if !ret.is_empty() {
                ctx.return_closures.insert(name_str, ret);
            }
            exit_func(ctx, params);
        }
        Decl::TypeAnno { name: type_name, methods, .. } => {
            let type_str = ctx.symbols.display(*type_name).to_owned();
            for method in methods {
                if let Decl::FuncDef { name: method_name, params, body, .. } = method {
                    let method_str = ctx.symbols.display(*method_name);
                    let mangled = method_key(&type_str, method_str);
                    if !ctx.reachable.contains(&mangled) { continue; }
                    enter_func(ctx, &mangled, params);
                    scan_expr(ctx, body);
                    let ret = expr_closures(ctx, body);
                    if !ret.is_empty() {
                        ctx.return_closures.insert(mangled, ret);
                    }
                    exit_func(ctx, params);
                }
            }
        }
    }
}

fn enter_func(ctx: &mut Ctx<'_>, name: &str, params: &[SymbolId]) {
    ctx.current_func = name.to_owned();
    ctx.current_params.clear();
    ctx.ho_vars.clear();
    ctx.local_closures.clear();
    for (i, p) in params.iter().enumerate() {
        ctx.current_params.insert(*p, (name.to_owned(), i));
        if let Some(&ls) = ctx.param_to_set.get(&(name.to_owned(), i)) {
            ctx.ho_vars.insert(*p, ls);
        }
    }
}

fn exit_func(ctx: &mut Ctx<'_>, params: &[SymbolId]) {
    for p in params {
        ctx.ho_vars.remove(p);
    }
}

// ---- Expression scanning ----

fn scan_expr(ctx: &mut Ctx<'_>, expr: &Expr<'_>) {
    match &expr.kind {
        ExprKind::Call { target, args, .. } if ctx.is_known_func(*target) => {
            let name = ctx.symbols.display(*target).to_owned();
            scan_call_args(ctx, &name, args, 0);
        }
        ExprKind::Call { target, args, .. } => {
            if !ctx.is_constructor(*target) {
                // Call to a parameter → mark as HO.
                if let Some((func_name, param_idx)) = ctx.current_params.get(target).cloned() {
                    let key = (func_name.clone(), param_idx);
                    ctx.ho_params.insert(key.clone());
                    if !ctx.param_to_set.contains_key(&key) {
                        let ls = ctx.get_or_create_set(&func_name, param_idx, args.len());
                        ctx.ho_vars.insert(*target, ls);
                    } else if !ctx.ho_vars.contains_key(target) {
                        let ls = ctx.param_to_set[&key];
                        ctx.ho_vars.insert(*target, ls);
                    }
                }
                // Call to a local variable holding closures.
                if let Some(closures) = ctx.local_closures.get(target).cloned() {
                    if !ctx.ho_vars.contains_key(target) {
                        let caller = ctx.current_func.replace('.', "_");
                        let local = ctx.symbols.display(*target);
                        let key = format!("{caller}__local_{local}");
                        let ls = ctx.get_or_create_set(&key, 0, args.len());
                        for (func_sym, captures) in &closures {
                            ctx.add_entry(ls, *func_sym, captures.clone(), None);
                        }
                        ctx.ho_vars.insert(*target, ls);
                        ctx.local_ho_vars.insert(*target, ls);
                    }
                }
            }
            for a in args { scan_expr(ctx, a); }
        }
        ExprKind::QualifiedCall { segments, args, .. } => {
            let mangled = segments.join(".");
            if is_list_walk(&mangled) || ctx.funcs.contains(&mangled) {
                scan_call_args(ctx, &mangled, args, 0);
            } else {
                for a in args { scan_expr(ctx, a); }
            }
        }
        ExprKind::MethodCall { receiver, args, resolved, .. } => {
            scan_expr(ctx, receiver);
            if let Some(target) = resolved.as_deref() {
                if is_list_walk(target) || ctx.funcs.contains(target) {
                    // Check receiver at position 0.
                    scan_call_args(ctx, target, std::slice::from_ref(receiver.as_ref()), 0);
                    scan_call_args(ctx, target, args, 1);
                } else {
                    for a in args { scan_expr(ctx, a); }
                }
            } else {
                for a in args { scan_expr(ctx, a); }
            }
        }
        ExprKind::BinOp { lhs, rhs, .. } => {
            scan_expr(ctx, lhs);
            scan_expr(ctx, rhs);
        }
        ExprKind::Block(stmts, result) => {
            for s in stmts { scan_stmt(ctx, s); }
            scan_expr(ctx, result);
        }
        ExprKind::If { expr: s, arms, else_body } => {
            scan_expr(ctx, s);
            for arm in arms {
                for g in &arm.guards { scan_expr(ctx, g); }
                scan_expr(ctx, &arm.body);
            }
            if let Some(eb) = else_body { scan_expr(ctx, eb); }
        }
        ExprKind::Fold { expr: s, arms } => {
            scan_expr(ctx, s);
            for arm in arms {
                for g in &arm.guards { scan_expr(ctx, g); }
                scan_expr(ctx, &arm.body);
            }
        }
        ExprKind::Closure { func, captures } => {
            // The lifted function has already been processed (topo order).
            // Propagate HO status from its params to our params through captures.
            let func_name = ctx.symbols.display(*func).to_owned();
            for (cap_idx, cap_expr) in captures.iter().enumerate() {
                let cap_key = (func_name.clone(), cap_idx);
                if ctx.ho_params.contains(&cap_key) {
                    // This capture position is HO in the lifted func.
                    // If the capture expression is a Name referencing a
                    // param of the current function, propagate HO status.
                    if let ExprKind::Name(sym) = &cap_expr.kind {
                        if let Some((enc_func, enc_idx)) = ctx.current_params.get(sym).cloned() {
                            let enc_key = (enc_func.clone(), enc_idx);
                            ctx.ho_params.insert(enc_key.clone());
                            // Link the lambda sets: merge if both exist.
                            if let Some(&lifted_ls) = ctx.param_to_set.get(&cap_key) {
                                let enc_ls = ctx.get_or_create_set(&enc_func, enc_idx, 0);
                                ctx.merge_sets(enc_ls, lifted_ls);
                                ctx.ho_vars.insert(*sym, lifted_ls);
                            }
                        }
                    }
                }
                scan_expr(ctx, cap_expr);
            }
        }
        ExprKind::Lambda { body, .. } => scan_expr(ctx, body),
        ExprKind::Record { fields } => {
            for (_, e) in fields { scan_expr(ctx, e); }
        }
        ExprKind::RecordUpdate { base, updates } => {
            scan_expr(ctx, base);
            for (_, e) in updates { scan_expr(ctx, e); }
        }
        ExprKind::FieldAccess { record, .. } => scan_expr(ctx, record),
        ExprKind::Tuple(elems) | ExprKind::ListLit(elems) => {
            for e in elems { scan_expr(ctx, e); }
        }
        ExprKind::Is { expr: inner, .. } => scan_expr(ctx, inner),
        ExprKind::IntLit(_) | ExprKind::FloatLit(_) | ExprKind::StrLit(_) | ExprKind::Name(_) => {}
    }
}

fn scan_stmt(ctx: &mut Ctx<'_>, stmt: &Stmt<'_>) {
    match stmt {
        Stmt::Let { name, val } => {
            scan_expr(ctx, val);
            let closures = expr_closures(ctx, val);
            if !closures.is_empty() {
                ctx.local_closures.insert(*name, closures);
            }
        }
        Stmt::Destructure { val, .. } => scan_expr(ctx, val),
        Stmt::Guard { condition, return_val } => {
            scan_expr(ctx, condition);
            scan_expr(ctx, return_val);
        }
        Stmt::TypeHint { .. } => {}
    }
}

// ---- Call argument scanning ----

fn scan_call_args(ctx: &mut Ctx<'_>, callee: &str, args: &[Expr<'_>], offset: usize) {
    for (i, arg) in args.iter().enumerate() {
        let idx = i + offset;
        match &arg.kind {
            ExprKind::Closure { func, captures } => {
                let ls = ctx.get_or_create_set(callee, idx, 0);
                let caps = collect_capture_syms(captures);
                ctx.add_entry(ls, *func, caps, None);
            }
            ExprKind::Name(sym) => {
                if ctx.is_known_func(*sym) && !ctx.is_constructor(*sym) {
                    let display = ctx.symbols.display(*sym).to_owned();
                    // Function that returns closures → register the returns.
                    if let Some(ret) = ctx.return_closures.get(&display).cloned() {
                        let ls = ctx.get_or_create_set(callee, idx, 0);
                        for (func_sym, captures) in ret {
                            ctx.add_entry(ls, func_sym, captures, None);
                        }
                    } else {
                        let arity = ctx.func_arity(*sym);
                        if arity > 0 {
                            let ls = ctx.get_or_create_set(callee, idx, arity);
                            ctx.add_entry(ls, *sym, Vec::new(), Some(display));
                        }
                    }
                } else if let Some(&ls) = ctx.ho_vars.get(sym) {
                    // Pass-through HO var.
                    let key = (callee.to_owned(), idx);
                    ctx.param_to_set.entry(key).or_insert(ls);
                } else if let Some(closures) = ctx.local_closures.get(sym).cloned() {
                    // Local variable holding closures.
                    let ls = ctx.get_or_create_set(callee, idx, 0);
                    for (func_sym, captures) in closures {
                        ctx.add_entry(ls, func_sym, captures, None);
                    }
                }
                // Propagate: if callee position is HO and sym is our param, merge.
                if let Some(&callee_ls) = ctx.param_to_set.get(&(callee.to_owned(), idx)) {
                    if let Some((func_name, param_idx)) = ctx.current_params.get(sym).cloned() {
                        let my_key = (func_name.clone(), param_idx);
                        ctx.ho_params.insert(my_key.clone());
                        let my_ls = ctx.get_or_create_set(&func_name, param_idx, 0);
                        ctx.merge_sets(my_ls, callee_ls);
                        ctx.ho_vars.insert(*sym, callee_ls);
                    }
                }
            }
            _ => {
                // Arbitrary expression (Call result, MethodCall result, etc.)
                let closures = expr_closures(ctx, arg);
                if !closures.is_empty() {
                    let ls = ctx.get_or_create_set(callee, idx, 0);
                    for (func_sym, captures) in closures {
                        ctx.add_entry(ls, func_sym, captures, None);
                    }
                }
            }
        }
        scan_expr(ctx, arg);
    }
}

// ---- Closure flow tracking ----

/// What closures can this expression evaluate to?
fn expr_closures(ctx: &Ctx<'_>, expr: &Expr<'_>) -> Vec<(SymbolId, Vec<SymbolId>)> {
    match &expr.kind {
        ExprKind::Closure { func, captures } => {
            vec![(*func, collect_capture_syms(captures))]
        }
        ExprKind::Name(sym) => {
            if let Some(c) = ctx.local_closures.get(sym) { return c.clone(); }
            // Parameter with known lambda set → return its entries.
            if let Some((func_name, param_idx)) = ctx.current_params.get(sym) {
                let key = (func_name.clone(), *param_idx);
                if let Some(&ls) = ctx.param_to_set.get(&key) {
                    return ctx.sets[ls].entries.iter()
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
            resolved.as_ref()
                .and_then(|n| ctx.return_closures.get(n).cloned())
                .unwrap_or_default()
        }
        ExprKind::Block(_, result) => expr_closures(ctx, result),
        ExprKind::If { arms, else_body, .. } => {
            let mut all = Vec::new();
            for arm in arms { all.extend(expr_closures(ctx, &arm.body)); }
            if let Some(eb) = else_body { all.extend(expr_closures(ctx, eb)); }
            all
        }
        _ => Vec::new(),
    }
}

fn collect_capture_syms(captures: &[Expr<'_>]) -> Vec<SymbolId> {
    captures.iter().map(|c| match &c.kind {
        ExprKind::Name(sym) => *sym,
        _ => panic!("expected Name in Closure captures"),
    }).collect()
}

// ---- Completion: fallback for missed closures ----

fn ensure_all_closures(ctx: &mut Ctx<'_>, decls: &[Decl<'_>]) {
    let mut missing: Vec<(SymbolId, Vec<SymbolId>)> = Vec::new();
    for decl in decls {
        match decl {
            Decl::FuncDef { body, .. } => find_missing(ctx, body, &mut missing),
            Decl::TypeAnno { methods, .. } => {
                for m in methods {
                    if let Decl::FuncDef { body, .. } = m {
                        find_missing(ctx, body, &mut missing);
                    }
                }
            }
        }
    }
    for (func_sym, captures) in missing {
        let name = ctx.symbols.display(func_sym).to_owned();
        let total = ctx.func_arities.get(&name).copied().unwrap_or(0);
        let arity = total.saturating_sub(captures.len());
        let key = format!("__fallback_{name}");
        let ls = ctx.get_or_create_set(&key, 0, arity);
        ctx.add_entry(ls, func_sym, captures, None);
    }
}

fn find_missing(ctx: &Ctx<'_>, expr: &Expr<'_>, out: &mut Vec<(SymbolId, Vec<SymbolId>)>) {
    if let ExprKind::Closure { func, captures } = &expr.kind {
        let in_set = ctx.sets.iter().any(|s| s.entries.iter().any(|e| e.lifted_func == *func));
        if !in_set {
            out.push((*func, collect_capture_syms(captures)));
        }
    }
    // Recurse into all children.
    match &expr.kind {
        ExprKind::Call { args, .. } | ExprKind::QualifiedCall { args, .. } => {
            for a in args { find_missing(ctx, a, out); }
        }
        ExprKind::MethodCall { receiver, args, .. } => {
            find_missing(ctx, receiver, out);
            for a in args { find_missing(ctx, a, out); }
        }
        ExprKind::BinOp { lhs, rhs, .. } => {
            find_missing(ctx, lhs, out); find_missing(ctx, rhs, out);
        }
        ExprKind::Block(stmts, result) => {
            for s in stmts { match s {
                Stmt::Let { val, .. } | Stmt::Destructure { val, .. } => find_missing(ctx, val, out),
                Stmt::Guard { condition, return_val } => {
                    find_missing(ctx, condition, out); find_missing(ctx, return_val, out);
                }
                Stmt::TypeHint { .. } => {}
            }}
            find_missing(ctx, result, out);
        }
        ExprKind::If { expr: s, arms, else_body } => {
            find_missing(ctx, s, out);
            for arm in arms {
                for g in &arm.guards { find_missing(ctx, g, out); }
                find_missing(ctx, &arm.body, out);
            }
            if let Some(eb) = else_body { find_missing(ctx, eb, out); }
        }
        ExprKind::Fold { expr: s, arms } => {
            find_missing(ctx, s, out);
            for arm in arms {
                for g in &arm.guards { find_missing(ctx, g, out); }
                find_missing(ctx, &arm.body, out);
            }
        }
        ExprKind::Closure { captures, .. } => {
            for c in captures { find_missing(ctx, c, out); }
        }
        ExprKind::Lambda { body, .. } => find_missing(ctx, body, out),
        ExprKind::Record { fields } => { for (_, e) in fields { find_missing(ctx, e, out); } }
        ExprKind::RecordUpdate { base, updates } => {
            find_missing(ctx, base, out);
            for (_, e) in updates { find_missing(ctx, e, out); }
        }
        ExprKind::FieldAccess { record, .. } => find_missing(ctx, record, out),
        ExprKind::Tuple(elems) | ExprKind::ListLit(elems) => {
            for e in elems { find_missing(ctx, e, out); }
        }
        ExprKind::Is { expr: inner, .. } => find_missing(ctx, inner, out),
        _ => {}
    }
}

fn is_list_walk(name: &str) -> bool {
    let base = name.strip_prefix("List.")
        .or_else(|| name.rsplit_once(".List.").map(|(_, r)| r));
    matches!(base, Some("walk" | "walk_until"))
}
