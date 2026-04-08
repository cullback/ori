use std::collections::{HashMap, HashSet};

use crate::decl_info::{ConstructorMeta, DeclInfo, method_key};
use crate::ssa::ScalarType;
use crate::syntax::ast::{self, Decl, Expr, ExprKind, Stmt};
use crate::types::infer::InferResult;

// ---- Defunctionalization data structures ----

#[derive(Clone)]
pub struct LambdaEntry<'src> {
    pub tag_name: String,
    pub captures: Vec<&'src str>,
    pub capture_ho: Vec<Option<usize>>,
    pub params: Vec<&'src str>,
    pub body: Option<Expr<'src>>,
    pub func_ref: Option<String>,
}

#[derive(Clone)]
pub struct LambdaSet<'src> {
    pub apply_name: String,
    pub entries: Vec<LambdaEntry<'src>>,
    pub arity: usize,
}

pub struct DefuncTable<'src> {
    pub lambda_sets: Vec<LambdaSet<'src>>,
    pub ho_param_sets: HashMap<(String, usize), usize>,
    /// Constructor metadata for closure types (to be merged into DeclInfo.constructors).
    pub closure_constructors: HashMap<String, ConstructorMeta>,
}

/// Collect all lambdas and function references used in higher-order positions,
/// building the defunctionalization table.
pub fn collect<'src>(
    module: &ast::Module<'src>,
    decls: &DeclInfo,
    reachable: &HashSet<String>,
    infer_result: &InferResult,
) -> DefuncTable<'src> {
    let mut ctx = ScanCtx {
        funcs: &decls.funcs,
        func_arities: &decls.func_arities,
        constructors: &decls.constructors,
        list_builtins: &decls.list_builtins,
        method_resolutions: &infer_result.method_resolutions,
        lambda_sets: Vec::new(),
        ho_param_sets: HashMap::new(),
        ho_vars: HashMap::new(),
        lambda_counter: 0,
    };

    // Scan user declarations
    collect_lambdas(&mut ctx, &module.decls, reachable);

    // Duplicate ho_param_sets entries for function aliases
    let alias_entries: Vec<((String, usize), usize)> = ctx
        .ho_param_sets
        .iter()
        .flat_map(|((name, idx), &ls_idx)| {
            decls
                .func_aliases
                .get(name)
                .map(|aliases| {
                    aliases
                        .iter()
                        .map(move |alias| ((alias.clone(), *idx), ls_idx))
                        .collect::<Vec<_>>()
                })
                .unwrap_or_default()
        })
        .collect();
    for (key, ls_idx) in alias_entries {
        ctx.ho_param_sets.entry(key).or_insert(ls_idx);
    }

    // Build closure constructors
    let closure_constructors = register_lambda_types(&ctx.lambda_sets);

    DefuncTable {
        lambda_sets: ctx.lambda_sets,
        ho_param_sets: ctx.ho_param_sets,
        closure_constructors,
    }
}

/// Internal scanning context, used only during `collect`.
struct ScanCtx<'a, 'src> {
    funcs: &'a HashSet<String>,
    func_arities: &'a HashMap<String, usize>,
    constructors: &'a HashMap<String, ConstructorMeta>,
    list_builtins: &'a HashSet<String>,
    method_resolutions: &'a HashMap<ast::Span, String>,
    lambda_sets: Vec<LambdaSet<'src>>,
    ho_param_sets: HashMap<(String, usize), usize>,
    ho_vars: HashMap<String, usize>,
    lambda_counter: usize,
}

fn collect_lambdas<'src>(
    ctx: &mut ScanCtx<'_, 'src>,
    decls: &[Decl<'src>],
    reachable: &HashSet<String>,
) {
    // Pass 1: scan free function bodies (establishes lambda sets from callers)
    for decl in decls {
        if let Decl::FuncDef {
            name, params, body, ..
        } = decl
            && reachable.contains(*name)
        {
            for (i, p) in params.iter().enumerate() {
                let key = ((*name).to_owned(), i);
                if let Some(&ls_idx) = ctx.ho_param_sets.get(&key) {
                    ctx.ho_vars.insert((*p).to_owned(), ls_idx);
                }
            }
            scan_expr(ctx, body);
            for p in params {
                ctx.ho_vars.remove(*p);
            }
        }
    }

    // Pass 2: scan method bodies (uses lambda sets established by callers)
    for decl in decls {
        if let Decl::TypeAnno {
            name: type_name,
            methods,
            ..
        } = decl
        {
            for method_decl in methods {
                if let Decl::FuncDef {
                    name: method_name,
                    params,
                    body,
                    ..
                } = method_decl
                {
                    let mangled = method_key(type_name, method_name);
                    if reachable.contains(&mangled) {
                        for (i, p) in params.iter().enumerate() {
                            let key = (mangled.clone(), i);
                            if let Some(&ls_idx) = ctx.ho_param_sets.get(&key) {
                                ctx.ho_vars.insert((*p).to_owned(), ls_idx);
                            }
                        }
                        scan_expr(ctx, body);
                        for p in params {
                            ctx.ho_vars.remove(*p);
                        }
                    }
                }
            }
        }
    }
}

fn scan_expr<'src>(ctx: &mut ScanCtx<'_, 'src>, expr: &Expr<'src>) {
    match &expr.kind {
        ExprKind::Call { func, args } if ctx.funcs.contains(*func) => {
            scan_call_args(ctx, func, args);
        }
        ExprKind::Call { args, .. } => {
            for arg in args {
                scan_expr(ctx, arg);
            }
        }
        ExprKind::BinOp { lhs, rhs, .. } => {
            scan_expr(ctx, lhs);
            scan_expr(ctx, rhs);
        }
        ExprKind::Block(stmts, result) => {
            for stmt in stmts {
                match stmt {
                    Stmt::Let { val, .. } | Stmt::Destructure { val, .. } => {
                        scan_expr(ctx, val);
                    }
                    Stmt::TypeHint { .. } => {}
                }
            }
            scan_expr(ctx, result);
        }
        ExprKind::If {
            expr: scrutinee,
            arms,
            else_body,
            ..
        } => {
            scan_expr(ctx, scrutinee);
            for arm in arms {
                scan_expr(ctx, &arm.body);
            }
            if let Some(eb) = else_body {
                scan_expr(ctx, eb);
            }
        }
        ExprKind::Fold {
            expr: scrutinee,
            arms,
        } => {
            scan_expr(ctx, scrutinee);
            for arm in arms {
                scan_expr(ctx, &arm.body);
            }
        }
        ExprKind::QualifiedCall { segments, args } => {
            let mangled = segments.join(".");
            let is_list_ho = is_list_walk(&mangled);
            if is_list_ho || ctx.funcs.contains(&mangled) {
                scan_call_args(ctx, &mangled, args);
            } else {
                for arg in args {
                    scan_expr(ctx, arg);
                }
            }
        }
        ExprKind::Lambda { body, .. } => {
            scan_expr(ctx, body);
        }
        ExprKind::Record { fields } => {
            for (_, field_expr) in fields {
                scan_expr(ctx, field_expr);
            }
        }
        ExprKind::FieldAccess { record, .. } => {
            scan_expr(ctx, record);
        }
        ExprKind::MethodCall { receiver, args, .. } => {
            scan_expr(ctx, receiver);
            if let Some(resolved) = ctx.method_resolutions.get(&expr.span).cloned() {
                let is_ho = is_list_walk(&resolved) || ctx.funcs.contains(&resolved);
                if is_ho {
                    scan_call_args_offset(ctx, &resolved, args, 1);
                } else {
                    for a in args {
                        scan_expr(ctx, a);
                    }
                }
            } else {
                for a in args {
                    scan_expr(ctx, a);
                }
            }
        }
        ExprKind::Tuple(elems) | ExprKind::ListLit(elems) => {
            for e in elems {
                scan_expr(ctx, e);
            }
        }
        ExprKind::IntLit(_) | ExprKind::FloatLit(_) | ExprKind::StrLit(_) | ExprKind::Name(_) => {}
    }
}

fn scan_call_args<'src>(ctx: &mut ScanCtx<'_, 'src>, func_name: &str, args: &[Expr<'src>]) {
    scan_call_args_offset(ctx, func_name, args, 0);
}

fn scan_call_args_offset<'src>(
    ctx: &mut ScanCtx<'_, 'src>,
    func_name: &str,
    args: &[Expr<'src>],
    offset: usize,
) {
    for (i, arg) in args.iter().enumerate() {
        let idx = i + offset;
        match &arg.kind {
            ExprKind::Lambda { params, body } => {
                let free = compute_free_vars(ctx, body, params);
                register_lambda(ctx, func_name, idx, params.clone(), Some(body), free, None);
            }
            ExprKind::Name(name) => {
                let name = *name;
                if ctx.funcs.contains(name) && !ctx.constructors.contains_key(name) {
                    let arity = ctx.func_arities.get(name).copied().unwrap_or(0);
                    register_lambda(
                        ctx,
                        func_name,
                        idx,
                        Vec::new(),
                        None,
                        Vec::new(),
                        Some((name.to_owned(), arity)),
                    );
                }
            }
            _ => {}
        }
        scan_expr(ctx, arg);
    }
}

fn register_lambda<'src>(
    ctx: &mut ScanCtx<'_, 'src>,
    callee_func: &str,
    arg_index: usize,
    params: Vec<&'src str>,
    body: Option<&Expr<'src>>,
    captures: Vec<&'src str>,
    func_ref: Option<(String, usize)>,
) {
    let key = (callee_func.to_owned(), arg_index);
    let arity = if let Some((_, a)) = &func_ref {
        *a
    } else {
        params.len()
    };

    let ls_idx = if let Some(&idx) = ctx.ho_param_sets.get(&key) {
        assert!(
            ctx.lambda_sets[idx].arity == arity,
            "arity mismatch in lambda set for {callee_func} arg {arg_index}"
        );
        idx
    } else {
        let apply_name = format!("__apply_{callee_func}_{arg_index}");
        let idx = ctx.lambda_sets.len();
        ctx.lambda_sets.push(LambdaSet {
            apply_name,
            entries: Vec::new(),
            arity,
        });
        ctx.ho_param_sets.insert(key, idx);
        idx
    };

    let capture_ho: Vec<Option<usize>> = captures
        .iter()
        .map(|name| ctx.ho_vars.get(*name).copied())
        .collect();
    let tag_name = format!("__lambda_{}", ctx.lambda_counter);
    ctx.lambda_counter += 1;
    ctx.lambda_sets[ls_idx].entries.push(LambdaEntry {
        tag_name,
        capture_ho,
        captures,
        params,
        body: body.cloned(),
        func_ref: func_ref.map(|(name, _)| name),
    });
}

/// Register constructor metas for lambda closure types.
fn register_lambda_types(lambda_sets: &[LambdaSet<'_>]) -> HashMap<String, ConstructorMeta> {
    let mut constructors = HashMap::new();
    for ls in lambda_sets {
        let max_fields = ls
            .entries
            .iter()
            .map(|e| e.captures.len())
            .max()
            .unwrap_or(0);
        for (i, entry) in ls.entries.iter().enumerate() {
            constructors.insert(
                entry.tag_name.clone(),
                ConstructorMeta {
                    tag_index: i as u64,
                    num_fields: entry.captures.len(),
                    max_fields,
                    recursive_flags: vec![false; entry.captures.len()],
                    field_types: vec![ScalarType::Ptr; entry.captures.len()],
                },
            );
        }
    }
    constructors
}

// ---- Free variable computation ----

fn compute_free_vars<'src>(
    ctx: &ScanCtx<'_, 'src>,
    body: &Expr<'src>,
    params: &[&'src str],
) -> Vec<&'src str> {
    let mut free = Vec::new();
    let mut seen = HashSet::new();
    let bound: HashSet<&str> = params.iter().copied().collect();
    collect_free(ctx, body, &bound, &mut seen, &mut free);
    free
}

#[expect(clippy::too_many_lines, reason = "traverses all expression forms")]
fn collect_free<'src>(
    ctx: &ScanCtx<'_, 'src>,
    expr: &Expr<'src>,
    bound: &HashSet<&'src str>,
    seen: &mut HashSet<&'src str>,
    free: &mut Vec<&'src str>,
) {
    match &expr.kind {
        ExprKind::Name(name) => {
            let name = *name;
            if !bound.contains(name)
                && !ctx.constructors.contains_key(name)
                && !ctx.funcs.contains(name)
                && !seen.contains(name)
            {
                seen.insert(name);
                free.push(name);
            }
        }
        ExprKind::IntLit(_) | ExprKind::FloatLit(_) | ExprKind::StrLit(_) => {}
        ExprKind::BinOp { lhs, rhs, .. } => {
            collect_free(ctx, lhs, bound, seen, free);
            collect_free(ctx, rhs, bound, seen, free);
        }
        ExprKind::Call { func, args } => {
            if !bound.contains(func)
                && !ctx.constructors.contains_key(*func)
                && !ctx.funcs.contains(*func)
                && !ctx.list_builtins.contains(*func)
                && !seen.contains(func)
            {
                seen.insert(func);
                free.push(func);
            }
            for arg in args {
                collect_free(ctx, arg, bound, seen, free);
            }
        }
        ExprKind::QualifiedCall { args, .. } => {
            for arg in args {
                collect_free(ctx, arg, bound, seen, free);
            }
        }
        ExprKind::Record { fields } => {
            for (_, field_expr) in fields {
                collect_free(ctx, field_expr, bound, seen, free);
            }
        }
        ExprKind::FieldAccess { record, .. } => {
            collect_free(ctx, record, bound, seen, free);
        }
        ExprKind::MethodCall { receiver, args, .. } => {
            collect_free(ctx, receiver, bound, seen, free);
            for a in args {
                collect_free(ctx, a, bound, seen, free);
            }
        }
        ExprKind::Lambda { params, body } => {
            let mut inner = bound.clone();
            for p in params {
                inner.insert(p);
            }
            collect_free(ctx, body, &inner, seen, free);
        }
        ExprKind::Tuple(elems) | ExprKind::ListLit(elems) => {
            for e in elems {
                collect_free(ctx, e, bound, seen, free);
            }
        }
        ExprKind::Block(stmts, result) => {
            let mut inner = bound.clone();
            for stmt in stmts {
                match stmt {
                    Stmt::Let { name, val } => {
                        collect_free(ctx, val, &inner, seen, free);
                        inner.insert(name);
                    }
                    Stmt::Destructure { pattern, val } => {
                        collect_free(ctx, val, &inner, seen, free);
                        pattern_names(pattern, &mut inner);
                    }
                    Stmt::TypeHint { .. } => {}
                }
            }
            collect_free(ctx, result, &inner, seen, free);
        }
        ExprKind::If {
            expr: scrutinee,
            arms,
            else_body,
        } => {
            collect_free(ctx, scrutinee, bound, seen, free);
            for arm in arms {
                let mut arm_bound = bound.clone();
                pattern_names(&arm.pattern, &mut arm_bound);
                collect_free(ctx, &arm.body, &arm_bound, seen, free);
            }
            if let Some(eb) = else_body {
                collect_free(ctx, eb, bound, seen, free);
            }
        }
        ExprKind::Fold {
            expr: scrutinee,
            arms,
        } => {
            collect_free(ctx, scrutinee, bound, seen, free);
            for arm in arms {
                let mut arm_bound = bound.clone();
                pattern_names(&arm.pattern, &mut arm_bound);
                collect_free(ctx, &arm.body, &arm_bound, seen, free);
            }
        }
    }
}

/// Check whether a function name is a List walk variant.
fn is_list_walk(name: &str) -> bool {
    let base = name
        .strip_prefix("List.")
        .or_else(|| name.rsplit_once(".List.").map(|(_, rest)| rest));
    matches!(
        base,
        Some("walk" | "walk_backwards" | "walk_until" | "walk_backwards_until")
    )
}

pub fn pattern_names<'src>(pat: &ast::Pattern<'src>, bound: &mut HashSet<&'src str>) {
    match pat {
        ast::Pattern::Constructor { fields, .. } => {
            for f in fields {
                pattern_names(f, bound);
            }
        }
        ast::Pattern::Record { fields } => {
            for (_, field_pat) in fields {
                pattern_names(field_pat, bound);
            }
        }
        ast::Pattern::Tuple(elems) => {
            for e in elems {
                pattern_names(e, bound);
            }
        }
        ast::Pattern::Binding(name) => {
            bound.insert(name);
        }
        ast::Pattern::Wildcard => {}
    }
}
