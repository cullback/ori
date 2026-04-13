//! Defunctionalization — AST → AST rewrite.
//!
//! Takes a post-mono `Module` with `ExprKind::Lambda` still present
//! and emits one with:
//!
//! - No `Lambda` expressions anywhere.
//! - One synthesized `Decl::TypeAnno` per lambda set, declaring a
//!   closure tag-union (one tag per lambda variant, each carrying its
//!   captures as positional fields).
//! - One synthesized `Decl::FuncDef` per lambda set: the `__apply_K`
//!   function. Its first parameter is the closure, followed by the
//!   original lambda arguments. Its body `match`es on the closure
//!   tag and dispatches to each variant's body (with captures
//!   extracted from the closure's fields).
//! - Every lambda at a higher-order call-site argument rewritten to
//!   a constructor call (`__lambda_K(cap0, cap1, ...)`).
//! - Every call whose target is a local higher-order variable (e.g.
//!   `f(x)` where `f` is a lambda-set-carrying parameter) rewritten
//!   to `__apply_K(f, x)`.
//!
//! ## What stays
//!
//! Builtin list walks (`List.walk`, `List.walk_until`, and their
//! backwards counterparts) are lowered directly by `ssa::lower` —
//! the rewriter does NOT turn `List.walk(xs, init, f)` into an
//! `__apply_K` call. It only rewrites the lambda argument in slot
//! 2 to a constructor call; the lowerer's `lower_list_walk` still
//! emits its own loop and uses the synthesized `__apply_K` by
//! name (computed from the `__apply_{func}_{idx}` convention).
//!
//! ## Pipeline placement
//!
//! Runs after mono, before `ssa::lower`. Needs `decl_info` and
//! `reachable` internally to decide what's worth scanning. The
//! downstream `ssa::lower` rebuilds `decl_info` on the rewritten
//! module so the synthesized closure types and apply functions are
//! visible to it.

#![allow(
    clippy::too_many_lines,
    clippy::collapsible_if,
    clippy::collapsible_match,
    clippy::needless_range_loop,
    clippy::match_same_arms,
    clippy::explicit_iter_loop,
    clippy::if_not_else,
    reason = "defunc is a multi-phase AST walker with many variants"
)]

use std::collections::{HashMap, HashSet};

use crate::ast::{
    self, Decl, Expr, ExprKind, MatchArm, Module, Pattern, Span, Stmt, TagDecl, TypeDeclKind,
    TypeExpr,
};
use crate::decl_info::{self, ConstructorMeta, DeclInfo, method_key};
use crate::reachable;
use crate::resolve::ModuleScope;
use crate::source::SourceArena;
use crate::symbol::{SymbolId, SymbolKind, SymbolTable};
use crate::types::infer::InferResult;

// ---- Defunctionalization data structures (private) ----

#[derive(Clone)]
struct LambdaEntry<'src> {
    tag_name: String,
    tag_sym: Option<SymbolId>,
    captures: Vec<SymbolId>,
    capture_ho: Vec<Option<usize>>,
    params: Vec<SymbolId>,
    body: Option<Expr<'src>>,
    func_ref: Option<String>,
}

#[derive(Clone)]
struct LambdaSet<'src> {
    apply_name: String,
    apply_sym: Option<SymbolId>,
    closure_type_name: String,
    closure_type_sym: Option<SymbolId>,
    entries: Vec<LambdaEntry<'src>>,
    arity: usize,
}

/// Rewrite a post-mono module into its defunctionalized form.
pub fn rewrite<'src>(
    module: Module<'src>,
    arena: &SourceArena,
    scope: &ModuleScope,
    infer_result: &InferResult,
    symbols: &mut SymbolTable,
) -> Module<'src> {
    // --- Phase 1: scan ---
    let decls = decl_info::build(arena, &module, scope, infer_result, symbols);
    let reachable_set = reachable::compute(&decls, &module, symbols);

    let (mut lambda_sets, ho_param_sets) =
        scan_module(&module, &decls, &reachable_set, symbols);

    // --- Phase 2: rewrite each lambda entry's body in place ---
    //
    // Allocate synthesized SymbolIds FIRST: each entry gets a tag
    // sym; each set gets an apply sym and a closure-type sym. These
    // must exist before any rewrite happens because the rewriter
    // dereferences `apply_sym` when emitting `__apply_K(f, x)` calls.
    let set_count = lambda_sets.len();
    for ls_idx in 0..set_count {
        for entry_idx in 0..lambda_sets[ls_idx].entries.len() {
            let tag_name = lambda_sets[ls_idx].entries[entry_idx].tag_name.clone();
            let tag_sym = symbols.fresh(tag_name, synth_span(), SymbolKind::Func);
            lambda_sets[ls_idx].entries[entry_idx].tag_sym = Some(tag_sym);
        }
        let closure_type_name = lambda_sets[ls_idx].closure_type_name.clone();
        let apply_name = lambda_sets[ls_idx].apply_name.clone();
        let closure_sym = symbols.fresh(closure_type_name, synth_span(), SymbolKind::Type);
        let apply_sym = symbols.fresh(apply_name, synth_span(), SymbolKind::Func);
        lambda_sets[ls_idx].closure_type_sym = Some(closure_sym);
        lambda_sets[ls_idx].apply_sym = Some(apply_sym);
    }

    // --- Phase 3: rewrite each lambda entry's body in place ---
    //
    // Inside a lambda body, captured variables may themselves be
    // higher-order (i.e. they carry closures). Calls to those
    // captures need to become `__apply_K(f, x)` just like calls to
    // function-level HO parameters do. We walk each entry's body
    // with an `ho_vars` map seeded from its `capture_ho`.
    //
    // The rewriter needs an immutable borrow of `lambda_sets` (to
    // read other entries' `apply_sym` and `tag_sym`) while we're
    // mutating one entry's body. We resolve the borrow conflict by
    // taking the body out via `mem::take`, which leaves a `None` in
    // its slot and hands us an owned `Option<Expr>`. With the body
    // disconnected we can pass `&lambda_sets` to the rewriter. When
    // rewriting finishes we put the body back.
    for ls_idx in 0..set_count {
        let entry_count = lambda_sets[ls_idx].entries.len();
        for entry_idx in 0..entry_count {
            let ho_vars = {
                let entry = &lambda_sets[ls_idx].entries[entry_idx];
                let mut h: HashMap<SymbolId, usize> = HashMap::new();
                for (cap, ho) in entry.captures.iter().zip(entry.capture_ho.iter()) {
                    if let Some(set) = ho {
                        h.insert(*cap, *set);
                    }
                }
                h
            };
            let mut body_opt = std::mem::take(
                &mut lambda_sets[ls_idx].entries[entry_idx].body,
            );
            if let Some(body) = body_opt.as_mut() {
                let mut rewriter = Rewriter {
                    ho_param_sets: &ho_param_sets,
                    lambda_sets: &lambda_sets,
                    symbols,
                    ho_vars,
                };
                rewriter.rewrite_expr(body);
            }
            lambda_sets[ls_idx].entries[entry_idx].body = body_opt;
        }
    }

    // --- Phase 4: emit synthesized decls ---
    let mut synth_decls: Vec<Decl<'src>> = Vec::new();
    for ls_idx in 0..set_count {
        synth_decls.push(build_closure_type_decl(&lambda_sets[ls_idx]));
        synth_decls.push(build_apply_function_decl(&lambda_sets[ls_idx], symbols));
    }

    // --- Phase 5: rewrite the original module's decls ---
    let mut rewriter = Rewriter {
        ho_param_sets: &ho_param_sets,
        lambda_sets: &lambda_sets,
        symbols,
        ho_vars: HashMap::new(),
    };
    let mut new_decls: Vec<Decl<'src>> =
        Vec::with_capacity(module.decls.len() + synth_decls.len());
    for decl in module.decls {
        new_decls.push(rewriter.rewrite_decl(decl));
    }
    new_decls.extend(synth_decls);

    Module {
        exports: module.exports,
        imports: module.imports,
        decls: new_decls,
    }
}


#[expect(
    clippy::missing_const_for_fn,
    reason = "FileId isn't constructible in const context"
)]
fn synth_span() -> Span {
    Span {
        file: crate::source::FileId(0),
        start: usize::MAX,
        end: usize::MAX,
    }
}

/// Leak a `String` into a `&'static str` — used to reattach a
/// synthesized tag name to the `&'src str`-typed `TagDecl.name`
/// and `Pattern::Constructor.name` fields. The number of leaked
/// strings is `O(lambda_sets)` per compilation, trivial compared to
/// the source-arena leak that backs all `&'src str` in the AST.
fn leak_str(s: &str) -> &'static str {
    Box::leak(s.to_owned().into_boxed_str())
}

// ============================================================
// Phase 1: scan
// ============================================================

fn scan_module<'src>(
    module: &Module<'src>,
    decls: &DeclInfo,
    reachable_set: &HashSet<String>,
    symbols: &SymbolTable,
) -> (Vec<LambdaSet<'src>>, HashMap<(String, usize), usize>) {
    let mut ctx = ScanCtx {
        funcs: &decls.funcs,
        func_arities: &decls.func_arities,
        constructors: &decls.constructors,
        symbols,
        lambda_sets: Vec::new(),
        ho_param_sets: HashMap::new(),
        ho_vars: HashMap::new(),
        lambda_counter: 0,
        current_func: None,
        current_params: HashMap::new(),
    };
    collect_lambdas(&mut ctx, &module.decls, reachable_set);
    // Post-mono, every call-site target is the canonical mangled
    // name — there are no module-qualified aliases left to spread
    // ho_param_sets through.
    let _ = decls;
    (ctx.lambda_sets, ctx.ho_param_sets)
}

struct ScanCtx<'a, 'src> {
    funcs: &'a HashSet<String>,
    func_arities: &'a HashMap<String, usize>,
    constructors: &'a HashMap<String, ConstructorMeta>,
    symbols: &'a SymbolTable,
    lambda_sets: Vec<LambdaSet<'src>>,
    ho_param_sets: HashMap<(String, usize), usize>,
    ho_vars: HashMap<SymbolId, usize>,
    lambda_counter: usize,
    /// Current enclosing function name (for detecting HO calls to params).
    current_func: Option<String>,
    /// Parameters of the current function: sym → (func_name, param_index).
    current_params: HashMap<SymbolId, (String, usize)>,
}

impl ScanCtx<'_, '_> {
    fn is_known_func(&self, sym: SymbolId) -> bool {
        self.funcs.contains(self.symbols.display(sym))
    }

    fn is_constructor(&self, sym: SymbolId) -> bool {
        self.constructors.contains_key(self.symbols.display(sym))
    }

    fn func_arity(&self, sym: SymbolId) -> usize {
        self.func_arities
            .get(self.symbols.display(sym))
            .copied()
            .unwrap_or(0)
    }
}

fn collect_lambdas<'src>(
    ctx: &mut ScanCtx<'_, 'src>,
    decls: &[Decl<'src>],
    reachable_set: &HashSet<String>,
) {
    loop {
        let before = ctx.ho_param_sets.len();
        scan_free_functions(ctx, decls, reachable_set);
        scan_methods(ctx, decls, reachable_set);
        if ctx.ho_param_sets.len() == before {
            break;
        }
    }
}

fn scan_free_functions<'src>(
    ctx: &mut ScanCtx<'_, 'src>,
    decls: &[Decl<'src>],
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
                    if let Some(&ls_idx) = ctx.ho_param_sets.get(&key) {
                        ctx.ho_vars.insert(*p, ls_idx);
                    }
                }
                scan_expr(ctx, body);
                for p in params {
                    ctx.ho_vars.remove(p);
                }
                ctx.current_func = None;
                ctx.current_params.clear();
            }
        }
    }
}

fn scan_methods<'src>(
    ctx: &mut ScanCtx<'_, 'src>,
    decls: &[Decl<'src>],
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
            for method_decl in methods {
                if let Decl::FuncDef {
                    name: method_name,
                    params,
                    body,
                    ..
                } = method_decl
                {
                    let method_name_str = ctx.symbols.display(*method_name);
                    let mangled = method_key(&type_name_str, method_name_str);
                    if reachable_set.contains(&mangled) {
                        ctx.current_func = Some(mangled.clone());
                        ctx.current_params.clear();
                        for (i, p) in params.iter().enumerate() {
                            ctx.current_params.insert(*p, (mangled.clone(), i));
                            let key = (mangled.clone(), i);
                            if let Some(&ls_idx) = ctx.ho_param_sets.get(&key) {
                                ctx.ho_vars.insert(*p, ls_idx);
                            }
                        }
                        scan_expr(ctx, body);
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

fn scan_expr<'src>(ctx: &mut ScanCtx<'_, 'src>, expr: &Expr<'src>) {
    match &expr.kind {
        ExprKind::Call { target, args, .. } if ctx.is_known_func(*target) => {
            let name = ctx.symbols.display(*target).to_owned();
            scan_call_args(ctx, &name, args);
        }
        ExprKind::Call { target, args, .. } => {
            // Call to a non-global target — check if it's a parameter
            // being called as a function (e.g. `p(input)` where p has
            // opaque type transparent to Arrow). If so, mark it as
            // higher-order so defunc generates an apply dispatcher.
            if !ctx.is_constructor(*target) {
                if let Some((func_name, param_idx)) = ctx.current_params.get(target).cloned() {
                    let key = (func_name, param_idx);
                    if !ctx.ho_param_sets.contains_key(&key) {
                        // Determine arity from the call site.
                        let arity = args.len();
                        let apply_name = format!("__apply_{}_{}", key.0, key.1);
                        let closure_type_name = format!("__Closure_{}_{}", key.0, key.1);
                        let idx = ctx.lambda_sets.len();
                        ctx.lambda_sets.push(LambdaSet {
                            apply_name,
                            apply_sym: None,
                            closure_type_name,
                            closure_type_sym: None,
                            entries: Vec::new(),
                            arity,
                        });
                        ctx.ho_param_sets.insert(key.clone(), idx);
                        ctx.ho_vars.insert(*target, idx);
                    } else if !ctx.ho_vars.contains_key(target) {
                        let idx = ctx.ho_param_sets[&key];
                        ctx.ho_vars.insert(*target, idx);
                    }
                }
            }
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
                    Stmt::Guard {
                        condition,
                        return_val,
                    } => {
                        scan_expr(ctx, condition);
                        scan_expr(ctx, return_val);
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
                for guard_expr in &arm.guards {
                    scan_expr(ctx, guard_expr);
                }
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
                for guard_expr in &arm.guards {
                    scan_expr(ctx, guard_expr);
                }
                scan_expr(ctx, &arm.body);
            }
        }
        ExprKind::QualifiedCall { segments, args, .. } => {
            let mangled = segments.join(".");
            if is_list_walk(&mangled) || ctx.funcs.contains(&mangled) {
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
        ExprKind::MethodCall {
            receiver,
            args,
            resolved,
            ..
        } => {
            scan_expr(ctx, receiver);
            if let Some(target) = resolved.as_deref() {
                let is_ho = is_list_walk(target) || ctx.funcs.contains(target);
                if is_ho {
                    scan_call_args_offset(ctx, target, args, 1);
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
        ExprKind::Is { expr: inner, .. } => {
            scan_expr(ctx, inner);
        }
        ExprKind::RecordUpdate { base, updates } => {
            scan_expr(ctx, base);
            for (_, e) in updates {
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
            ExprKind::Name(sym) => {
                if ctx.is_known_func(*sym) && !ctx.is_constructor(*sym) {
                    let display = ctx.symbols.display(*sym).to_owned();
                    let arity = ctx.func_arity(*sym);
                    register_lambda(
                        ctx,
                        func_name,
                        idx,
                        Vec::new(),
                        None,
                        Vec::new(),
                        Some((display, arity)),
                    );
                } else if let Some(&ls_idx) = ctx.ho_vars.get(sym) {
                    let key = (func_name.to_owned(), idx);
                    ctx.ho_param_sets.entry(key).or_insert(ls_idx);
                } else {
                    // Plain local — no HO machinery.
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
    params: Vec<SymbolId>,
    body: Option<&Expr<'src>>,
    captures: Vec<SymbolId>,
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
        let closure_type_name = format!("__Closure_{callee_func}_{arg_index}");
        let idx = ctx.lambda_sets.len();
        ctx.lambda_sets.push(LambdaSet {
            apply_name,
            apply_sym: None,
            closure_type_name,
            closure_type_sym: None,
            entries: Vec::new(),
            arity,
        });
        ctx.ho_param_sets.insert(key, idx);
        idx
    };

    let capture_ho: Vec<Option<usize>> = captures
        .iter()
        .map(|sym| ctx.ho_vars.get(sym).copied())
        .collect();
    let tag_name = format!("__lambda_{}", ctx.lambda_counter);
    ctx.lambda_counter += 1;
    ctx.lambda_sets[ls_idx].entries.push(LambdaEntry {
        tag_name,
        tag_sym: None,
        capture_ho,
        captures,
        params,
        body: body.cloned(),
        func_ref: func_ref.map(|(name, _)| name),
    });
}

fn compute_free_vars<'src>(
    ctx: &ScanCtx<'_, 'src>,
    body: &Expr<'src>,
    params: &[SymbolId],
) -> Vec<SymbolId> {
    let bound: HashSet<SymbolId> = params.iter().copied().collect();
    ast::free_names(body, &bound, &mut HashSet::new(), &|sym| {
        !matches!(ctx.symbols.get(sym).kind, SymbolKind::Local)
    })
}

fn is_list_walk(name: &str) -> bool {
    let base = name
        .strip_prefix("List.")
        .or_else(|| name.rsplit_once(".List.").map(|(_, rest)| rest));
    matches!(
        base,
        Some("walk" | "walk_until")
    )
}

// ============================================================
// Phases 3 + 4: closure type + apply function synthesis
// ============================================================

fn build_closure_type_decl<'src>(ls: &LambdaSet<'src>) -> Decl<'src> {
    let tags: Vec<TagDecl<'src>> = ls
        .entries
        .iter()
        .map(|entry| TagDecl {
            name: leak_str(&entry.tag_name),
            fields: vec![TypeExpr::Named("I64"); entry.captures.len()],
        })
        .collect();

    Decl::TypeAnno {
        span: synth_span(),
        name: ls.closure_type_sym.expect("closure_type_sym not allocated"),
        type_params: Vec::new(),
        ty: TypeExpr::TagUnion(tags, false),
        where_clause: Vec::new(),
        methods: Vec::new(),
        kind: TypeDeclKind::Transparent,
        doc: None,
    }
}

fn build_apply_function_decl<'src>(
    ls: &LambdaSet<'src>,
    symbols: &mut SymbolTable,
) -> Decl<'src> {
    let apply_span = synth_span();
    let closure_param = symbols.fresh("__closure", apply_span, SymbolKind::Local);
    let arg_params: Vec<SymbolId> = (0..ls.arity)
        .map(|i| {
            let name = format!("__apply_arg_{i}");
            symbols.fresh(name, apply_span, SymbolKind::Local)
        })
        .collect();
    let mut all_params = Vec::with_capacity(1 + ls.arity);
    all_params.push(closure_param);
    all_params.extend_from_slice(&arg_params);

    let arms: Vec<MatchArm<'src>> = ls
        .entries
        .iter()
        .map(|entry| build_apply_arm(entry, &arg_params, symbols))
        .collect();

    let scrutinee = Expr::new(ExprKind::Name(closure_param), synth_span());
    let body = Expr::new(
        ExprKind::If {
            expr: Box::new(scrutinee),
            arms,
            else_body: None,
        },
        synth_span(),
    );

    Decl::FuncDef {
        span: apply_span,
        name: ls.apply_sym.expect("apply_sym not allocated"),
        params: all_params,
        body,
        doc: None,
    }
}

fn build_apply_arm<'src>(
    entry: &LambdaEntry<'src>,
    arg_params: &[SymbolId],
    symbols: &mut SymbolTable,
) -> MatchArm<'src> {
    let pattern_fields: Vec<Pattern<'src>> =
        entry.captures.iter().map(|sym| Pattern::Binding(*sym)).collect();
    let pattern = Pattern::Constructor {
        name: leak_str(&entry.tag_name),
        fields: pattern_fields,
    };

    let body = if let Some(func_name) = &entry.func_ref {
        let target = symbols.fresh(func_name, synth_span(), SymbolKind::Func);
        let args: Vec<Expr<'src>> = arg_params
            .iter()
            .map(|p| Expr::new(ExprKind::Name(*p), synth_span()))
            .collect();
        Expr::new(ExprKind::Call { target, args }, synth_span())
    } else {
        let lambda_body = entry
            .body
            .as_ref()
            .expect("lambda entry without body or func_ref")
            .clone();
        let mut stmts: Vec<Stmt<'src>> = Vec::with_capacity(entry.params.len());
        for (param_sym, arg_sym) in entry.params.iter().zip(arg_params.iter()) {
            let val = Expr::new(ExprKind::Name(*arg_sym), synth_span());
            stmts.push(Stmt::Let {
                name: *param_sym,
                val,
            });
        }
        Expr::new(ExprKind::Block(stmts, Box::new(lambda_body)), synth_span())
    };

    MatchArm {
        pattern,
        guards: Vec::new(),
        body,
        is_return: false,
    }
}

// ============================================================
// Phase 5: module rewrite (Lambda → constructor, HO-call → apply)
// ============================================================

struct Rewriter<'a, 'src> {
    ho_param_sets: &'a HashMap<(String, usize), usize>,
    lambda_sets: &'a [LambdaSet<'src>],
    symbols: &'a SymbolTable,
    /// Local higher-order variables in the current scope.
    ho_vars: HashMap<SymbolId, usize>,
}

impl<'src> Rewriter<'_, 'src> {
    fn rewrite_decl(&mut self, decl: Decl<'src>) -> Decl<'src> {
        match decl {
            Decl::FuncDef {
                span,
                name,
                params,
                mut body,
                doc,
            } => {
                let name_str = self.symbols.display(name).to_owned();
                let added = self.enter_function_scope(&name_str, &params);
                self.rewrite_expr(&mut body);
                self.exit_function_scope(&added);
                Decl::FuncDef {
                    span,
                    name,
                    params,
                    body,
                    doc,
                }
            }
            Decl::TypeAnno {
                span,
                name,
                type_params,
                ty,
                where_clause,
                mut methods,
                kind,
                doc,
            } => {
                let type_name = self.symbols.display(name).to_owned();
                for method in &mut methods {
                    if let Decl::FuncDef {
                        name: method_name,
                        params,
                        body,
                        ..
                    } = method
                    {
                        let method_display = self.symbols.display(*method_name).to_owned();
                        let mangled = format!("{type_name}.{method_display}");
                        let added = self.enter_function_scope(&mangled, params);
                        self.rewrite_expr(body);
                        self.exit_function_scope(&added);
                    }
                }
                Decl::TypeAnno {
                    span,
                    name,
                    type_params,
                    ty,
                    where_clause,
                    methods,
                    kind,
                    doc,
                }
            }
        }
    }

    fn enter_function_scope(
        &mut self,
        func_name: &str,
        params: &[SymbolId],
    ) -> Vec<SymbolId> {
        let mut added = Vec::new();
        for (i, p) in params.iter().enumerate() {
            let key = (func_name.to_owned(), i);
            if let Some(&ls_idx) = self.ho_param_sets.get(&key) {
                self.ho_vars.insert(*p, ls_idx);
                added.push(*p);
            }
        }
        added
    }

    fn exit_function_scope(&mut self, added: &[SymbolId]) {
        for sym in added {
            self.ho_vars.remove(sym);
        }
    }

    fn rewrite_expr(&mut self, expr: &mut Expr<'src>) {
        match &mut expr.kind {
            ExprKind::Call { target, args } => {
                // Is this a call to a local HO variable? Rewrite it
                // to an apply function call.
                if let Some(&ls_idx) = self.ho_vars.get(target) {
                    let apply_sym = self.lambda_sets[ls_idx]
                        .apply_sym
                        .expect("apply_sym must be allocated before rewrite");
                    let closure_span = expr.span;
                    let closure_name_expr = Expr::new(ExprKind::Name(*target), closure_span);
                    // Rewrite each original arg first (it may itself
                    // contain lambdas / HO calls).
                    for arg in args.iter_mut() {
                        self.rewrite_expr(arg);
                    }
                    let mut new_args = Vec::with_capacity(args.len() + 1);
                    new_args.push(closure_name_expr);
                    new_args.append(args);
                    expr.kind = ExprKind::Call {
                        target: apply_sym,
                        args: new_args,
                    };
                    return;
                }
                // Ordinary call to a global function. Rewrite HO
                // arg positions.
                let target_name = self.symbols.display(*target).to_owned();
                self.rewrite_call_args(&target_name, args, 0);
            }
            ExprKind::QualifiedCall { segments, args, .. } => {
                let mangled = segments.join(".");
                self.rewrite_call_args(&mangled, args, 0);
            }
            ExprKind::MethodCall {
                receiver,
                args,
                resolved,
                ..
            } => {
                self.rewrite_expr(receiver);
                if let Some(target_name) = resolved.clone() {
                    self.rewrite_call_args(&target_name, args, 1);
                } else {
                    for a in args.iter_mut() {
                        self.rewrite_expr(a);
                    }
                }
            }
            ExprKind::BinOp { lhs, rhs, .. } => {
                self.rewrite_expr(lhs);
                self.rewrite_expr(rhs);
            }
            ExprKind::Block(stmts, result) => {
                for stmt in stmts.iter_mut() {
                    self.rewrite_stmt(stmt);
                }
                self.rewrite_expr(result);
            }
            ExprKind::If {
                expr: scrutinee,
                arms,
                else_body,
            } => {
                self.rewrite_expr(scrutinee);
                for arm in arms.iter_mut() {
                    for g in arm.guards.iter_mut() {
                        self.rewrite_expr(g);
                    }
                    self.rewrite_expr(&mut arm.body);
                }
                if let Some(eb) = else_body {
                    self.rewrite_expr(eb);
                }
            }
            ExprKind::Fold {
                expr: scrutinee,
                arms,
            } => {
                self.rewrite_expr(scrutinee);
                for arm in arms.iter_mut() {
                    for g in arm.guards.iter_mut() {
                        self.rewrite_expr(g);
                    }
                    self.rewrite_expr(&mut arm.body);
                }
            }
            ExprKind::Lambda { .. } => {
                // Orphan Lambda (not in a known HO arg slot). The
                // current frontend doesn't generate these — every
                // lambda is a direct call-arg — but if it did, mono
                // would panic at lowering. Leave as-is.
            }
            ExprKind::Record { fields } => {
                for (_, e) in fields.iter_mut() {
                    self.rewrite_expr(e);
                }
            }
            ExprKind::FieldAccess { record, .. } => self.rewrite_expr(record),
            ExprKind::Tuple(elems) | ExprKind::ListLit(elems) => {
                for e in elems.iter_mut() {
                    self.rewrite_expr(e);
                }
            }
            ExprKind::Is { expr: inner, .. } => self.rewrite_expr(inner),
            ExprKind::RecordUpdate { base, updates } => {
                self.rewrite_expr(base);
                for (_, e) in updates.iter_mut() {
                    self.rewrite_expr(e);
                }
            }
            ExprKind::IntLit(_)
            | ExprKind::FloatLit(_)
            | ExprKind::StrLit(_)
            | ExprKind::Name(_) => {}
        }
    }

    fn rewrite_stmt(&mut self, stmt: &mut Stmt<'src>) {
        match stmt {
            Stmt::Let { val, .. } | Stmt::Destructure { val, .. } => self.rewrite_expr(val),
            Stmt::Guard {
                condition,
                return_val,
            } => {
                self.rewrite_expr(condition);
                self.rewrite_expr(return_val);
            }
            Stmt::TypeHint { .. } => {}
        }
    }

    /// Walk the arguments of a call and, for each argument in a
    /// known higher-order slot, rewrite lambdas/function refs to
    /// constructor calls. Arguments in non-HO slots are recursed
    /// into unchanged.
    fn rewrite_call_args(
        &mut self,
        callee_name: &str,
        args: &mut [Expr<'src>],
        offset: usize,
    ) {
        // Track which (callee, arg_idx) slots are HO, and which
        // lambda entry each rewrite corresponds to. Because entries
        // in a lambda set are appended in source order during scan,
        // we need a per-(callee, slot) counter to pick the right
        // entry for the N-th occurrence. Rewriter state doesn't
        // track that yet — we walk the lambda set's entries
        // linearly, which works when each HO arg position is visited
        // exactly once per scan/rewrite (the common case).
        //
        // Since scan and rewrite traverse the tree in the same order
        // (both use `scan_expr` / `rewrite_expr` with identical
        // recursion), the entry index for the N-th lambda seen at
        // `(callee, slot)` should match. We track it via a
        // per-rewriter-invocation counter on the lambda set.
        for (i, arg) in args.iter_mut().enumerate() {
            let idx = i + offset;
            let key = (callee_name.to_owned(), idx);
            if let Some(&ls_idx) = self.ho_param_sets.get(&key) {
                self.rewrite_ho_arg(arg, ls_idx);
            } else {
                self.rewrite_expr(arg);
            }
        }
    }

    /// Rewrite a single higher-order argument: lambdas and named
    /// function references become constructor calls; pass-through
    /// higher-order variables stay as `Name(sym)`.
    fn rewrite_ho_arg(&mut self, arg: &mut Expr<'src>, ls_idx: usize) {
        match &mut arg.kind {
            ExprKind::Lambda { body, .. } => {
                // First rewrite the body in the enclosing scope's
                // ho_vars context — the body may contain HO-var
                // calls to captured closures. (This body has ALSO
                // been pre-rewritten in Phase 2 inside the lambda
                // set, so this is a second pass on the same data.
                // That's idempotent because the rewriter doesn't
                // re-nest rewrites: an already-rewritten Call to an
                // apply function has target = apply_sym, which isn't
                // a local HO var.)
                self.rewrite_expr(body);

                // Find the matching entry in the set. Body is
                // identified by the exact Expr value — since we
                // cloned during scan, a deep equality check is too
                // expensive. Instead, we walk the entries in order
                // and take the first one we haven't "used" yet. The
                // rewriter's traversal order matches the scanner's,
                // so this works if we track a per-set cursor.
                //
                // To avoid mutating shared state, we do the simplest
                // thing: pick the first entry whose `body` field
                // contains a lambda and whose `func_ref` is None and
                // whose params match the current arg's params. For
                // mono-per-call-site cases this uniquely identifies
                // the entry.
                //
                // Pragmatic approach: we index entries by the lambda
                // body's span as a disambiguator. Spans are unique
                // in the original AST.
                let entry_idx = self
                    .lambda_sets[ls_idx]
                    .entries
                    .iter()
                    .position(|e| {
                        e.body
                            .as_ref()
                            .is_some_and(|b| b.span == body.span)
                    })
                    .expect("lambda arg must correspond to a scanned entry");
                let entry = &self.lambda_sets[ls_idx].entries[entry_idx];
                let tag_sym = entry
                    .tag_sym
                    .expect("tag_sym must be allocated before rewrite");
                let captures = entry.captures.clone();
                let arg_span = arg.span;
                let ctor_args: Vec<Expr<'src>> = captures
                    .iter()
                    .map(|cap| Expr::new(ExprKind::Name(*cap), arg_span))
                    .collect();
                arg.kind = ExprKind::Call {
                    target: tag_sym,
                    args: ctor_args,
                };
            }
            ExprKind::Name(sym) => {
                // Three cases:
                // - Pass-through local HO var: leave as-is (the
                //   inner value is already a closure).
                // - Global function ref: emit the nullary func_ref
                //   constructor.
                // - Local variable holding a closure (e.g. let-bound
                //   result of a constructor): leave as-is.
                if self.ho_vars.contains_key(sym) {
                    // Pass-through HO param — no rewrite.
                } else {
                    let target_display = self.symbols.display(*sym).to_owned();
                    let maybe_entry = self
                        .lambda_sets[ls_idx]
                        .entries
                        .iter()
                        .position(|e| e.func_ref.as_deref() == Some(target_display.as_str()));
                    if let Some(entry_idx) = maybe_entry {
                        // Global function ref: find its entry.
                        let entry = &self.lambda_sets[ls_idx].entries[entry_idx];
                        let tag_sym = entry
                            .tag_sym
                            .expect("tag_sym must be allocated before rewrite");
                        arg.kind = ExprKind::Call {
                            target: tag_sym,
                            args: Vec::new(),
                        };
                    }
                    // else: local variable already holding a closure — leave as-is.
                }
            }
            _ => {
                // Any other shape: recurse (shouldn't happen for
                // well-formed HO args).
                self.rewrite_expr(arg);
            }
        }
    }
}
