#![allow(
    clippy::too_many_lines,
    clippy::collapsible_if,
    clippy::needless_range_loop,
    clippy::match_same_arms,
    clippy::if_not_else,
    clippy::missing_docs_in_private_items,
    clippy::doc_markdown,
    clippy::redundant_clone,
    clippy::needless_pass_by_value,
    clippy::explicit_iter_loop,
    clippy::missing_const_for_fn,
    unused_variables,
    unused_imports,
    reason = "lambda specialize is a multi-phase AST walker"
)]

//! Lambda specialization — replace `Closure` nodes with constructor
//! calls and higher-order calls with apply-function dispatch.
//!
//! Consumes the `LambdaSolution` from `lambda_solve` and produces a
//! module with no `Closure` or `Lambda` nodes and no function-typed
//! parameters. Every call has a known, first-order target.

use std::collections::HashMap;

use crate::ast::{
    self, Decl, Expr, ExprKind, MatchArm, Module, Pattern, Span, Stmt, TagDecl, TypeDeclKind,
    TypeExpr,
};
use crate::passes::lambda_solve::{LambdaEntry, LambdaSet, LambdaSolution};
use crate::passes::mono::Monomorphized;
use crate::source::SourceArena;
use crate::symbol::{SymbolId, SymbolKind, SymbolTable};

/// Direct-call info for a singleton lambda set.
pub struct SingletonTarget {
    /// Display name of the target function.
    pub target_func: String,
    /// Number of captures stored in the closure (after the tag slot).
    pub num_captures: usize,
}

/// Specialize the module using the lambda set solution.
pub fn specialize(mono: &mut Monomorphized<'_>, solution: &LambdaSolution) {
    let module = std::mem::take(&mut mono.module);
    let (new_module, singletons, tag_targets) = specialize_module(module, solution, &mut mono.symbols);
    mono.module = new_module;
    mono.singletons = singletons;
    mono.tag_targets = tag_targets;
}

fn specialize_module<'src>(
    module: Module<'src>,
    solution: &LambdaSolution,
    symbols: &mut SymbolTable,
) -> (Module<'src>, HashMap<String, SingletonTarget>, HashMap<String, SingletonTarget>) {
    // Allocate SymbolIds for all synthesized names.
    let alloc = allocate_symbols(solution, symbols);

    // Build ho_vars for each function: which params map to lambda sets.
    let mut rewriter = Rewriter {
        param_to_set: &solution.param_to_set,
        sets: &solution.sets,
        alloc: &alloc,
        symbols,
        ho_vars: solution.local_ho_vars.clone(),
    };

    // Rewrite module decls.
    let mut new_decls: Vec<Decl<'src>> = module
        .decls
        .into_iter()
        .map(|d| rewriter.rewrite_decl(d))
        .collect();

    // Synthesize closure types and apply functions.
    // Singletons still get apply functions (to keep lifted funcs
    // reachable) but call sites use direct calls instead.
    let mut singletons = HashMap::new();
    let mut tag_targets = HashMap::new();
    for (ls_idx, ls) in solution.sets.iter().enumerate() {
        new_decls.push(build_closure_type(ls, &alloc, ls_idx));
        new_decls.push(build_apply_function(ls, &alloc, ls_idx, symbols));
        for entry in &ls.entries {
            let target_func = entry.func_ref.clone().unwrap_or_else(|| {
                symbols.display(entry.lifted_func).to_owned()
            });
            tag_targets.insert(entry.tag_name.clone(), SingletonTarget {
                target_func,
                num_captures: entry.captures.len(),
            });
        }
        if ls.entries.len() == 1 {
            let entry = &ls.entries[0];
            let target_func = entry.func_ref.clone().unwrap_or_else(|| {
                symbols.display(entry.lifted_func).to_owned()
            });
            singletons.insert(ls.apply_name.clone(), SingletonTarget {
                target_func,
                num_captures: entry.captures.len(),
            });
        }
    }

    (Module {
        exports: module.exports,
        imports: module.imports,
        decls: new_decls,
    }, singletons, tag_targets)
}

// ---- Symbol allocation ----

struct AllocatedSymbols {
    /// Per lambda set: apply function sym, closure type sym.
    set_syms: Vec<(SymbolId, SymbolId)>,
    /// Per entry across all sets: tag constructor sym.
    tag_syms: HashMap<(usize, usize), SymbolId>,
    /// Pre-allocated capture bindings for singleton inline destructures.
    singleton_captures: HashMap<usize, Vec<SymbolId>>,
}

fn allocate_symbols(solution: &LambdaSolution, symbols: &mut SymbolTable) -> AllocatedSymbols {
    let span = synth_span();
    let mut set_syms = Vec::new();
    let mut tag_syms = HashMap::new();
    let mut singleton_captures = HashMap::new();

    for (ls_idx, ls) in solution.sets.iter().enumerate() {
        let apply_sym = symbols.fresh(&ls.apply_name, span, SymbolKind::Func);
        let closure_sym = symbols.fresh(&ls.closure_type_name, span, SymbolKind::Type);
        set_syms.push((apply_sym, closure_sym));

        for (entry_idx, entry) in ls.entries.iter().enumerate() {
            let tag_sym = symbols.fresh(&entry.tag_name, span, SymbolKind::Func);
            tag_syms.insert((ls_idx, entry_idx), tag_sym);
        }

        // Pre-allocate capture bindings for singleton sets with captures.
        if ls.entries.len() == 1 && !ls.entries[0].captures.is_empty() {
            let bindings: Vec<SymbolId> = ls.entries[0]
                .captures
                .iter()
                .map(|&cap| {
                    let name = symbols.display(cap).to_owned();
                    symbols.fresh(format!("__sc_{name}"), span, SymbolKind::Local)
                })
                .collect();
            singleton_captures.insert(ls_idx, bindings);
        }
    }

    AllocatedSymbols { set_syms, tag_syms, singleton_captures }
}

// ---- Closure type synthesis ----

fn build_closure_type<'src>(
    ls: &LambdaSet,
    alloc: &AllocatedSymbols,
    ls_idx: usize,
) -> Decl<'src> {
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
        name: alloc.set_syms[ls_idx].1, // closure type sym
        type_params: Vec::new(),
        ty: TypeExpr::TagUnion(tags, false),
        where_clause: Vec::new(),
        methods: Vec::new(),
        kind: TypeDeclKind::Transparent,
        doc: None,
    }
}

// ---- Apply function synthesis ----

fn build_apply_function<'src>(
    ls: &LambdaSet,
    alloc: &AllocatedSymbols,
    ls_idx: usize,
    symbols: &mut SymbolTable,
) -> Decl<'src> {
    let span = synth_span();
    let closure_param = symbols.fresh("__closure", span, SymbolKind::Local);
    let arg_params: Vec<SymbolId> = (0..ls.arity)
        .map(|i| symbols.fresh(format!("__apply_arg_{i}"), span, SymbolKind::Local))
        .collect();

    let mut all_params = Vec::with_capacity(1 + ls.arity);
    all_params.push(closure_param);
    all_params.extend_from_slice(&arg_params);

    let arms: Vec<MatchArm<'src>> = ls
        .entries
        .iter()
        .enumerate()
        .map(|(entry_idx, entry)| build_apply_arm(entry, &arg_params, alloc, ls_idx, entry_idx, symbols))
        .collect();

    let scrutinee = Expr::new(ExprKind::Name(closure_param), span);
    let body = Expr::new(
        ExprKind::If {
            expr: Box::new(scrutinee),
            arms,
            else_body: None,
        },
        span,
    );

    Decl::FuncDef {
        span,
        name: alloc.set_syms[ls_idx].0, // apply sym
        params: all_params,
        body,
        doc: None,
    }
}

fn build_apply_arm<'src>(
    entry: &LambdaEntry,
    arg_params: &[SymbolId],
    alloc: &AllocatedSymbols,
    ls_idx: usize,
    entry_idx: usize,
    symbols: &mut SymbolTable,
) -> MatchArm<'src> {
    let span = synth_span();

    // Pattern: Constructor(cap0, cap1, ...)
    let capture_bindings: Vec<SymbolId> = entry
        .captures
        .iter()
        .map(|&cap| {
            let name = symbols.display(cap).to_owned();
            symbols.fresh(name, span, SymbolKind::Local)
        })
        .collect();
    let pattern = Pattern::Constructor {
        name: leak_str(&entry.tag_name),
        fields: capture_bindings.iter().map(|s| Pattern::Binding(*s)).collect(),
    };

    // Body: call the lifted function with captures + args.
    let body = if let Some(func_name) = &entry.func_ref {
        // Named function ref: Call(func, [args...])
        let target = symbols.fresh(func_name, span, SymbolKind::Func);
        let args: Vec<Expr<'src>> = arg_params
            .iter()
            .map(|p| Expr::new(ExprKind::Name(*p), span))
            .collect();
        Expr::new(ExprKind::Call { target, args }, span)
    } else {
        // Lifted lambda: Call(lifted_func, [captures..., args...])
        let mut args: Vec<Expr<'src>> = capture_bindings
            .iter()
            .map(|s| Expr::new(ExprKind::Name(*s), span))
            .collect();
        args.extend(arg_params.iter().map(|p| Expr::new(ExprKind::Name(*p), span)));
        Expr::new(
            ExprKind::Call {
                target: entry.lifted_func,
                args,
            },
            span,
        )
    };

    MatchArm {
        pattern,
        guards: Vec::new(),
        body,
        is_return: false,
    }
}

// ---- Module rewrite ----

struct Rewriter<'a> {
    param_to_set: &'a HashMap<(String, usize), usize>,
    sets: &'a [LambdaSet],
    alloc: &'a AllocatedSymbols,
    symbols: &'a SymbolTable,
    ho_vars: HashMap<SymbolId, usize>,
}

impl<'src> Rewriter<'_> {
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
                let added = self.enter_scope(&name_str, &params);
                self.rewrite_expr(&mut body);
                self.exit_scope(&added);
                Decl::FuncDef { span, name, params, body, doc }
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
                        let method_str = self.symbols.display(*method_name).to_owned();
                        let mangled = format!("{type_name}.{method_str}");
                        let added = self.enter_scope(&mangled, params);
                        self.rewrite_expr(body);
                        self.exit_scope(&added);
                    }
                }
                Decl::TypeAnno { span, name, type_params, ty, where_clause, methods, kind, doc }
            }
        }
    }

    /// Find which (lambda_set_index, entry_index) a lifted func belongs to.
    fn find_entry_for_func(&self, func: SymbolId) -> Option<(usize, usize)> {
        for (ls_idx, ls) in self.sets.iter().enumerate() {
            for (entry_idx, entry) in ls.entries.iter().enumerate() {
                if entry.lifted_func == func {
                    return Some((ls_idx, entry_idx));
                }
            }
        }
        None
    }

    fn enter_scope(&mut self, func_name: &str, params: &[SymbolId]) -> Vec<SymbolId> {
        let mut added = Vec::new();
        for (i, p) in params.iter().enumerate() {
            let key = (func_name.to_owned(), i);
            if let Some(&ls_idx) = self.param_to_set.get(&key) {
                self.ho_vars.insert(*p, ls_idx);
                added.push(*p);
            }
        }
        added
    }

    fn exit_scope(&mut self, added: &[SymbolId]) {
        for sym in added {
            self.ho_vars.remove(sym);
        }
    }

    fn rewrite_expr(&mut self, expr: &mut Expr<'src>) {
        match &mut expr.kind {
            ExprKind::Call { target, args } => {
                // Call to a local HO variable → apply dispatch.
                if let Some(&ls_idx) = self.ho_vars.get(target) {
                    let ls = &self.sets[ls_idx];
                    if ls.entries.len() == 1 {
                        // Singleton: emit direct call, skip apply dispatch.
                        let entry = &ls.entries[0];
                        let direct_target = entry.lifted_func;
                        for arg in args.iter_mut() {
                            self.rewrite_expr(arg);
                        }
                        if entry.captures.is_empty() {
                            // Zero captures: call target directly.
                            expr.kind = ExprKind::Call {
                                target: direct_target,
                                args: std::mem::take(args),
                            };
                        } else {
                            // With captures: destructure closure inline.
                            let span = expr.span;
                            let closure_expr = Box::new(Expr::new(ExprKind::Name(*target), span));
                            let tag_name = leak_str(&entry.tag_name);
                            let caps = &self.alloc.singleton_captures[&ls_idx];
                            let pattern = Pattern::Constructor {
                                name: tag_name,
                                fields: caps.iter().map(|s| Pattern::Binding(*s)).collect(),
                            };
                            let mut call_args: Vec<Expr<'src>> = caps.iter()
                                .map(|s| Expr::new(ExprKind::Name(*s), span))
                                .collect();
                            call_args.append(args);
                            let call = Expr::new(ExprKind::Call {
                                target: direct_target,
                                args: call_args,
                            }, span);
                            expr.kind = ExprKind::If {
                                expr: closure_expr,
                                arms: vec![MatchArm {
                                    pattern,
                                    guards: vec![],
                                    body: call,
                                    is_return: false,
                                }],
                                else_body: None,
                            };
                        }
                        return;
                    }
                    // Multi-entry: use apply dispatch.
                    let apply_sym = self.alloc.set_syms[ls_idx].0;
                    let closure_expr = Expr::new(ExprKind::Name(*target), expr.span);
                    for arg in args.iter_mut() {
                        self.rewrite_expr(arg);
                    }
                    let mut new_args = Vec::with_capacity(args.len() + 1);
                    new_args.push(closure_expr);
                    new_args.append(args);
                    expr.kind = ExprKind::Call {
                        target: apply_sym,
                        args: new_args,
                    };
                    return;
                }
                // Ordinary call: rewrite HO arg positions.
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
                if let Some(target) = resolved.clone() {
                    self.rewrite_call_args(&target, args, 1);
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
                for s in stmts.iter_mut() {
                    self.rewrite_stmt(s);
                }
                self.rewrite_expr(result);
            }
            ExprKind::If { expr: scrutinee, arms, else_body } => {
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
            ExprKind::Fold { expr: scrutinee, arms } => {
                self.rewrite_expr(scrutinee);
                for arm in arms.iter_mut() {
                    for g in arm.guards.iter_mut() {
                        self.rewrite_expr(g);
                    }
                    self.rewrite_expr(&mut arm.body);
                }
            }
            ExprKind::Record { fields } => {
                for (_, e) in fields.iter_mut() {
                    self.rewrite_expr(e);
                }
            }
            ExprKind::RecordUpdate { base, updates } => {
                self.rewrite_expr(base);
                for (_, e) in updates.iter_mut() {
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
            ExprKind::Closure { func, captures } => {
                for c in captures.iter_mut() {
                    self.rewrite_expr(c);
                }
                // Stray Closure (return value, let-binding, etc.) —
                // find which lambda set contains this func and rewrite
                // to a constructor call.
                let func = *func;
                if let Some((ls_idx, entry_idx)) = self.find_entry_for_func(func) {
                    let tag_sym = self.alloc.tag_syms[&(ls_idx, entry_idx)];
                    let capture_args: Vec<Expr<'src>> = std::mem::take(captures)
                        .into_iter()
                        .collect();
                    expr.kind = ExprKind::Call {
                        target: tag_sym,
                        args: capture_args,
                    };
                }
            }
            ExprKind::Lambda { .. } => {}
            ExprKind::IntLit(_)
            | ExprKind::FloatLit(_)
            | ExprKind::StrLit(_)
            | ExprKind::Name(_) => {}
        }
    }

    fn rewrite_stmt(&mut self, stmt: &mut Stmt<'src>) {
        match stmt {
            Stmt::Let { val, .. } | Stmt::Destructure { val, .. } => self.rewrite_expr(val),
            Stmt::Guard { condition, return_val } => {
                self.rewrite_expr(condition);
                self.rewrite_expr(return_val);
            }
            Stmt::TypeHint { .. } => {}
        }
    }

    fn rewrite_call_args(&mut self, callee: &str, args: &mut [Expr<'src>], offset: usize) {
        for (i, arg) in args.iter_mut().enumerate() {
            let idx = i + offset;
            let key = (callee.to_owned(), idx);
            if let Some(&ls_idx) = self.param_to_set.get(&key) {
                self.rewrite_ho_arg(arg, ls_idx);
            } else {
                self.rewrite_expr(arg);
            }
        }
    }

    fn rewrite_ho_arg(&mut self, arg: &mut Expr<'src>, ls_idx: usize) {
        match &mut arg.kind {
            ExprKind::Closure { func, captures } => {
                // Rewrite captures first.
                for c in captures.iter_mut() {
                    self.rewrite_expr(c);
                }
                // Find the entry for this lifted func.
                let entry_idx = self.sets[ls_idx]
                    .entries
                    .iter()
                    .position(|e| e.lifted_func == *func)
                    .expect("Closure func must be in lambda set");
                let tag_sym = self.alloc.tag_syms[&(ls_idx, entry_idx)];
                // Replace Closure with constructor call.
                let capture_args: Vec<Expr<'src>> = std::mem::take(captures)
                    .into_iter()
                    .collect();
                arg.kind = ExprKind::Call {
                    target: tag_sym,
                    args: capture_args,
                };
            }
            ExprKind::Name(sym) => {
                if self.ho_vars.contains_key(sym) {
                    // Pass-through: already a closure value.
                } else {
                    // Check if it's a named function ref in this set.
                    let display = self.symbols.display(*sym).to_owned();
                    if let Some(entry_idx) = self.sets[ls_idx]
                        .entries
                        .iter()
                        .position(|e| e.func_ref.as_deref() == Some(&display))
                    {
                        let tag_sym = self.alloc.tag_syms[&(ls_idx, entry_idx)];
                        arg.kind = ExprKind::Call {
                            target: tag_sym,
                            args: Vec::new(),
                        };
                    }
                    // else: local variable already holding a closure — leave as-is.
                }
            }
            _ => {
                self.rewrite_expr(arg);
            }
        }
    }
}

// ---- Utilities ----

fn synth_span() -> Span {
    Span {
        file: crate::source::FileId(0),
        start: usize::MAX,
        end: usize::MAX,
    }
}

fn leak_str(s: &str) -> &'static str {
    Box::leak(s.to_owned().into_boxed_str())
}
