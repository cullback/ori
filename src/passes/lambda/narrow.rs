//! Per-call-site narrowing of user HOFs.
//!
//! Closes the multi-callsite gap left after `lambda_specialize`:
//! when two call sites pass different concrete closures to the same
//! user HOF, `lambda_solve` merges them into one multi-variant
//! lambda set, the closure value lowers to the D2
//! `(tag, payload_ptr)` shape, and `__apply_K` dispatches at runtime.
//! Phase E's single-variant decomposition can't fire because the
//! callee's HO param has the wider, merged type.
//!
//! This pass walks every post-specialize body and, for each
//! `Call(user_hof, [tag_constructor_call, ...])`, generates a clone
//! of the callee specialized to the singleton subset. The clone gets
//! its own narrow `TagDecl`, its own tag constructor, and an inlined
//! singleton dispatch in place of `__apply_K`. The closure value at
//! the rewritten call site then has a single-variant type, so the
//! existing lower-stage `is_single_variant_tag_union` check fires
//! and Phase E decomposes the closure into `Multi(captures)` — no
//! heap object.
//!
//! See `notes/lambda-set-specialization.md` for the design.

#![allow(
    clippy::too_many_lines,
    clippy::too_many_arguments,
    clippy::collapsible_if,
    clippy::doc_markdown,
    clippy::missing_const_for_fn,
    reason = "AST walker with several distinct phases"
)]

use std::collections::HashMap;

use crate::ast::{
    self, Decl, Expr, ExprKind, ListPatternElem, MatchArm, Module, Pattern,
    RecordPatternRest, Span, Stmt, TagDecl, TypeDeclKind, TypeExpr,
};
use crate::passes::lambda::specialize::SingletonTarget;
use crate::passes::mono::Monomorphized;
use crate::symbol::{FieldSym, SymbolId, SymbolKind, SymbolTable};
use crate::types::engine::{Scheme, Type};

pub fn narrow(mono: &mut Monomorphized<'_>) {
    let module = std::mem::take(&mut mono.module);
    let (new_module, new_tag_targets, new_singletons) = narrow_module(
        module,
        &mut mono.symbols,
        &mut mono.infer.func_schemes,
        &mono.tag_targets,
    );
    mono.module = new_module;
    for (k, v) in new_tag_targets {
        mono.tag_targets.insert(k, v);
    }
    for (k, v) in new_singletons {
        mono.singletons.insert(k, v);
    }
}

fn narrow_module<'src>(
    mut module: Module<'src>,
    symbols: &mut SymbolTable,
    func_schemes: &mut HashMap<String, Scheme>,
    tag_targets: &HashMap<String, SingletonTarget>,
) -> (
    Module<'src>,
    HashMap<String, SingletonTarget>,
    HashMap<String, SingletonTarget>,
) {
    // Index FuncDef decls by name SymbolId. Only top-level user
    // FuncDefs are narrowing candidates (methods inside TypeAnno are
    // out of scope for this v1).
    let mut sym_to_decl_idx: HashMap<SymbolId, usize> = HashMap::new();
    for (idx, decl) in module.decls.iter().enumerate() {
        if let Decl::FuncDef { name, .. } = decl {
            sym_to_decl_idx.insert(*name, idx);
        }
    }

    // Build a tag name set: any Call(tag_sym, ...) where the tag is
    // in tag_targets is a closure constructor. We need to detect
    // these by sym, so build a reverse map from sym display name →
    // tag_targets entry.
    //
    // Skip tags whose enclosing TagDecl is already single-variant —
    // narrowing them is a no-op semantically and the existing
    // const_eval/static_promote pipeline already optimizes them. The
    // only payoff is narrowing multi-variant tag unions that force the
    // D2 (tag, payload_ptr) heap shape; for singleton TagDecls the
    // existing lowering already fires Phase E.
    let multi_variant_tags: std::collections::HashSet<String> = {
        let mut s = std::collections::HashSet::new();
        for decl in &module.decls {
            if let Decl::TypeAnno { ty: TypeExpr::TagUnion(tags, _), .. } = decl {
                if tags.len() > 1 {
                    for t in tags {
                        s.insert(t.name.to_owned());
                    }
                }
            }
        }
        s
    };
    let tag_names_in_targets: std::collections::HashSet<&String> = tag_targets
        .keys()
        .filter(|k| multi_variant_tags.contains(k.as_str()))
        .collect();

    // Phase 1: discover narrow opportunities.
    let mut sites: Vec<NarrowSite> = Vec::new();
    for decl in &module.decls {
        match decl {
            Decl::FuncDef { body, .. } => collect_sites(
                body,
                &sym_to_decl_idx,
                &tag_names_in_targets,
                symbols,
                &mut sites,
            ),
            Decl::TypeAnno { methods, .. } => {
                for m in methods {
                    if let Decl::FuncDef { body, .. } = m {
                        collect_sites(
                            body,
                            &sym_to_decl_idx,
                            &tag_names_in_targets,
                            symbols,
                            &mut sites,
                        );
                    }
                }
            }
        }
    }
    if sites.is_empty() {
        return (module, HashMap::new(), HashMap::new());
    }

    // Phase 2: group by (callee_sym, signature) so identical
    // narrowings dedupe across call sites.
    let mut groups: HashMap<(SymbolId, Vec<Option<String>>), GroupEntry> = HashMap::new();
    for site in sites {
        let key = (site.callee_sym, site.signature.clone());
        groups
            .entry(key)
            .or_insert_with(|| GroupEntry {
                spans: Vec::new(),
                signature: site.signature.clone(),
                callee_sym: site.callee_sym,
            })
            .spans
            .push(site.call_site_span);
    }

    // Phase 3: synthesize clones, new TagDecls, new constructors.
    let mut synth = Synthesizer {
        symbols,
        func_schemes,
        tag_targets,
        new_tag_targets: HashMap::new(),
        new_singletons: HashMap::new(),
        new_decls: Vec::new(),
        clone_counter: 0,
    };
    let mut rewrites: HashMap<Span, RewritePlan> = HashMap::new();
    for ((callee_sym, _sig), group) in groups {
        let decl_idx = sym_to_decl_idx[&callee_sym];
        let original_decl = module.decls[decl_idx].clone();
        let plan_template = synth.generate_clone(&original_decl, &group);
        if let Some(template) = plan_template {
            for span in &group.spans {
                rewrites.insert(*span, template.clone());
            }
        }
    }

    // Phase 4: apply rewrites — walk decls again, swap Call targets
    // and closure-constructor tag syms at matching spans.
    let rewriter = CallSiteRewriter { rewrites };
    for decl in &mut module.decls {
        match decl {
            Decl::FuncDef { body, .. } => rewriter.walk_expr(body),
            Decl::TypeAnno { methods, .. } => {
                for m in methods {
                    if let Decl::FuncDef { body, .. } = m {
                        rewriter.walk_expr(body);
                    }
                }
            }
        }
    }

    let _ = &rewriter;
    let new_tag_targets = synth.new_tag_targets;
    let new_singletons = synth.new_singletons;
    module.decls.extend(synth.new_decls);

    (module, new_tag_targets, new_singletons)
}

// ---- Phase 1: discover narrow opportunities ----

struct NarrowSite {
    call_site_span: Span,
    callee_sym: SymbolId,
    /// Per-arg-position: `Some(tag_name)` if the arg is a tag
    /// constructor call; `None` otherwise.
    signature: Vec<Option<String>>,
}

fn collect_sites<'src>(
    expr: &Expr<'src>,
    sym_to_decl_idx: &HashMap<SymbolId, usize>,
    tag_names_in_targets: &std::collections::HashSet<&String>,
    symbols: &SymbolTable,
    out: &mut Vec<NarrowSite>,
) {
    match &expr.kind {
        ExprKind::Call { target, args } => {
            if sym_to_decl_idx.contains_key(target) {
                // Possible narrow site. Inspect each arg.
                let mut signature: Vec<Option<String>> = Vec::with_capacity(args.len());
                let mut any_narrow = false;
                for arg in args {
                    let tag_name = if let ExprKind::Call {
                        target: arg_target,
                        args: _,
                    } = &arg.kind
                    {
                        let arg_display = symbols.display(*arg_target);
                        if tag_names_in_targets.contains(&arg_display.to_owned()) {
                            Some(arg_display.to_owned())
                        } else {
                            None
                        }
                    } else {
                        None
                    };
                    if tag_name.is_some() {
                        any_narrow = true;
                    }
                    signature.push(tag_name);
                }
                if any_narrow {
                    out.push(NarrowSite {
                        call_site_span: expr.span,
                        callee_sym: *target,
                        signature,
                    });
                }
            }
            for a in args {
                collect_sites(a, sym_to_decl_idx, tag_names_in_targets, symbols, out);
            }
        }
        ExprKind::BinOp { lhs, rhs, .. } => {
            collect_sites(lhs, sym_to_decl_idx, tag_names_in_targets, symbols, out);
            collect_sites(rhs, sym_to_decl_idx, tag_names_in_targets, symbols, out);
        }
        ExprKind::Block(stmts, result) => {
            for s in stmts {
                collect_sites_stmt(s, sym_to_decl_idx, tag_names_in_targets, symbols, out);
            }
            collect_sites(result, sym_to_decl_idx, tag_names_in_targets, symbols, out);
        }
        ExprKind::If {
            expr: s,
            arms,
            else_body,
        } => {
            collect_sites(s, sym_to_decl_idx, tag_names_in_targets, symbols, out);
            for arm in arms {
                for g in &arm.guards {
                    collect_sites(g, sym_to_decl_idx, tag_names_in_targets, symbols, out);
                }
                collect_sites(&arm.body, sym_to_decl_idx, tag_names_in_targets, symbols, out);
            }
            if let Some(eb) = else_body {
                collect_sites(eb, sym_to_decl_idx, tag_names_in_targets, symbols, out);
            }
        }
        ExprKind::Fold { expr: s, arms } => {
            collect_sites(s, sym_to_decl_idx, tag_names_in_targets, symbols, out);
            for arm in arms {
                for g in &arm.guards {
                    collect_sites(g, sym_to_decl_idx, tag_names_in_targets, symbols, out);
                }
                collect_sites(&arm.body, sym_to_decl_idx, tag_names_in_targets, symbols, out);
            }
        }
        ExprKind::Record { fields } => {
            for (_, e) in fields {
                collect_sites(e, sym_to_decl_idx, tag_names_in_targets, symbols, out);
            }
        }
        ExprKind::RecordUpdate { base, updates } => {
            collect_sites(base, sym_to_decl_idx, tag_names_in_targets, symbols, out);
            for (_, e) in updates {
                collect_sites(e, sym_to_decl_idx, tag_names_in_targets, symbols, out);
            }
        }
        ExprKind::FieldAccess { record, .. } => {
            collect_sites(record, sym_to_decl_idx, tag_names_in_targets, symbols, out);
        }
        ExprKind::Tuple(elems) | ExprKind::ListLit(elems) => {
            for e in elems {
                collect_sites(e, sym_to_decl_idx, tag_names_in_targets, symbols, out);
            }
        }
        ExprKind::QualifiedCall { args, .. } => {
            for a in args {
                collect_sites(a, sym_to_decl_idx, tag_names_in_targets, symbols, out);
            }
        }
        ExprKind::MethodCall { receiver, args, .. } => {
            collect_sites(receiver, sym_to_decl_idx, tag_names_in_targets, symbols, out);
            for a in args {
                collect_sites(a, sym_to_decl_idx, tag_names_in_targets, symbols, out);
            }
        }
        ExprKind::Is { expr: inner, .. } => {
            collect_sites(inner, sym_to_decl_idx, tag_names_in_targets, symbols, out);
        }
        ExprKind::Closure { captures, .. } => {
            for c in captures {
                collect_sites(c, sym_to_decl_idx, tag_names_in_targets, symbols, out);
            }
        }
        ExprKind::Lambda { body, .. } => {
            collect_sites(body, sym_to_decl_idx, tag_names_in_targets, symbols, out);
        }
        ExprKind::IntLit(_)
        | ExprKind::FloatLit(_)
        | ExprKind::StrLit(_)
        | ExprKind::Name(_) => {}
    }
}

fn collect_sites_stmt<'src>(
    stmt: &Stmt<'src>,
    sym_to_decl_idx: &HashMap<SymbolId, usize>,
    tag_names_in_targets: &std::collections::HashSet<&String>,
    symbols: &SymbolTable,
    out: &mut Vec<NarrowSite>,
) {
    match stmt {
        Stmt::Let { val, .. } | Stmt::Destructure { val, .. } => {
            collect_sites(val, sym_to_decl_idx, tag_names_in_targets, symbols, out);
        }
        Stmt::Guard {
            condition,
            return_val,
        } => {
            collect_sites(condition, sym_to_decl_idx, tag_names_in_targets, symbols, out);
            collect_sites(return_val, sym_to_decl_idx, tag_names_in_targets, symbols, out);
        }
        Stmt::TypeHint { .. } => {}
    }
}

// ---- Phase 2 grouping ----

#[derive(Clone)]
struct GroupEntry {
    spans: Vec<Span>,
    signature: Vec<Option<String>>,
    #[allow(dead_code)]
    callee_sym: SymbolId,
}

// ---- Phase 3: synthesize clones ----

struct Synthesizer<'a> {
    symbols: &'a mut SymbolTable,
    func_schemes: &'a mut HashMap<String, Scheme>,
    tag_targets: &'a HashMap<String, SingletonTarget>,
    new_tag_targets: HashMap<String, SingletonTarget>,
    new_singletons: HashMap<String, SingletonTarget>,
    new_decls: Vec<Decl<'static>>,
    clone_counter: usize,
}

impl<'a> Synthesizer<'a> {
    fn generate_clone<'src>(
        &mut self,
        original_decl: &Decl<'src>,
        group: &GroupEntry,
    ) -> Option<RewritePlan> {
        let Decl::FuncDef {
            name: orig_name,
            params,
            body,
            ..
        } = original_decl
        else {
            return None;
        };
        let orig_display = self.symbols.display(*orig_name).to_owned();
        let clone_idx = self.clone_counter;
        self.clone_counter += 1;

        // 1. Allocate a fresh clone name and its scheme.
        let clone_display = format!("{orig_display}__narrow{clone_idx}");
        let clone_sym = self
            .symbols
            .fresh(&clone_display, synth_span(), SymbolKind::Func);

        // 2. For each narrowed HO position, allocate new tag
        //    constructor + new TagDecl + new closure type name.
        let mut new_tags_per_arg: Vec<Option<SymbolId>> =
            Vec::with_capacity(group.signature.len());
        let mut new_arg_tys: Vec<Option<Type>> =
            Vec::with_capacity(group.signature.len());
        // Map from arg position → (new_tag_sym, num_captures,
        // target_func) for clone body rewriting.
        let mut narrow_info: Vec<Option<NarrowedTag>> =
            Vec::with_capacity(group.signature.len());

        for (arg_idx, tag_opt) in group.signature.iter().enumerate() {
            let Some(orig_tag_name) = tag_opt else {
                new_tags_per_arg.push(None);
                new_arg_tys.push(None);
                narrow_info.push(None);
                continue;
            };
            let Some(original_target) = self.tag_targets.get(orig_tag_name) else {
                new_tags_per_arg.push(None);
                new_arg_tys.push(None);
                narrow_info.push(None);
                continue;
            };
            let num_captures = original_target.num_captures;
            let target_func = original_target.target_func.clone();

            let new_tag_display =
                format!("{orig_tag_name}__narrow{clone_idx}_a{arg_idx}");
            let new_tag_sym = self.symbols.fresh(
                &new_tag_display,
                synth_span(),
                SymbolKind::Func,
            );
            let new_closure_type_display =
                format!("__Closure_{clone_display}_a{arg_idx}");
            let new_closure_type_sym = self.symbols.fresh(
                &new_closure_type_display,
                synth_span(),
                SymbolKind::Type,
            );

            // Add a TagDecl in the module.
            self.new_decls.push(build_singleton_tagdecl(
                new_closure_type_sym,
                leak_str(&new_tag_display),
                num_captures,
            ));

            // Register tag_targets entry so lower's
            // resolve_closure_target picks up the new tag.
            self.new_tag_targets.insert(
                new_tag_display.clone(),
                SingletonTarget {
                    target_func: target_func.clone(),
                    num_captures,
                },
            );

            new_tags_per_arg.push(Some(new_tag_sym));
            let info_for_ty = NarrowedTag {
                arg_idx,
                callee_param_sym: params[arg_idx],
                new_tag_sym,
                new_tag_name: new_tag_display.clone(),
                new_closure_type_sym,
                new_closure_type_name: new_closure_type_display.clone(),
                num_captures,
                target_func: target_func.clone(),
            };
            new_arg_tys.push(Some(singleton_tagunion_type(&info_for_ty)));
            narrow_info.push(Some(NarrowedTag {
                arg_idx,
                callee_param_sym: params[arg_idx],
                new_tag_sym,
                new_tag_name: new_tag_display.clone(),
                new_closure_type_sym,
                new_closure_type_name: new_closure_type_display.clone(),
                num_captures,
                target_func,
            }));
        }

        // 3. Clone the body with fresh syms for params and locals.
        let mut cloner = AstCloner::new(self.symbols);
        let new_params: Vec<SymbolId> = params
            .iter()
            .map(|p| cloner.rename(*p, synth_span(), SymbolKind::Local))
            .collect();
        let cloned_body = cloner.clone_expr(body);

        // 4. Build a per-clone narrow-info table keyed on the
        //    *cloned* param sym (the clone's own f sym). For each
        //    narrowed position, the clone's body will dispatch on
        //    cloned_param via the new tag.
        let clone_narrow_info: Vec<Option<NarrowedTag>> = narrow_info
            .into_iter()
            .enumerate()
            .map(|(i, info)| {
                info.map(|mut t| {
                    t.callee_param_sym = new_params[i];
                    t
                })
            })
            .collect();

        // 5. Walk the cloned body, replacing `__apply_K(f, args)`
        //    where f is a narrowed param with the singleton dispatch.
        let mut narrow_param_info: HashMap<SymbolId, NarrowedTag> = HashMap::new();
        for info in clone_narrow_info.into_iter().flatten() {
            narrow_param_info.insert(info.callee_param_sym, info);
        }
        let mut body_rewriter = CloneBodyRewriter {
            narrow_params: &narrow_param_info,
            symbols: self.symbols,
            func_schemes: self.func_schemes,
        };
        let mut final_body = cloned_body;
        body_rewriter.walk_expr(&mut final_body);

        // 6. Register a clone scheme in func_schemes with the HO
        //    params at narrowed positions retyped to the new
        //    singleton closure types. Without this, the SSA Call
        //    boundary's arg/param slot counts mismatch: callers
        //    pass the closure as Phase E Multi(captures) but the
        //    callee param expects Ptr (the default for Arrow types).
        let info_by_pos: HashMap<usize, NarrowedTag> = narrow_param_info
            .values()
            .map(|info| (info.arg_idx, info.clone()))
            .collect();
        if let Some(orig_scheme) = self.func_schemes.get(&orig_display).cloned() {
            let new_scheme = retype_scheme_params(&orig_scheme, &info_by_pos);
            self.func_schemes.insert(clone_display.clone(), new_scheme);
        }

        // 7. Push the clone FuncDef into new_decls.
        // The clone's body has 'src lifetime — but new_decls is
        // Vec<Decl<'static>>. We can't bridge that directly. So
        // we leak the body's wrapping into 'static by transmuting
        // the lifetime: the body only references &'src strings via
        // QualifiedCall::segments etc., which are interned in
        // SourceArena and live for the program's lifetime. The
        // narrowing pass runs once; after the module is returned,
        // these references stay valid for the rest of compilation.
        //
        // SAFETY: SourceArena's interned strings outlive the
        // module's lifetime in practice (the arena is a top-level
        // value in main). This is the same convention used by
        // lambda_specialize's `leak_str` for synthesized tag
        // names.
        let final_body_static: Expr<'static> = unsafe { std::mem::transmute(final_body) };
        self.new_decls.push(Decl::FuncDef {
            span: synth_span(),
            name: clone_sym,
            params: new_params,
            body: final_body_static,
            doc: None,
        });

        Some(RewritePlan {
            new_target: clone_sym,
            new_tags: new_tags_per_arg,
            new_arg_tys,
        })
    }
}

#[derive(Clone)]
struct NarrowedTag {
    arg_idx: usize,
    callee_param_sym: SymbolId,
    #[allow(dead_code)]
    new_tag_sym: SymbolId,
    new_tag_name: String,
    #[allow(dead_code)]
    new_closure_type_sym: SymbolId,
    #[allow(dead_code)]
    new_closure_type_name: String,
    num_captures: usize,
    target_func: String,
}

/// Build the canonical singleton TagUnion type for a narrowed closure
/// position. lower's `is_single_variant_tag_union` matches Type::TagUnion
/// directly, so setting the closure expr's `ty` to this shape (rather
/// than to a Type::Con that would need a `transparent` table lookup)
/// makes Phase E fire without further registration. The capture types
/// are `I64`-shaped: that's the same simplification `lambda_specialize`
/// uses for its synthesized `TagDecl` fields and is correct as long as
/// every capture is 8 bytes (which Ori's current scalar types and
/// pointer kinds all satisfy).
fn singleton_tagunion_type(info: &NarrowedTag) -> Type {
    let cap_tys: Vec<Type> = (0..info.num_captures)
        .map(|_| Type::Con("I64".to_owned()))
        .collect();
    Type::TagUnion {
        tags: vec![(info.new_tag_name.clone(), cap_tys)],
        rest: None,
    }
}

// ---- Phase 3.5: rewrite clone body — singleton dispatch ----

struct CloneBodyRewriter<'a> {
    narrow_params: &'a HashMap<SymbolId, NarrowedTag>,
    symbols: &'a mut SymbolTable,
    func_schemes: &'a HashMap<String, Scheme>,
}

impl<'a, 'src> CloneBodyRewriter<'a> {
    fn walk_expr(&mut self, expr: &mut Expr<'src>) {
        // First handle the targeted pattern: a Call to `__apply_*`
        // where the first arg is a Name reference to a narrowed
        // param.
        if let ExprKind::Call { target: _, args } = &mut expr.kind {
            if let Some(first) = args.first() {
                if let ExprKind::Name(name_sym) = &first.kind {
                    if let Some(info) = self.narrow_params.get(name_sym).cloned() {
                        // This is the apply dispatch we want to
                        // narrow. The Call's target is __apply_K;
                        // we replace the whole Call with a singleton
                        // match.
                        //
                        // New shape:
                        //   if f : new_tag(c0, c1, ...) then
                        //       target_func(c0, c1, ..., apply_args[1..])
                        //
                        // Collect the non-closure args (everything
                        // after position 0).
                        let mut apply_args = std::mem::take(args);
                        let mut closure_arg = apply_args.remove(0);
                        // Pin the scrutinee's type to the singleton
                        // TagUnion so lower's match path matches
                        // `is_single_variant_tag_union` and emits the
                        // Phase E decomposed form (registers, not
                        // load-from-payload).
                        closure_arg.ty = singleton_tagunion_type(&info);
                        let other_args = apply_args;

                        // Allocate fresh syms for the captured
                        // values (pattern bindings).
                        let cap_syms: Vec<SymbolId> = (0..info.num_captures)
                            .map(|i| {
                                let nm = format!("__nc_{}", i);
                                self.symbols.fresh(&nm, expr.span, SymbolKind::Local)
                            })
                            .collect();
                        let pattern = Pattern::Constructor {
                            name: leak_str(&info.new_tag_name),
                            fields: cap_syms
                                .iter()
                                .map(|s| Pattern::Binding(*s))
                                .collect(),
                        };

                        // Build the direct call: target_func(c0,
                        // c1, ..., other_args...).
                        //
                        // Each cap-Name's `ty` must be set to the
                        // source-level capture type from the lifted
                        // function's scheme. Without this, `lower`'s
                        // `to_slots` at the call boundary can't expand
                        // a multi-slot capture (e.g. a List) back into
                        // its slot trio — it would pass a single Ptr
                        // where the lifted function expects 3 slots,
                        // and the runtime would mis-interpret bytes.
                        let target_func_sym = self.symbols.fresh(
                            &info.target_func,
                            expr.span,
                            SymbolKind::Func,
                        );
                        let cap_tys = lifted_func_capture_types(
                            self.func_schemes,
                            &info.target_func,
                            info.num_captures,
                        );
                        let mut call_args: Vec<Expr<'src>> = cap_syms
                            .iter()
                            .enumerate()
                            .map(|(i, s)| {
                                let mut e = Expr::new(ExprKind::Name(*s), expr.span);
                                if let Some(ty) = cap_tys.get(i) {
                                    e.ty = ty.clone();
                                }
                                e
                            })
                            .collect();
                        for a in other_args {
                            call_args.push(a);
                        }
                        let body_call = Expr::new(
                            ExprKind::Call {
                                target: target_func_sym,
                                args: call_args,
                            },
                            expr.span,
                        );

                        // Wrap in `if closure_arg : pattern then body_call`.
                        // Tag arm body and the If with the original
                        // call's return type so lower's merge block
                        // gets a matching-typed param.
                        let result_ty = expr.ty.clone();
                        let mut typed_body_call = body_call;
                        typed_body_call.ty = result_ty.clone();
                        let new_if = Expr {
                            kind: ExprKind::If {
                                expr: Box::new(closure_arg),
                                arms: vec![MatchArm {
                                    pattern,
                                    guards: Vec::new(),
                                    body: typed_body_call,
                                    is_return: false,
                                }],
                                else_body: None,
                            },
                            span: expr.span,
                            id: ast::ExprId::fresh(),
                            ty: result_ty,
                        };
                        *expr = new_if;
                        // Don't recurse further into the rewritten
                        // expression (it's already in final shape).
                        return;
                    }
                }
            }
        }

        // Recurse normally.
        self.recurse(expr);
    }

    fn recurse(&mut self, expr: &mut Expr<'src>) {
        match &mut expr.kind {
            ExprKind::Call { args, .. } => {
                for a in args.iter_mut() {
                    self.walk_expr(a);
                }
            }
            ExprKind::BinOp { lhs, rhs, .. } => {
                self.walk_expr(lhs);
                self.walk_expr(rhs);
            }
            ExprKind::Block(stmts, result) => {
                for s in stmts.iter_mut() {
                    self.walk_stmt(s);
                }
                self.walk_expr(result);
            }
            ExprKind::If {
                expr: s,
                arms,
                else_body,
            } => {
                self.walk_expr(s);
                for arm in arms.iter_mut() {
                    for g in arm.guards.iter_mut() {
                        self.walk_expr(g);
                    }
                    self.walk_expr(&mut arm.body);
                }
                if let Some(eb) = else_body {
                    self.walk_expr(eb);
                }
            }
            ExprKind::Fold { expr: s, arms } => {
                self.walk_expr(s);
                for arm in arms.iter_mut() {
                    for g in arm.guards.iter_mut() {
                        self.walk_expr(g);
                    }
                    self.walk_expr(&mut arm.body);
                }
            }
            ExprKind::Record { fields } => {
                for (_, e) in fields.iter_mut() {
                    self.walk_expr(e);
                }
            }
            ExprKind::RecordUpdate { base, updates } => {
                self.walk_expr(base);
                for (_, e) in updates.iter_mut() {
                    self.walk_expr(e);
                }
            }
            ExprKind::FieldAccess { record, .. } => self.walk_expr(record),
            ExprKind::Tuple(elems) | ExprKind::ListLit(elems) => {
                for e in elems.iter_mut() {
                    self.walk_expr(e);
                }
            }
            ExprKind::QualifiedCall { args, .. } => {
                for a in args.iter_mut() {
                    self.walk_expr(a);
                }
            }
            ExprKind::MethodCall { receiver, args, .. } => {
                self.walk_expr(receiver);
                for a in args.iter_mut() {
                    self.walk_expr(a);
                }
            }
            ExprKind::Is { expr: inner, .. } => self.walk_expr(inner),
            ExprKind::Closure { captures, .. } => {
                for c in captures.iter_mut() {
                    self.walk_expr(c);
                }
            }
            ExprKind::Lambda { body, .. } => self.walk_expr(body),
            ExprKind::IntLit(_)
            | ExprKind::FloatLit(_)
            | ExprKind::StrLit(_)
            | ExprKind::Name(_) => {}
        }
    }

    fn walk_stmt(&mut self, stmt: &mut Stmt<'src>) {
        match stmt {
            Stmt::Let { val, .. } | Stmt::Destructure { val, .. } => self.walk_expr(val),
            Stmt::Guard {
                condition,
                return_val,
            } => {
                self.walk_expr(condition);
                self.walk_expr(return_val);
            }
            Stmt::TypeHint { .. } => {}
        }
    }
}

// ---- Phase 4: rewrite call sites ----

#[derive(Clone)]
struct RewritePlan {
    new_target: SymbolId,
    new_tags: Vec<Option<SymbolId>>,
    /// For each arg position, the new closure type (`Type::TagUnion`
    /// singleton) to set on the arg's `expr.ty`. Setting this makes
    /// `lower`'s `is_single_variant_tag_union` fire on the closure
    /// constructor call so it lowers to a Phase E `Multi(captures)`
    /// instead of allocating the (tag, payload_ptr) D2 shell.
    new_arg_tys: Vec<Option<Type>>,
}

struct CallSiteRewriter {
    rewrites: HashMap<Span, RewritePlan>,
}

impl CallSiteRewriter {
    fn walk_expr<'src>(&self, expr: &mut Expr<'src>) {
        if let Some(plan) = self.rewrites.get(&expr.span).cloned() {
            if let ExprKind::Call { target, args } = &mut expr.kind {
                *target = plan.new_target;
                for (i, arg) in args.iter_mut().enumerate() {
                    if let Some(Some(new_tag_sym)) = plan.new_tags.get(i) {
                        if let ExprKind::Call {
                            target: arg_target,
                            ..
                        } = &mut arg.kind
                        {
                            *arg_target = *new_tag_sym;
                        }
                    }
                    // Retype the arg expr to the singleton TagUnion
                    // so `lower::is_single_variant_tag_union` matches
                    // directly (no `transparent` lookup needed).
                    if let Some(Some(new_ty)) = plan.new_arg_tys.get(i) {
                        arg.ty = new_ty.clone();
                    }
                }
            }
        }
        self.recurse(expr);
    }

    fn recurse<'src>(&self, expr: &mut Expr<'src>) {
        match &mut expr.kind {
            ExprKind::Call { args, .. } => {
                for a in args.iter_mut() {
                    self.walk_expr(a);
                }
            }
            ExprKind::BinOp { lhs, rhs, .. } => {
                self.walk_expr(lhs);
                self.walk_expr(rhs);
            }
            ExprKind::Block(stmts, result) => {
                for s in stmts.iter_mut() {
                    self.walk_stmt(s);
                }
                self.walk_expr(result);
            }
            ExprKind::If {
                expr: s,
                arms,
                else_body,
            } => {
                self.walk_expr(s);
                for arm in arms.iter_mut() {
                    for g in arm.guards.iter_mut() {
                        self.walk_expr(g);
                    }
                    self.walk_expr(&mut arm.body);
                }
                if let Some(eb) = else_body {
                    self.walk_expr(eb);
                }
            }
            ExprKind::Fold { expr: s, arms } => {
                self.walk_expr(s);
                for arm in arms.iter_mut() {
                    for g in arm.guards.iter_mut() {
                        self.walk_expr(g);
                    }
                    self.walk_expr(&mut arm.body);
                }
            }
            ExprKind::Record { fields } => {
                for (_, e) in fields.iter_mut() {
                    self.walk_expr(e);
                }
            }
            ExprKind::RecordUpdate { base, updates } => {
                self.walk_expr(base);
                for (_, e) in updates.iter_mut() {
                    self.walk_expr(e);
                }
            }
            ExprKind::FieldAccess { record, .. } => self.walk_expr(record),
            ExprKind::Tuple(elems) | ExprKind::ListLit(elems) => {
                for e in elems.iter_mut() {
                    self.walk_expr(e);
                }
            }
            ExprKind::QualifiedCall { args, .. } => {
                for a in args.iter_mut() {
                    self.walk_expr(a);
                }
            }
            ExprKind::MethodCall { receiver, args, .. } => {
                self.walk_expr(receiver);
                for a in args.iter_mut() {
                    self.walk_expr(a);
                }
            }
            ExprKind::Is { expr: inner, .. } => self.walk_expr(inner),
            ExprKind::Closure { captures, .. } => {
                for c in captures.iter_mut() {
                    self.walk_expr(c);
                }
            }
            ExprKind::Lambda { body, .. } => self.walk_expr(body),
            ExprKind::IntLit(_)
            | ExprKind::FloatLit(_)
            | ExprKind::StrLit(_)
            | ExprKind::Name(_) => {}
        }
    }

    fn walk_stmt<'src>(&self, stmt: &mut Stmt<'src>) {
        match stmt {
            Stmt::Let { val, .. } | Stmt::Destructure { val, .. } => self.walk_expr(val),
            Stmt::Guard {
                condition,
                return_val,
            } => {
                self.walk_expr(condition);
                self.walk_expr(return_val);
            }
            Stmt::TypeHint { .. } => {}
        }
    }
}

// ---- AST clone with symbol substitution ----

struct AstCloner<'a> {
    symbols: &'a mut SymbolTable,
    sub: HashMap<SymbolId, SymbolId>,
}

impl<'a> AstCloner<'a> {
    fn new(symbols: &'a mut SymbolTable) -> Self {
        Self {
            symbols,
            sub: HashMap::new(),
        }
    }

    fn rename(&mut self, sym: SymbolId, span: Span, kind: SymbolKind) -> SymbolId {
        let name = self.symbols.display(sym).to_owned();
        let fresh = self.symbols.fresh(name, span, kind);
        self.sub.insert(sym, fresh);
        fresh
    }

    fn lookup(&self, sym: SymbolId) -> SymbolId {
        self.sub.get(&sym).copied().unwrap_or(sym)
    }

    fn clone_expr<'src>(&mut self, expr: &Expr<'src>) -> Expr<'src> {
        let new_kind = match &expr.kind {
            ExprKind::IntLit(n) => ExprKind::IntLit(*n),
            ExprKind::FloatLit(n) => ExprKind::FloatLit(*n),
            ExprKind::StrLit(b) => ExprKind::StrLit(b.clone()),
            ExprKind::Name(sym) => ExprKind::Name(self.lookup(*sym)),
            ExprKind::BinOp { op, lhs, rhs } => ExprKind::BinOp {
                op: *op,
                lhs: Box::new(self.clone_expr(lhs)),
                rhs: Box::new(self.clone_expr(rhs)),
            },
            ExprKind::Call { target, args } => ExprKind::Call {
                target: self.lookup(*target),
                args: args.iter().map(|a| self.clone_expr(a)).collect(),
            },
            ExprKind::Block(stmts, result) => {
                let new_stmts: Vec<Stmt<'src>> =
                    stmts.iter().map(|s| self.clone_stmt(s)).collect();
                let new_result = Box::new(self.clone_expr(result));
                ExprKind::Block(new_stmts, new_result)
            }
            ExprKind::If {
                expr: s,
                arms,
                else_body,
            } => ExprKind::If {
                expr: Box::new(self.clone_expr(s)),
                arms: arms.iter().map(|a| self.clone_arm(a)).collect(),
                else_body: else_body.as_ref().map(|eb| Box::new(self.clone_expr(eb))),
            },
            ExprKind::Fold { expr: s, arms } => ExprKind::Fold {
                expr: Box::new(self.clone_expr(s)),
                arms: arms.iter().map(|a| self.clone_arm(a)).collect(),
            },
            ExprKind::Lambda { params, body } => {
                let new_params: Vec<SymbolId> = params
                    .iter()
                    .map(|p| self.rename(*p, expr.span, SymbolKind::Local))
                    .collect();
                ExprKind::Lambda {
                    params: new_params,
                    body: Box::new(self.clone_expr(body)),
                }
            }
            ExprKind::QualifiedCall {
                segments,
                args,
                resolved,
            } => ExprKind::QualifiedCall {
                segments: segments.clone(),
                args: args.iter().map(|a| self.clone_expr(a)).collect(),
                resolved: resolved.clone(),
            },
            ExprKind::Record { fields } => ExprKind::Record {
                fields: fields
                    .iter()
                    .map(|(f, e)| (*f, self.clone_expr(e)))
                    .collect(),
            },
            ExprKind::RecordUpdate { base, updates } => ExprKind::RecordUpdate {
                base: Box::new(self.clone_expr(base)),
                updates: updates
                    .iter()
                    .map(|(f, e)| (*f, self.clone_expr(e)))
                    .collect(),
            },
            ExprKind::FieldAccess { record, field } => ExprKind::FieldAccess {
                record: Box::new(self.clone_expr(record)),
                field: *field,
            },
            ExprKind::Tuple(elems) => {
                ExprKind::Tuple(elems.iter().map(|e| self.clone_expr(e)).collect())
            }
            ExprKind::ListLit(elems) => {
                ExprKind::ListLit(elems.iter().map(|e| self.clone_expr(e)).collect())
            }
            ExprKind::MethodCall {
                receiver,
                method,
                args,
                resolved,
            } => ExprKind::MethodCall {
                receiver: Box::new(self.clone_expr(receiver)),
                method,
                args: args.iter().map(|a| self.clone_expr(a)).collect(),
                resolved: resolved.clone(),
            },
            ExprKind::Is { expr: inner, pattern } => ExprKind::Is {
                expr: Box::new(self.clone_expr(inner)),
                pattern: self.clone_pattern(pattern, expr.span),
            },
            ExprKind::Closure { func, captures } => ExprKind::Closure {
                func: self.lookup(*func),
                captures: captures.iter().map(|c| self.clone_expr(c)).collect(),
            },
        };
        Expr {
            kind: new_kind,
            span: expr.span,
            id: ast::ExprId::fresh(),
            ty: expr.ty.clone(),
        }
    }

    fn clone_stmt<'src>(&mut self, stmt: &Stmt<'src>) -> Stmt<'src> {
        match stmt {
            Stmt::Let { name, val } => {
                let span = synth_span();
                let new_name = self.rename(*name, span, SymbolKind::Local);
                let new_val = self.clone_expr(val);
                Stmt::Let {
                    name: new_name,
                    val: new_val,
                }
            }
            Stmt::Destructure { pattern, val } => {
                let new_val = self.clone_expr(val);
                let new_pat = self.clone_pattern(pattern, synth_span());
                Stmt::Destructure {
                    pattern: new_pat,
                    val: new_val,
                }
            }
            Stmt::Guard {
                condition,
                return_val,
            } => Stmt::Guard {
                condition: self.clone_expr(condition),
                return_val: self.clone_expr(return_val),
            },
            Stmt::TypeHint { name, ty } => Stmt::TypeHint {
                name,
                ty: ty.clone(),
            },
        }
    }

    fn clone_arm<'src>(&mut self, arm: &MatchArm<'src>) -> MatchArm<'src> {
        let pat = self.clone_pattern(&arm.pattern, synth_span());
        let guards = arm.guards.iter().map(|g| self.clone_expr(g)).collect();
        let body = self.clone_expr(&arm.body);
        MatchArm {
            pattern: pat,
            guards,
            body,
            is_return: arm.is_return,
        }
    }

    fn clone_pattern<'src>(&mut self, pat: &Pattern<'src>, span: Span) -> Pattern<'src> {
        match pat {
            Pattern::Constructor { name, fields } => Pattern::Constructor {
                name,
                fields: fields.iter().map(|p| self.clone_pattern(p, span)).collect(),
            },
            Pattern::Record { fields, rest } => {
                let new_fields: Vec<(FieldSym, Pattern<'src>)> = fields
                    .iter()
                    .map(|(f, p)| (*f, self.clone_pattern(p, span)))
                    .collect();
                let new_rest = match rest {
                    RecordPatternRest::Capture(sym) => {
                        RecordPatternRest::Capture(self.rename(*sym, span, SymbolKind::Local))
                    }
                    RecordPatternRest::None => RecordPatternRest::None,
                    RecordPatternRest::Ignore => RecordPatternRest::Ignore,
                };
                Pattern::Record {
                    fields: new_fields,
                    rest: new_rest,
                }
            }
            Pattern::List(elems) => Pattern::List(
                elems
                    .iter()
                    .map(|e| match e {
                        ListPatternElem::Pattern(p) => {
                            ListPatternElem::Pattern(self.clone_pattern(p, span))
                        }
                        ListPatternElem::Spread(Some(sym)) => ListPatternElem::Spread(Some(
                            self.rename(*sym, span, SymbolKind::Local),
                        )),
                        ListPatternElem::Spread(None) => ListPatternElem::Spread(None),
                    })
                    .collect(),
            ),
            Pattern::Tuple(elems) => Pattern::Tuple(
                elems.iter().map(|p| self.clone_pattern(p, span)).collect(),
            ),
            Pattern::IntLit(n) => Pattern::IntLit(*n),
            Pattern::StrLit(b) => Pattern::StrLit(b.clone()),
            Pattern::Wildcard => Pattern::Wildcard,
            Pattern::Binding(sym) => {
                Pattern::Binding(self.rename(*sym, span, SymbolKind::Local))
            }
        }
    }
}

// ---- Helpers ----

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

/// Look up the source-level types of the first `n` parameters of a
/// lifted function — these are its captures (placed first by
/// `lambda_lift`). Returns an empty Vec on lookup failure so the
/// caller can leave the placeholder type in place (harmless for
/// scalar captures; only matters when a capture is multi-slot and
/// `lower::to_slots` needs the type to expand the binding).
fn lifted_func_capture_types(
    func_schemes: &HashMap<String, Scheme>,
    target_func: &str,
    n: usize,
) -> Vec<Type> {
    let Some(scheme) = func_schemes.get(target_func) else {
        return Vec::new();
    };
    let Type::Arrow(params, _) = &scheme.ty else {
        return Vec::new();
    };
    if params.len() < n {
        return Vec::new();
    }
    params[..n].to_vec()
}

/// Build a new Scheme by replacing param types at the indices in
/// `info_by_pos` with the new closure type. Leaves other params and
/// the return type alone.
fn retype_scheme_params(orig: &Scheme, info_by_pos: &HashMap<usize, NarrowedTag>) -> Scheme {
    let new_ty = match &orig.ty {
        Type::Arrow(params, ret) => {
            let new_params: Vec<Type> = params
                .iter()
                .enumerate()
                .map(|(i, p)| {
                    if let Some(info) = info_by_pos.get(&i) {
                        singleton_tagunion_type(info)
                    } else {
                        p.clone()
                    }
                })
                .collect();
            Type::Arrow(new_params, ret.clone())
        }
        other => other.clone(),
    };
    Scheme {
        vars: orig.vars.clone(),
        constraints: orig.constraints.clone(),
        ty: new_ty,
    }
}

fn build_singleton_tagdecl(
    type_sym: SymbolId,
    tag_name: &'static str,
    captures_count: usize,
) -> Decl<'static> {
    let tag = TagDecl {
        name: tag_name,
        fields: vec![TypeExpr::Named("I64"); captures_count],
    };
    Decl::TypeAnno {
        span: synth_span(),
        name: type_sym,
        type_params: Vec::new(),
        ty: TypeExpr::TagUnion(vec![tag], false),
        where_clause: Vec::new(),
        methods: Vec::new(),
        kind: TypeDeclKind::Transparent,
        doc: None,
    }
}

// `Type` and `Scheme` are referenced indirectly through func_schemes
// but not constructed in this v1 (we copy the original's scheme).
// Keep them in scope so the imports above aren't dead.
const _PHANTOM_TYPE: Option<Type> = None;
const _PHANTOM_SCHEME: Option<Scheme> = None;
