#![allow(
    clippy::too_many_lines,
    clippy::iter_over_hash_type,
    clippy::iter_on_single_items,
    clippy::needless_pass_by_value,
    clippy::explicit_iter_loop,
    clippy::collapsible_if,
    clippy::collapsible_match,
    clippy::match_wildcard_for_single_variants,
    clippy::match_same_arms,
    clippy::needless_borrow,
    reason = "mono is a large AST-walk state machine"
)]
//! Monomorphization pass — AST → AST rewrite.
//!
//! Specializes every polymorphic user function per concrete
//! instantiation reachable from `main`. After this pass, every
//! `FuncDef` has a monomorphic `Scheme` and every `Expr.ty` is fully
//! concrete.
//!
//! ## Output shape
//!
//! **All** specialized and identity-specialized method `FuncDef`s
//! are emitted as *top-level* `Decl::FuncDef`s with their fully
//! mangled display names (e.g. `List.map__I64`, `Foo.bar`). Nothing
//! stays inside `TypeAnno.methods` except annotation-only methods
//! (stdlib builtins like `List.walk` that never had a body). This
//! uniform layout lets `decl_info`, `reachable`, `defunc`, and
//! `ssa::lower` all iterate free functions with a single loop.
//!
//! Free-function monomorphic specializations are the only exception:
//! they keep the original `SymbolId` (and therefore the original
//! display name) because the source name is already the canonical
//! mangled name.
//!
//! ## Algorithm
//!
//! Seed a worklist with `main`. Process the worklist by walking each
//! reachable function body, rewriting every call to a polymorphic
//! function to point at a freshly-allocated specialization. A
//! specialization is keyed by `(original_display_name, normalized
//! type arguments)`. Duplicate keys reuse the existing
//! specialization's `SymbolId`; fresh keys allocate a new one and
//! enqueue the body for processing.
//!
//! ## Normalization
//!
//! A type used as a specialization key is normalized by resolving
//! residual `Type::Var(_)` to an `I64` sentinel, sorting record
//! fields for stable field order, and dropping open row variables.
//!
//! ## What stays polymorphic
//!
//! - **Constructors** stay polymorphic. Mono only touches
//!   `Decl::FuncDef`. Constructor tag indices are stable across
//!   specializations.
//! - **Annotation-only methods** (`List.walk`, `List.len`, etc.)
//!   stay as `TypeAnno.methods` entries without bodies. Mono can't
//!   specialize them because it has nothing to clone.
//! - **`__fold_N` helpers** synthesized by `fold_lift` are already
//!   monomorphic.

use std::collections::{HashMap, VecDeque};

use crate::ast::{Decl, Expr, ExprKind, Module, Span, Stmt};
use crate::symbol::{SymbolId, SymbolKind, SymbolTable};
use crate::types::engine::{Scheme, Type, TypeVar};
use crate::types::infer::InferResult;

/// Post-monomorphization state: fully concrete module, specialized
/// inference results, and the symbol table (which gains new entries
/// for specialized function copies).
pub struct Monomorphized<'src> {
    pub module: Module<'src>,
    pub infer: InferResult,
    pub symbols: SymbolTable,
    /// Maps apply function names to direct call targets for singleton lambda sets.
    pub singletons: std::collections::HashMap<String, crate::passes::lambda::SingletonTarget>,
    /// Maps closure tag constructor names to direct call targets (all entries, not just singletons).
    pub tag_targets: std::collections::HashMap<String, crate::passes::lambda::SingletonTarget>,
}

/// Specialize every polymorphic function reachable from `main`.
pub fn specialize<'src>(
    module: Module<'src>,
    infer_result: InferResult,
    mut symbols: SymbolTable,
) -> Monomorphized<'src> {
    // The module lives for this function. We destructure it into
    // its parts so we can borrow from `input_decls` while the
    // worklist processes bodies (Phase 1–3) and then consume
    // `input_decls` in Phase 4 assembly. This keeps lambda bodies
    // as honest `&'src Expr<'src>` borrows instead of forcing a
    // `'src → 'static` transmute.
    let Module {
        exports,
        imports,
        decls: input_decls,
    } = module;

    let (specialized, specialized_schemes) = {
        let mut ctx = MonoCtx::new(&infer_result, &mut symbols);

        // Pass 1: index every `FuncDef` (free or method) by its
        // fully mangled name so the worklist can look up bodies.
        for decl in &input_decls {
            ctx.index_decl(decl);
        }

        // Pass 2: seed the worklist with `main` as an identity
        // specialization. Other decls enter the worklist only when
        // they're reached from a processed body.
        let main_name = "main".to_owned();
        let main_sym = ctx
            .original_syms
            .get(&main_name)
            .copied()
            .expect("mono: no 'main' function");
        ctx.spec_map
            .insert((main_name.clone(), Vec::new()), main_sym);
        ctx.worklist.push_back(SpecRequest {
            name: main_name,
            substitution: Vec::new(),
            extra_mapping: HashMap::new(),
            spec_sym: main_sym,
        });

        // Pass 3: drain the worklist. Each iteration clones a body,
        // substitutes type vars in every `Expr::ty`, rewrites nested
        // call sites (which may enqueue further specializations),
        // and emits a `Decl::FuncDef`.
        let mut specialized: Vec<Decl<'src>> = Vec::new();
        while let Some(req) = ctx.worklist.pop_front() {
            if let Some(decl) = ctx.process_request(req) {
                specialized.push(decl);
            }
        }
        (specialized, ctx.specialized_schemes)
        // `ctx` is dropped here — the `&input_decls` borrow ends.
    };

    // Pass 4: assemble the output module. Now that `ctx` is gone
    // we can consume `input_decls`.
    //
    // - Keep every `TypeAnno` decl, but drop its `FuncDef` methods
    //   (replaced by top-level specializations in `specialized`).
    //   Annotation-only methods pass through unchanged.
    // - Drop every input `FuncDef` — it's either replaced by its
    //   specializations in `specialized` or dead from `main`.
    // - Append every `specialized` entry at top level.
    let mut out_decls: Vec<Decl<'src>> =
        Vec::with_capacity(input_decls.len() + specialized.len());
    for decl in input_decls {
        match decl {
            Decl::FuncDef { .. } => {}
            Decl::TypeAnno {
                span,
                name,
                type_params,
                ty,
                where_clause,
                methods,
                kind,
                doc,
            } => {
                let kept_methods: Vec<Decl<'src>> = methods
                    .into_iter()
                    .filter(|m| !matches!(m, Decl::FuncDef { .. }))
                    .collect();
                out_decls.push(Decl::TypeAnno {
                    span,
                    name,
                    type_params,
                    ty,
                    where_clause,
                    methods: kept_methods,
                    kind,
                    doc,
                });
            }
        }
    }
    out_decls.extend(specialized);

    let new_infer = build_new_infer_result(&infer_result, &specialized_schemes);

    Monomorphized {
        module: Module {
            exports,
            imports,
            decls: out_decls,
        },
        infer: new_infer,
        symbols,
        singletons: std::collections::HashMap::new(),
        tag_targets: std::collections::HashMap::new(),
    }
}

// ---- Mono context ----

struct SpecRequest {
    /// The original mangled name (`"main"`, `"get_age"`, `"List.map"`).
    name: String,
    /// The concrete types to substitute for the scheme's type vars.
    /// Empty for identity specializations of monomorphic functions.
    substitution: Vec<Type>,
    /// Additional `TypeVar → Type` bindings for vars that appear in
    /// `scheme.ty` but not in `scheme.vars` — extracted from the
    /// call-site concrete via the transparent-aware
    /// `extract_substitution_with`. Carries foreign vars whose
    /// concrete value is determined at the use site (e.g. a row var
    /// from the enclosing scope leaking into a lifted lambda's
    /// scheme.ty). Without this, body substitution would default
    /// such vars to I64 and mistype downstream method-call sites.
    extra_mapping: HashMap<TypeVar, Type>,
    /// The `SymbolId` the resulting `FuncDef` should carry.
    spec_sym: SymbolId,
}

struct MonoCtx<'a, 'src> {
    infer: &'a InferResult,
    symbols: &'a mut SymbolTable,
    /// Original `FuncDef` bodies indexed by fully mangled name.
    /// Each entry borrows directly from the input module's decls,
    /// which we keep alive for the duration of the worklist drain.
    decl_bodies: HashMap<String, StoredBody<'a, 'src>>,
    /// Fully mangled name → original `SymbolId`. Used when seeding
    /// `main` and when a monomorphic free function's identity
    /// specialization reuses its original `SymbolId`.
    original_syms: HashMap<String, SymbolId>,
    /// Forward map: `(original_name, type_args)` → specialized sym.
    spec_map: HashMap<(String, Vec<Type>), SymbolId>,
    /// Specialized schemes, keyed by the specialized function's
    /// mangled display name. Feeds the new `InferResult`.
    specialized_schemes: HashMap<String, Scheme>,
    worklist: VecDeque<SpecRequest>,
}

/// Borrowed view of a `FuncDef` body plus the scheme and
/// provenance needed to specialize it. Everything borrows from
/// either the input module (for `body` / `params` / `doc`) or the
/// inference result (for `scheme`), so no clones or lifetime
/// extensions are required.
#[derive(Clone, Copy)]
struct StoredBody<'a, 'src> {
    span: Span,
    params: &'a [SymbolId],
    body: &'a Expr<'src>,
    scheme: &'a Scheme,
    doc: &'a Option<String>,
    /// `true` if this came from a `TypeAnno.methods` entry, `false`
    /// if it's a free function. Methods always get a fresh top-level
    /// `SymbolId` allocated for their specialization (even for the
    /// identity spec) because they need their display name rewritten
    /// from `"bar"` to `"Foo.bar"`.
    is_method: bool,
}

impl<'a, 'src> MonoCtx<'a, 'src> {
    fn new(infer: &'a InferResult, symbols: &'a mut SymbolTable) -> Self {
        Self {
            infer,
            symbols,
            decl_bodies: HashMap::new(),
            original_syms: HashMap::new(),
            spec_map: HashMap::new(),
            specialized_schemes: HashMap::new(),
            worklist: VecDeque::new(),
        }
    }

    fn index_decl(&mut self, decl: &'a Decl<'src>) {
        match decl {
            Decl::FuncDef {
                span,
                name,
                params,
                body,
                doc,
            } => {
                let display = self.symbols.display(*name).to_owned();
                self.original_syms.insert(display.clone(), *name);
                if let Some(scheme) = self.infer.func_schemes.get(&display) {
                    self.decl_bodies.insert(
                        display,
                        StoredBody {
                            span: *span,
                            params,
                            body,
                            scheme,
                            doc,
                            is_method: false,
                        },
                    );
                }
            }
            Decl::TypeAnno { name, methods, .. } => {
                let type_name = self.symbols.display(*name).to_owned();
                for m in methods {
                    if let Decl::FuncDef {
                        span,
                        name: method_name,
                        params,
                        body,
                        doc,
                    } = m
                    {
                        let method_display = self.symbols.display(*method_name);
                        let mangled = format!("{type_name}.{method_display}");
                        self.original_syms.insert(mangled.clone(), *method_name);
                        if let Some(scheme) = self.infer.func_schemes.get(&mangled) {
                            self.decl_bodies.insert(
                                mangled,
                                StoredBody {
                                    span: *span,
                                    params,
                                    body,
                                    scheme,
                                    doc,
                                    is_method: true,
                                },
                            );
                        }
                    }
                }
            }
        }
    }

    /// Process one specialization request. Returns the specialized
    /// `FuncDef` (to be appended to the output module) or `None` if
    /// the name doesn't correspond to a body we can clone (e.g. a
    /// dangling reference through an annotation-only method).
    fn process_request(&mut self, req: SpecRequest) -> Option<Decl<'src>> {
        // Snapshot the stored-body metadata we need into owned
        // values / fresh clones so the mutable walk over `body`
        // below doesn't alias the still-borrowed `decl_bodies`.
        let stored = *self.decl_bodies.get(&req.name)?;
        let span = stored.span;
        let params = stored.params.to_vec();
        let mut body = stored.body.clone();
        let scheme_ty = stored.scheme.ty.clone();
        let scheme_vars = stored.scheme.vars.clone();
        let doc = stored.doc.clone();

        let mut mapping: HashMap<TypeVar, Type> = scheme_vars
            .iter()
            .zip(req.substitution.iter())
            .map(|(v, t)| (*v, t.clone()))
            .collect();
        // Layer in foreign-var bindings (vars that appear in
        // scheme.ty but not scheme.vars). See SpecRequest.extra_mapping.
        for (v, t) in &req.extra_mapping {
            mapping.entry(*v).or_insert_with(|| t.clone());
        }

        substitute_types_in_expr(&mut body, &mapping);
        self.rewrite_calls_in_expr(&mut body);

        let specialized_ty = apply_mapping(&scheme_ty, &mapping);
        let spec_display = self.symbols.display(req.spec_sym).to_owned();
        self.specialized_schemes.insert(
            spec_display,
            Scheme {
                vars: Vec::new(),
                constraints: Vec::new(),
                ty: specialized_ty,
            },
        );

        Some(Decl::FuncDef {
            span,
            name: req.spec_sym,
            params,
            body,
            doc,
        })
    }

    /// Walk an expression and rewrite every `Call`, `QualifiedCall`,
    /// and `MethodCall` whose target is a known polymorphic function
    /// (or a method that needs its display reshaped).
    fn rewrite_calls_in_expr(&mut self, expr: &mut Expr<'src>) {
        match &mut expr.kind {
            ExprKind::Call { target, args } => {
                let concrete = call_signature(args, &expr.ty);
                if let Some(new_sym) = self.specialize_target(*target, &concrete) {
                    *target = new_sym;
                }
                for a in args.iter_mut() {
                    self.rewrite_calls_in_expr(a);
                }
            }
            ExprKind::QualifiedCall {
                segments,
                args,
                resolved,
            } => {
                // Inference leaves `resolved = None` for stdlib-style
                // static qualified calls (e.g. `List.sum(xs)`), in
                // which case the callable name is the joined
                // segments. If `resolved` is set, inference decided
                // this is a method-on-local-receiver dispatch.
                let resolved_was_set = resolved.is_some();
                let target_name = resolved
                    .clone()
                    .unwrap_or_else(|| segments.join("."));
                let concrete = call_signature(args, &expr.ty);
                if let Some(new_name) =
                    self.specialize_by_name(&target_name, &concrete)
                {
                    if resolved_was_set {
                        *resolved = Some(new_name);
                    } else {
                        // Static qualified call: rebuild `segments`
                        // so `segments.join(".")` yields the new
                        // mangled name.
                        let parts: Vec<&'static str> =
                            new_name.split('.').map(leak_str).collect();
                        *segments = parts;
                    }
                }
                for a in args.iter_mut() {
                    self.rewrite_calls_in_expr(a);
                }
            }
            ExprKind::MethodCall {
                receiver,
                args,
                resolved,
                ..
            } => {
                if let Some(resolved_name) = resolved.clone() {
                    let mut arg_types: Vec<Type> = vec![receiver.ty.clone()];
                    arg_types.extend(args.iter().map(|a| a.ty.clone()));
                    let concrete =
                        Type::Arrow(arg_types, Box::new(expr.ty.clone()), None);
                    if let Some(new_name) =
                        self.specialize_by_name(&resolved_name, &concrete)
                    {
                        *resolved = Some(new_name);
                    }
                }
                self.rewrite_calls_in_expr(receiver);
                for a in args.iter_mut() {
                    self.rewrite_calls_in_expr(a);
                }
            }
            ExprKind::BinOp { lhs, rhs, .. } => {
                self.rewrite_calls_in_expr(lhs);
                self.rewrite_calls_in_expr(rhs);
            }
            ExprKind::Block(stmts, result) => {
                for s in stmts.iter_mut() {
                    self.rewrite_calls_in_stmt(s);
                }
                self.rewrite_calls_in_expr(result);
            }
            ExprKind::If {
                expr: scrutinee,
                arms,
                else_body,
            } => {
                self.rewrite_calls_in_expr(scrutinee);
                for arm in arms.iter_mut() {
                    for g in arm.guards.iter_mut() {
                        self.rewrite_calls_in_expr(g);
                    }
                    self.rewrite_calls_in_expr(&mut arm.body);
                }
                if let Some(eb) = else_body {
                    self.rewrite_calls_in_expr(eb);
                }
            }
            ExprKind::Fold {
                expr: scrutinee,
                arms,
            } => {
                self.rewrite_calls_in_expr(scrutinee);
                for arm in arms.iter_mut() {
                    for g in arm.guards.iter_mut() {
                        self.rewrite_calls_in_expr(g);
                    }
                    self.rewrite_calls_in_expr(&mut arm.body);
                }
            }
            ExprKind::Lambda { .. } => {
                unreachable!("lift_pre_infer removes all Lambda nodes before mono runs")
            }
            ExprKind::Record { fields } => {
                for (_, e) in fields.iter_mut() {
                    self.rewrite_calls_in_expr(e);
                }
            }
            ExprKind::FieldAccess { record, .. } => self.rewrite_calls_in_expr(record),
            ExprKind::Tuple(elems) | ExprKind::ListLit(elems) => {
                for e in elems.iter_mut() {
                    self.rewrite_calls_in_expr(e);
                }
            }
            ExprKind::Is { expr: inner, .. } => self.rewrite_calls_in_expr(inner),
            ExprKind::RecordUpdate { base, updates } => {
                self.rewrite_calls_in_expr(base);
                for (_, e) in updates.iter_mut() {
                    self.rewrite_calls_in_expr(e);
                }
            }
            ExprKind::Name(sym) => {
                // Bare function reference (e.g. passing `step` as a
                // higher-order arg, or referencing a zero-param value
                // binding). If `sym` points at a known global function,
                // ensure a specialization is on the worklist.
                let name = self.symbols.display(*sym).to_owned();
                if let Some(stored) = self.decl_bodies.get(&name) {
                    if stored.scheme.vars.is_empty() && !stored.is_method {
                        // Monomorphic: identity specialization.
                        let key = (name.clone(), Vec::new());
                        if let std::collections::hash_map::Entry::Vacant(e) =
                            self.spec_map.entry(key)
                        {
                            let orig_sym = self.original_syms[&name];
                            e.insert(orig_sym);
                            self.worklist.push_back(SpecRequest {
                                name,
                                substitution: Vec::new(),
                                extra_mapping: HashMap::new(),
                                spec_sym: orig_sym,
                            });
                        }
                    } else if !stored.scheme.vars.is_empty() {
                        // Polymorphic: specialize using the concrete type
                        // from inference (carried on expr.ty).
                        if let Some(new_sym) = self.specialize_by_sym(&name, &expr.ty) {
                            *sym = new_sym;
                        }
                    }
                } else {
                    // Not a known function — might be a local variable.
                    // This is fine; Name references to locals are handled
                    // by the vars map in the lowerer.
                }
            }
            ExprKind::IntLit(_) | ExprKind::FloatLit(_) | ExprKind::StrLit(_) => {}
            ExprKind::Closure { func, captures } => {
                // Recurse into captures first so their types are
                // substituted to their concrete form before we use
                // them in the lifted func's specialization key.
                for c in captures.iter_mut() {
                    self.rewrite_calls_in_expr(c);
                }
                // Build the concrete type for the lifted function:
                // capture types prepended to the closure's callable
                // params. The Closure node's `ty` is the *callable*
                // view (Arrow(remaining_params, ret)) — the lifted
                // function's scheme is Arrow(captures + remaining,
                // ret), so mono needs the full arrow to extract type
                // substitutions correctly. (See `infer_closure`.)
                // Capture and param types may be transparent-newtype
                // applications (e.g., `App("Set", [{x,y}])`) while the
                // scheme.ty is the underlying record (since infer ran
                // inside the method body with the transparent unwrap
                // active). Unwrap before passing to mono so
                // extract_substitution matches structurally.
                let unwrap = |t: &Type| {
                    crate::passes::core::lower::resolve_transparent(
                        t, &self.infer.transparent,
                    )
                };
                let concrete = match &expr.ty {
                    Type::Arrow(call_params, ret, _) => {
                        let mut full = Vec::with_capacity(captures.len() + call_params.len());
                        for c in captures.iter() {
                            full.push(unwrap(&c.ty));
                        }
                        for p in call_params {
                            full.push(unwrap(p));
                        }
                        Type::Arrow(full, Box::new(unwrap(ret)), None)
                    }
                    other => unwrap(other),
                };
                if let Some(new_sym) = self.specialize_target(*func, &concrete) {
                    *func = new_sym;
                }
            }
        }
    }

    fn rewrite_calls_in_stmt(&mut self, stmt: &mut Stmt<'src>) {
        match stmt {
            Stmt::Let { val, .. } | Stmt::Destructure { val, .. } => {
                self.rewrite_calls_in_expr(val);
            }
            Stmt::Guard {
                condition,
                return_val,
            } => {
                self.rewrite_calls_in_expr(condition);
                self.rewrite_calls_in_expr(return_val);
            }
            Stmt::TypeHint { .. } => {}
        }
    }

    /// Handle a `Call { target }` site: look up the target's mangled
    /// display name, compute its specialization (if needed), and
    /// return the new `SymbolId` to write back to `target`. `None`
    /// means "no rewrite needed" (the original sym is still correct).
    fn specialize_target(&mut self, target: SymbolId, concrete: &Type) -> Option<SymbolId> {
        let name = self.symbols.display(target).to_owned();
        self.specialize_by_sym(&name, concrete)
    }

    /// String-keyed form of `specialize_target`, used by
    /// `QualifiedCall` and `MethodCall` which track their target as
    /// a mangled string. Returns the new mangled name to write back
    /// to `resolved` / `segments`.
    fn specialize_by_name(&mut self, name: &str, concrete: &Type) -> Option<String> {
        let new_sym = self.specialize_by_sym(name, concrete)?;
        Some(self.symbols.display(new_sym).to_owned())
    }

    /// Core specialization logic. Returns `Some(new_sym)` when the
    /// call site should be rewritten to reference the new sym;
    /// `None` when the original target is still correct (the only
    /// case is a monomorphic free function that reuses its original
    /// `SymbolId`).
    fn specialize_by_sym(&mut self, name: &str, concrete: &Type) -> Option<SymbolId> {
        let stored = *self.decl_bodies.get(name)?;

        // Compute the type-arg substitution. Empty for monomorphic
        // functions; extracted and normalized for polymorphic ones.
        // Resolution priority for each scheme var:
        //   1. `extract_substitution_with` — call-site type binds the
        //      var via its structural position in `scheme.ty`.
        //   2. `default_type` — truly unconstrained (defaults to I64
        //      to keep List.sum's `forall a [a.add]. List(a) -> a`
        //      working when its body fixes `a` via `0` literal).
        // Identify lambda-set vars structurally. They get substituted
        // through the body like any var (so process_request's mapping
        // is complete) but are filtered from the mangled name to keep
        // it stable (Phase D uses the row content as a spec sub-key
        // via `args`, not via the display).
        let mut ls_vars: std::collections::HashSet<TypeVar> =
            std::collections::HashSet::new();
        collect_lambda_set_vars(&stored.scheme.ty, &mut ls_vars);

        let (args, extra_mapping): (Vec<Type>, HashMap<TypeVar, Type>) =
            if stored.scheme.vars.is_empty() {
                (Vec::new(), HashMap::new())
            } else {
                let mut extracted: HashMap<TypeVar, Type> = HashMap::new();
                extract_substitution_with(
                    &stored.scheme.ty,
                    concrete,
                    &mut extracted,
                    Some(&self.infer.transparent),
                );
                let var_set: std::collections::HashSet<TypeVar> =
                    stored.scheme.vars.iter().copied().collect();
                let args: Vec<Type> = stored
                    .scheme
                    .vars
                    .iter()
                    .map(|tv| {
                        extracted
                            .get(tv)
                            .cloned()
                            .map_or_else(default_type, |t| normalize_type(&t))
                    })
                    .collect();
                // Foreign vars: scheme.ty references vars NOT in
                // scheme.vars (e.g. a transparent newtype's type
                // params leaking through from an outer scheme).
                // Carry them in extra_mapping so process_request
                // substitutes them in the body. Lambda-set rows
                // didn't subsume this case — it's specifically about
                // type-args from enclosing scopes that appear in
                // scheme.ty's structure.
                let extra: HashMap<TypeVar, Type> = extracted
                    .into_iter()
                    .filter(|(tv, _)| !var_set.contains(tv))
                    .map(|(tv, t)| (tv, normalize_type(&t)))
                    .collect();
                (args, extra)
            };

        // Two cases where we reuse the original sym with no rewrite:
        //   - Free function, monomorphic identity spec: the original
        //     sym's display is already the canonical name.
        // Everything else needs a fresh top-level sym with the
        // fully mangled display name.
        let reuse_original =
            args.is_empty() && !stored.is_method;

        let key = (name.to_owned(), args.clone());
        if let Some(&sym) = self.spec_map.get(&key) {
            return if reuse_original { None } else { Some(sym) };
        }

        let spec_sym = if reuse_original {
            let orig_sym = self.original_syms[name];
            self.enqueue(name, Vec::new(), extra_mapping, orig_sym);
            return None;
        } else {
            // Mangle from the type-arg list with lambda-set vars
            // stripped — they contribute to per-call-site behavior
            // (Phase D) but shouldn't appear in the mangled name.
            let mangle_args: Vec<Type> = stored
                .scheme
                .vars
                .iter()
                .zip(args.iter())
                .filter(|(tv, _)| !ls_vars.contains(tv))
                .map(|(_, t)| t.clone())
                .collect();
            let display = if mangle_args.is_empty() {
                // Mono method identity spec: display is the full
                // mangled name like `"Bool.not"`.
                name.to_owned()
            } else {
                mangle(name, &mangle_args)
            };
            let kind = if stored.is_method {
                SymbolKind::Method
            } else {
                SymbolKind::Func
            };
            self.symbols.fresh(display, stored.span, kind)
        };

        self.enqueue(name, args, extra_mapping, spec_sym);
        Some(spec_sym)
    }

    /// Record a `(name, args)` → `spec_sym` binding in `spec_map`
    /// and push a worklist entry to later process the body.
    fn enqueue(
        &mut self,
        name: &str,
        args: Vec<Type>,
        extra_mapping: HashMap<TypeVar, Type>,
        spec_sym: SymbolId,
    ) {
        let key = (name.to_owned(), args.clone());
        self.spec_map.insert(key, spec_sym);
        self.worklist.push_back(SpecRequest {
            name: name.to_owned(),
            substitution: args,
            extra_mapping,
            spec_sym,
        });
    }
}

/// Helper: build an `Arrow` call signature from the call's arg types
/// and return type, as needed by the substitution extractor.
fn call_signature(args: &[Expr<'_>], ret_ty: &Type) -> Type {
    let arg_types: Vec<Type> = args.iter().map(|a| a.ty.clone()).collect();
    Type::Arrow(arg_types, Box::new(ret_ty.clone()), None)
}

/// Rewrite the parsed infer result to reflect specialized schemes.
/// Polymorphic originals are removed; specializations are added with
/// empty `vars`.
fn build_new_infer_result(
    old: &InferResult,
    specialized_schemes: &HashMap<String, Scheme>,
) -> InferResult {
    let mut func_schemes: HashMap<String, Scheme> = HashMap::new();
    for (name, scheme) in &old.func_schemes {
        if scheme.vars.is_empty() {
            func_schemes.insert(name.clone(), scheme.clone());
        }
    }
    for (name, scheme) in specialized_schemes {
        func_schemes.insert(name.clone(), scheme.clone());
    }
    InferResult {
        func_schemes,
        constructor_schemes: old.constructor_schemes.clone(),
        transparent: old.transparent.clone(),
        binop_method: old.binop_method.clone(),
    }
}

// ---- Specialization key: type substitution extraction ----

/// Walk `scheme_ty` alongside `concrete_ty` and record every
/// `TypeVar → Type` mapping needed to make them match. Pass
/// `transparent: Some(&table)` to recover bindings across the
/// transparent-newtype boundary (e.g. `App("Set", [V])` vs the
/// underlying record).
fn extract_substitution_with(
    scheme_ty: &Type,
    concrete_ty: &Type,
    out: &mut HashMap<TypeVar, Type>,
    transparent: Option<&crate::passes::core::lower::TransparentTable>,
) {
    // If the two types have mismatching outer shapes but one (or
    // both) is a transparent newtype, unwrap and retry. This lets
    // mono extract substitutions across the transparent boundary —
    // e.g. scheme.ty is `App("Set", [V])` while concrete is the
    // underlying record (or vice versa), depending on whether the
    // inferred type was captured pre- or post-unwrap. Without this
    // the extract misses the bind and the var defaults to I64.
    if let Some(tt) = transparent {
        let scheme_is_transparent = matches!(scheme_ty, Type::App(n, _) | Type::Con(n) if tt.contains_key(n));
        let concrete_is_transparent = matches!(concrete_ty, Type::App(n, _) | Type::Con(n) if tt.contains_key(n));
        if scheme_is_transparent != concrete_is_transparent {
            let s_unwrapped = crate::passes::core::lower::resolve_transparent(scheme_ty, tt);
            let c_unwrapped = crate::passes::core::lower::resolve_transparent(concrete_ty, tt);
            extract_substitution_with(&s_unwrapped, &c_unwrapped, out, transparent);
            return;
        }
    }
    match (scheme_ty, concrete_ty) {
        (Type::Var(v), _) => {
            out.insert(*v, concrete_ty.clone());
        }
        (_, Type::Var(_)) => {}
        (Type::Con(a), Type::Con(b)) if a == b => {}
        (Type::App(n1, a1), Type::App(n2, a2)) if n1 == n2 && a1.len() == a2.len() => {
            for (x, y) in a1.iter().zip(a2.iter()) {
                extract_substitution_with(x, y, out, transparent);
            }
        }
        (Type::Arrow(p1, r1, ls1), Type::Arrow(p2, r2, ls2)) if p1.len() == p2.len() => {
            for (x, y) in p1.iter().zip(p2.iter()) {
                extract_substitution_with(x, y, out, transparent);
            }
            extract_substitution_with(r1, r2, out, transparent);
            // Phase D: extract lambda-set var bindings. If scheme has
            // `Some(Var(rv))` (open row) and concrete has any row
            // content, bind rv → that content. process_request then
            // substitutes the row into the body, preserving the
            // call-site's closure-shape info.
            if let (Some(s_ls), Some(c_ls)) = (ls1.as_deref(), ls2.as_deref()) {
                extract_substitution_with(s_ls, c_ls, out, transparent);
            }
        }
        (Type::Tuple(a), Type::Tuple(b)) if a.len() == b.len() => {
            for (x, y) in a.iter().zip(b.iter()) {
                extract_substitution_with(x, y, out, transparent);
            }
        }
        (
            Type::Record {
                fields: f1,
                rest: r1,
            },
            Type::Record {
                fields: f2,
                rest: r2,
            },
        ) => {
            for (name, t1) in f1 {
                if let Some((_, t2)) = f2.iter().find(|(n, _)| n == name) {
                    extract_substitution_with(t1, t2, out, transparent);
                }
            }
            // Row polymorphism: if scheme has an open row and
            // concrete has extra fields, bind the row variable to
            // a closed record of the extras.
            if let (Some(row_var_ty), _) = (r1.as_deref(), r2) {
                if let Type::Var(row_var) = row_var_ty {
                    let extra_fields: Vec<(String, Type)> = f2
                        .iter()
                        .filter(|(n, _)| !f1.iter().any(|(n2, _)| n2 == n))
                        .cloned()
                        .collect();
                    out.insert(
                        *row_var,
                        Type::Record {
                            fields: extra_fields,
                            rest: None,
                        },
                    );
                }
            }
        }
        (
            Type::TagUnion {
                tags: t1,
                rest: r1,
            },
            Type::TagUnion {
                tags: t2,
                rest: _r2,
            },
        ) => {
            // Unify common tags' payloads recursively.
            for (name, p1) in t1 {
                if let Some((_, p2)) = t2.iter().find(|(n, _)| n == name) {
                    for (x, y) in p1.iter().zip(p2.iter()) {
                        extract_substitution_with(x, y, out, transparent);
                    }
                }
            }
            // Row polymorphism: if the scheme has an open row and
            // the concrete type has extra tags, bind the row
            // variable to a closed union of the extras so that
            // later substitutions close the expression types in
            // the specialized body. Mirrors the record row logic
            // above.
            if let Some(row_var_ty) = r1.as_deref() {
                if let Type::Var(row_var) = row_var_ty {
                    let extra_tags: Vec<(String, Vec<Type>)> = t2
                        .iter()
                        .filter(|(n, _)| !t1.iter().any(|(n2, _)| n2 == n))
                        .cloned()
                        .collect();
                    out.insert(
                        *row_var,
                        Type::TagUnion {
                            tags: extra_tags,
                            rest: None,
                        },
                    );
                }
            }
        }
        _ => {}
    }
}

// ---- Type normalization for stable specialization keys ----

fn default_type() -> Type {
    Type::Con("I64".to_owned())
}

/// Canonicalize a type for use as a specialization key. Replaces
/// residual `Var(_)` with the sentinel, sorts record fields by name,
/// and drops residual open rows.
fn normalize_type(ty: &Type) -> Type {
    match ty {
        Type::Var(_) => default_type(),
        Type::Con(name) => Type::Con(name.clone()),
        Type::App(name, args) => Type::App(
            name.clone(),
            args.iter().map(normalize_type).collect(),
        ),
        Type::Arrow(params, ret, ls) => Type::Arrow(
            params.iter().map(normalize_type).collect(),
            Box::new(normalize_type(ret)),
            ls.as_ref().map(|r| Box::new(normalize_type(r))),
        ),
        Type::Record { fields, .. } => {
            let mut norm_fields: Vec<(String, Type)> = fields
                .iter()
                .map(|(n, t)| (n.clone(), normalize_type(t)))
                .collect();
            norm_fields.sort_by(|a, b| a.0.cmp(&b.0));
            Type::Record {
                fields: norm_fields,
                rest: None,
            }
        }
        Type::TagUnion { tags, .. } => {
            // Canonicalize: sort tags by name, recursively normalize
            // payloads, drop any residual open row. Post-mono types
            // are always closed.
            let mut norm_tags: Vec<(String, Vec<Type>)> = tags
                .iter()
                .map(|(n, payloads)| {
                    (n.clone(), payloads.iter().map(normalize_type).collect())
                })
                .collect();
            norm_tags.sort_by(|a, b| a.0.cmp(&b.0));
            Type::TagUnion {
                tags: norm_tags,
                rest: None,
            }
        }
        Type::Tuple(elems) => Type::Tuple(elems.iter().map(normalize_type).collect()),
    }
}

/// Walk `ty` and collect every TypeVar that appears in a lambda-set
/// position (the third field of `Type::Arrow`). Used by mono to
/// distinguish ordinary type-arg vars (which contribute to mangled
/// names) from row vars (which don't, but still need substitution
/// through the body).
fn collect_lambda_set_vars(ty: &Type, out: &mut std::collections::HashSet<TypeVar>) {
    match ty {
        Type::Var(_) | Type::Con(_) => {}
        Type::App(_, args) => {
            for a in args {
                collect_lambda_set_vars(a, out);
            }
        }
        Type::Arrow(params, ret, ls) => {
            for p in params {
                collect_lambda_set_vars(p, out);
            }
            collect_lambda_set_vars(ret, out);
            if let Some(ls_ty) = ls {
                // Every var reachable through the lambda-set is a
                // row-position var. (TagUnion fields can have type
                // params of their own, but in lambda-set rows the
                // payload types are capture types — which we DO want
                // in mangling. So we only mark the row-var-shaped
                // ones: a bare `Var(_)` directly under LambdaSet, or
                // a TagUnion's `rest` row variable.)
                collect_ls_row_vars(ls_ty, out);
            }
        }
        Type::Record { fields, rest } => {
            for (_, t) in fields {
                collect_lambda_set_vars(t, out);
            }
            if let Some(r) = rest {
                collect_lambda_set_vars(r, out);
            }
        }
        Type::TagUnion { tags, rest } => {
            for (_, payloads) in tags {
                for p in payloads {
                    collect_lambda_set_vars(p, out);
                }
            }
            if let Some(r) = rest {
                collect_lambda_set_vars(r, out);
            }
        }
        Type::Tuple(elems) => {
            for e in elems {
                collect_lambda_set_vars(e, out);
            }
        }
    }
}

/// Visit only the lambda-set row variable positions: the bare
/// `Type::Var(_)` directly under a LambdaSet (an open row), and the
/// `rest` row var of a TagUnion lambda set. Payload types inside
/// lambda-set tags are *not* row vars — they're capture types and
/// continue to contribute to mangling.
fn collect_ls_row_vars(ls_ty: &Type, out: &mut std::collections::HashSet<TypeVar>) {
    match ls_ty {
        Type::Var(tv) => {
            out.insert(*tv);
        }
        Type::TagUnion { tags, rest } => {
            // Recurse into payloads via collect_lambda_set_vars (they
            // are normal type positions — only their lambda-set
            // sub-positions count as row vars).
            for (_, payloads) in tags {
                for p in payloads {
                    collect_lambda_set_vars(p, out);
                }
            }
            if let Some(r) = rest {
                if let Type::Var(tv) = r.as_ref() {
                    out.insert(*tv);
                } else {
                    collect_ls_row_vars(r, out);
                }
            }
        }
        _ => {}
    }
}

// ---- Mangled specialization names ----

/// Produce a stable mangled name for a specialization. Format:
/// `originalName__Arg1_Arg2`. Callers pass the full mangled origin
/// name (`"List.map"`, not `"map"`), so the result is always a
/// ready-to-use top-level display name.
fn mangle(orig: &str, args: &[Type]) -> String {
    let mut out = orig.to_owned();
    out.push_str("__");
    for (i, arg) in args.iter().enumerate() {
        if i > 0 {
            out.push('_');
        }
        append_type_mangling(&mut out, arg);
    }
    out
}

pub(crate) fn append_type_mangling(out: &mut String, ty: &Type) {
    match ty {
        Type::Var(_) => out.push('?'),
        Type::Con(name) => out.push_str(name),
        Type::App(name, args) => {
            out.push_str(name);
            out.push('(');
            for (i, a) in args.iter().enumerate() {
                if i > 0 {
                    out.push(',');
                }
                append_type_mangling(out, a);
            }
            out.push(')');
        }
        Type::Arrow(params, ret, _) => {
            out.push('(');
            for (i, p) in params.iter().enumerate() {
                if i > 0 {
                    out.push(',');
                }
                append_type_mangling(out, p);
            }
            out.push_str(")->");
            append_type_mangling(out, ret);
        }
        Type::Record { fields, .. } => {
            out.push('{');
            for (i, (n, t)) in fields.iter().enumerate() {
                if i > 0 {
                    out.push(',');
                }
                out.push_str(n);
                out.push(':');
                append_type_mangling(out, t);
            }
            out.push('}');
        }
        Type::TagUnion { tags, .. } => {
            out.push('[');
            for (i, (n, payloads)) in tags.iter().enumerate() {
                if i > 0 {
                    out.push(',');
                }
                out.push_str(n);
                if !payloads.is_empty() {
                    out.push('(');
                    for (j, p) in payloads.iter().enumerate() {
                        if j > 0 {
                            out.push(',');
                        }
                        append_type_mangling(out, p);
                    }
                    out.push(')');
                }
            }
            out.push(']');
        }
        Type::Tuple(elems) => {
            out.push('(');
            for (i, e) in elems.iter().enumerate() {
                if i > 0 {
                    out.push(',');
                }
                append_type_mangling(out, e);
            }
            out.push(')');
        }
    }
}

// ---- Type substitution inside expressions ----

fn substitute_types_in_expr(expr: &mut Expr<'_>, mapping: &HashMap<TypeVar, Type>) {
    expr.ty = apply_mapping(&expr.ty, mapping);
    match &mut expr.kind {
        ExprKind::BinOp { lhs, rhs, .. } => {
            substitute_types_in_expr(lhs, mapping);
            substitute_types_in_expr(rhs, mapping);
        }
        ExprKind::Call { args, .. } => {
            for a in args.iter_mut() {
                substitute_types_in_expr(a, mapping);
            }
        }
        ExprKind::QualifiedCall { args, .. } => {
            for a in args.iter_mut() {
                substitute_types_in_expr(a, mapping);
            }
        }
        ExprKind::MethodCall { receiver, args, .. } => {
            substitute_types_in_expr(receiver, mapping);
            for a in args.iter_mut() {
                substitute_types_in_expr(a, mapping);
            }
        }
        ExprKind::Block(stmts, result) => {
            for s in stmts.iter_mut() {
                substitute_types_in_stmt(s, mapping);
            }
            substitute_types_in_expr(result, mapping);
        }
        ExprKind::If {
            expr: scrutinee,
            arms,
            else_body,
        } => {
            substitute_types_in_expr(scrutinee, mapping);
            for arm in arms.iter_mut() {
                for g in arm.guards.iter_mut() {
                    substitute_types_in_expr(g, mapping);
                }
                substitute_types_in_expr(&mut arm.body, mapping);
            }
            if let Some(eb) = else_body {
                substitute_types_in_expr(eb, mapping);
            }
        }
        ExprKind::Fold {
            expr: scrutinee,
            arms,
        } => {
            substitute_types_in_expr(scrutinee, mapping);
            for arm in arms.iter_mut() {
                for g in arm.guards.iter_mut() {
                    substitute_types_in_expr(g, mapping);
                }
                substitute_types_in_expr(&mut arm.body, mapping);
            }
        }
        ExprKind::Lambda { .. } => {
            unreachable!("lift_pre_infer removes all Lambda nodes before mono runs")
        }
        ExprKind::Record { fields } => {
            for (_, e) in fields.iter_mut() {
                substitute_types_in_expr(e, mapping);
            }
        }
        ExprKind::FieldAccess { record, .. } => substitute_types_in_expr(record, mapping),
        ExprKind::Tuple(elems) | ExprKind::ListLit(elems) => {
            for e in elems.iter_mut() {
                substitute_types_in_expr(e, mapping);
            }
        }
        ExprKind::Is { expr: inner, .. } => substitute_types_in_expr(inner, mapping),
        ExprKind::RecordUpdate { base, updates } => {
            substitute_types_in_expr(base, mapping);
            for (_, e) in updates.iter_mut() {
                substitute_types_in_expr(e, mapping);
            }
        }
        ExprKind::IntLit(_)
        | ExprKind::FloatLit(_)
        | ExprKind::StrLit(_)
        | ExprKind::Name(_) => {}
        ExprKind::Closure { captures, .. } => {
            for c in captures.iter_mut() {
                substitute_types_in_expr(c, mapping);
            }
        }
    }
}

fn substitute_types_in_stmt(stmt: &mut Stmt<'_>, mapping: &HashMap<TypeVar, Type>) {
    match stmt {
        Stmt::Let { val, .. } | Stmt::Destructure { val, .. } => {
            substitute_types_in_expr(val, mapping);
        }
        Stmt::Guard {
            condition,
            return_val,
        } => {
            substitute_types_in_expr(condition, mapping);
            substitute_types_in_expr(return_val, mapping);
        }
        Stmt::TypeHint { .. } => {}
    }
}

/// Apply a `TypeVar → Type` mapping at a row-variable position.
/// Unlike the generic `apply_mapping`, an unresolved row variable
/// defaults to an empty closed row rather than `Con("I64")`, because
/// a row position is structurally a "possibly more tags" slot and the
/// natural default for "no further tags" is an empty closed union.
/// The caller is expected to run `flatten_rows` afterwards to absorb
/// the empty row.
fn apply_mapping_row(ty: &Type, mapping: &HashMap<TypeVar, Type>) -> Type {
    match ty {
        Type::Var(v) => mapping.get(v).cloned().unwrap_or_else(|| {
            Type::TagUnion {
                tags: Vec::new(),
                rest: None,
            }
        }),
        _ => apply_mapping(ty, mapping),
    }
}

/// Apply a `TypeVar → Type` mapping to a type. Also normalizes
/// residual vars to the default sentinel so post-mono types are
/// fully concrete.
fn apply_mapping(ty: &Type, mapping: &HashMap<TypeVar, Type>) -> Type {
    match ty {
        Type::Var(v) => mapping
            .get(v)
            .cloned()
            .map_or_else(default_type, |t| normalize_type(&t)),
        Type::Con(name) => Type::Con(name.clone()),
        Type::App(name, args) => Type::App(
            name.clone(),
            args.iter().map(|a| apply_mapping(a, mapping)).collect(),
        ),
        Type::Arrow(params, ret, ls) => Type::Arrow(
            params.iter().map(|p| apply_mapping(p, mapping)).collect(),
            Box::new(apply_mapping(ret, mapping)),
            ls.as_ref().map(|r| Box::new(apply_mapping(r, mapping))),
        ),
        Type::Record { fields, rest } => {
            // First substitute through the named fields.
            let mut new_fields: Vec<(String, Type)> = fields
                .iter()
                .map(|(n, t)| (n.clone(), apply_mapping(t, mapping)))
                .collect();
            // If there's an open row variable, look it up in the
            // mapping and merge its fields in. Mono receives row vars
            // bound to a closed Record carrying the "extras" extracted
            // from the call-site concrete type — dropping the rest
            // would lose those fields and produce a wrongly-shaped
            // record. (Surfaces for lifted closures whose body sees
            // an open-row capture from a transparent newtype like
            // Set, where scheme.ty has `{entries: V322, rest: V323}`
            // with V323 → `{len: U64}`. Without the merge, grown
            // decomposes to a single slot for `entries` instead of
            // four for `{entries, len}`.)
            if let Some(rest_var_ty) = rest {
                if let Type::Var(rv) = rest_var_ty.as_ref() {
                    if let Some(rest_resolved) = mapping.get(rv) {
                        let rest_norm = normalize_type(rest_resolved);
                        if let Type::Record { fields: extra, .. } = rest_norm {
                            for (n, t) in extra {
                                if !new_fields.iter().any(|(en, _)| en == &n) {
                                    new_fields.push((n, t));
                                }
                            }
                        }
                    }
                }
            }
            // Canonical record field order is alphabetical. Sort
            // here so substituted records stay canonical without
            // each caller having to remember to normalize_type.
            new_fields.sort_by(|a, b| a.0.cmp(&b.0));
            Type::Record { fields: new_fields, rest: None }
        }
        Type::TagUnion { tags, rest } => {
            // Substitute through both the tag payloads and the
            // row-variable rest. Row vars are handled specially:
            // if the rest is an unresolved type variable, default
            // to an empty closed row (no extra tags) rather than
            // the generic `default_type()` (which is `I64` and
            // makes no sense at a row position). `flatten_rows`
            // then folds the empty row into the outer tags. This
            // path handles open rows that never got closed during
            // inference — e.g., let-generalized tag values whose
            // row var stayed unresolved inside the original
            // function body even though the call site closed it.
            let substituted = Type::TagUnion {
                tags: tags
                    .iter()
                    .map(|(n, payloads)| {
                        (
                            n.clone(),
                            payloads.iter().map(|p| apply_mapping(p, mapping)).collect(),
                        )
                    })
                    .collect(),
                rest: rest.as_ref().map(|r| Box::new(apply_mapping_row(r, mapping))),
            };
            crate::types::engine::flatten_rows(substituted)
        }
        Type::Tuple(elems) => Type::Tuple(elems.iter().map(|e| apply_mapping(e, mapping)).collect()),
    }
}

/// Leak a `String` into a `&'static str`. Used by mono when
/// rebuilding `QualifiedCall.segments` with a specialized mangled
/// name — the leak is O(specializations), trivial compared to the
/// source arena leak in `SourceArena::add`.
fn leak_str(s: &str) -> &'static str {
    Box::leak(s.to_owned().into_boxed_str())
}
