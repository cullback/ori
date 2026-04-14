use std::collections::HashMap;

use crate::ast::{self, BinOp, Decl, Expr, ExprKind, Span, Stmt, TypeDeclKind, TypeExpr};
use crate::error::CompileError;
use crate::symbol::{FieldInterner, SymbolId, SymbolKind, SymbolTable};
use crate::types::engine::{Constraint, Scheme, Type, TypeEngine, TypeVar};

/// Build a mangled key for a method on a type, e.g. `method_key("List", "sum")` -> `"List.sum"`.
fn method_key(type_name: &str, method: &str) -> String {
    format!("{type_name}.{method}")
}


/// Value restriction: only generalize let bindings whose value is a
/// syntactic function (lambda). Non-function bindings like records or
/// tag values can carry open row variables — generalizing those would
/// give each use site a fresh row, breaking structural field/tag
/// propagation. This is a row-polymorphism concern, not a mutation
/// concern (System T's lack of mutation doesn't help here).
const fn is_syntactic_value(expr: &Expr<'_>) -> bool {
    matches!(expr.kind, ExprKind::Lambda { .. })
}

/// Results of type inference, communicated to the lowerer.
///
/// Post-Step-2c, `InferResult` only carries data that isn't naturally
/// attached to `Expr` nodes: top-level schemes for functions/constructors.
/// Per-expression types, numeric literal defaulting, method resolutions,
/// and `is` bindings all live on the AST nodes themselves.
pub struct InferResult {
    /// Resolved type schemes for all functions/methods.
    /// Used by the lowerer to compute type parameter mappings for specialization.
    pub func_schemes: HashMap<String, Scheme>,
    /// Constructor type schemes (e.g., Ok: forall ok err. ok -> Result(ok, err)).
    /// Used by the lowerer to compute concrete field types from instantiations.
    pub constructor_schemes: HashMap<String, Scheme>,
}

// ---- Inference context ----

use super::post_infer::EtaInfo;

struct InferCtx<'a, 'src> {
    // -- Core inference state --
    engine: TypeEngine,
    /// Names → schemes. Locals keyed by display name, globals by
    /// mangled name (e.g. `"List.map"`). Scoped via `self.scoped()`.
    env: HashMap<String, Scheme>,
    constructors: HashMap<String, Scheme>,
    type_aliases: HashMap<String, Scheme>,
    /// Declared type annotations for checking against inferred types.
    type_annos: HashMap<String, TypeExpr<'src>>,
    known_types: std::collections::HashSet<String>,
    /// Span for each constraint (parallel to engine.constraints).
    constraint_spans: Vec<Span>,
    /// Return type of each enclosing function/lambda, innermost on
    /// top. `return` statements unify against the top. Depth is
    /// bounded by lambda nesting (System T forbids recursion, so
    /// `infer_func_body` never re-enters for the same function).
    ret_ty_stack: Vec<Type>,

    // -- Literal defaulting --
    int_literal_vars: Vec<(TypeVar, Span)>,
    float_literal_vars: Vec<(TypeVar, Span)>,

    // -- Output side tables (consumed by post_infer::rewrite) --
    /// Per-expression types, resolved to concrete types at end of inference.
    expr_types: HashMap<Span, Type>,
    /// Bindings from `is` expressions, indexed by the Is expression's span.
    is_bindings: HashMap<Span, Vec<(String, Type)>>,
    /// Resolved method calls: span → mangled method name.
    method_resolutions: HashMap<Span, String>,
    /// Constructor references to eta-expand in post-inference rewrite.
    eta_expansions: HashMap<Span, EtaInfo>,

    // -- Borrowed context --
    symbols: &'a SymbolTable,
    fields: &'a FieldInterner,
}

impl<'a, 'src> InferCtx<'a, 'src> {
    fn lookup(&self, name: &str) -> Option<&Scheme> {
        self.env.get(name).or_else(|| self.constructors.get(name))
    }

    fn scoped<R>(&mut self, f: impl FnOnce(&mut Self) -> R) -> R {
        let saved = self.env.clone();
        let result = f(self);
        self.env = saved;
        result
    }

    fn new(symbols: &'a SymbolTable, fields: &'a FieldInterner) -> Self {
        Self {
            engine: TypeEngine::new(),
            env: HashMap::new(),
            constructors: HashMap::new(),
            type_aliases: HashMap::new(),
            type_annos: HashMap::new(),
            known_types: std::collections::HashSet::new(),
            constraint_spans: Vec::new(),
            ret_ty_stack: Vec::new(),
            int_literal_vars: Vec::new(),
            float_literal_vars: Vec::new(),
            expr_types: HashMap::new(),
            is_bindings: HashMap::new(),
            method_resolutions: HashMap::new(),
            eta_expansions: HashMap::new(),
            symbols,
            fields,
        }
    }

    fn push_constraint(&mut self, constraint: Constraint, span: Span) {
        self.engine.constraints.push(constraint);
        self.constraint_spans.push(span);
    }

    fn type_error(span: Span, msg: &str) -> CompileError {
        CompileError::at(span, format!("type error: {msg}"))
    }

    fn unify_at(&mut self, t1: &Type, t2: &Type, span: Span) -> Result<(), CompileError> {
        self.engine
            .unify(t1, t2)
            .map_err(|msg| Self::type_error(span, &msg))
    }

    /// Unify `found` against `expected`, and on failure produce a
    /// context-attributed error of the form
    ///
    /// ```text
    /// in {what}, expected `{expected}`, got `{found}`
    /// ```
    ///
    /// where both types are resolved and pretty-printed. The `what`
    /// is a short noun phrase identifying the site — "match arm
    /// body", "argument 2 of `foo`", "`if` guard return value",
    /// and so on. Both "expected" and "got" are user-facing
    /// framings: the former is whatever the context demanded (a
    /// declared annotation, a previously-inferred sibling type, or
    /// the enclosing function's return type), and the latter is
    /// what the local expression produced.
    fn unify_expected(
        &mut self,
        found: &Type,
        expected: &Type,
        span: Span,
        what: &str,
    ) -> Result<(), CompileError> {
        if self.unify_at(found, expected, span).is_err() {
            let resolved_expected = self.engine.resolve(expected);
            let resolved_found = self.engine.resolve(found);
            return Err(Self::type_error(
                span,
                &format!(
                    "in {what}, expected `{}`, got `{}`",
                    self.engine.display_type(&resolved_expected),
                    self.engine.display_type(&resolved_found)
                ),
            ));
        }
        Ok(())
    }

    // ---- Convert surface TypeExpr to inference Type ----

    /// Convert a type expression without pre-existing type variable bindings.
    fn resolve_type_expr(&mut self, texpr: &TypeExpr<'src>) -> Result<Type, CompileError> {
        self.type_expr_to_type(texpr, &mut HashMap::new())
    }

    /// Resolve a type expression AND return the `TypeVar`s for the given
    /// type parameters. Used for transparent/opaque type registration
    /// where we need to know which vars correspond to the declaration's params.
    fn resolve_type_expr_with_params(
        &mut self,
        texpr: &TypeExpr<'src>,
        type_params: &[&str],
    ) -> Result<(Vec<TypeVar>, Type), CompileError> {
        let mut tvar_env = HashMap::new();
        let ty = self.type_expr_to_type(texpr, &mut tvar_env)?;
        let param_vars: Vec<TypeVar> = type_params
            .iter()
            .map(|p| tvar_env.get(*p).copied().unwrap_or_else(|| {
                let t = self.engine.fresh();
                let Type::Var(tv) = t else { unreachable!() };
                tv
            }))
            .collect();
        Ok((param_vars, ty))
    }

    /// Convert a type expression, accumulating implicit type variable bindings
    /// into `tvar_env` (so `a` in `a -> a` resolves to the same variable).
    fn type_expr_to_type(
        &mut self,
        texpr: &TypeExpr<'src>,
        tvar_env: &mut HashMap<String, TypeVar>,
    ) -> Result<Type, CompileError> {
        match texpr {
            TypeExpr::Named(name) => {
                let name = *name;
                if let Some(&tv) = tvar_env.get(name) {
                    Ok(Type::Var(tv))
                } else if let Some(scheme) = self.type_aliases.get(name).cloned() {
                    Ok(self.engine.instantiate(&scheme))
                } else if name.starts_with(|c: char| c.is_ascii_lowercase()) {
                    // Lowercase names are implicit type variables
                    let tv = self.engine.fresh();
                    let Type::Var(tv_id) = tv else { unreachable!() };
                    tvar_env.insert(name.to_owned(), tv_id);
                    Ok(tv)
                } else if self.known_types.contains(name) {
                    Ok(Type::Con(name.to_owned()))
                } else {
                    Err(CompileError::new(format!(
                        "type error: unknown type '{name}'"
                    )))
                }
            }
            TypeExpr::App(name, args) => {
                let name = *name;
                if !self.known_types.contains(name) {
                    return Err(CompileError::new(format!(
                        "type error: unknown type '{name}'"
                    )));
                }
                let mut arg_types = Vec::new();
                for a in args {
                    arg_types.push(self.type_expr_to_type(a, tvar_env)?);
                }
                Ok(Type::App(name.to_owned(), arg_types))
            }
            TypeExpr::Arrow(params, ret) => {
                let mut param_types = Vec::new();
                for p in params {
                    param_types.push(self.type_expr_to_type(p, tvar_env)?);
                }
                Ok(Type::Arrow(
                    param_types,
                    Box::new(self.type_expr_to_type(ret, tvar_env)?),
                ))
            }
            TypeExpr::TagUnion(tags, open) => {
                // Inline tag union in a type annotation becomes a
                // `Type::TagUnion`. Closed (`[Red, Green]`) annotations
                // set `rest: None`; open (`[Red, ..]`) annotations set
                // `rest: Some(fresh)` so the row can grow through
                // unification. Nominal tag-union declarations still
                // go through `register_type_decl` and produce a
                // `Type::Con` — this path only fires for inline
                // annotations on function signatures or let bindings.
                let mut tag_entries: Vec<(String, Vec<Type>)> = Vec::new();
                for tag in tags {
                    let mut payload_types = Vec::new();
                    for payload in &tag.fields {
                        payload_types.push(self.type_expr_to_type(payload, tvar_env)?);
                    }
                    tag_entries.push((tag.name.to_owned(), payload_types));
                }
                let rest = open.then(|| Box::new(self.engine.fresh()));
                Ok(Type::TagUnion {
                    tags: tag_entries,
                    rest,
                })
            }
            TypeExpr::Record(fields) => {
                let mut type_fields = Vec::new();
                for (field_sym, field_texpr) in fields {
                    let field_ty = self.type_expr_to_type(field_texpr, tvar_env)?;
                    type_fields.push((self.fields.get(*field_sym).to_owned(), field_ty));
                }
                Ok(Type::Record {
                    fields: type_fields,
                    rest: None,
                })
            }
            TypeExpr::Tuple(elems) => {
                let mut elem_types = Vec::new();
                for e in elems {
                    elem_types.push(self.type_expr_to_type(e, tvar_env)?);
                }
                Ok(Type::Tuple(elem_types))
            }
        }
    }

    // ---- Register type declarations ----

    fn register_type_decl(
        &mut self,
        name: &str,
        type_params: &[&str],
        tags: &[ast::TagDecl<'src>],
    ) -> Result<(), CompileError> {
        self.known_types.insert(name.to_owned());
        // Create type variables for each type parameter
        let mut tvar_env: HashMap<String, TypeVar> = type_params
            .iter()
            .map(|p| {
                let tv = self.engine.fresh();
                let Type::Var(tv_id) = tv else { unreachable!() };
                ((*p).to_owned(), tv_id)
            })
            .collect();

        let tvars: Vec<TypeVar> = type_params.iter().map(|p| tvar_env[*p]).collect();

        // The return type for constructors of this type
        let return_type = if tvars.is_empty() {
            Type::Con(name.to_owned())
        } else {
            Type::App(
                name.to_owned(),
                tvars.iter().map(|&tv| Type::Var(tv)).collect(),
            )
        };

        for tag in tags {
            let con_type = if tag.fields.is_empty() {
                return_type.clone()
            } else {
                let mut field_types = Vec::new();
                for f in &tag.fields {
                    field_types.push(self.type_expr_to_type(f, &mut tvar_env)?);
                }
                Type::Arrow(field_types, Box::new(return_type.clone()))
            };
            self.constructors.insert(
                tag.name.to_owned(),
                Scheme {
                    vars: tvars.clone(),
                    constraints: vec![],
                    ty: con_type,
                },
            );
        }
        Ok(())
    }

    // ---- Method registration (shared between tag-union and non-tag-union TypeAnno) ----

    /// Register method signatures and annotations for a type's methods.
    /// For each `FuncDef` method: registers a fresh arrow scheme (unless
    /// a preceding `TypeAnno` already resolved an annotation). For each
    /// `TypeAnno` method: eagerly resolves the annotation to a scheme so
    /// callers see the intended type, and registers it in `type_annos`.
    fn register_methods(
        &mut self,
        type_name: &str,
        methods: &[Decl<'src>],
        scope: &crate::passes::resolve::ModuleScope,
    ) -> Result<(), CompileError> {
        for method in methods {
            match method {
                Decl::FuncDef {
                    name: method_name,
                    params,
                    ..
                } => {
                    let method_name = self.symbols.display(*method_name);
                    let mangled = method_key(type_name, method_name);
                    if !self.env.contains_key(&mangled) {
                        let param_types: Vec<Type> =
                            params.iter().map(|_| self.engine.fresh()).collect();
                        let ret = self.engine.fresh();
                        let func_ty = Type::Arrow(param_types, Box::new(ret));
                        self.env.insert(mangled.clone(), Scheme::mono(func_ty));
                    }
                    if let Some(mod_name) = scope.qualified_types.get(type_name) {
                        let qual = format!("{mod_name}.{mangled}");
                        if let Some(scheme) = self.env.get(&mangled).cloned() {
                            self.env.insert(qual, scheme);
                        }
                    }
                }
                Decl::TypeAnno {
                    name: method_name,
                    ty,
                    ..
                } => {
                    let method_name = self.symbols.display(*method_name);
                    let mangled = method_key(type_name, method_name);
                    if let Some(mod_name) = scope.qualified_types.get(type_name) {
                        let qual = format!("{mod_name}.{mangled}");
                        self.type_annos.insert(qual, ty.clone());
                    }
                    self.type_annos.insert(mangled.clone(), ty.clone());
                    let mut tvar_env = HashMap::new();
                    let anno_ty = self.type_expr_to_type(ty, &mut tvar_env)?;
                    let tvars: Vec<_> = tvar_env.into_values().collect();
                    let scheme = Scheme {
                        vars: tvars,
                        constraints: vec![],
                        ty: anno_ty,
                    };
                    self.env.insert(mangled, scheme);
                }
            }
        }
        Ok(())
    }

    // ---- Expression inference ----

    fn infer_expr(&mut self, expr: &Expr<'src>) -> Result<Type, CompileError> {
        let ty = self.infer_expr_inner(expr)?;
        self.expr_types.insert(expr.span, ty.clone());
        Ok(ty)
    }

    /// Bidirectional check: infer `expr` given a type `expected` from
    /// the surrounding context. For most expression kinds this is
    /// equivalent to `infer_expr(expr)` followed by unifying the
    /// result with `expected`. The specialized case: a bare `Name`
    /// reference to a constructor, in a context where the expected
    /// type is an arrow, gets upgraded into a function form — the
    /// constructor's arity is taken from the expected arrow, payload
    /// types are unified with the arrow's parameters, and the span
    /// is marked for post-inference rewrite into an explicit lambda.
    ///
    /// This is what makes `List.map2(xs, ys, Pair)` work: `Pair` is
    /// a structural constructor that normally infers as a nullary
    /// value `[Pair, ..]`, but when passed to a function expecting
    /// `(a, b) -> c`, it's eta-expanded to `|a, b| Pair(a, b)`.
    ///
    /// Applies to both structural constructors and declared
    /// constructors whose scheme would produce an arrow. The
    /// detection uses `SymbolKind::Constructor` from the symbol table
    /// so both share a single code path.
    /// Try the bidirectional call path. Returns `Ok(Some(ret_ty))`
    /// when the callee was found in `self.constructors` or `self.env`
    /// with an arrow-typed instantiated scheme and every argument
    /// was successfully checked against its parameter type. Returns
    /// `Ok(None)` when the caller should fall through to the legacy
    /// synthesize-then-unify path (zero-arg calls, structural
    /// constructor calls, method-on-var dispatch). Returns `Err` on
    /// unification failures or arity mismatches.
    fn try_infer_call_bidir(
        &mut self,
        func: &str,
        args: &[Expr<'src>],
        span: Span,
    ) -> Result<Option<Type>, CompileError> {
        if args.is_empty() {
            return Ok(None);
        }
        let scheme = self.lookup(func).cloned();
        let Some(scheme) = scheme else {
            return Ok(None);
        };
        let func_ty = self.engine.instantiate(&scheme);
        let resolved = self.engine.resolve(&func_ty);
        let Type::Arrow(params, ret_ty) = resolved else {
            // Non-arrow scheme with args: fall through to legacy
            // path so its existing error handling fires.
            return Ok(None);
        };
        if params.len() != args.len() {
            return Err(Self::type_error(
                span,
                &format!(
                    "'{func}' expected {} arguments, got {}",
                    params.len(),
                    args.len()
                ),
            ));
        }
        for (i, (arg, param_ty)) in args.iter().zip(params.iter()).enumerate() {
            self.check_expr(arg, param_ty, Some((func, i + 1)))?;
        }
        Ok(Some(*ret_ty))
    }

    /// Check an expression against an `expected` type, optionally
    /// with attribution context `(func_name, arg_index)` used for
    /// error messages. If unification fails, the context is baked
    /// into the error as `"in argument N of `func`: expected X,
    /// got Y"`, which is friendlier than the bare
    /// `"cannot unify X with Y"` form.
    fn check_expr(
        &mut self,
        expr: &Expr<'src>,
        expected: &Type,
        ctx: Option<(&str, usize)>,
    ) -> Result<Type, CompileError> {
        if let ExprKind::Name(sym) = &expr.kind
            && self.symbols.get(*sym).kind == SymbolKind::Constructor
            && matches!(self.engine.resolve(expected), Type::Arrow(_, _))
        {
            return self.check_con_as_function(*sym, expr.span, expected);
        }

        // Lambda against arrow: push expected param types into env
        // BEFORE inferring the body so method calls on parameters
        // see concrete types, not fresh vars.
        if let ExprKind::Lambda { params, body } = &expr.kind {
            let resolved_expected = self.engine.resolve(expected);
            // Look through transparent types: if the expected type is
            // an App that's transparent to an Arrow (e.g. Parser(a) ::
            // (List(U8) -> Result(...))), resolve it so the lambda
            // gets bidirectional checking.
            let arrow_expected = match &resolved_expected {
                Type::Arrow(..) => Some(resolved_expected.clone()),
                Type::App(name, args) => {
                    if let Some((param_vars, underlying)) =
                        self.engine.transparent.get(name).cloned()
                    {
                        // Create fresh copies of param vars and substitute
                        // them into the underlying type, then unify the
                        // fresh vars with the concrete args. This avoids
                        // polluting the stored param vars across uses.
                        let fresh_map: Vec<(TypeVar, Type)> = param_vars
                            .iter()
                            .zip(args.iter())
                            .map(|(old_var, arg)| (*old_var, arg.clone()))
                            .collect();
                        let substituted = self.engine.substitute_vars(&underlying, &fresh_map);
                        let resolved_sub = self.engine.resolve(&substituted);
                        matches!(resolved_sub, Type::Arrow(..)).then_some(resolved_sub)
                    } else {
                        None
                    }
                }
                _ => None,
            };
            if let Some(Type::Arrow(expected_params, expected_ret)) = &arrow_expected
                && expected_params.len() == params.len()
            {
                let result =
                    self.check_lambda(params, body, expected_params, expected_ret, expr.span)?;
                // Also unify the lambda result with the original expected
                // type so the opaque wrapper is properly linked.
                self.unify_at(&result, expected, expr.span)?;
                return Ok(result);
            }
        }

        // Default path: synthesize the expression's type and unify
        // with the expected type. On failure, the context (if any)
        // gives a "in argument N of `func`" prefix; otherwise the
        // error just says "expected X, got Y" without a site hint.
        let ty = self.infer_expr(expr)?;
        let what = match ctx {
            Some((func, idx)) => format!("argument {idx} of `{func}`"),
            None => "expression".to_owned(),
        };
        self.unify_expected(&ty, expected, expr.span, &what)?;
        Ok(ty)
    }

    /// Upgrade a bare constructor reference to its function form so
    /// it can be passed as a higher-order argument. Handles both
    /// declared constructors (whose stored scheme is already an
    /// arrow for payload variants) and structural constructors
    /// (whose arrow is synthesized on demand from the expected
    /// arrow's parameter types). Either way, records the eta
    /// expansion so the post-inference rewrite replaces the `Name`
    /// node with an explicit `Lambda`.
    fn check_con_as_function(
        &mut self,
        con_sym: SymbolId,
        span: Span,
        expected: &Type,
    ) -> Result<Type, CompileError> {
        let name = self.symbols.display(con_sym).to_owned();

        // Declared constructor: use its stored scheme. For payload
        // constructors the scheme's type is already an arrow
        // (`a -> Result(a, e)` etc.); unifying with the expected
        // arrow pins the type variables to the concrete types at
        // this call site. Nullary declared constructors would fall
        // through here with a non-arrow instantiated type, and the
        // unify below would error out with "cannot unify <nominal>
        // with <arrow>" — which is the right error because a nullary
        // constructor isn't callable.
        let con_arrow = if let Some(scheme) = self.constructors.get(&name).cloned() {
            self.engine.instantiate(&scheme)
        } else {
            // Structural constructor: synthesize an arrow using the
            // expected arrow's param types as the constructor's
            // payload types. Unification with `expected` then lets
            // the return slot flow back to the caller.
            let Type::Arrow(expected_params, _) = self.engine.resolve(expected) else {
                unreachable!("caller checked expected is Arrow");
            };
            let rest = self.engine.fresh();
            let ret_ty = Type::TagUnion {
                tags: vec![(name, expected_params.clone())],
                rest: Some(Box::new(rest)),
            };
            Type::Arrow(expected_params, Box::new(ret_ty))
        };

        self.unify_at(&con_arrow, expected, span)?;
        let resolved = self.engine.resolve(&con_arrow);
        self.expr_types.insert(span, resolved.clone());
        self.eta_expansions
            .insert(span, EtaInfo::Constructor { con_sym });
        Ok(resolved)
    }

    #[expect(clippy::too_many_lines)]
    fn infer_expr_inner(&mut self, expr: &Expr<'src>) -> Result<Type, CompileError> {
        match &expr.kind {
            ExprKind::IntLit(_) => {
                let ty = self.engine.fresh();
                let Type::Var(tv) = ty else { unreachable!() };
                self.int_literal_vars.push((tv, expr.span));
                Ok(ty)
            }

            ExprKind::StrLit(_) => Ok(Type::Con("Str".to_owned())),

            ExprKind::FloatLit(_) => {
                let ty = self.engine.fresh();
                let Type::Var(tv) = ty else { unreachable!() };
                self.float_literal_vars.push((tv, expr.span));
                Ok(ty)
            }

            ExprKind::Name(sym) => self.infer_name(*sym, expr.span),

            ExprKind::BinOp { op, lhs, rhs } => match op {
                BinOp::And => self.infer_bool_binop(lhs, rhs, true),
                BinOp::Or => self.infer_bool_binop(lhs, rhs, false),
                _ => self.infer_binop(*op, lhs, rhs, expr.span),
            },

            ExprKind::Call { target, args, .. } => {
                let func = self.symbols.display(*target).to_owned();
                self.infer_call(&func, args, expr.span)
            }

            ExprKind::QualifiedCall { segments, args, .. } => {
                let mangled = segments.join(".");
                self.infer_call(&mangled, args, expr.span)
            }

            ExprKind::Block(stmts, result) => self.infer_block(stmts, result),

            ExprKind::If {
                expr: scrutinee,
                arms,
                else_body,
            } => self.infer_if(scrutinee, arms, else_body.as_deref(), expr.span),

            ExprKind::Fold {
                expr: scrutinee,
                arms,
            } => self.infer_fold(scrutinee, arms, expr.span),

            ExprKind::Record { fields } => {
                let mut type_fields = Vec::new();
                for (field_sym, field_expr) in fields {
                    let field_ty = self.infer_expr(field_expr)?;
                    let name = self.fields.get(*field_sym).to_owned();
                    type_fields.push((name, field_ty));
                }
                Ok(Type::Record {
                    fields: type_fields,
                    rest: None,
                })
            }

            ExprKind::FieldAccess { record, field } => {
                self.infer_field_access(record, *field, expr.span)
            }

            ExprKind::Lambda { params, body } => self.infer_lambda(params, body),

            ExprKind::Tuple(elems) => {
                let mut elem_types = Vec::new();
                for e in elems {
                    elem_types.push(self.infer_expr(e)?);
                }
                Ok(Type::Tuple(elem_types))
            }

            ExprKind::ListLit(elems) => {
                let elem_ty = self.engine.fresh();
                for e in elems {
                    let t = self.infer_expr(e)?;
                    self.unify_at(&elem_ty, &t, e.span)?;
                }
                Ok(Type::App("List".to_owned(), vec![elem_ty]))
            }

            ExprKind::MethodCall {
                receiver,
                method,
                args,
                ..
            } => self.infer_method_call(receiver, method, args, expr.span),

            ExprKind::Is {
                expr: inner,
                pattern,
            } => {
                let inner_ty = self.infer_expr(inner)?;
                let bindings = self.infer_pattern(pattern, &inner_ty, expr.span, None)?;
                // Store as (display_name, type) — the downstream
                // `collect_is_bindings` walk inserts into `env` by
                // display name for scope flow.
                let named: Vec<(String, Type)> = bindings
                    .into_iter()
                    .map(|(sym, ty)| (self.symbols.display(sym).to_owned(), ty))
                    .collect();
                self.is_bindings.insert(expr.span, named);
                Ok(Type::Con("Bool".to_owned()))
            }

            ExprKind::RecordUpdate { base, updates } => {
                // The base must be a record. Infer it, then check that
                // each update field exists in the record type. The result
                // type is the same as the base type.
                let base_ty = self.infer_expr(base)?;
                for (field_sym, val_expr) in updates {
                    let field_name = self.fields.get(*field_sym).to_owned();
                    let field_ty = self.engine.fresh();
                    let rest = self.engine.fresh();
                    // The base must have this field.
                    let expected = Type::Record {
                        fields: vec![(field_name, field_ty.clone())],
                        rest: Some(Box::new(rest)),
                    };
                    self.unify_at(&base_ty, &expected, expr.span)?;
                    // The update value must match the field type.
                    let val_ty = self.infer_expr(val_expr)?;
                    self.unify_at(&val_ty, &field_ty, val_expr.span)?;
                }
                Ok(base_ty)
            }

            ExprKind::Closure { .. } => {
                panic!("Closure should not exist during type inference")
            }
        }
    }

    // ---- Extracted match arms from infer_expr_inner ----

    fn infer_block(
        &mut self,
        stmts: &[Stmt<'src>],
        result: &Expr<'src>,
    ) -> Result<Type, CompileError> {
        self.scoped(|ctx| {
            let mut pending_hints: HashMap<String, TypeExpr<'src>> = HashMap::new();
            for stmt in stmts {
                match stmt {
                    Stmt::TypeHint { name, ty } => {
                        pending_hints.insert((*name).to_owned(), ty.clone());
                    }
                    Stmt::Let { name, val } => {
                        let name_str = ctx.symbols.display(*name).to_owned();
                        let val_ty = ctx.infer_expr(val)?;
                        if let Some(hint) = pending_hints.remove(&name_str) {
                            let hint_ty = ctx.resolve_type_expr(&hint)?;
                            ctx.unify_expected(
                                &val_ty,
                                &hint_ty,
                                val.span,
                                &format!("let binding `{name_str}`"),
                            )?;
                        }
                        let scheme = if is_syntactic_value(val) {
                            ctx.engine.generalize(&val_ty, &ctx.env)
                        } else {
                            Scheme::mono(val_ty)
                        };
                        ctx.env.insert(name_str, scheme);
                    }
                    Stmt::Destructure { pattern, val } => {
                        let val_ty = ctx.infer_expr(val)?;
                        let bindings = ctx.infer_pattern(pattern, &val_ty, val.span, None)?;
                        let is_value = is_syntactic_value(val);
                        for (sym, ty) in bindings {
                            let name = ctx.symbols.display(sym).to_owned();
                            let scheme = if is_value {
                                ctx.engine.generalize(&ty, &ctx.env)
                            } else {
                                Scheme::mono(ty)
                            };
                            ctx.env.insert(name, scheme);
                        }
                    }
                    Stmt::Guard {
                        condition,
                        return_val,
                    } => {
                        let cond_ty = ctx.infer_expr(condition)?;
                        let bool_ty = Type::Con("Bool".to_owned());
                        ctx.unify_at(&cond_ty, &bool_ty, condition.span)?;
                        ctx.scoped(|ctx| {
                            ctx.collect_is_bindings(condition);
                            let ret_val_ty = ctx.infer_expr(return_val)?;
                            if let Some(fn_ret) = ctx.ret_ty_stack.last().cloned() {
                                ctx.unify_expected(
                                    &ret_val_ty,
                                    &fn_ret,
                                    return_val.span,
                                    "`return` value of guard clause",
                                )?;
                            }
                            Ok(())
                        })?;
                    }
                }
            }
            ctx.infer_expr(result)
        })
    }

    fn infer_if(
        &mut self,
        scrutinee: &Expr<'src>,
        arms: &[ast::MatchArm<'src>],
        else_body: Option<&Expr<'src>>,
        span: Span,
    ) -> Result<Type, CompileError> {
        let scrutinee_ty = self.infer_expr(scrutinee)?;
        let result_ty = self.engine.fresh();
        let bool_ty = Type::Con("Bool".to_owned());
        for arm in arms {
            let bindings = self.infer_pattern(&arm.pattern, &scrutinee_ty, span, None)?;
            self.scoped(|ctx| {
                for (sym, ty) in bindings {
                    let name = ctx.symbols.display(sym).to_owned();
                    ctx.env.insert(name, Scheme::mono(ty));
                }
                if let ast::Pattern::Constructor { name: "True", .. } = &arm.pattern {
                    ctx.collect_is_bindings(scrutinee);
                }
                for guard_expr in &arm.guards {
                    let guard_ty = ctx.infer_expr(guard_expr)?;
                    ctx.unify_at(&guard_ty, &bool_ty, guard_expr.span)?;
                    ctx.collect_is_bindings(guard_expr);
                }
                let body_ty = ctx.infer_expr(&arm.body)?;
                if arm.is_return {
                    if let Some(fn_ret) = ctx.ret_ty_stack.last().cloned() {
                        ctx.unify_expected(
                            &body_ty,
                            &fn_ret,
                            arm.body.span,
                            "`return` value of match arm",
                        )?;
                    }
                } else {
                    ctx.unify_expected(&body_ty, &result_ty, arm.body.span, "match arm body")?;
                }
                Ok(())
            })?;
        }
        if let Some(eb) = else_body {
            let eb_ty = self.infer_expr(eb)?;
            self.unify_expected(&eb_ty, &result_ty, eb.span, "`else` branch")?;
        } else {
            // Literal patterns can never be exhaustive — require else.
            let has_literal = arms
                .iter()
                .any(|a| matches!(a.pattern, ast::Pattern::IntLit(_) | ast::Pattern::StrLit(_)));
            if has_literal {
                return Err(Self::type_error(
                    span,
                    "match on literal patterns requires an `else` branch",
                ));
            }
            self.close_open_tag_row(&scrutinee_ty);
        }
        Ok(result_ty)
    }

    fn infer_fold(
        &mut self,
        scrutinee: &Expr<'src>,
        arms: &[ast::MatchArm<'src>],
        span: Span,
    ) -> Result<Type, CompileError> {
        let scrutinee_ty = self.infer_expr(scrutinee)?;
        let result_ty = self.engine.fresh();
        let bool_ty = Type::Con("Bool".to_owned());
        for arm in arms {
            let bindings = self.infer_pattern(
                &arm.pattern,
                &scrutinee_ty,
                span,
                Some(&result_ty),
            )?;
            self.scoped(|ctx| {
                for (sym, ty) in bindings {
                    let name = ctx.symbols.display(sym).to_owned();
                    ctx.env.insert(name, Scheme::mono(ty));
                }
                for guard_expr in &arm.guards {
                    let guard_ty = ctx.infer_expr(guard_expr)?;
                    ctx.unify_at(&guard_ty, &bool_ty, guard_expr.span)?;
                    ctx.collect_is_bindings(guard_expr);
                }
                let body_ty = ctx.infer_expr(&arm.body)?;
                ctx.unify_expected(&body_ty, &result_ty, arm.body.span, "fold arm body")
            })?;
        }
        self.close_open_tag_row(&scrutinee_ty);
        Ok(result_ty)
    }

    /// Infer `lhs and rhs` or `lhs or rhs`. Both sides must be Bool.
    /// `and` flows `is`-bindings from LHS into RHS scope; `or` does not.
    fn infer_bool_binop(
        &mut self,
        lhs: &Expr<'src>,
        rhs: &Expr<'src>,
        flow_is_bindings: bool,
    ) -> Result<Type, CompileError> {
        let lhs_ty = self.infer_expr(lhs)?;
        let bool_ty = Type::Con("Bool".to_owned());
        self.unify_at(&lhs_ty, &bool_ty, lhs.span)?;
        if flow_is_bindings {
            self.scoped(|ctx| {
                ctx.collect_is_bindings(lhs);
                let rhs_ty = ctx.infer_expr(rhs)?;
                ctx.unify_at(&rhs_ty, &bool_ty, rhs.span)
            })?;
        } else {
            let rhs_ty = self.infer_expr(rhs)?;
            self.unify_at(&rhs_ty, &bool_ty, rhs.span)?;
        }
        Ok(bool_ty)
    }

    fn infer_name(&mut self, sym: SymbolId, span: Span) -> Result<Type, CompileError> {
        let name = self.symbols.display(sym);
        if let Some(scheme) = self.lookup(name).cloned() {
            return Ok(self.engine.instantiate(&scheme));
        }
        // Structural constructor: uppercase name not in any declaration
        // produces an open tag union `[Name, ..ρ]`.
        if name.starts_with(|c: char| c.is_ascii_uppercase()) {
            let rest = self.engine.fresh();
            return Ok(Type::TagUnion {
                tags: vec![(name.to_owned(), vec![])],
                rest: Some(Box::new(rest)),
            });
        }
        Err(Self::type_error(span, &format!("undefined name '{name}'")))
    }

    fn infer_field_access(
        &mut self,
        record: &Expr<'src>,
        field: crate::symbol::FieldSym,
        span: Span,
    ) -> Result<Type, CompileError> {
        // Method reference via `Type.method`: if the record is a
        // `Name` referencing a type symbol and there's a registered
        // method scheme under `"Type.method"`, produce the method's
        // arrow type as a first-class function value. The post-
        // inference eta-expansion pass rewrites the node into an
        // explicit lambda + `QualifiedCall`.
        if let ExprKind::Name(sym) = &record.kind
            && self.symbols.get(*sym).kind == SymbolKind::Type
        {
            let type_name = self.symbols.display(*sym).to_owned();
            let field_name = self.fields.get(field).to_owned();
            let mangled = format!("{type_name}.{field_name}");
            if let Some(scheme) = self.env.get(&mangled).cloned() {
                let method_ty = self.engine.instantiate(&scheme);
                self.expr_types.insert(span, method_ty.clone());
                self.eta_expansions.insert(
                    span,
                    EtaInfo::Method {
                        type_name,
                        method_name: field_name,
                    },
                );
                return Ok(method_ty);
            }
        }
        let record_ty = self.infer_expr(record)?;
        let field_ty = self.engine.fresh();
        let rest_row = self.engine.fresh();
        let field_name = self.fields.get(field).to_owned();
        let expected = Type::Record {
            fields: vec![(field_name, field_ty.clone())],
            rest: Some(Box::new(rest_row)),
        };
        self.unify_at(&record_ty, &expected, span)?;
        Ok(field_ty)
    }

    /// Bidirectional lambda check: infer the lambda body with
    /// parameter types pushed from the expected arrow type. This
    /// ensures method calls on parameters see concrete types during
    /// inference, not fresh vars that only resolve after the body.
    fn check_lambda(
        &mut self,
        params: &[SymbolId],
        body: &Expr<'src>,
        expected_params: &[Type],
        expected_ret: &Type,
        span: Span,
    ) -> Result<Type, CompileError> {
        self.scoped(|ctx| {
            let param_types: Vec<Type> = params
                .iter()
                .zip(expected_params.iter())
                .map(|(p, expected_ty)| {
                    let name = ctx.symbols.display(*p).to_owned();
                    ctx.env.insert(name, Scheme::mono(expected_ty.clone()));
                    expected_ty.clone()
                })
                .collect();
            let ret = ctx.engine.fresh();
            ctx.ret_ty_stack.push(ret.clone());
            let body_ty = ctx.infer_expr(body)?;
            ctx.ret_ty_stack.pop();
            ctx.unify_at(&ret, &body_ty, body.span)?;
            ctx.unify_at(&ret, expected_ret, span)?;
            Ok(Type::Arrow(param_types, Box::new(ret)))
        })
    }

    fn infer_lambda(
        &mut self,
        params: &[SymbolId],
        body: &Expr<'src>,
    ) -> Result<Type, CompileError> {
        self.scoped(|ctx| {
            let param_types: Vec<Type> = params
                .iter()
                .map(|p| {
                    let ty = ctx.engine.fresh();
                    let name = ctx.symbols.display(*p).to_owned();
                    ctx.env.insert(name, Scheme::mono(ty.clone()));
                    ty
                })
                .collect();
            let ret = ctx.engine.fresh();
            ctx.ret_ty_stack.push(ret.clone());
            let body_ty = ctx.infer_expr(body)?;
            ctx.ret_ty_stack.pop();
            ctx.unify_at(&ret, &body_ty, body.span)?;
            Ok(Type::Arrow(param_types, Box::new(ret)))
        })
    }

    // ---- Call inference ----

    fn infer_call(
        &mut self,
        func: &str,
        args: &[Expr<'src>],
        span: Span,
    ) -> Result<Type, CompileError> {
        // Bidirectional path: if the callee has a known scheme whose
        // instantiated type is an arrow, check each argument against
        // the corresponding parameter type. This lets bare
        // constructor references (and numeric literals, if later
        // extended) flow with context. Falls through to the legacy
        // synthesize-first path for zero-arg calls, structural
        // constructors, and method-on-var dispatch.
        if let Some(result) = self.try_infer_call_bidir(func, args, span)? {
            self.maybe_mark_numeric_builtin(func, span);
            return Ok(result);
        }

        // Legacy path: synthesize arg types, then dispatch. Used for
        // zero-arg calls, structural constructor calls, and method
        // constraint generation on type variables.
        let mut arg_types = Vec::new();
        for a in args {
            arg_types.push(self.infer_expr(a)?);
        }
        let ret = self.engine.fresh();

        if let Some(scheme) = self.lookup(func).cloned() {
            let func_ty = self.engine.instantiate(&scheme);
            if arg_types.is_empty() && self.constructors.contains_key(func) {
                return Ok(func_ty);
            }
            let expected = Type::Arrow(arg_types, Box::new(ret.clone()));
            self.unify_at(&func_ty, &expected, span)?;
            self.maybe_mark_numeric_builtin(func, span);
            return Ok(ret);
        }

        // Structural constructor call: `Ok(42)` where `Ok` isn't in
        // any declared `TypeAnno`. Produces an open tag union with
        // one tag whose payload types are the inferred arg types.
        if func.starts_with(|c: char| c.is_ascii_uppercase()) {
            let rest = self.engine.fresh();
            return Ok(Type::TagUnion {
                tags: vec![(func.to_owned(), arg_types)],
                rest: Some(Box::new(rest)),
            });
        }

        // Dotted call: x.method(args) → dispatch through resolve_method
        if let Some(dot_pos) = func.find('.') {
            let var_name = &func[..dot_pos];
            let method_name = &func[dot_pos + 1..];
            if let Some(scheme) = self.env.get(var_name).cloned() {
                let var_ty = self.engine.instantiate(&scheme);
                return self.resolve_method(var_ty, method_name, arg_types, span);
            }
        }

        Err(Self::type_error(
            span,
            &format!("undefined function '{func}'"),
        ))
    }

    // ---- Binary operator inference ----

    fn infer_binop(
        &mut self,
        op: BinOp,
        lhs: &Expr<'src>,
        rhs: &Expr<'src>,
        span: Span,
    ) -> Result<Type, CompileError> {
        let lt = self.infer_expr(lhs)?;
        let rt = self.infer_expr(rhs)?;
        let op_name = match op {
            BinOp::Add => "+",
            BinOp::Sub => "-",
            BinOp::Mul => "*",
            BinOp::Div => "/",
            BinOp::Rem => "%",
            BinOp::Eq => "==",
            BinOp::Neq => "!=",
            BinOp::Lt => "<",
            BinOp::Gt => ">",
            BinOp::Le => "<=",
            BinOp::Ge => ">=",
            BinOp::And | BinOp::Or => unreachable!(),
        };
        if self.unify_at(&lt, &rt, span).is_err() {
            // Binop sides are symmetric — neither is "expected" —
            // so use a "left ... right" framing instead of the
            // unify_expected "expected/got" shape.
            let resolved_l = self.engine.resolve(&lt);
            let resolved_r = self.engine.resolve(&rt);
            return Err(Self::type_error(
                span,
                &format!(
                    "in `{op_name}`, left operand is `{}` but right operand is `{}`",
                    self.engine.display_type(&resolved_l),
                    self.engine.display_type(&resolved_r)
                ),
            ));
        }

        let is_eq = matches!(op, BinOp::Eq | BinOp::Neq);
        let is_ord = matches!(op, BinOp::Lt | BinOp::Gt | BinOp::Le | BinOp::Ge);
        // `!=` requires the same `equals` method as `==` — the
        // negation is handled at the lowering level, not as a
        // separate method on the type.
        let method_name = match op {
            BinOp::Add => "add",
            BinOp::Sub => "sub",
            BinOp::Mul => "mul",
            BinOp::Div => "div",
            BinOp::Rem => "mod",
            BinOp::Eq | BinOp::Neq => "equals",
            BinOp::Lt | BinOp::Gt | BinOp::Le | BinOp::Ge => "compare",
            BinOp::And | BinOp::Or => unreachable!(),
        };

        let resolved = self.engine.resolve(&lt);
        if let Type::Var(tv) = resolved {
            let ret_ty = if is_eq || is_ord {
                Type::Con("Bool".to_owned())
            } else {
                Type::Var(tv)
            };
            let method_type = Type::Arrow(vec![Type::Var(tv), Type::Var(tv)], Box::new(ret_ty));
            self.push_constraint(
                Constraint {
                    type_var: tv,
                    method_name: method_name.to_owned(),
                    method_type,
                },
                span,
            );
        }

        if is_eq || is_ord {
            Ok(Type::Con("Bool".to_owned()))
        } else {
            Ok(lt)
        }
    }

    // ---- Method call inference ----

    fn infer_method_call(
        &mut self,
        receiver: &Expr<'src>,
        method: &'src str,
        args: &[Expr<'src>],
        span: Span,
    ) -> Result<Type, CompileError> {
        let recv_ty = self.infer_expr(receiver)?;
        let mut arg_types = Vec::new();
        for a in args {
            arg_types.push(self.infer_expr(a)?);
        }
        self.resolve_method(recv_ty, method, arg_types, span)
    }

    /// Shared method dispatch: given a receiver type, method name, and
    /// already-inferred argument types, look up the method on the
    /// receiver's concrete type or generate a constraint for type
    /// variables. Used by both `infer_method_call` and the dotted-call
    /// path in `infer_call`.
    fn resolve_method(
        &mut self,
        recv_ty: Type,
        method: &str,
        arg_types: Vec<Type>,
        span: Span,
    ) -> Result<Type, CompileError> {
        let ret = self.engine.fresh();
        let resolved = self.engine.resolve(&recv_ty);

        if let Type::Con(name) | Type::App(name, _) = &resolved {
            let mangled = format!("{name}.{method}");
            if let Some(scheme) = self.env.get(&mangled).cloned() {
                let func_ty = self.engine.instantiate(&scheme);
                let mut full_args = vec![recv_ty];
                full_args.extend(arg_types);
                let expected = Type::Arrow(full_args, Box::new(ret.clone()));
                self.unify_at(&func_ty, &expected, span)?;
                let resolution = if super::post_infer::is_numeric_builtin(name, method) {
                    format!("__builtin.{method}")
                } else {
                    mangled
                };
                self.method_resolutions.insert(span, resolution);
                return Ok(ret);
            }
        }

        // Record types: compiler-generated equals and to_str.
        if let Type::Record { .. } = &resolved {
            match method {
                "equals" => {
                    let bool_ty = Type::Con("Bool".to_owned());
                    self.unify_at(&ret, &bool_ty, span)?;
                    self.method_resolutions
                        .insert(span, "__record_equals".to_owned());
                    return Ok(ret);
                }
                "to_str" => {
                    let str_ty = Type::Con("Str".to_owned());
                    self.unify_at(&ret, &str_ty, span)?;
                    self.method_resolutions
                        .insert(span, "__record_to_str".to_owned());
                    return Ok(ret);
                }
                _ => {}
            }
        }

        if let Type::Var(tv) = resolved {
            let mut param_types = vec![Type::Var(tv)];
            param_types.extend(arg_types);
            let method_type = Type::Arrow(param_types, Box::new(ret.clone()));
            self.push_constraint(
                Constraint {
                    type_var: tv,
                    method_name: method.to_owned(),
                    method_type,
                },
                span,
            );
            return Ok(ret);
        }

        Err(CompileError::at(
            span,
            format!(
                "no method '{method}' on type {}",
                self.engine.display_type(&resolved)
            ),
        ))
    }

    // ---- Match exhaustiveness closure ----

    /// Close an open tag union row on a scrutinee type. Called after
    /// all arms of an exhaustive match have been typed. If the
    /// scrutinee's type is a `Type::TagUnion` with an open `rest`
    /// variable, unify that variable with an empty closed union so
    /// the row becomes exactly the set of tags matched by the arms.
    ///
    /// Safe to call on any type — if the resolved scrutinee isn't an
    /// open tag union, this is a no-op. If unification fails (e.g.
    /// the row was already constrained), the error is silently
    /// discarded because closure is best-effort: a genuine
    /// type error would already have been surfaced during the
    /// per-arm unification.
    fn close_open_tag_row(&mut self, scrutinee_ty: &Type) {
        let resolved = self.engine.resolve(scrutinee_ty);
        let Type::TagUnion {
            rest: Some(rest_var),
            ..
        } = resolved
        else {
            return;
        };
        let empty_closed = Type::TagUnion {
            tags: vec![],
            rest: None,
        };
        if let Err(_err) = self.engine.unify(&rest_var, &empty_closed) {
            // Best-effort closure — a genuine type error would have
            // already been caught by per-arm unification.
        }
    }

    // ---- Pattern inference ----

    /// Infer bindings for a Constructor pattern that references a
    /// declared `TagUnion` constructor (scheme already in
    /// `self.constructors`). Extracted from `infer_pattern` so the
    /// structural path is a peer rather than an inner branch.
    fn infer_declared_con_pattern(
        &mut self,
        scheme: &Scheme,
        fields: &[ast::Pattern<'src>],
        expected: &Type,
        span: Span,
        rec_subst: Option<&Type>,
    ) -> Result<Vec<(SymbolId, Type)>, CompileError> {
        let con_ty = self.engine.instantiate(scheme);

        if fields.is_empty() {
            // Nullary constructor
            self.unify_at(&con_ty, expected, span)?;
            return Ok(vec![]);
        }

        let field_types: Vec<Type> =
            fields.iter().map(|_| self.engine.fresh()).collect();
        let con_ret = self.engine.fresh();
        let arrow = Type::Arrow(field_types.clone(), Box::new(con_ret.clone()));
        self.unify_at(&con_ty, &arrow, span)?;
        self.unify_at(&con_ret, expected, span)?;

        let mut bindings = Vec::new();
        for (field_pat, field_ty) in fields.iter().zip(field_types.iter()) {
            // For fold patterns: if field type matches scrutinee and
            // rec_subst is Some, use the substitution type instead.
            let bind_ty = if let Some(result_ty) = rec_subst {
                let resolved = self.engine.resolve(field_ty);
                let scrutinee_resolved = self.engine.resolve(expected);
                if self.engine.types_match(&resolved, &scrutinee_resolved) {
                    result_ty.clone()
                } else {
                    field_ty.clone()
                }
            } else {
                field_ty.clone()
            };
            match field_pat {
                ast::Pattern::Binding(sym) => {
                    bindings.push((*sym, bind_ty));
                }
                ast::Pattern::Wildcard
                | ast::Pattern::IntLit(_)
                | ast::Pattern::StrLit(_) => {}
                ast::Pattern::Constructor { .. }
                | ast::Pattern::Record { .. }
                | ast::Pattern::Tuple(_)
                | ast::Pattern::List(_) => {
                    bindings.extend(self.infer_pattern(field_pat, &bind_ty, span, None)?);
                }
            }
        }
        Ok(bindings)
    }

    /// Infer bindings for a Constructor pattern that references a
    /// structural (undeclared) tag. Unifies the scrutinee against an
    /// open tag union `[Name(payload..), ..ρ]`, letting the
    /// unification engine widen the scrutinee's row to include the
    /// new tag if it was also open.
    ///
    /// The scrutinee's row stays open here. Match-arm closure (the
    /// "exhaustive match closes the row" rule) is applied later by
    /// `close_open_match_rows` after all arms have been typed.
    fn infer_structural_con_pattern(
        &mut self,
        name: &str,
        fields: &[ast::Pattern<'src>],
        expected: &Type,
        span: Span,
    ) -> Result<Vec<(SymbolId, Type)>, CompileError> {
        let payload_types: Vec<Type> =
            fields.iter().map(|_| self.engine.fresh()).collect();
        let rest = self.engine.fresh();
        let pattern_ty = Type::TagUnion {
            tags: vec![(name.to_owned(), payload_types.clone())],
            rest: Some(Box::new(rest)),
        };
        self.unify_at(&pattern_ty, expected, span)?;

        let mut bindings = Vec::new();
        for (field_pat, field_ty) in fields.iter().zip(payload_types.iter()) {
            match field_pat {
                ast::Pattern::Binding(sym) => {
                    bindings.push((*sym, field_ty.clone()));
                }
                ast::Pattern::Wildcard
                | ast::Pattern::IntLit(_)
                | ast::Pattern::StrLit(_) => {}
                ast::Pattern::Constructor { .. }
                | ast::Pattern::Record { .. }
                | ast::Pattern::Tuple(_)
                | ast::Pattern::List(_) => {
                    bindings.extend(self.infer_pattern(field_pat, field_ty, span, None)?);
                }
            }
        }
        Ok(bindings)
    }

    fn infer_pattern(
        &mut self,
        pat: &ast::Pattern<'src>,
        expected: &Type,
        span: Span,
        rec_subst: Option<&Type>,
    ) -> Result<Vec<(SymbolId, Type)>, CompileError> {
        match pat {
            ast::Pattern::Constructor { name, fields } => {
                let name = *name;
                // Declared constructor (from a `TypeAnno`): use the
                // stored scheme. Structural constructor (bare
                // reference to an undeclared uppercase tag): produce
                // an open TagUnion and unify against the scrutinee.
                if let Some(scheme) = self.constructors.get(name).cloned() {
                    return self.infer_declared_con_pattern(
                        &scheme, fields, expected, span, rec_subst,
                    );
                }
                self.infer_structural_con_pattern(name, fields, expected, span)
            }
            ast::Pattern::Record { fields, .. } => {
                let rest = self.engine.fresh(); // open rest for row polymorphism
                let mut type_fields = Vec::new();
                let mut bindings = Vec::new();
                for (field_sym, field_pat) in fields {
                    let field_ty = self.engine.fresh();
                    let name = self.fields.get(*field_sym).to_owned();
                    type_fields.push((name, field_ty.clone()));
                    bindings.extend(self.infer_pattern(field_pat, &field_ty, span, None)?);
                }
                let expected_record = Type::Record {
                    fields: type_fields,
                    rest: Some(Box::new(rest)),
                };
                self.unify_at(&expected_record, expected, span)?;
                Ok(bindings)
            }
            ast::Pattern::Tuple(elems) => {
                let elem_types: Vec<Type> = elems.iter().map(|_| self.engine.fresh()).collect();
                let tuple_ty = Type::Tuple(elem_types.clone());
                self.unify_at(&tuple_ty, expected, span)?;
                let mut bindings = Vec::new();
                for (elem_pat, elem_ty) in elems.iter().zip(elem_types.iter()) {
                    bindings.extend(self.infer_pattern(elem_pat, elem_ty, span, None)?);
                }
                Ok(bindings)
            }
            ast::Pattern::Binding(sym) => Ok(vec![(*sym, expected.clone())]),
            ast::Pattern::Wildcard => Ok(vec![]),
            ast::Pattern::IntLit(_) => {
                // Pattern literals get their type from the scrutinee —
                // don't push to int_literal_vars (which would default
                // them to I64 and corrupt the scrutinee's type).
                Ok(vec![])
            }
            ast::Pattern::StrLit(_) => {
                let str_ty = Type::Con("Str".to_owned());
                self.unify_at(&str_ty, expected, span)?;
                Ok(vec![])
            }
            ast::Pattern::List(elems) => {
                let elem_ty = self.engine.fresh();
                let list_ty = Type::App("List".to_owned(), vec![elem_ty.clone()]);
                self.unify_at(&list_ty, expected, span)?;
                let mut bindings = Vec::new();
                for elem in elems {
                    match elem {
                        ast::ListPatternElem::Pattern(p) => {
                            bindings.extend(self.infer_pattern(p, &elem_ty, span, None)?);
                        }
                        ast::ListPatternElem::Spread(Some(sym)) => {
                            // Spread captures a sub-list of the same type.
                            bindings.push((*sym, list_ty.clone()));
                        }
                        ast::ListPatternElem::Spread(None) => {}
                    }
                }
                Ok(bindings)
            }
        }
    }

    /// Collect Is bindings from an expression tree and add them to the environment.
    /// Used by `And` to flow bindings from LHS `is` expressions into RHS scope.
    fn collect_is_bindings(&mut self, expr: &Expr<'src>) {
        match &expr.kind {
            ExprKind::Is { .. } => {
                if let Some(bindings) = self.is_bindings.get(&expr.span).cloned() {
                    for (name, ty) in bindings {
                        self.env.insert(name, Scheme::mono(ty));
                    }
                }
            }
            ExprKind::BinOp {
                op: BinOp::And,
                lhs,
                rhs,
            } => {
                self.collect_is_bindings(lhs);
                self.collect_is_bindings(rhs);
            }
            _ => {}
        }
    }

    // ---- Function body inference ----

    fn infer_func_body(
        &mut self,
        name: &str,
        params: &[SymbolId],
        body: &Expr<'src>,
    ) -> Result<(), CompileError> {
        // Zero-param bindings are value bindings, not zero-arg functions.
        if params.is_empty() {
            let body_ty = self.scoped(|ctx| {
                let body_ty = ctx.infer_expr(body)?;
                if let Some(anno) = ctx.type_annos.get(name).cloned() {
                    let anno_ty = ctx.resolve_type_expr(&anno)?;
                    ctx.unify_expected(
                        &body_ty,
                        &anno_ty,
                        body.span,
                        &format!("value `{name}`"),
                    )?;
                }
                Ok(body_ty)
            })?;
            self.env.remove(name);
            let generalized = self.engine.generalize(&body_ty, &self.env);
            self.env.insert(name.to_owned(), generalized);
            return Ok(());
        }

        // Methods still have a pre-declared scheme from Pass 1 and we
        // reuse it so any earlier call sites that unified with it stay
        // linked. Free functions no longer get forward-declared (Step 5),
        // so env lookup returns None and we synthesize a fresh arrow
        // and register it under the function's name for the duration of
        // body inference. The self-registration lets `__fold_N` and
        // similar synthesized recursive helpers resolve calls to
        // themselves; it's restored/generalized at the end of this
        // function so no spurious mono scheme leaks into later callers.
        let external_ty = self.scoped(|ctx| {
            let func_ty = if let Some(pre_scheme) = ctx.env.get(name).cloned() {
                ctx.engine.instantiate(&pre_scheme)
            } else {
                let param_types: Vec<Type> = params.iter().map(|_| ctx.engine.fresh()).collect();
                let ret = ctx.engine.fresh();
                let func_ty = Type::Arrow(param_types, Box::new(ret));
                ctx.env
                    .insert(name.to_owned(), Scheme::mono(func_ty.clone()));
                func_ty
            };

            let param_types: Vec<Type> = params.iter().map(|_| ctx.engine.fresh()).collect();
            let ret = ctx.engine.fresh();
            let expected = Type::Arrow(param_types.clone(), Box::new(ret.clone()));
            ctx.unify_at(&func_ty, &expected, body.span)?;

            for (p, ty) in params.iter().zip(param_types.iter()) {
                let pname = ctx.symbols.display(*p).to_owned();
                ctx.env.insert(pname, Scheme::mono(ty.clone()));
            }
            ctx.ret_ty_stack.push(ret.clone());
            let body_ty = ctx.check_expr(body, &ret, Some((name, 0)))?;
            ctx.ret_ty_stack.pop();
            ctx.unify_expected(
                &body_ty,
                &ret,
                body.span,
                &format!("body of function `{name}`"),
            )?;

            if let Some(anno) = ctx.type_annos.get(name).cloned() {
                let anno_ty = ctx.resolve_type_expr(&anno)?;
                ctx.unify_expected(
                    &func_ty,
                    &anno_ty,
                    body.span,
                    &format!("function `{name}`"),
                )?;
                Ok(anno_ty)
            } else {
                Ok(ctx.engine.resolve(&func_ty))
            }
        })?;

        self.env.remove(name);
        let generalized = self.engine.generalize(&external_ty, &self.env);
        self.env.insert(name.to_owned(), generalized);
        Ok(())
    }

    /// If `func` is a dotted `Type.method` that matches a numeric
    /// builtin, insert the `__builtin.<method>` marker into
    /// `method_resolutions` at `span`. Called after `infer_call` /
    /// `try_infer_call_bidir` resolve a `QualifiedCall` via env so
    /// the lowerer routes it through the intrinsic path.
    fn maybe_mark_numeric_builtin(&mut self, func: &str, span: Span) {
        if let Some(dot) = func.find('.') {
            let type_name = &func[..dot];
            let method = &func[dot + 1..];
            if super::post_infer::is_numeric_builtin(type_name, method) {
                self.method_resolutions
                    .insert(span, format!("__builtin.{method}"));
            }
        }
    }

    /// Verify constraints whose type vars resolved to concrete types,
    /// and store method resolutions for the lowerer. Runs in a loop
    /// because constraint resolution can trigger further unifications
    /// that resolve previously-unresolved type vars.
    fn verify_constraints(&mut self) -> Result<(), CompileError> {
        let mut remaining: Vec<usize> = (0..self.engine.constraints.len()).collect();
        loop {
            let mut progress = false;
            let mut still_remaining = Vec::new();
            for i in remaining {
                let c = self.engine.constraints[i].clone();
                let resolved = self.engine.resolve(&Type::Var(c.type_var));
                let maybe_span = self.constraint_spans.get(i).copied();

                // Record types: compiler-generated equals/to_str.
                if let Type::Record { .. } = &resolved
                    && matches!(c.method_name.as_str(), "equals" | "to_str")
                {
                    if let Some(s) = maybe_span {
                        self.method_resolutions
                            .insert(s, format!("__record_{}", c.method_name));
                    }
                    progress = true;
                    continue;
                }

                let (Type::Con(type_name) | Type::App(type_name, _)) = &resolved else {
                    still_remaining.push(i);
                    continue;
                };
                let mangled = format!("{type_name}.{}", c.method_name);
                if let Some(scheme) = self.env.get(&mangled).cloned() {
                    let actual_ty = self.engine.instantiate(&scheme);
                    drop(self.engine.unify(&c.method_type, &actual_ty));
                    if let Some(s) = maybe_span {
                        let resolution = if super::post_infer::is_numeric_builtin(type_name, &c.method_name) {
                            format!("__builtin.{}", c.method_name)
                        } else {
                            mangled
                        };
                        self.method_resolutions.insert(s, resolution);
                    }
                } else if let Some(s) = maybe_span {
                    return Err(CompileError::at(
                        s,
                        format!("no method '{0}' on type {type_name}", c.method_name),
                    ));
                } else {
                    return Err(CompileError::new(format!(
                        "no method '{0}' on type {type_name}",
                        c.method_name
                    )));
                }
                progress = true;
            }
            remaining = still_remaining;
            if !progress {
                break;
            }
        }
        Ok(())
    }

    /// Default unresolved numeric literal type vars to `I64` / `F64` and
    /// check that each literal resolves to a valid numeric type. The
    /// resolved types propagate onto `Expr::ty` via `write_types_back`.
    fn resolve_literals(&mut self) -> Result<(), CompileError> {
        let i64_ty = Type::Con("I64".to_owned());
        let f64_ty = Type::Con("F64".to_owned());

        // Default unresolved int literals to I64. Use `unify`
        // rather than inserting into `subst` directly so the
        // default propagates to the *root* of the var's
        // substitution chain — direct inserts can orphan a
        // downstream var in the chain when the literal's var
        // points transitively to another unresolved var (which
        // happens whenever `unify_at(lit_var, other_var)` set
        // lit_var := other_var earlier). Unification cannot fail
        // here because the chain root is a free Var.
        for &(tv, _) in &self.int_literal_vars {
            if matches!(self.engine.resolve(&Type::Var(tv)), Type::Var(_))
                && self.engine.unify(&Type::Var(tv), &i64_ty).is_err()
            {
                unreachable!("unresolved var cannot fail to unify with I64");
            }
        }

        // Default unresolved float literals to F64 (same
        // consideration as above).
        for &(tv, _) in &self.float_literal_vars {
            if matches!(self.engine.resolve(&Type::Var(tv)), Type::Var(_))
                && self.engine.unify(&Type::Var(tv), &f64_ty).is_err()
            {
                unreachable!("unresolved var cannot fail to unify with F64");
            }
        }

        // Validate that every literal resolved to a supported numeric type.
        for &(tv, span) in &self.int_literal_vars {
            let resolved = self.engine.resolve(&Type::Var(tv));
            match &resolved {
                Type::Con(name)
                    if crate::numeric::NumericType::from_name(name).is_some() => {}
                other => {
                    return Err(CompileError::at(
                        span,
                        format!(
                            "type error: integer literal resolved to non-numeric type: {}",
                            self.engine.display_type(other)
                        ),
                    ));
                }
            }
        }
        for &(tv, span) in &self.float_literal_vars {
            let resolved = self.engine.resolve(&Type::Var(tv));
            match &resolved {
                Type::Con(name)
                    if crate::numeric::NumericType::from_name(name)
                        .is_some_and(|n| !n.is_integer()) => {}
                other => {
                    return Err(CompileError::at(
                        span,
                        format!(
                            "type error: float literal resolved to non-numeric type: {}",
                            self.engine.display_type(other)
                        ),
                    ));
                }
            }
        }
        Ok(())
    }
}

// ---- Public API ----

#[expect(
    clippy::too_many_lines,
    reason = "multi-pass type checking orchestration"
)]
pub fn check(
    resolved: &mut crate::passes::resolve::Resolved<'_>,
) -> Result<InferResult, CompileError> {
    let (module, scope, symbols, fields) = (
        &mut resolved.module,
        &resolved.scope,
        &mut resolved.symbols,
        &resolved.fields,
    );
    let mut ctx = InferCtx::new(&*symbols, fields);

    // Register to_str for all numeric types (not as full modules — their
    // := {} declaration would incorrectly make them transparent to {}).
    for num in crate::numeric::ALL {
        let mangled = format!("{}.to_str", num.name());
        let param_ty = Type::Con(num.name().to_owned());
        let ret_ty = Type::Con("Str".to_owned());
        let scheme = Scheme {
            vars: vec![],
            constraints: vec![],
            ty: Type::Arrow(vec![param_ty], Box::new(ret_ty)),
        };
        ctx.env.insert(mangled, scheme);
    }

    // `crash : Str -> a` — polymorphic return; aborts with a message.
    let crash_ret = ctx.engine.fresh();
    let Type::Var(crash_tv) = crash_ret else {
        unreachable!()
    };
    ctx.env.insert(
        "crash".to_owned(),
        Scheme {
            vars: vec![crash_tv],
            constraints: vec![],
            ty: Type::Arrow(
                vec![Type::Con("Str".to_owned())],
                Box::new(Type::Var(crash_tv)),
            ),
        },
    );

    // Pre-register all type names into `known_types` before Pass 1
    // processes method signatures. This breaks dependency cycles
    // between stdlib modules — e.g. I64's `to_str : I64 -> Str`
    // references Str, which isn't processed until later. Forward
    // type-name references are fine; only the name needs to exist in
    // `known_types` for `type_expr_to_type` to accept it.
    for decl in &module.decls {
        if let Decl::TypeAnno { name, kind, .. } = decl {
            let n = symbols.display(*name);
            if n.starts_with(|c: char| c.is_ascii_uppercase()) && *kind != TypeDeclKind::Alias {
                ctx.known_types.insert(n.to_owned());
            }
        }
    }

    // Pass 1: register all type declarations and function signatures
    for decl in &module.decls {
        match decl {
            Decl::TypeAnno {
                name,
                type_params,
                ty: TypeExpr::TagUnion(tags, _),
                methods,
                ..
            } => {
                let name = symbols.display(*name);
                ctx.register_type_decl(name, type_params, tags)?;
                ctx.register_methods(name, methods, scope)?;
            }
            Decl::TypeAnno {
                name,
                type_params,
                ty,
                methods,
                kind,
                ..
            } => {
                let name = symbols.display(*name);
                if name.starts_with(|c: char| c.is_ascii_uppercase())
                    && *kind != TypeDeclKind::Alias
                {
                    // Nominal type (:= or ::) — distinct type, not an alias
                    ctx.known_types.insert(name.to_owned());
                    ctx.register_methods(name, methods, scope)?;
                } else if name.starts_with(|c: char| c.is_ascii_uppercase()) {
                    // CamelCase alias (:) — type alias (e.g. Point : { x: I64, y: I64 })
                    let mut tvar_env: HashMap<String, TypeVar> = type_params
                        .iter()
                        .map(|p| {
                            let t = ctx.engine.fresh();
                            let Type::Var(tv) = t else { unreachable!() };
                            ((*p).to_owned(), tv)
                        })
                        .collect();
                    let tvars: Vec<TypeVar> = type_params.iter().map(|p| tvar_env[*p]).collect();
                    let alias_ty = ctx.type_expr_to_type(ty, &mut tvar_env)?;
                    let alias_scheme = Scheme {
                        vars: tvars,
                        constraints: vec![],
                        ty: alias_ty,
                    };
                    if let Some(mod_name) = scope.qualified_types.get(name) {
                        let qual = format!("{mod_name}.{name}");
                        ctx.type_aliases.insert(qual, alias_scheme.clone());
                    }
                    ctx.type_aliases.insert(name.to_owned(), alias_scheme);
                    ctx.known_types.insert(name.to_owned());
                } else {
                    // snake_case: value/function annotation (e.g. get_x : I64 -> I64)
                    ctx.type_annos.insert(name.to_owned(), ty.clone());
                }
            }
            Decl::FuncDef { .. } => {
                // Step 5: free functions are no longer forward-declared
                // here. They're inferred on first encounter in topo
                // order, which gives top-level let-polymorphism — each
                // function is generalized before any later caller sees
                // it, so the same function can be instantiated at
                // multiple types across call sites. `topo::compute`
                // guarantees callees come before callers (and rejects
                // cycles as System T violations).
            }
        }
    }

    // Pass 2a: Set transparency for `:=` nominal types so free functions
    // in Pass 2b can see through them (the whole point of transparent
    // types is that their internals are globally visible). `::` opaque
    // types are NOT made transparent here — their transparency is
    // scoped to their own method processing in Pass 2c, so code
    // outside the `.()` block can't see through them.
    //
    // Also validate that every method annotation has a matching
    // definition (body-less methods are only allowed in stdlib).
    for decl in &module.decls {
        if let Decl::TypeAnno {
            name,
            type_params,
            ty,
            kind,
            ..
        } = decl
        {
            let name = symbols.display(*name);
            if *kind == TypeDeclKind::Transparent && !matches!(ty, TypeExpr::TagUnion(..)) {
                // Skip transparency for `Type := {}` — the empty record
                // body means "compiler builtin, no real underlying type."
                // Registering these as transparent to {} would make all
                // builtins unify with each other through the empty record.
                if !matches!(ty, TypeExpr::Record(fields) if fields.is_empty()) {
                    let (param_vars, underlying) =
                        ctx.resolve_type_expr_with_params(ty, type_params)?;
                    ctx.engine
                        .transparent
                        .insert(name.to_owned(), (param_vars, underlying));
                }
            }
        }
    }

    // Pass 2b: Infer free FuncDef bodies. Must run before any method
    // body inference so that methods calling fold-lift-synthesized
    // helpers (e.g. `Lnk.sum` calling `__fold_0`) find the helper's
    // scheme in env. Free FuncDefs are already in topological order
    // from `topo::compute`, so callees are generalized before callers.
    for decl in &module.decls {
        if let Decl::FuncDef {
            name, params, body, ..
        } = decl
        {
            let name = symbols.display(*name);
            ctx.infer_func_body(name, params, body)?;
            if let Some(mod_name) = scope.qualified_funcs.get(name) {
                let qual = format!("{mod_name}.{name}");
                if let Some(scheme) = ctx.env.get(name).cloned() {
                    ctx.env.insert(qual, scheme);
                }
            }
        }
    }

    // Pass 2c: Infer method bodies. Opaque types get their transparency
    // set up only for the duration of their own method processing so
    // the implementation can see through the nominal wrapper; it's
    // removed before the next TypeAnno runs.
    for decl in &module.decls {
        if let Decl::TypeAnno {
            name,
            type_params,
            ty,
            kind,
            methods,
            ..
        } = decl
        {
            let name = symbols.display(*name);
            let opaque_set_up =
                if *kind == TypeDeclKind::Opaque && !matches!(ty, TypeExpr::TagUnion(..)) {
                    let (param_vars, underlying) =
                        ctx.resolve_type_expr_with_params(ty, type_params)?;
                    ctx.engine
                        .transparent
                        .insert(name.to_owned(), (param_vars, underlying));
                    true
                } else {
                    false
                };
            for method in methods {
                if let Decl::FuncDef {
                    name: method_name,
                    params,
                    body,
                    ..
                } = method
                {
                    let method_name = symbols.display(*method_name);
                    let mangled = method_key(name, method_name);
                    ctx.infer_func_body(&mangled, params, body)?;
                    if let Some(mod_name) = scope.qualified_types.get(name) {
                        let qual = format!("{mod_name}.{mangled}");
                        if let Some(scheme) = ctx.env.get(&mangled).cloned() {
                            ctx.env.insert(qual, scheme);
                        }
                    }
                }
            }
            if opaque_set_up {
                ctx.engine.transparent.remove(name);
            }
        }
    }

    ctx.verify_constraints()?;
    ctx.resolve_literals()?;
    // Second pass: constraints that depended on literal defaulting
    // (e.g. `x.to_str()` where `x` was an unresolved int literal
    // that just got defaulted to I64) can now resolve.
    ctx.verify_constraints()?;

    // Resolve all expression types now that inference is complete.
    let expr_types: HashMap<Span, Type> = ctx
        .expr_types
        .iter()
        .map(|(span, ty)| (*span, ctx.engine.resolve(ty)))
        .collect();

    // Collect resolved function/method schemes for monomorphization.
    let func_schemes: HashMap<String, Scheme> = ctx
        .env
        .iter()
        .map(|(name, scheme)| {
            let resolved_ty = ctx.engine.resolve(&scheme.ty);
            (
                name.clone(),
                Scheme {
                    vars: scheme.vars.clone(),
                    constraints: scheme.constraints.clone(),
                    ty: resolved_ty,
                },
            )
        })
        .collect();

    // Collect resolved constructor schemes for monomorphization.
    let constructor_schemes: HashMap<String, Scheme> = ctx
        .constructors
        .iter()
        .map(|(name, scheme)| {
            let resolved_ty = ctx.engine.resolve(&scheme.ty);
            (
                name.clone(),
                Scheme {
                    vars: scheme.vars.clone(),
                    constraints: scheme.constraints.clone(),
                    ty: resolved_ty,
                },
            )
        })
        .collect();

    // Single combined post-inference walk: write resolved types onto
    // Expr::ty, write method resolutions onto MethodCall/QualifiedCall
    // nodes, and eta-expand constructor/method references.
    super::post_infer::rewrite(
        module,
        &expr_types,
        &ctx.method_resolutions,
        &ctx.eta_expansions,
        symbols,
    );

    Ok(InferResult {
        func_schemes,
        constructor_schemes,
    })
}

// Post-inference write-back and eta-expansion moved to
// `src/types/post_infer.rs` — single combined walk replaces three
// separate traversals.
