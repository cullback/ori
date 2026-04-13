use std::collections::HashMap;

use crate::ast::{self, BinOp, Decl, Expr, ExprKind, Module, Span, Stmt, TypeDeclKind, TypeExpr};
use crate::error::CompileError;
use crate::source::SourceArena;
use crate::symbol::{FieldInterner, SymbolId, SymbolKind, SymbolTable};
use crate::types::engine::{Constraint, Scheme, Type, TypeEngine, TypeVar};

/// Build a mangled key for a method on a type, e.g. `method_key("List", "sum")` -> `"List.sum"`.
fn method_key(type_name: &str, method: &str) -> String {
    format!("{type_name}.{method}")
}

/// Value restriction helper: is this expression a syntactic value
/// safe to let-generalize? Functions (lambdas) are always safe.
/// Everything else — calls, matches, records, tag values — is not,
/// because generalizing a non-function let-binding can freeze row
/// variables prematurely and break structural tag row propagation.
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

/// Information a post-inference rewrite needs to turn a bare
/// callable reference into an explicit lambda. Two shapes:
///
/// - `Constructor` — a bare constructor name (declared or
///   structural) used where a function is expected, like
///   `List.map(xs, Ok)`. The rewrite produces `|a| Ok(a)`.
/// - `Method` — a qualified method name like `I64.add` used as
///   a value, like `xs.scan(0, I64.add)`. The rewrite produces
///   `|a, b| I64.add(a, b)` via a `QualifiedCall`.
///
/// In both cases the arrow type is read from `expr.ty` at rewrite
/// time (populated by `write_types_back`), so the stored info only
/// needs the kind-specific bits. This way any further unification
/// between inference-populate time and end-of-inference resolve
/// flows through to the rewrite automatically.
enum EtaInfo {
    /// Constructor eta-expansion. Carries the constructor's
    /// `SymbolId` so the rewrite can emit `Call { target }`.
    Constructor { con_sym: SymbolId },
    /// Method-reference eta-expansion. Carries the type and
    /// method names so the rewrite can emit the `QualifiedCall`
    /// that the method dispatch pipeline expects. Stored as
    /// `String` (rather than `&'src str`) so the rewrite can
    /// leak them to `'static` without lifetime gymnastics.
    Method {
        type_name: String,
        method_name: String,
    },
}

struct InferCtx<'a, 'src> {
    engine: TypeEngine,
    /// Names to schemes. Keyed by display name (string).
    ///
    /// Locals (`let`, function params, lambda params, pattern bindings)
    /// are inserted under `symbols.display(sym)`. Globals (free
    /// functions, methods, stdlib) are inserted under their mangled
    /// names (e.g. `"List.map"`). Shadowing is implemented via the
    /// usual save/restore of `env` around scope exits.
    env: HashMap<String, Scheme>,
    constructors: HashMap<String, Scheme>,
    /// Type aliases: Name -> Scheme (e.g. Point -> { x: I64, y: I64 })
    type_aliases: HashMap<String, Scheme>,
    /// Declared type annotations for checking against inferred types.
    type_annos: HashMap<String, TypeExpr<'src>>,
    /// Known type names (I64, Bool, List, user-defined types).
    known_types: std::collections::HashSet<String>,
    /// Track integer literal type vars for defaulting and side table.
    int_literal_vars: Vec<(TypeVar, Span)>,
    /// Track float literal type vars for defaulting and side table.
    float_literal_vars: Vec<(TypeVar, Span)>,
    /// Bindings from `is` expressions, indexed by the Is expression's span.
    is_bindings: HashMap<Span, Vec<(String, Type)>>,
    /// Resolved method calls: span → mangled method name.
    method_resolutions: HashMap<Span, String>,
    /// Span for each constraint (parallel to engine.constraints).
    constraint_spans: Vec<Span>,
    /// Raw (possibly unresolved) types for each expression, keyed by span.
    /// Resolved to concrete types at the end of inference.
    expr_types: HashMap<Span, Type>,
    /// Constructor references that should be eta-expanded by the
    /// post-inference rewrite. Populated by `check_expr` when a bare
    /// `Name(con_sym)` is checked against an arrow type and the
    /// constructor needs to be upgraded from a nullary value to a
    /// function. Keyed by the `Name` expression's span so the rewrite
    /// can find and replace it later.
    eta_expansions: HashMap<Span, EtaInfo>,
    /// Stack of enclosing function / lambda return types. The top of
    /// the stack is the return type of the innermost enclosing
    /// function body currently being inferred; `return` statements
    /// (arm-level `is_return` and `Stmt::Guard::return_val`) unify
    /// their value against it. Push in `infer_func_body` and
    /// `ExprKind::Lambda`; pop on exit.
    ret_ty_stack: Vec<Type>,
    /// Borrowed symbol table for display-name lookups.
    symbols: &'a SymbolTable,
    /// Borrowed field interner for recovering source names at the
    /// engine boundary (engine stores record fields as `String`).
    fields: &'a FieldInterner,
}

impl<'a, 'src> InferCtx<'a, 'src> {
    fn new(symbols: &'a SymbolTable, fields: &'a FieldInterner) -> Self {
        Self {
            engine: TypeEngine::new(),
            env: HashMap::new(),
            constructors: HashMap::new(),
            type_aliases: HashMap::new(),
            type_annos: HashMap::new(),
            known_types: std::collections::HashSet::new(),
            int_literal_vars: Vec::new(),
            float_literal_vars: Vec::new(),
            is_bindings: HashMap::new(),
            method_resolutions: HashMap::new(),
            constraint_spans: Vec::new(),
            expr_types: HashMap::new(),
            eta_expansions: HashMap::new(),
            ret_ty_stack: Vec::new(),
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
        let scheme = self
            .constructors
            .get(func)
            .cloned()
            .or_else(|| self.env.get(func).cloned());
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
        }
    }

    // ---- Extracted match arms from infer_expr_inner ----

    fn infer_block(
        &mut self,
        stmts: &[Stmt<'src>],
        result: &Expr<'src>,
    ) -> Result<Type, CompileError> {
        let saved_env = self.env.clone();
        let mut pending_hints: HashMap<String, TypeExpr<'src>> = HashMap::new();
        for stmt in stmts {
            match stmt {
                Stmt::TypeHint { name, ty } => {
                    pending_hints.insert((*name).to_owned(), ty.clone());
                }
                Stmt::Let { name, val } => {
                    let name_str = self.symbols.display(*name).to_owned();
                    let val_ty = self.infer_expr(val)?;
                    if let Some(hint) = pending_hints.remove(&name_str) {
                        let hint_ty = self.resolve_type_expr(&hint)?;
                        self.unify_expected(
                            &val_ty,
                            &hint_ty,
                            val.span,
                            &format!("let binding `{name_str}`"),
                        )?;
                    }
                    // Value restriction: only generalize let bindings
                    // whose value is syntactically a function.
                    let scheme = if is_syntactic_value(val) {
                        self.engine.generalize(&val_ty, &self.env)
                    } else {
                        Scheme::mono(val_ty)
                    };
                    self.env.insert(name_str, scheme);
                }
                Stmt::Destructure { pattern, val } => {
                    let val_ty = self.infer_expr(val)?;
                    let bindings = self.infer_pattern(pattern, &val_ty, val.span, None)?;
                    let is_value = is_syntactic_value(val);
                    for (sym, ty) in bindings {
                        let name = self.symbols.display(sym).to_owned();
                        let scheme = if is_value {
                            self.engine.generalize(&ty, &self.env)
                        } else {
                            Scheme::mono(ty)
                        };
                        self.env.insert(name, scheme);
                    }
                }
                Stmt::Guard {
                    condition,
                    return_val,
                } => {
                    let cond_ty = self.infer_expr(condition)?;
                    let bool_ty = Type::Con("Bool".to_owned());
                    self.unify_at(&cond_ty, &bool_ty, condition.span)?;
                    let guard_saved_env = self.env.clone();
                    self.collect_is_bindings(condition);
                    let ret_val_ty = self.infer_expr(return_val)?;
                    if let Some(fn_ret) = self.ret_ty_stack.last().cloned() {
                        self.unify_expected(
                            &ret_val_ty,
                            &fn_ret,
                            return_val.span,
                            "`return` value of guard clause",
                        )?;
                    }
                    self.env = guard_saved_env;
                }
            }
        }
        let result_ty = self.infer_expr(result)?;
        self.env = saved_env;
        Ok(result_ty)
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
            let saved_env = self.env.clone();
            for (sym, ty) in bindings {
                let name = self.symbols.display(sym).to_owned();
                self.env.insert(name, Scheme::mono(ty));
            }
            if let ast::Pattern::Constructor { name: "True", .. } = &arm.pattern {
                self.collect_is_bindings(scrutinee);
            }
            for guard_expr in &arm.guards {
                let guard_ty = self.infer_expr(guard_expr)?;
                self.unify_at(&guard_ty, &bool_ty, guard_expr.span)?;
                self.collect_is_bindings(guard_expr);
            }
            let body_ty = self.infer_expr(&arm.body)?;
            if arm.is_return {
                if let Some(fn_ret) = self.ret_ty_stack.last().cloned() {
                    self.unify_expected(
                        &body_ty,
                        &fn_ret,
                        arm.body.span,
                        "`return` value of match arm",
                    )?;
                }
            } else {
                self.unify_expected(&body_ty, &result_ty, arm.body.span, "match arm body")?;
            }
            self.env = saved_env;
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
            let saved_env = self.env.clone();
            for (sym, ty) in bindings {
                let name = self.symbols.display(sym).to_owned();
                self.env.insert(name, Scheme::mono(ty));
            }
            for guard_expr in &arm.guards {
                let guard_ty = self.infer_expr(guard_expr)?;
                self.unify_at(&guard_ty, &bool_ty, guard_expr.span)?;
                self.collect_is_bindings(guard_expr);
            }
            let body_ty = self.infer_expr(&arm.body)?;
            self.unify_expected(&body_ty, &result_ty, arm.body.span, "fold arm body")?;
            self.env = saved_env;
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
        let saved_env = flow_is_bindings.then(|| {
            let saved = self.env.clone();
            self.collect_is_bindings(lhs);
            saved
        });
        let rhs_ty = self.infer_expr(rhs)?;
        self.unify_at(&rhs_ty, &bool_ty, rhs.span)?;
        if let Some(saved) = saved_env {
            self.env = saved;
        }
        Ok(bool_ty)
    }

    fn infer_name(&mut self, sym: SymbolId, span: Span) -> Result<Type, CompileError> {
        let name = self.symbols.display(sym);
        if let Some(scheme) = self.env.get(name).cloned() {
            return Ok(self.engine.instantiate(&scheme));
        }
        if let Some(scheme) = self.constructors.get(name).cloned() {
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
        let saved_env = self.env.clone();
        let param_types: Vec<Type> = params
            .iter()
            .zip(expected_params.iter())
            .map(|(p, expected_ty)| {
                let name = self.symbols.display(*p).to_owned();
                self.env.insert(name, Scheme::mono(expected_ty.clone()));
                expected_ty.clone()
            })
            .collect();
        let ret = self.engine.fresh();
        self.ret_ty_stack.push(ret.clone());
        let body_ty = self.infer_expr(body)?;
        self.ret_ty_stack.pop();
        self.unify_at(&ret, &body_ty, body.span)?;
        self.unify_at(&ret, expected_ret, span)?;
        self.env = saved_env;
        Ok(Type::Arrow(param_types, Box::new(ret)))
    }

    fn infer_lambda(
        &mut self,
        params: &[SymbolId],
        body: &Expr<'src>,
    ) -> Result<Type, CompileError> {
        let saved_env = self.env.clone();
        let param_types: Vec<Type> = params
            .iter()
            .map(|p| {
                let ty = self.engine.fresh();
                let name = self.symbols.display(*p).to_owned();
                self.env.insert(name, Scheme::mono(ty.clone()));
                ty
            })
            .collect();
        let ret = self.engine.fresh();
        self.ret_ty_stack.push(ret.clone());
        let body_ty = self.infer_expr(body)?;
        self.ret_ty_stack.pop();
        self.unify_at(&ret, &body_ty, body.span)?;
        self.env = saved_env;
        Ok(Type::Arrow(param_types, Box::new(ret)))
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

        if let Some(scheme) = self.constructors.get(func).cloned() {
            let con_ty = self.engine.instantiate(&scheme);
            if arg_types.is_empty() {
                // Nullary constructor called with parens
                return Ok(con_ty);
            }
            let expected = Type::Arrow(arg_types, Box::new(ret.clone()));
            self.unify_at(&con_ty, &expected, span)?;
            return Ok(ret);
        }

        if let Some(scheme) = self.env.get(func).cloned() {
            let func_ty = self.engine.instantiate(&scheme);
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

        // Method call on a type variable: x.method(args) → generate constraint
        if let Some(dot_pos) = func.find('.') {
            let var_name = &func[..dot_pos];
            let method_name = &func[dot_pos + 1..];
            if let Some(scheme) = self.env.get(var_name).cloned() {
                let var_ty = self.engine.instantiate(&scheme);
                let resolved = self.engine.resolve(&var_ty);
                if let Type::Var(tv) = resolved {
                    // Generate constraint: tv.method_name : (tv, args...) -> ret
                    let mut param_types = vec![Type::Var(tv)];
                    param_types.extend(arg_types);
                    let method_type = Type::Arrow(param_types, Box::new(ret.clone()));
                    self.push_constraint(
                        Constraint {
                            type_var: tv,
                            method_name: method_name.to_owned(),
                            method_type,
                        },
                        span,
                    );
                    return Ok(ret);
                }
                // Resolved to a concrete type: look up Type.method
                if let Type::Con(concrete_name) | Type::App(concrete_name, _) = &resolved {
                    let mangled = format!("{concrete_name}.{method_name}");
                    if let Some(scheme) = self.env.get(&mangled).cloned() {
                        let func_ty = self.engine.instantiate(&scheme);
                        let mut full_args = vec![var_ty];
                        full_args.extend(arg_types);
                        let expected = Type::Arrow(full_args, Box::new(ret.clone()));
                        self.unify_at(&func_ty, &expected, span)?;
                        let resolution = if Self::is_numeric_builtin(concrete_name, method_name) {
                            format!("__builtin.{method_name}")
                        } else {
                            mangled
                        };
                        self.method_resolutions.insert(span, resolution);
                        return Ok(ret);
                    }
                }
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
        let ret = self.engine.fresh();
        let resolved = self.engine.resolve(&recv_ty);
        // Concrete type: look up Type.method in env. For numeric
        // builtins, write `__builtin.<method>` so the lowerer emits
        // an SSA op instead of a function call.
        if let Type::Con(name) | Type::App(name, _) = &resolved {
            let mangled = format!("{name}.{method}");
            if let Some(scheme) = self.env.get(&mangled).cloned() {
                let func_ty = self.engine.instantiate(&scheme);
                let mut full_args = vec![recv_ty];
                full_args.extend(arg_types);
                let expected = Type::Arrow(full_args, Box::new(ret.clone()));
                self.unify_at(&func_ty, &expected, span)?;
                let resolution = if Self::is_numeric_builtin(name, method) {
                    format!("__builtin.{method}")
                } else {
                    mangled
                };
                self.method_resolutions.insert(span, resolution);
                return Ok(ret);
            }
        }

        // Type variable: generate constraint
        if let Type::Var(tv) = resolved {
            let mut param_types = vec![Type::Var(tv)];
            param_types.extend(arg_types);
            let method_type = Type::Arrow(param_types, Box::new(ret.clone()));
            self.push_constraint(
                Constraint {
                    type_var: tv,
                    method_name: (*method).to_owned(),
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
        let saved_env = self.env.clone();

        // Zero-param bindings are value bindings, not zero-arg functions.
        // Infer the body directly and register the result type (not
        // wrapped in Arrow). If there's a type annotation, unify with it.
        if params.is_empty() {
            let body_ty = self.infer_expr(body)?;
            if let Some(anno) = self.type_annos.get(name).cloned() {
                let anno_ty = self.resolve_type_expr(&anno)?;
                self.unify_expected(
                    &body_ty,
                    &anno_ty,
                    body.span,
                    &format!("value `{name}`"),
                )?;
            }
            self.env = saved_env;
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
        let func_ty = if let Some(pre_scheme) = self.env.get(name).cloned() {
            self.engine.instantiate(&pre_scheme)
        } else {
            let param_types: Vec<Type> = params.iter().map(|_| self.engine.fresh()).collect();
            let ret = self.engine.fresh();
            let func_ty = Type::Arrow(param_types, Box::new(ret));
            self.env
                .insert(name.to_owned(), Scheme::mono(func_ty.clone()));
            func_ty
        };

        let param_types: Vec<Type> = params.iter().map(|_| self.engine.fresh()).collect();
        let ret = self.engine.fresh();
        let expected = Type::Arrow(param_types.clone(), Box::new(ret.clone()));
        self.unify_at(&func_ty, &expected, body.span)?;

        for (p, ty) in params.iter().zip(param_types.iter()) {
            let pname = self.symbols.display(*p).to_owned();
            self.env.insert(pname, Scheme::mono(ty.clone()));
        }
        // Push the return type so any `return` statement inside the
        // body can flow its value here. Use check_expr to push the
        // expected return type into lambdas bidirectionally — this
        // enables opaque type transparency (e.g. Parser(a) → Arrow)
        // to flow into nested lambda param types.
        self.ret_ty_stack.push(ret.clone());
        let body_ty = self.check_expr(body, &ret, Some((name, 0)))?;
        self.ret_ty_stack.pop();
        self.unify_expected(
            &body_ty,
            &ret,
            body.span,
            &format!("body of function `{name}`"),
        )?;

        // If there's an annotation, unify with it and use it as
        // the external type. A mismatch here is the classic
        // "function body doesn't match its signature" error —
        // attribute it to the function name so the user knows
        // which definition is wrong, not just that a unify failed.
        let external_ty = if let Some(anno) = self.type_annos.get(name).cloned() {
            let anno_ty = self.resolve_type_expr(&anno)?;
            self.unify_expected(
                &func_ty,
                &anno_ty,
                body.span,
                &format!("function `{name}`"),
            )?;
            anno_ty
        } else {
            self.engine.resolve(&func_ty)
        };

        self.env = saved_env;
        self.env.remove(name);

        let generalized = self.engine.generalize(&external_ty, &self.env);
        self.env.insert(name.to_owned(), generalized);
        Ok(())
    }

    /// True if `type_name.method` is a compiler-intrinsic numeric
    /// method that should resolve to `__builtin.<method>` instead of
    /// the env-provided scheme name.
    fn is_numeric_builtin(type_name: &str, method: &str) -> bool {
        crate::numeric::NumericType::from_name(type_name)
            .is_some_and(|num| num.has_builtin_method(method))
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
            if Self::is_numeric_builtin(type_name, method) {
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
                let (Type::Con(type_name) | Type::App(type_name, _)) = &resolved else {
                    still_remaining.push(i);
                    continue;
                };
            let maybe_span = self.constraint_spans.get(i).copied();
            let mangled = format!("{type_name}.{}", c.method_name);
            if let Some(scheme) = self.env.get(&mangled).cloned() {
                // Unify the constraint's method type with the actual method signature
                // so that arg types (e.g. index literals) resolve correctly.
                let actual_ty = self.engine.instantiate(&scheme);
                drop(self.engine.unify(&c.method_type, &actual_ty));
                if let Some(s) = maybe_span {
                    let resolution = if Self::is_numeric_builtin(type_name, &c.method_name) {
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
pub fn check<'src>(
    arena: &'src SourceArena,
    module: &mut Module<'src>,
    scope: &crate::resolve::ModuleScope,
    symbols: &mut crate::symbol::SymbolTable,
    fields: &FieldInterner,
) -> Result<InferResult, CompileError> {
    // Inference itself only needs an immutable view of the symbol
    // table. The post-pass that eta-expands constructor references
    // allocates fresh lambda parameter syms, which is why `check`
    // takes `&mut`.
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
                // Register method signatures and collect method annotations
                for method in methods {
                    match method {
                        Decl::FuncDef {
                            name: method_name,
                            params,
                            ..
                        } => {
                            let method_name = symbols.display(*method_name);
                            let mangled = method_key(name, method_name);
                            // Only register a fresh arrow if the
                            // preceding `TypeAnno` arm didn't already
                            // resolve an annotation to a proper scheme —
                            // otherwise we'd overwrite the user's
                            // declared type with a fresh unconstrained
                            // arrow and lose the annotation.
                            if !ctx.env.contains_key(&mangled) {
                                let param_types: Vec<Type> =
                                    params.iter().map(|_| ctx.engine.fresh()).collect();
                                let ret = ctx.engine.fresh();
                                let func_ty = Type::Arrow(param_types, Box::new(ret));
                                ctx.env.insert(mangled.clone(), Scheme::mono(func_ty));
                            }
                            // Dual-register: module-qualified alias
                            if let Some(mod_name) = scope.qualified_types.get(name) {
                                let qual = format!("{mod_name}.{mangled}");
                                if let Some(scheme) = ctx.env.get(&mangled).cloned() {
                                    ctx.env.insert(qual, scheme);
                                }
                            }
                        }
                        Decl::TypeAnno {
                            name: method_name,
                            ty,
                            ..
                        } => {
                            let method_name = symbols.display(*method_name);
                            let mangled = method_key(name, method_name);
                            if let Some(mod_name) = scope.qualified_types.get(name) {
                                let qual = format!("{mod_name}.{mangled}");
                                ctx.type_annos.insert(qual, ty.clone());
                            }
                            ctx.type_annos.insert(mangled.clone(), ty.clone());
                            // Eagerly resolve the annotation to a concrete
                            // scheme so callers see the intended type,
                            // not a fresh arrow that later unifications
                            // might pollute. This used to only happen
                            // for stdlib methods; post-Step 5, free
                            // functions are inferred before methods, so
                            // user methods need the same early resolution
                            // to avoid call-site contamination.
                            let mut tvar_env = HashMap::new();
                            let anno_ty = ctx.type_expr_to_type(ty, &mut tvar_env)?;
                            let tvars: Vec<_> = tvar_env.into_values().collect();
                            let scheme = Scheme {
                                vars: tvars,
                                constraints: vec![],
                                ty: anno_ty,
                            };
                            ctx.env.insert(mangled, scheme);
                        }
                    }
                }
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
                    // Register methods
                    for method in methods {
                        match method {
                            Decl::FuncDef {
                                name: method_name,
                                params,
                                ..
                            } => {
                                let method_name = symbols.display(*method_name);
                                let mangled = method_key(name, method_name);
                                // See the tag-union branch above: don't
                                // overwrite a scheme already inserted
                                // from the method's TypeAnno annotation.
                                if !ctx.env.contains_key(&mangled) {
                                    let param_types: Vec<Type> =
                                        params.iter().map(|_| ctx.engine.fresh()).collect();
                                    let ret = ctx.engine.fresh();
                                    let func_ty = Type::Arrow(param_types, Box::new(ret));
                                    ctx.env.insert(mangled, Scheme::mono(func_ty));
                                }
                            }
                            Decl::TypeAnno {
                                name: method_name,
                                ty: method_ty,
                                ..
                            } => {
                                let method_name = symbols.display(*method_name);
                                let mangled = method_key(name, method_name);
                                ctx.type_annos.insert(mangled.clone(), method_ty.clone());
                                // Eagerly resolve the annotation (see the
                                // tag-union branch above for the rationale).
                                let mut tvar_env = HashMap::new();
                                let anno_ty = ctx.type_expr_to_type(method_ty, &mut tvar_env)?;
                                let tvars: Vec<_> = tvar_env.into_values().collect();
                                let scheme = Scheme {
                                    vars: tvars,
                                    constraints: vec![],
                                    ty: anno_ty,
                                };
                                ctx.env.insert(mangled, scheme);
                            }
                        }
                    }
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
            methods,
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
            let func_names: std::collections::HashSet<&str> = methods
                .iter()
                .filter_map(|m| {
                    if let Decl::FuncDef { name, .. } = m {
                        Some(symbols.display(*name))
                    } else {
                        None
                    }
                })
                .collect();
            for method in methods {
                if let Decl::TypeAnno {
                    span: method_span,
                    name: method_name,
                    ..
                } = method
                {
                    let method_name = symbols.display(*method_name);
                    if !func_names.contains(method_name) {
                        let is_stdlib = arena.path(method_span.file).starts_with("<stdlib:");
                        if !is_stdlib {
                            return Err(CompileError::at(
                                *method_span,
                                format!("method '{name}.{method_name}' declared but not defined"),
                            ));
                        }
                    }
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
    // This map is consumed by `write_types_back` below and is not part of
    // the public `InferResult`.
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

    // Write resolved types back onto Expr::ty so downstream passes can
    // read types directly from the AST.
    write_types_back(module, &expr_types);
    // Write method resolutions onto MethodCall / QualifiedCall nodes.
    write_resolutions_back(module, &ctx.method_resolutions);

    // Eta-expand constructor references that were checked against an
    // arrow type. `check_expr` marked the spans; this rewrite walks
    // the module and replaces each marked `Name` with an explicit
    // `Lambda` wrapping a `Call` to the constructor. Allocates fresh
    // lambda parameter symbols from `symbols`, which is why `check`
    // takes `&mut SymbolTable`.
    if !ctx.eta_expansions.is_empty() {
        eta_expand_con_refs(module, &ctx.eta_expansions, symbols);
    }

    Ok(InferResult {
        func_schemes,
        constructor_schemes,
    })
}

// ---- Eta-expansion of constructor references ----

/// Rewrite `Name(con_sym)` expressions marked by `check_expr` into
/// explicit `Lambda` wrappers. See `EtaInfo` and `check_expr` for the
/// inference-side bookkeeping; this is the mutation side.
///
/// For an expression at span `S` marked with `EtaInfo { con_sym,
/// arrow_ty: Arrow([T1, T2, ..., Tn], ret) }`, rewrite to
///
/// ```ignore
/// Lambda {
///     params: [p1, p2, ..., pn],
///     body: Call { target: con_sym, args: [Name(p1), Name(p2), ...] }
/// }
/// ```
///
/// Types on the synthesized nodes come from the stored arrow: the
/// lambda itself has type `arrow_ty`, each param Name has the
/// corresponding `T_i`, and the inner Call has type `ret`.
fn eta_expand_con_refs(
    module: &mut Module<'_>,
    eta: &HashMap<Span, EtaInfo>,
    symbols: &mut SymbolTable,
) {
    for decl in &mut module.decls {
        eta_expand_decl(decl, eta, symbols);
    }
}

fn eta_expand_decl(
    decl: &mut Decl<'_>,
    eta: &HashMap<Span, EtaInfo>,
    symbols: &mut SymbolTable,
) {
    match decl {
        Decl::FuncDef { body, .. } => eta_expand_expr(body, eta, symbols),
        Decl::TypeAnno { methods, .. } => {
            for m in methods {
                eta_expand_decl(m, eta, symbols);
            }
        }
    }
}

fn eta_expand_expr(
    expr: &mut Expr<'_>,
    eta: &HashMap<Span, EtaInfo>,
    symbols: &mut SymbolTable,
) {
    // First recurse into children so inner constructor references
    // are rewritten before we consider the current node.
    match &mut expr.kind {
        ExprKind::IntLit(_)
        | ExprKind::FloatLit(_)
        | ExprKind::StrLit(_)
        | ExprKind::Name(_) => {}
        ExprKind::BinOp { lhs, rhs, .. } => {
            eta_expand_expr(lhs, eta, symbols);
            eta_expand_expr(rhs, eta, symbols);
        }
        ExprKind::Call { args, .. } | ExprKind::QualifiedCall { args, .. } => {
            for a in args {
                eta_expand_expr(a, eta, symbols);
            }
        }
        ExprKind::Block(stmts, result) => {
            for stmt in stmts {
                match stmt {
                    Stmt::Let { val, .. } | Stmt::Destructure { val, .. } => {
                        eta_expand_expr(val, eta, symbols);
                    }
                    Stmt::Guard {
                        condition,
                        return_val,
                    } => {
                        eta_expand_expr(condition, eta, symbols);
                        eta_expand_expr(return_val, eta, symbols);
                    }
                    Stmt::TypeHint { .. } => {}
                }
            }
            eta_expand_expr(result, eta, symbols);
        }
        ExprKind::If {
            expr: scrutinee,
            arms,
            else_body,
        } => {
            eta_expand_expr(scrutinee, eta, symbols);
            for arm in arms {
                for g in &mut arm.guards {
                    eta_expand_expr(g, eta, symbols);
                }
                eta_expand_expr(&mut arm.body, eta, symbols);
            }
            if let Some(eb) = else_body {
                eta_expand_expr(eb, eta, symbols);
            }
        }
        ExprKind::Fold {
            expr: scrutinee,
            arms,
        } => {
            eta_expand_expr(scrutinee, eta, symbols);
            for arm in arms {
                for g in &mut arm.guards {
                    eta_expand_expr(g, eta, symbols);
                }
                eta_expand_expr(&mut arm.body, eta, symbols);
            }
        }
        ExprKind::Lambda { body, .. } => eta_expand_expr(body, eta, symbols),
        ExprKind::Record { fields } => {
            for (_, e) in fields {
                eta_expand_expr(e, eta, symbols);
            }
        }
        ExprKind::FieldAccess { record, .. } => eta_expand_expr(record, eta, symbols),
        ExprKind::Tuple(elems) | ExprKind::ListLit(elems) => {
            for e in elems {
                eta_expand_expr(e, eta, symbols);
            }
        }
        ExprKind::MethodCall { receiver, args, .. } => {
            eta_expand_expr(receiver, eta, symbols);
            for a in args {
                eta_expand_expr(a, eta, symbols);
            }
        }
        ExprKind::Is { expr: inner, .. } => {
            eta_expand_expr(inner, eta, symbols);
        }
        ExprKind::RecordUpdate { base, updates } => {
            eta_expand_expr(base, eta, symbols);
            for (_, e) in updates {
                eta_expand_expr(e, eta, symbols);
            }
        }
    }

    // Post-order rewrite: replace marked callable references
    // (Name → constructor, FieldAccess → method) with synthesized
    // Lambdas. The arrow type comes from `expr.ty` which was
    // resolved by `write_types_back` immediately before this pass
    // runs, so any post-creation unification on the reference's
    // type flows through automatically.
    if let Some(info) = eta.get(&expr.span)
        && matches!(
            &expr.kind,
            ExprKind::Name(_) | ExprKind::FieldAccess { .. }
        )
        && matches!(&expr.ty, Type::Arrow(_, _))
    {
        rewrite_callable_ref_to_lambda(expr, info, symbols);
    }
}

/// Replace a marked callable reference (either a bare constructor
/// `Name` or a `Type.method` `FieldAccess`) with an explicit Lambda
/// that forwards its arguments to the underlying call.
///
/// Assumes the caller has verified that `expr.ty` is an `Arrow`
/// and that `expr.kind` is one of the two supported reference
/// shapes. The arrow's parameter count determines the lambda's
/// arity; fresh `SymbolId`s are allocated for each parameter.
fn rewrite_callable_ref_to_lambda(
    expr: &mut Expr<'_>,
    info: &EtaInfo,
    symbols: &mut SymbolTable,
) {
    let Type::Arrow(param_types, ret_ty) = expr.ty.clone() else {
        unreachable!("caller checked expr.ty is Arrow");
    };
    let span = expr.span;
    let param_syms: Vec<SymbolId> = (0..param_types.len())
        .map(|i| {
            let name = format!("__eta_{i}");
            symbols.fresh(name, span, SymbolKind::Local)
        })
        .collect();
    let call_args: Vec<Expr<'_>> = param_syms
        .iter()
        .zip(param_types.iter())
        .map(|(sym, ty)| {
            let mut name_expr = Expr::new(ExprKind::Name(*sym), span);
            name_expr.ty = ty.clone();
            name_expr
        })
        .collect();

    // Build the inner call based on which kind of reference we
    // have. Constructors emit `Call { target, args }`; methods
    // emit `QualifiedCall { segments, args, resolved }` so the
    // existing method dispatch pipeline in mono and lowering
    // picks them up the same way a hand-written call would.
    let inner_kind = match info {
        EtaInfo::Constructor { con_sym } => ExprKind::Call {
            target: *con_sym,
            args: call_args,
        },
        EtaInfo::Method {
            type_name,
            method_name,
        } => {
            // Leak segment strings to 'static so they satisfy the
            // 'src lifetime of the AST. Parse-time synthesized
            // names already follow this pattern (fold_lift,
            // desugar_try). Leak cost is O(methods-passed-as-args).
            let type_seg: &'static str =
                Box::leak(type_name.clone().into_boxed_str());
            let method_seg: &'static str =
                Box::leak(method_name.clone().into_boxed_str());
            // Numeric builtin methods (`I64.add` etc.) are dispatched
            // via the `__builtin.<op>` marker that `resolve_numeric_builtin`
            // and the method-call path already use; populating it here
            // lets the lowerer's existing `strip_prefix("__builtin.")`
            // handle the eta-expanded call uniformly with hand-written
            // `x.add(y)` method calls. Non-numeric method references
            // leave `resolved` at `None` so normal function-call
            // dispatch handles them.
            let resolved =
                InferCtx::is_numeric_builtin(type_name, method_name)
                    .then(|| format!("__builtin.{method_name}"));
            ExprKind::QualifiedCall {
                segments: vec![type_seg, method_seg],
                args: call_args,
                resolved,
            }
        }
    };
    let mut inner_expr = Expr::new(inner_kind, span);
    inner_expr.ty = *ret_ty;

    expr.kind = ExprKind::Lambda {
        params: param_syms,
        body: Box::new(inner_expr),
    };
    // `expr.ty` is already the correct arrow type — set when
    // inference populated expr_types and copied back.
}

// ---- Write-back of resolved types onto AST nodes ----

/// Walk `module` and copy each expression's resolved type from `expr_types`
/// into its `Expr::ty` field. `expr_types` already contains fully-resolved
/// types (including defaulted numeric literals), so this is a simple
/// span-keyed lookup on every `Expr` node we encounter.
fn write_types_back(module: &mut Module<'_>, expr_types: &HashMap<Span, Type>) {
    for decl in &mut module.decls {
        write_back_decl(decl, expr_types);
    }
}

fn write_back_decl(decl: &mut Decl<'_>, expr_types: &HashMap<Span, Type>) {
    match decl {
        Decl::FuncDef { body, .. } => write_back_expr(body, expr_types),
        Decl::TypeAnno { methods, .. } => {
            for m in methods {
                write_back_decl(m, expr_types);
            }
        }
    }
}

fn write_back_expr(expr: &mut Expr<'_>, expr_types: &HashMap<Span, Type>) {
    if let Some(ty) = expr_types.get(&expr.span) {
        expr.ty = ty.clone();
    }
    match &mut expr.kind {
        ExprKind::IntLit(_) | ExprKind::FloatLit(_) | ExprKind::StrLit(_) | ExprKind::Name(_) => {}
        ExprKind::BinOp { lhs, rhs, .. } => {
            write_back_expr(lhs, expr_types);
            write_back_expr(rhs, expr_types);
        }
        ExprKind::Call { args, .. } | ExprKind::QualifiedCall { args, .. } => {
            for a in args {
                write_back_expr(a, expr_types);
            }
        }
        ExprKind::Block(stmts, result) => {
            for s in stmts {
                write_back_stmt(s, expr_types);
            }
            write_back_expr(result, expr_types);
        }
        ExprKind::If {
            expr: scrutinee,
            arms,
            else_body,
        } => {
            write_back_expr(scrutinee, expr_types);
            for arm in arms {
                write_back_arm(arm, expr_types);
            }
            if let Some(eb) = else_body {
                write_back_expr(eb, expr_types);
            }
        }
        ExprKind::Fold {
            expr: scrutinee,
            arms,
        } => {
            write_back_expr(scrutinee, expr_types);
            for arm in arms {
                write_back_arm(arm, expr_types);
            }
        }
        ExprKind::Lambda { body, .. } => write_back_expr(body, expr_types),
        ExprKind::Record { fields } => {
            for (_, e) in fields {
                write_back_expr(e, expr_types);
            }
        }
        ExprKind::FieldAccess { record, .. } => write_back_expr(record, expr_types),
        ExprKind::Tuple(elems) | ExprKind::ListLit(elems) => {
            for e in elems {
                write_back_expr(e, expr_types);
            }
        }
        ExprKind::MethodCall { receiver, args, .. } => {
            write_back_expr(receiver, expr_types);
            for a in args {
                write_back_expr(a, expr_types);
            }
        }
        ExprKind::Is { expr: inner, .. } => write_back_expr(inner, expr_types),
        ExprKind::RecordUpdate { base, updates } => {
            write_back_expr(base, expr_types);
            for (_, e) in updates {
                write_back_expr(e, expr_types);
            }
        }
    }
}

fn write_back_arm(arm: &mut ast::MatchArm<'_>, expr_types: &HashMap<Span, Type>) {
    for g in &mut arm.guards {
        write_back_expr(g, expr_types);
    }
    write_back_expr(&mut arm.body, expr_types);
}

fn write_back_stmt(stmt: &mut Stmt<'_>, expr_types: &HashMap<Span, Type>) {
    match stmt {
        Stmt::Let { val, .. } | Stmt::Destructure { val, .. } => {
            write_back_expr(val, expr_types);
        }
        Stmt::Guard {
            condition,
            return_val,
        } => {
            write_back_expr(condition, expr_types);
            write_back_expr(return_val, expr_types);
        }
        Stmt::TypeHint { .. } => {}
    }
}

// ---- Write-back of method resolutions onto AST nodes ----

/// Walk `module` and copy each `MethodCall`/`QualifiedCall` resolution
/// from the side table onto the node's `resolved` field.
fn write_resolutions_back(module: &mut Module<'_>, resolutions: &HashMap<Span, String>) {
    for decl in &mut module.decls {
        write_res_decl(decl, resolutions);
    }
}

fn write_res_decl(decl: &mut Decl<'_>, resolutions: &HashMap<Span, String>) {
    match decl {
        Decl::FuncDef { body, .. } => write_res_expr(body, resolutions),
        Decl::TypeAnno { methods, .. } => {
            for m in methods {
                write_res_decl(m, resolutions);
            }
        }
    }
}

fn write_res_expr(expr: &mut Expr<'_>, resolutions: &HashMap<Span, String>) {
    let span = expr.span;
    match &mut expr.kind {
        ExprKind::QualifiedCall { args, resolved, .. } => {
            if let Some(r) = resolutions.get(&span) {
                *resolved = Some(r.clone());
            }
            for a in args {
                write_res_expr(a, resolutions);
            }
        }
        ExprKind::MethodCall {
            receiver,
            args,
            resolved,
            ..
        } => {
            if let Some(r) = resolutions.get(&span) {
                *resolved = Some(r.clone());
            }
            write_res_expr(receiver, resolutions);
            for a in args {
                write_res_expr(a, resolutions);
            }
        }
        ExprKind::IntLit(_) | ExprKind::FloatLit(_) | ExprKind::StrLit(_) | ExprKind::Name(_) => {}
        ExprKind::BinOp { lhs, rhs, .. } => {
            write_res_expr(lhs, resolutions);
            write_res_expr(rhs, resolutions);
        }
        ExprKind::Call { args, .. } => {
            for a in args {
                write_res_expr(a, resolutions);
            }
        }
        ExprKind::Block(stmts, result) => {
            for s in stmts {
                write_res_stmt(s, resolutions);
            }
            write_res_expr(result, resolutions);
        }
        ExprKind::If {
            expr: scrutinee,
            arms,
            else_body,
        } => {
            write_res_expr(scrutinee, resolutions);
            for arm in arms {
                write_res_arm(arm, resolutions);
            }
            if let Some(eb) = else_body {
                write_res_expr(eb, resolutions);
            }
        }
        ExprKind::Fold {
            expr: scrutinee,
            arms,
        } => {
            write_res_expr(scrutinee, resolutions);
            for arm in arms {
                write_res_arm(arm, resolutions);
            }
        }
        ExprKind::Lambda { body, .. } => write_res_expr(body, resolutions),
        ExprKind::Record { fields } => {
            for (_, e) in fields {
                write_res_expr(e, resolutions);
            }
        }
        ExprKind::FieldAccess { record, .. } => write_res_expr(record, resolutions),
        ExprKind::Tuple(elems) | ExprKind::ListLit(elems) => {
            for e in elems {
                write_res_expr(e, resolutions);
            }
        }
        ExprKind::Is { expr: inner, .. } => write_res_expr(inner, resolutions),
        ExprKind::RecordUpdate { base, updates } => {
            write_res_expr(base, resolutions);
            for (_, e) in updates {
                write_res_expr(e, resolutions);
            }
        }
    }
}

fn write_res_arm(arm: &mut ast::MatchArm<'_>, resolutions: &HashMap<Span, String>) {
    for g in &mut arm.guards {
        write_res_expr(g, resolutions);
    }
    write_res_expr(&mut arm.body, resolutions);
}

fn write_res_stmt(stmt: &mut Stmt<'_>, resolutions: &HashMap<Span, String>) {
    match stmt {
        Stmt::Let { val, .. } | Stmt::Destructure { val, .. } => {
            write_res_expr(val, resolutions);
        }
        Stmt::Guard {
            condition,
            return_val,
        } => {
            write_res_expr(condition, resolutions);
            write_res_expr(return_val, resolutions);
        }
        Stmt::TypeHint { .. } => {}
    }
}
