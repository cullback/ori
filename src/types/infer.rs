use std::collections::HashMap;

use crate::error::CompileError;
use crate::source::SourceArena;
use crate::syntax::ast::{
    self, BinOp, Decl, Expr, ExprKind, Module, Span, Stmt, TypeDeclKind, TypeExpr,
};
use crate::types::engine::{Constraint, Scheme, Type, TypeEngine, TypeVar};

/// Build a mangled key for a method on a type, e.g. `method_key("List", "sum")` -> `"List.sum"`.
fn method_key(type_name: &str, method: &str) -> String {
    format!("{type_name}.{method}")
}

/// Results of type inference, communicated to the lowerer.
pub struct InferResult {
    /// Resolved numeric types for literals (by span).
    pub lit_types: HashMap<Span, NumType>,
    /// Resolved method calls: span of qualified call → resolved mangled name.
    pub method_resolutions: HashMap<Span, String>,
    /// Fully-resolved concrete type for every expression (by span).
    /// Used by the lowerer for monomorphization and layout computation.
    pub expr_types: HashMap<Span, Type>,
    /// Resolved type schemes for all functions/methods.
    /// Used by the lowerer to compute type parameter mappings for specialization.
    pub func_schemes: HashMap<String, Scheme>,
    /// Constructor type schemes (e.g., Ok: forall ok err. ok -> Result(ok, err)).
    /// Used by the lowerer to compute concrete field types from instantiations.
    pub constructor_schemes: HashMap<String, Scheme>,
}

/// Resolved numeric type for a literal, used to communicate from inference to lowering.
#[derive(Debug, Clone, Copy)]
pub enum NumType {
    U8,
    I8,
    I64,
    U64,
    F64,
}

// ---- Inference context ----

struct InferCtx<'src> {
    engine: TypeEngine,
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
}

impl<'src> InferCtx<'src> {
    fn new() -> Self {
        Self {
            engine: TypeEngine::new(),
            env: HashMap::new(),
            constructors: HashMap::new(),
            type_aliases: HashMap::new(),
            type_annos: HashMap::new(),
            known_types: std::collections::HashSet::from([
                "U8".to_owned(),
                "I8".to_owned(),
                "I64".to_owned(),
                "U64".to_owned(),
                "F64".to_owned(),
            ]),
            int_literal_vars: Vec::new(),
            float_literal_vars: Vec::new(),
            is_bindings: HashMap::new(),
            method_resolutions: HashMap::new(),
            constraint_spans: Vec::new(),
            expr_types: HashMap::new(),
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

    // ---- Convert surface TypeExpr to inference Type ----

    /// Convert a type expression without pre-existing type variable bindings.
    fn resolve_type_expr(&mut self, texpr: &TypeExpr<'src>) -> Result<Type, CompileError> {
        self.type_expr_to_type(texpr, &mut HashMap::new())
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
            TypeExpr::TagUnion(_) => {
                // Inline tag unions in type expressions are not supported in inference yet
                Ok(self.engine.fresh())
            }
            TypeExpr::Record(fields) => {
                let mut type_fields = Vec::new();
                for (name, field_texpr) in fields {
                    let field_ty = self.type_expr_to_type(field_texpr, tvar_env)?;
                    type_fields.push(((*name).to_owned(), field_ty));
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

            ExprKind::Name(name) => {
                let name = *name;
                if let Some(scheme) = self.env.get(name).cloned() {
                    return Ok(self.engine.instantiate(&scheme));
                }
                if let Some(scheme) = self.constructors.get(name).cloned() {
                    return Ok(self.engine.instantiate(&scheme));
                }
                Err(Self::type_error(
                    expr.span,
                    &format!("undefined name '{name}'"),
                ))
            }

            ExprKind::BinOp {
                op: BinOp::And,
                lhs,
                rhs,
            } => {
                let lhs_ty = self.infer_expr(lhs)?;
                let bool_ty = Type::Con("Bool".to_owned());
                self.unify_at(&lhs_ty, &bool_ty, lhs.span)?;

                // Collect Is bindings from LHS and add to env for RHS
                let saved_env = self.env.clone();
                self.collect_is_bindings(lhs);

                let rhs_ty = self.infer_expr(rhs)?;
                self.unify_at(&rhs_ty, &bool_ty, rhs.span)?;
                self.env = saved_env;
                Ok(bool_ty)
            }

            ExprKind::BinOp {
                op: BinOp::Or,
                lhs,
                rhs,
            } => {
                let lhs_ty = self.infer_expr(lhs)?;
                let bool_ty = Type::Con("Bool".to_owned());
                self.unify_at(&lhs_ty, &bool_ty, lhs.span)?;
                let rhs_ty = self.infer_expr(rhs)?;
                self.unify_at(&rhs_ty, &bool_ty, rhs.span)?;
                Ok(bool_ty)
            }

            ExprKind::BinOp { op, lhs, rhs } => self.infer_binop(op, lhs, rhs, expr.span),

            ExprKind::Call { func, args } => {
                let func = *func;
                self.infer_call(func, args, expr.span)
            }

            ExprKind::QualifiedCall { segments, args } => {
                let mangled = segments.join(".");
                self.infer_call(&mangled, args, expr.span)
            }

            ExprKind::Block(stmts, result) => {
                let saved_env = self.env.clone();
                let mut pending_hints: HashMap<String, TypeExpr<'src>> = HashMap::new();
                for stmt in stmts {
                    match stmt {
                        Stmt::TypeHint { name, ty } => {
                            let name = *name;
                            pending_hints.insert(name.to_owned(), ty.clone());
                        }
                        Stmt::Let { name, val } => {
                            let name = *name;
                            let val_ty = self.infer_expr(val)?;
                            // If there's a type hint for this binding, enforce it
                            if let Some(hint) = pending_hints.remove(name) {
                                let hint_ty = self.resolve_type_expr(&hint)?;
                                self.unify_at(&val_ty, &hint_ty, val.span)?;
                            }
                            let scheme = self.engine.generalize(&val_ty, &self.env);
                            self.env.insert(name.to_owned(), scheme);
                        }
                        Stmt::Destructure { pattern, val } => {
                            let val_ty = self.infer_expr(val)?;
                            let bindings = self.infer_pattern(pattern, &val_ty, val.span, None)?;
                            for (name, ty) in bindings {
                                let scheme = self.engine.generalize(&ty, &self.env);
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
                            // Flow Is bindings from condition into return_val scope
                            let guard_saved_env = self.env.clone();
                            self.collect_is_bindings(condition);
                            // The return value must match the enclosing function's return type.
                            // For now, just infer it; the caller's context will unify as needed.
                            let _ret_ty = self.infer_expr(return_val)?;
                            self.env = guard_saved_env;
                        }
                    }
                }
                let result_ty = self.infer_expr(result)?;
                self.env = saved_env;
                Ok(result_ty)
            }

            ExprKind::If {
                expr: scrutinee,
                arms,
                ..
            } => {
                let scrutinee_ty = self.infer_expr(scrutinee)?;
                let result_ty = self.engine.fresh();
                let bool_ty = Type::Con("Bool".to_owned());
                for arm in arms {
                    let bindings =
                        self.infer_pattern(&arm.pattern, &scrutinee_ty, expr.span, None)?;
                    let saved_env = self.env.clone();
                    for (name, ty) in bindings {
                        self.env.insert(name, Scheme::mono(ty));
                    }
                    // For True arms of boolean if-then-else, flow Is bindings from scrutinee
                    if let ast::Pattern::Constructor { name: "True", .. } = &arm.pattern {
                        self.collect_is_bindings(scrutinee);
                    }
                    for guard_expr in &arm.guards {
                        let guard_ty = self.infer_expr(guard_expr)?;
                        self.unify_at(&guard_ty, &bool_ty, guard_expr.span)?;
                        // Flow Is bindings from guard into subsequent guards and arm body
                        self.collect_is_bindings(guard_expr);
                    }
                    let body_ty = self.infer_expr(&arm.body)?;
                    self.unify_at(&result_ty, &body_ty, arm.body.span)?;
                    self.env = saved_env;
                }
                Ok(result_ty)
            }

            ExprKind::Fold {
                expr: scrutinee,
                arms,
            } => {
                let scrutinee_ty = self.infer_expr(scrutinee)?;
                let result_ty = self.engine.fresh();
                let bool_ty = Type::Con("Bool".to_owned());
                for arm in arms {
                    // In fold, recursive fields bind to the result type, not the scrutinee type
                    let bindings = self.infer_pattern(
                        &arm.pattern,
                        &scrutinee_ty,
                        expr.span,
                        Some(&result_ty),
                    )?;
                    let saved_env = self.env.clone();
                    for (name, ty) in bindings {
                        self.env.insert(name, Scheme::mono(ty));
                    }
                    for guard_expr in &arm.guards {
                        let guard_ty = self.infer_expr(guard_expr)?;
                        self.unify_at(&guard_ty, &bool_ty, guard_expr.span)?;
                        // Flow Is bindings from guard into subsequent guards and arm body
                        self.collect_is_bindings(guard_expr);
                    }
                    let body_ty = self.infer_expr(&arm.body)?;
                    self.unify_at(&result_ty, &body_ty, arm.body.span)?;
                    self.env = saved_env;
                }
                Ok(result_ty)
            }

            ExprKind::Record { fields } => {
                let mut type_fields = Vec::new();
                for (name, field_expr) in fields {
                    let field_ty = self.infer_expr(field_expr)?;
                    type_fields.push(((*name).to_owned(), field_ty));
                }
                Ok(Type::Record {
                    fields: type_fields,
                    rest: None,
                })
            }

            ExprKind::FieldAccess { record, field } => {
                let field = *field;
                let record_ty = self.infer_expr(record)?;
                let field_ty = self.engine.fresh();
                let rest_row = self.engine.fresh();
                let expected = Type::Record {
                    fields: vec![(field.to_owned(), field_ty.clone())],
                    rest: Some(Box::new(rest_row)),
                };
                self.unify_at(&record_ty, &expected, expr.span)?;
                Ok(field_ty)
            }

            ExprKind::Lambda { params, body } => {
                let saved_env = self.env.clone();
                let param_types: Vec<Type> = params
                    .iter()
                    .map(|p| {
                        let ty = self.engine.fresh();
                        self.env.insert((*p).to_owned(), Scheme::mono(ty.clone()));
                        ty
                    })
                    .collect();
                let body_ty = self.infer_expr(body)?;
                self.env = saved_env;
                Ok(Type::Arrow(param_types, Box::new(body_ty)))
            }

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
            } => self.infer_method_call(receiver, method, args, expr.span),

            ExprKind::Is {
                expr: inner,
                pattern,
            } => {
                let inner_ty = self.infer_expr(inner)?;
                let bindings = self.infer_pattern(pattern, &inner_ty, expr.span, None)?;
                self.is_bindings.insert(expr.span, bindings);
                Ok(Type::Con("Bool".to_owned()))
            }
        }
    }

    fn infer_call(
        &mut self,
        func: &str,
        args: &[Expr<'src>],
        span: Span,
    ) -> Result<Type, CompileError> {
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
            return Ok(ret);
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
                        // Record resolution for the lowerer
                        self.method_resolutions.insert(span, mangled);
                        return Ok(ret);
                    }
                    if let Some(result) = self.resolve_numeric_builtin(
                        concrete_name, method_name, &var_ty, &arg_types, &resolved, span,
                    ) {
                        return result;
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
        op: &BinOp,
        lhs: &Expr<'src>,
        rhs: &Expr<'src>,
        span: Span,
    ) -> Result<Type, CompileError> {
        let lt = self.infer_expr(lhs)?;
        let rt = self.infer_expr(rhs)?;
        self.unify_at(&lt, &rt, span)?;

        let is_eq = matches!(op, BinOp::Eq | BinOp::Neq);
        let method_name = match op {
            BinOp::Add => "add",
            BinOp::Sub => "sub",
            BinOp::Mul => "mul",
            BinOp::Div => "div",
            BinOp::Rem => "rem",
            BinOp::Eq => "eq",
            BinOp::Neq => "neq",
            BinOp::And | BinOp::Or => unreachable!(),
        };

        let resolved = self.engine.resolve(&lt);
        if let Type::Var(tv) = resolved {
            let ret_ty = if is_eq {
                Type::Con("Bool".to_owned())
            } else {
                Type::Var(tv)
            };
            let method_type =
                Type::Arrow(vec![Type::Var(tv), Type::Var(tv)], Box::new(ret_ty));
            self.push_constraint(
                Constraint {
                    type_var: tv,
                    method_name: method_name.to_owned(),
                    method_type,
                },
                span,
            );
        }

        if is_eq {
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

        // Concrete type: look up Type.method
        if let Type::Con(name) | Type::App(name, _) = &resolved {
            let mangled = format!("{name}.{method}");
            if let Some(scheme) = self.env.get(&mangled).cloned() {
                let func_ty = self.engine.instantiate(&scheme);
                let mut full_args = vec![recv_ty];
                full_args.extend(arg_types);
                let expected = Type::Arrow(full_args, Box::new(ret.clone()));
                self.unify_at(&func_ty, &expected, span)?;
                self.method_resolutions.insert(span, mangled);
                return Ok(ret);
            }
            if let Some(result) =
                self.resolve_numeric_builtin(name, method, &recv_ty, &arg_types, &resolved, span)
            {
                return result;
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

    // ---- Numeric builtin resolution ----

    /// Try to resolve a method call as a numeric builtin (add, sub, eq, etc.).
    /// Returns `Some(Ok(ty))` if it matched, `None` if not a numeric builtin.
    fn resolve_numeric_builtin(
        &mut self,
        type_name: &str,
        method: &str,
        recv_ty: &Type,
        arg_types: &[Type],
        resolved: &Type,
        span: Span,
    ) -> Option<Result<Type, CompileError>> {
        if !Self::NUMERIC_TYPES.contains(&type_name) || !Self::ARITHMETIC_METHODS.contains(&method)
        {
            return None;
        }
        let concrete_ty = resolved.clone();
        if let Err(e) = self.unify_at(recv_ty, &concrete_ty, span) {
            return Some(Err(e));
        }
        for arg_ty in arg_types {
            if let Err(e) = self.unify_at(arg_ty, &concrete_ty, span) {
                return Some(Err(e));
            }
        }
        self.method_resolutions
            .insert(span, format!("__builtin.{method}"));
        if method == "eq" || method == "neq" {
            Some(Ok(Type::Con("Bool".to_owned())))
        } else {
            Some(Ok(concrete_ty))
        }
    }

    // ---- Pattern inference ----

    fn infer_pattern(
        &mut self,
        pat: &ast::Pattern<'src>,
        expected: &Type,
        span: Span,
        rec_subst: Option<&Type>,
    ) -> Result<Vec<(String, Type)>, CompileError> {
        match pat {
            ast::Pattern::Constructor { name, fields } => {
                let name = *name;
                let scheme = self
                    .constructors
                    .get(name)
                    .ok_or_else(|| {
                        Self::type_error(span, &format!("unknown constructor '{name}'"))
                    })?
                    .clone();
                let con_ty = self.engine.instantiate(&scheme);

                if fields.is_empty() {
                    // Nullary constructor
                    self.unify_at(&con_ty, expected, span)?;
                    Ok(vec![])
                } else {
                    // Constructor with fields
                    let field_types: Vec<Type> =
                        fields.iter().map(|_| self.engine.fresh()).collect();
                    let con_ret = self.engine.fresh();
                    let arrow = Type::Arrow(field_types.clone(), Box::new(con_ret.clone()));
                    self.unify_at(&con_ty, &arrow, span)?;
                    self.unify_at(&con_ret, expected, span)?;

                    let mut bindings = Vec::new();
                    for (field_pat, field_ty) in fields.iter().zip(field_types.iter()) {
                        // For fold patterns: if field type matches scrutinee and rec_subst
                        // is Some, use the substitution type instead.
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
                            ast::Pattern::Binding(n) => {
                                bindings.push(((*n).to_owned(), bind_ty));
                            }
                            ast::Pattern::Wildcard => {}
                            ast::Pattern::Constructor { .. }
                            | ast::Pattern::Record { .. }
                            | ast::Pattern::Tuple(_) => {
                                bindings
                                    .extend(self.infer_pattern(field_pat, &bind_ty, span, None)?);
                            }
                        }
                    }
                    Ok(bindings)
                }
            }
            ast::Pattern::Record { fields } => {
                let rest = self.engine.fresh(); // open rest for row polymorphism
                let mut type_fields = Vec::new();
                let mut bindings = Vec::new();
                for (field_name, field_pat) in fields {
                    let field_ty = self.engine.fresh();
                    type_fields.push(((*field_name).to_owned(), field_ty.clone()));
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
            ast::Pattern::Binding(name) => Ok(vec![((*name).to_owned(), expected.clone())]),
            ast::Pattern::Wildcard => Ok(vec![]),
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
        params: &[&'src str],
        body: &Expr<'src>,
    ) -> Result<(), CompileError> {
        let saved_env = self.env.clone();
        let pre_scheme = self.env[name].clone();
        let func_ty = self.engine.instantiate(&pre_scheme);

        let param_types: Vec<Type> = params.iter().map(|_| self.engine.fresh()).collect();
        let ret = self.engine.fresh();
        let expected = Type::Arrow(param_types.clone(), Box::new(ret.clone()));
        self.unify_at(&func_ty, &expected, body.span)?;

        for (p, ty) in params.iter().zip(param_types.iter()) {
            self.env.insert((*p).to_owned(), Scheme::mono(ty.clone()));
        }
        let body_ty = self.infer_expr(body)?;
        self.unify_at(&ret, &body_ty, body.span)?;

        // If there's an annotation, unify with it and use it as the external type
        let external_ty = if let Some(anno) = self.type_annos.get(name).cloned() {
            let anno_ty = self.resolve_type_expr(&anno)?;
            self.unify_at(&func_ty, &anno_ty, body.span)?;
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

    /// Numeric types that implicitly satisfy arithmetic constraints.
    const NUMERIC_TYPES: &'static [&'static str] = &["I8", "U8", "I64", "U64", "F64"];
    const ARITHMETIC_METHODS: &'static [&'static str] =
        &["add", "sub", "mul", "div", "rem", "eq", "neq"];

    /// Verify constraints whose type vars resolved to concrete types,
    /// and store method resolutions for the lowerer.
    fn verify_constraints(&mut self) -> Result<(), CompileError> {
        for (i, c) in self.engine.constraints.clone().iter().enumerate() {
            let resolved = self.engine.resolve(&Type::Var(c.type_var));
            let (Type::Con(type_name) | Type::App(type_name, _)) = &resolved else {
                continue; // still polymorphic or structural, stays as constraint
            };
            let maybe_span = self.constraint_spans.get(i).copied();
            // Numeric types implicitly have arithmetic methods
            if Self::NUMERIC_TYPES.contains(&type_name.as_str())
                && Self::ARITHMETIC_METHODS.contains(&c.method_name.as_str())
            {
                if let Some(s) = maybe_span {
                    self.method_resolutions
                        .insert(s, format!("__builtin.{}", c.method_name));
                }
                continue;
            }
            let mangled = format!("{type_name}.{}", c.method_name);
            if let Some(scheme) = self.env.get(&mangled).cloned() {
                // Unify the constraint's method type with the actual method signature
                // so that arg types (e.g. index literals) resolve correctly.
                let actual_ty = self.engine.instantiate(&scheme);
                drop(self.engine.unify(&c.method_type, &actual_ty));
                if let Some(s) = maybe_span {
                    self.method_resolutions.insert(s, mangled);
                }
            } else {
                return Err(CompileError::new(format!(
                    "type error: {type_name} has no method '{}'",
                    c.method_name
                )));
            }
        }
        Ok(())
    }

    /// Default unresolved literal type vars and build the span -> `NumType` side table.
    fn resolve_literals(&mut self) -> Result<HashMap<Span, NumType>, CompileError> {
        let i64_ty = Type::Con("I64".to_owned());
        let f64_ty = Type::Con("F64".to_owned());

        // Default unresolved int literals to I64
        for &(tv, _) in &self.int_literal_vars {
            let resolved = self.engine.resolve(&Type::Var(tv));
            if matches!(resolved, Type::Var(_)) {
                self.engine.subst.insert(tv, i64_ty.clone());
            }
        }

        // Default unresolved float literals to F64
        for &(tv, _) in &self.float_literal_vars {
            let resolved = self.engine.resolve(&Type::Var(tv));
            if matches!(resolved, Type::Var(_)) {
                self.engine.subst.insert(tv, f64_ty.clone());
            }
        }

        // Build side table
        let mut table = HashMap::new();
        for &(tv, span) in &self.int_literal_vars {
            let resolved = self.engine.resolve(&Type::Var(tv));
            let num_type = match &resolved {
                Type::Con(name) if name == "U8" => NumType::U8,
                Type::Con(name) if name == "I8" => NumType::I8,
                Type::Con(name) if name == "I64" => NumType::I64,
                Type::Con(name) if name == "U64" => NumType::U64,
                Type::Con(name) if name == "F64" => NumType::F64,
                other => {
                    return Err(CompileError::at(
                        span,
                        format!(
                            "type error: integer literal resolved to non-numeric type: {}",
                            self.engine.display_type(other)
                        ),
                    ));
                }
            };
            table.insert(span, num_type);
        }
        for &(tv, span) in &self.float_literal_vars {
            let resolved = self.engine.resolve(&Type::Var(tv));
            let num_type = match &resolved {
                Type::Con(name) if name == "F64" => NumType::F64,
                other => {
                    return Err(CompileError::at(
                        span,
                        format!(
                            "type error: float literal resolved to non-numeric type: {}",
                            self.engine.display_type(other)
                        ),
                    ));
                }
            };
            table.insert(span, num_type);
        }
        Ok(table)
    }
}

// ---- Public API ----

#[expect(
    clippy::too_many_lines,
    reason = "multi-pass type checking orchestration"
)]
pub fn check<'src>(
    arena: &'src SourceArena,
    module: &Module<'src>,
    scope: &crate::resolve::ModuleScope,
) -> Result<InferResult, CompileError> {
    let mut ctx = InferCtx::new();

    // Register to_str for all numeric types (not as full modules — their
    // := {} declaration would incorrectly make them transparent to {}).
    for ty in &["I64", "U64", "F64", "U8", "I8"] {
        let mangled = format!("{ty}.to_str");
        let param_ty = Type::Con((*ty).to_owned());
        let ret_ty = Type::Con("Str".to_owned());
        let scheme = Scheme {
            vars: vec![],
            constraints: vec![],
            ty: Type::Arrow(vec![param_ty], Box::new(ret_ty)),
        };
        ctx.env.insert(mangled, scheme);
    }

    // Pass 1: register all type declarations and function signatures
    for decl in &module.decls {
        match decl {
            Decl::TypeAnno {
                name,
                type_params,
                ty: TypeExpr::TagUnion(tags),
                methods,
                ..
            } => {
                let name = *name;
                ctx.register_type_decl(name, type_params, tags)?;
                // Register method signatures and collect method annotations
                for method in methods {
                    match method {
                        Decl::FuncDef {
                            name: method_name,
                            params,
                            ..
                        } => {
                            let method_name = *method_name;
                            let mangled = method_key(name, method_name);
                            let param_types: Vec<Type> =
                                params.iter().map(|_| ctx.engine.fresh()).collect();
                            let ret = ctx.engine.fresh();
                            let func_ty = Type::Arrow(param_types, Box::new(ret));
                            // Dual-register: module-qualified alias
                            if let Some(mod_name) = scope.qualified_types.get(name) {
                                let qual = format!("{mod_name}.{mangled}");
                                ctx.env.insert(qual, Scheme::mono(func_ty.clone()));
                            }
                            ctx.env.insert(mangled, Scheme::mono(func_ty));
                        }
                        Decl::TypeAnno {
                            name: method_name,
                            span: method_span,
                            ty,
                            ..
                        } => {
                            let method_name = *method_name;
                            let mangled = method_key(name, method_name);
                            if let Some(mod_name) = scope.qualified_types.get(name) {
                                let qual = format!("{mod_name}.{mangled}");
                                ctx.type_annos.insert(qual, ty.clone());
                            }
                            ctx.type_annos.insert(mangled.clone(), ty.clone());
                            if arena.path(method_span.file).starts_with("<stdlib:") {
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
            }
            Decl::TypeAnno {
                name,
                type_params,
                ty,
                methods,
                kind,
                ..
            } => {
                let name = *name;
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
                                let method_name = *method_name;
                                let mangled = method_key(name, method_name);
                                let param_types: Vec<Type> =
                                    params.iter().map(|_| ctx.engine.fresh()).collect();
                                let ret = ctx.engine.fresh();
                                let func_ty = Type::Arrow(param_types, Box::new(ret));
                                ctx.env.insert(mangled, Scheme::mono(func_ty));
                            }
                            Decl::TypeAnno {
                                name: method_name,
                                span: method_span,
                                ty: method_ty,
                                ..
                            } => {
                                let method_name = *method_name;
                                let mangled = method_key(name, method_name);
                                ctx.type_annos.insert(mangled.clone(), method_ty.clone());
                                if arena.path(method_span.file).starts_with("<stdlib:") {
                                    let mut tvar_env = HashMap::new();
                                    let anno_ty =
                                        ctx.type_expr_to_type(method_ty, &mut tvar_env)?;
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
            Decl::FuncDef { name, params, .. } => {
                let name = *name;
                let param_types: Vec<Type> = params.iter().map(|_| ctx.engine.fresh()).collect();
                let ret = ctx.engine.fresh();
                let func_ty = Type::Arrow(param_types, Box::new(ret));
                // Dual-register qualified alias for imported free functions
                if let Some(mod_name) = scope.qualified_funcs.get(name) {
                    let qual = format!("{mod_name}.{name}");
                    ctx.env.insert(qual, Scheme::mono(func_ty.clone()));
                }
                ctx.env.insert(name.to_owned(), Scheme::mono(func_ty));
            }
        }
    }

    // Pass 2: infer all function bodies
    for decl in &module.decls {
        match decl {
            Decl::FuncDef {
                name, params, body, ..
            } => {
                ctx.infer_func_body(name, params, body)?;
                // Dual-register qualified alias after inference
                if let Some(mod_name) = scope.qualified_funcs.get(*name) {
                    let qual = format!("{mod_name}.{name}");
                    if let Some(scheme) = ctx.env.get(*name).cloned() {
                        ctx.env.insert(qual, scheme);
                    }
                }
            }
            Decl::TypeAnno {
                name,
                ty,
                kind,
                methods,
                ..
            } => {
                let name = *name;
                // For nominal types (:= and ::), make the type transparent
                // so method bodies can convert between the nominal and underlying type.
                // For transparent (:=), this persists. For opaque (::), removed after.
                // Tag unions are not transparent — they define distinct sum types.
                if *kind != TypeDeclKind::Alias && !matches!(ty, TypeExpr::TagUnion(_)) {
                    let underlying = ctx.resolve_type_expr(ty)?;
                    ctx.engine.transparent.insert(name.to_owned(), underlying);
                }
                // Check for body-less declarations (only valid in stdlib builtins)
                let func_names: std::collections::HashSet<&str> = methods
                    .iter()
                    .filter_map(|m| {
                        if let Decl::FuncDef { name, .. } = m {
                            Some(*name)
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
                        && !func_names.contains(method_name)
                    {
                        let is_stdlib = arena.path(method_span.file).starts_with("<stdlib:");
                        if !is_stdlib {
                            return Err(CompileError::at(
                                *method_span,
                                format!("method '{name}.{method_name}' declared but not defined"),
                            ));
                        }
                    }
                }

                for method in methods {
                    if let Decl::FuncDef {
                        name: method_name,
                        params,
                        body,
                        ..
                    } = method
                    {
                        let mangled = method_key(name, method_name);
                        ctx.infer_func_body(&mangled, params, body)?;
                        // Dual-register qualified alias
                        if let Some(mod_name) = scope.qualified_types.get(name) {
                            let qual = format!("{mod_name}.{mangled}");
                            if let Some(scheme) = ctx.env.get(&mangled).cloned() {
                                ctx.env.insert(qual, scheme);
                            }
                        }
                    }
                }
                // Opaque (::): remove transparency so external code can't see through.
                // Transparent (:=): keep — internals visible everywhere.
                if *kind == TypeDeclKind::Opaque {
                    ctx.engine.transparent.remove(name);
                }
            }
        }
    }

    ctx.verify_constraints()?;
    let lit_types = ctx.resolve_literals()?;

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

    Ok(InferResult {
        lit_types,
        method_resolutions: ctx.method_resolutions,
        expr_types,
        func_schemes,
        constructor_schemes,
    })
}
