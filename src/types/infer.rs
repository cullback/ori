use std::collections::HashMap;

use crate::syntax::ast::{self, BinOp, Decl, Expr, ExprKind, Module, Span, Stmt, TypeExpr};
use crate::types::engine::{Scheme, Type, TypeEngine, TypeVar};

/// Build a mangled key for a method on a type, e.g. `method_key("List", "sum")` -> `"List.sum"`.
fn method_key(type_name: &str, method: &str) -> String {
    format!("{type_name}.{method}")
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
    source: &'src str,
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
}

impl<'src> InferCtx<'src> {
    fn new(source: &'src str) -> Self {
        Self {
            source,
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
                "List".to_owned(),
            ]),
            int_literal_vars: Vec::new(),
            float_literal_vars: Vec::new(),
        }
    }

    #[expect(clippy::arithmetic_side_effects, reason = "line/col counting")]
    fn type_error(&self, span: Span, msg: &str) -> ! {
        let mut line = 1_usize;
        let mut col = 1_usize;
        for (i, ch) in self.source.char_indices() {
            if i >= span.start {
                break;
            }
            if ch == '\n' {
                line += 1;
                col = 1;
            } else {
                col += 1;
            }
        }
        let line_start = self.source[..span.start]
            .rfind('\n')
            .map_or(0_usize, |i| i + 1);
        let line_end = self.source[span.start..]
            .find('\n')
            .map_or(self.source.len(), |i| span.start + i);
        let src_line = &self.source[line_start..line_end];
        let pad = " ".repeat(col - 1);
        let carets = "^".repeat((span.end - span.start).max(1));
        panic!(
            "\n --> {line}:{col}\n    | \n{line:>3} | {src_line}\n    | {pad}{carets}\n    | type error: {msg}"
        );
    }

    fn unify_at(&mut self, t1: &Type, t2: &Type, span: Span) {
        if let Err(msg) = self.engine.unify(t1, t2) {
            self.type_error(span, &msg);
        }
    }

    // ---- Convert surface TypeExpr to inference Type ----

    /// Convert a type expression without pre-existing type variable bindings.
    fn resolve_type_expr(&mut self, texpr: &TypeExpr<'src>) -> Type {
        self.type_expr_to_type(texpr, &mut HashMap::new())
    }

    /// Convert a type expression, accumulating implicit type variable bindings
    /// into `tvar_env` (so `a` in `a -> a` resolves to the same variable).
    fn type_expr_to_type(
        &mut self,
        texpr: &TypeExpr<'src>,
        tvar_env: &mut HashMap<String, TypeVar>,
    ) -> Type {
        match texpr {
            TypeExpr::Named(name) => {
                let name = *name;
                if let Some(&tv) = tvar_env.get(name) {
                    Type::Var(tv)
                } else if let Some(scheme) = self.type_aliases.get(name).cloned() {
                    self.engine.instantiate(&scheme)
                } else if name.starts_with(|c: char| c.is_ascii_lowercase()) {
                    // Lowercase names are implicit type variables
                    let tv = self.engine.fresh();
                    let Type::Var(tv_id) = tv else { unreachable!() };
                    tvar_env.insert(name.to_owned(), tv_id);
                    tv
                } else if self.known_types.contains(name) {
                    Type::Con(name.to_owned())
                } else {
                    panic!("type error: unknown type '{name}'");
                }
            }
            TypeExpr::App(name, args) => {
                let name = *name;
                assert!(
                    self.known_types.contains(name),
                    "type error: unknown type '{name}'"
                );
                let arg_types: Vec<Type> = args
                    .iter()
                    .map(|a| self.type_expr_to_type(a, tvar_env))
                    .collect();
                Type::App(name.to_owned(), arg_types)
            }
            TypeExpr::Arrow(params, ret) => {
                let param_types: Vec<Type> = params
                    .iter()
                    .map(|p| self.type_expr_to_type(p, tvar_env))
                    .collect();
                Type::Arrow(param_types, Box::new(self.type_expr_to_type(ret, tvar_env)))
            }
            TypeExpr::TagUnion(_) => {
                // Inline tag unions in type expressions are not supported in inference yet
                self.engine.fresh()
            }
            TypeExpr::Record(fields) => {
                let type_fields: Vec<(String, Type)> = fields
                    .iter()
                    .map(|(name, field_texpr)| {
                        let field_ty = self.type_expr_to_type(field_texpr, tvar_env);
                        ((*name).to_owned(), field_ty)
                    })
                    .collect();
                Type::Record {
                    fields: type_fields,
                    rest: None,
                }
            }
            TypeExpr::Tuple(elems) => {
                let elem_types: Vec<Type> = elems
                    .iter()
                    .map(|e| self.type_expr_to_type(e, tvar_env))
                    .collect();
                Type::Tuple(elem_types)
            }
        }
    }

    // ---- Register type declarations ----

    fn register_type_decl(
        &mut self,
        name: &str,
        type_params: &[&str],
        tags: &[ast::TagDecl<'src>],
    ) {
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
                let field_types: Vec<Type> = tag
                    .fields
                    .iter()
                    .map(|f| self.type_expr_to_type(f, &mut tvar_env))
                    .collect();
                Type::Arrow(field_types, Box::new(return_type.clone()))
            };
            self.constructors.insert(
                tag.name.to_owned(),
                Scheme {
                    vars: tvars.clone(),
                    ty: con_type,
                },
            );
        }
    }

    // ---- Stdlib module registration ----

    /// Parse and register a stdlib module: types, constructors, method signatures, and bodies.
    fn register_stdlib_module(&mut self, module_name: &str) {
        let src = crate::stdlib::get(module_name).unwrap_or("");
        let stdlib = crate::syntax::parse::parse(src);

        for decl in &stdlib.decls {
            match decl {
                Decl::TypeAnno {
                    name,
                    type_params,
                    ty: TypeExpr::TagUnion(tags),
                    methods,
                    ..
                } => {
                    let name = *name;
                    self.register_type_decl(name, type_params, tags);
                    self.register_methods(name, methods);
                    self.infer_method_bodies(name, methods);
                }
                Decl::TypeAnno { name, methods, .. } => {
                    let name = *name;
                    self.register_methods(name, methods);
                    self.infer_method_bodies(name, methods);
                }
                Decl::FuncDef { name, params, .. } => {
                    let name = *name;
                    let param_types: Vec<Type> =
                        params.iter().map(|_| self.engine.fresh()).collect();
                    let ret = self.engine.fresh();
                    let func_ty = Type::Arrow(param_types, Box::new(ret));
                    self.env.insert(name.to_owned(), Scheme::mono(func_ty));
                }
            }
        }

        // Infer free function bodies
        for decl in &stdlib.decls {
            if let Decl::FuncDef { name, params, body } = decl {
                self.infer_func_body(name, params, body);
            }
        }
    }

    /// Register method signatures and type annotations for methods on a type.
    fn register_methods(&mut self, type_name: &str, methods: &[Decl<'src>]) {
        for method in methods {
            match method {
                Decl::FuncDef {
                    name: method_name,
                    params,
                    ..
                } => {
                    let method_name = *method_name;
                    let mangled = method_key(type_name, method_name);
                    let param_types: Vec<Type> =
                        params.iter().map(|_| self.engine.fresh()).collect();
                    let ret = self.engine.fresh();
                    let func_ty = Type::Arrow(param_types, Box::new(ret));
                    self.env.insert(mangled, Scheme::mono(func_ty));
                }
                Decl::TypeAnno {
                    name: method_name,
                    ty,
                    ..
                } => {
                    let method_name = *method_name;
                    let mangled = method_key(type_name, method_name);
                    // Body-less annotation: convert to a proper scheme for builtins
                    let mut tvar_env = HashMap::new();
                    let anno_ty = self.type_expr_to_type(ty, &mut tvar_env);
                    let tvars: Vec<crate::types::engine::TypeVar> =
                        tvar_env.into_values().collect();
                    let scheme = Scheme {
                        vars: tvars,
                        ty: anno_ty,
                    };
                    self.env.insert(mangled.clone(), scheme);
                    self.type_annos.insert(mangled, ty.clone());
                }
            }
        }
    }

    /// Infer bodies of Ori-implemented methods on a type.
    fn infer_method_bodies(&mut self, type_name: &str, methods: &[Decl<'src>]) {
        for method in methods {
            if let Decl::FuncDef {
                name: method_name,
                params,
                body,
            } = method
            {
                let mangled = method_key(type_name, method_name);
                self.infer_func_body(&mangled, params, body);
            }
        }
    }

    // ---- Expression inference ----

    #[expect(
        clippy::too_many_lines,
        reason = "expression inference handles all forms"
    )]
    fn infer_expr(&mut self, expr: &Expr<'src>) -> Type {
        match &expr.kind {
            ExprKind::IntLit(_) => {
                let ty = self.engine.fresh();
                let Type::Var(tv) = ty else { unreachable!() };
                self.int_literal_vars.push((tv, expr.span));
                ty
            }

            ExprKind::FloatLit(_) => {
                let ty = self.engine.fresh();
                let Type::Var(tv) = ty else { unreachable!() };
                self.float_literal_vars.push((tv, expr.span));
                ty
            }

            ExprKind::Name(name) => {
                let name = *name;
                if let Some(scheme) = self.env.get(name).cloned() {
                    return self.engine.instantiate(&scheme);
                }
                if let Some(scheme) = self.constructors.get(name).cloned() {
                    return self.engine.instantiate(&scheme);
                }
                self.type_error(expr.span, &format!("undefined name '{name}'"));
            }

            ExprKind::BinOp { op, lhs, rhs } => {
                let lt = self.infer_expr(lhs);
                let rt = self.infer_expr(rhs);
                match op {
                    BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Rem => {
                        self.unify_at(&lt, &rt, expr.span);
                        lt
                    }
                    BinOp::Eq | BinOp::Neq => {
                        self.unify_at(&lt, &rt, expr.span);
                        Type::Con("Bool".to_owned())
                    }
                }
            }

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
                            let val_ty = self.infer_expr(val);
                            // If there's a type hint for this binding, enforce it
                            if let Some(hint) = pending_hints.remove(name) {
                                let hint_ty = self.resolve_type_expr(&hint);
                                self.unify_at(&val_ty, &hint_ty, val.span);
                            }
                            let scheme = self.engine.generalize(&val_ty, &self.env);
                            self.env.insert(name.to_owned(), scheme);
                        }
                        Stmt::Destructure { pattern, val } => {
                            let val_ty = self.infer_expr(val);
                            let bindings = self.infer_pattern(pattern, &val_ty, val.span, None);
                            for (name, ty) in bindings {
                                let scheme = self.engine.generalize(&ty, &self.env);
                                self.env.insert(name, scheme);
                            }
                        }
                    }
                }
                let result_ty = self.infer_expr(result);
                self.env = saved_env;
                result_ty
            }

            ExprKind::If {
                expr: scrutinee,
                arms,
                ..
            } => {
                let scrutinee_ty = self.infer_expr(scrutinee);
                let result_ty = self.engine.fresh();
                for arm in arms {
                    let bindings = self.infer_pattern(&arm.pattern, &scrutinee_ty, expr.span, None);
                    let saved_env = self.env.clone();
                    for (name, ty) in bindings {
                        self.env.insert(name, Scheme::mono(ty));
                    }
                    let body_ty = self.infer_expr(&arm.body);
                    self.unify_at(&result_ty, &body_ty, arm.body.span);
                    self.env = saved_env;
                }
                result_ty
            }

            ExprKind::Fold {
                expr: scrutinee,
                arms,
            } => {
                let scrutinee_ty = self.infer_expr(scrutinee);
                let result_ty = self.engine.fresh();
                for arm in arms {
                    // In fold, recursive fields bind to the result type, not the scrutinee type
                    let bindings = self.infer_pattern(
                        &arm.pattern,
                        &scrutinee_ty,
                        expr.span,
                        Some(&result_ty),
                    );
                    let saved_env = self.env.clone();
                    for (name, ty) in bindings {
                        self.env.insert(name, Scheme::mono(ty));
                    }
                    let body_ty = self.infer_expr(&arm.body);
                    self.unify_at(&result_ty, &body_ty, arm.body.span);
                    self.env = saved_env;
                }
                result_ty
            }

            ExprKind::Record { fields } => {
                let type_fields: Vec<(String, Type)> = fields
                    .iter()
                    .map(|(name, field_expr)| {
                        let field_ty = self.infer_expr(field_expr);
                        ((*name).to_owned(), field_ty)
                    })
                    .collect();
                Type::Record {
                    fields: type_fields,
                    rest: None,
                }
            }

            ExprKind::FieldAccess { record, field } => {
                let field = *field;
                let record_ty = self.infer_expr(record);
                let field_ty = self.engine.fresh();
                let rest_row = self.engine.fresh();
                let expected = Type::Record {
                    fields: vec![(field.to_owned(), field_ty.clone())],
                    rest: Some(Box::new(rest_row)),
                };
                self.unify_at(&record_ty, &expected, expr.span);
                field_ty
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
                let body_ty = self.infer_expr(body);
                self.env = saved_env;
                Type::Arrow(param_types, Box::new(body_ty))
            }

            ExprKind::Tuple(elems) => {
                let elem_types: Vec<Type> = elems.iter().map(|e| self.infer_expr(e)).collect();
                Type::Tuple(elem_types)
            }

            ExprKind::ListLit(elems) => {
                let elem_ty = self.engine.fresh();
                for e in elems {
                    let t = self.infer_expr(e);
                    self.unify_at(&elem_ty, &t, e.span);
                }
                Type::App("List".to_owned(), vec![elem_ty])
            }
        }
    }

    fn infer_call(&mut self, func: &str, args: &[Expr<'src>], span: Span) -> Type {
        let arg_types: Vec<Type> = args.iter().map(|a| self.infer_expr(a)).collect();
        let ret = self.engine.fresh();

        if let Some(scheme) = self.constructors.get(func).cloned() {
            let con_ty = self.engine.instantiate(&scheme);
            if arg_types.is_empty() {
                // Nullary constructor called with parens
                return con_ty;
            }
            let expected = Type::Arrow(arg_types, Box::new(ret.clone()));
            self.unify_at(&con_ty, &expected, span);
            return ret;
        }

        if let Some(scheme) = self.env.get(func).cloned() {
            let func_ty = self.engine.instantiate(&scheme);
            let expected = Type::Arrow(arg_types, Box::new(ret.clone()));
            self.unify_at(&func_ty, &expected, span);
            return ret;
        }

        panic!("type error: undefined function '{func}'");
    }

    // ---- Pattern inference ----

    fn infer_pattern(
        &mut self,
        pat: &ast::Pattern<'src>,
        expected: &Type,
        span: Span,
        rec_subst: Option<&Type>,
    ) -> Vec<(String, Type)> {
        match pat {
            ast::Pattern::Constructor { name, fields } => {
                let name = *name;
                let scheme = self
                    .constructors
                    .get(name)
                    .unwrap_or_else(|| panic!("type error: unknown constructor '{name}'"))
                    .clone();
                let con_ty = self.engine.instantiate(&scheme);

                if fields.is_empty() {
                    // Nullary constructor
                    self.unify_at(&con_ty, expected, span);
                    vec![]
                } else {
                    // Constructor with fields
                    let field_types: Vec<Type> =
                        fields.iter().map(|_| self.engine.fresh()).collect();
                    let con_ret = self.engine.fresh();
                    let arrow = Type::Arrow(field_types.clone(), Box::new(con_ret.clone()));
                    self.unify_at(&con_ty, &arrow, span);
                    self.unify_at(&con_ret, expected, span);

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
                                    .extend(self.infer_pattern(field_pat, &bind_ty, span, None));
                            }
                        }
                    }
                    bindings
                }
            }
            ast::Pattern::Record { fields } => {
                let rest = self.engine.fresh(); // open rest for row polymorphism
                let mut type_fields = Vec::new();
                let mut bindings = Vec::new();
                for (field_name, field_pat) in fields {
                    let field_ty = self.engine.fresh();
                    type_fields.push(((*field_name).to_owned(), field_ty.clone()));
                    bindings.extend(self.infer_pattern(field_pat, &field_ty, span, None));
                }
                let expected_record = Type::Record {
                    fields: type_fields,
                    rest: Some(Box::new(rest)),
                };
                self.unify_at(&expected_record, expected, span);
                bindings
            }
            ast::Pattern::Tuple(elems) => {
                let elem_types: Vec<Type> = elems.iter().map(|_| self.engine.fresh()).collect();
                let tuple_ty = Type::Tuple(elem_types.clone());
                self.unify_at(&tuple_ty, expected, span);
                let mut bindings = Vec::new();
                for (elem_pat, elem_ty) in elems.iter().zip(elem_types.iter()) {
                    bindings.extend(self.infer_pattern(elem_pat, elem_ty, span, None));
                }
                bindings
            }
            ast::Pattern::Binding(name) => {
                vec![((*name).to_owned(), expected.clone())]
            }
            ast::Pattern::Wildcard => vec![],
        }
    }

    // ---- Function body inference ----

    fn infer_func_body(&mut self, name: &str, params: &[&'src str], body: &Expr<'src>) {
        let saved_env = self.env.clone();
        let pre_scheme = self.env[name].clone();
        let func_ty = self.engine.instantiate(&pre_scheme);

        let param_types: Vec<Type> = params.iter().map(|_| self.engine.fresh()).collect();
        let ret = self.engine.fresh();
        let expected = Type::Arrow(param_types.clone(), Box::new(ret.clone()));
        self.unify_at(&func_ty, &expected, body.span);

        for (p, ty) in params.iter().zip(param_types.iter()) {
            self.env.insert((*p).to_owned(), Scheme::mono(ty.clone()));
        }
        let body_ty = self.infer_expr(body);
        self.unify_at(&ret, &body_ty, body.span);

        if let Some(anno) = self.type_annos.get(name).cloned() {
            let anno_ty = self.resolve_type_expr(&anno);
            self.unify_at(&func_ty, &anno_ty, body.span);
        }

        self.env = saved_env;
        self.env.remove(name);

        let resolved = self.engine.resolve(&func_ty);
        let generalized = self.engine.generalize(&resolved, &self.env);
        self.env.insert(name.to_owned(), generalized);
    }

    /// Default unresolved literal type vars and build the span -> `NumType` side table.
    fn resolve_literals(&mut self) -> HashMap<Span, NumType> {
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
                other => panic!(
                    "integer literal resolved to non-numeric type: {}",
                    self.engine.display_type(other)
                ),
            };
            table.insert(span, num_type);
        }
        for &(tv, span) in &self.float_literal_vars {
            let resolved = self.engine.resolve(&Type::Var(tv));
            let num_type = match &resolved {
                Type::Con(name) if name == "F64" => NumType::F64,
                other => panic!(
                    "float literal resolved to non-numeric type: {}",
                    self.engine.display_type(other)
                ),
            };
            table.insert(span, num_type);
        }
        table
    }
}

// ---- Public API ----

#[expect(
    clippy::too_many_lines,
    reason = "multi-pass type checking orchestration"
)]
pub fn check<'src>(
    source: &'src str,
    module: &Module<'src>,
    scope: &crate::resolve::ModuleScope,
) -> HashMap<Span, NumType> {
    let mut ctx = InferCtx::new(source);

    // Register stdlib modules
    ctx.register_stdlib_module("Bool");
    ctx.register_stdlib_module("List");

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
                ctx.register_type_decl(name, type_params, tags);
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
                            ty,
                            ..
                        } => {
                            let method_name = *method_name;
                            let mangled = method_key(name, method_name);
                            if let Some(mod_name) = scope.qualified_types.get(name) {
                                let qual = format!("{mod_name}.{mangled}");
                                ctx.type_annos.insert(qual, ty.clone());
                            }
                            ctx.type_annos.insert(mangled, ty.clone());
                        }
                    }
                }
            }
            Decl::TypeAnno {
                name,
                type_params,
                ty,
                ..
            } => {
                let name = *name;
                if name.starts_with(|c: char| c.is_ascii_uppercase()) {
                    // CamelCase: type alias (e.g. Point : { x: I64, y: I64 })
                    let mut tvar_env: HashMap<String, TypeVar> = type_params
                        .iter()
                        .map(|p| {
                            let t = ctx.engine.fresh();
                            let Type::Var(tv) = t else { unreachable!() };
                            ((*p).to_owned(), tv)
                        })
                        .collect();
                    let tvars: Vec<TypeVar> = type_params.iter().map(|p| tvar_env[*p]).collect();
                    let alias_ty = ctx.type_expr_to_type(ty, &mut tvar_env);
                    let alias_scheme = Scheme {
                        vars: tvars,
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
            Decl::FuncDef { name, params, body } => {
                ctx.infer_func_body(name, params, body);
                // Dual-register qualified alias after inference
                if let Some(mod_name) = scope.qualified_funcs.get(*name) {
                    let qual = format!("{mod_name}.{name}");
                    if let Some(scheme) = ctx.env.get(*name).cloned() {
                        ctx.env.insert(qual, scheme);
                    }
                }
            }
            Decl::TypeAnno { name, methods, .. } => {
                let name = *name;
                for method in methods {
                    if let Decl::FuncDef {
                        name: method_name,
                        params,
                        body,
                    } = method
                    {
                        let mangled = method_key(name, method_name);
                        ctx.infer_func_body(&mangled, params, body);
                        // Dual-register qualified alias
                        if let Some(mod_name) = scope.qualified_types.get(name) {
                            let qual = format!("{mod_name}.{mangled}");
                            if let Some(scheme) = ctx.env.get(&mangled).cloned() {
                                ctx.env.insert(qual, scheme);
                            }
                        }
                    }
                }
            }
        }
    }

    ctx.resolve_literals()
}
