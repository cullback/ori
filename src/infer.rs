use std::collections::{HashMap, HashSet};

use crate::ast::{self, BinOp, Decl, Expr, ExprKind, Module, Span, Stmt, TypeExpr};

// ---- Type representation ----

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct TypeVar(usize);

#[derive(Debug, Clone, PartialEq)]
enum Type {
    Var(TypeVar),
    Con(String),
    App(String, Vec<Type>),
    Arrow(Vec<Type>, Box<Type>),
    Record(Box<Type>),
    RowEmpty,
    RowExtend(String, Box<Type>, Box<Type>),
    Tuple(Vec<Type>),
}

#[derive(Debug, Clone)]
struct Scheme {
    vars: Vec<TypeVar>,
    ty: Type,
}

impl Scheme {
    const fn mono(ty: Type) -> Self {
        Self { vars: vec![], ty }
    }
}

// ---- Inference context ----

struct InferCtx<'src> {
    source: &'src str,
    next_var: usize,
    subst: HashMap<TypeVar, Type>,
    env: HashMap<String, Scheme>,
    constructors: HashMap<String, Scheme>,
    /// Type aliases: Name -> Scheme (e.g. Point -> { x: I64, y: I64 })
    type_aliases: HashMap<String, Scheme>,
    /// Declared type annotations for checking against inferred types.
    type_annos: HashMap<String, TypeExpr<'src>>,
    /// Current expression span for error reporting in unify.
    current_span: Span,
}

impl<'src> InferCtx<'src> {
    fn new(source: &'src str) -> Self {
        Self {
            source,
            next_var: 0,
            subst: HashMap::new(),
            env: HashMap::new(),
            constructors: HashMap::new(),
            type_aliases: HashMap::new(),
            type_annos: HashMap::new(),
            current_span: Span::default(),
        }
    }

    #[expect(
        clippy::arithmetic_side_effects,
        clippy::missing_const_for_fn,
        reason = "type variable counter"
    )]
    fn fresh(&mut self) -> Type {
        let tv = TypeVar(self.next_var);
        self.next_var += 1;
        Type::Var(tv)
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

    // ---- Substitution ----

    fn resolve(&self, ty: &Type) -> Type {
        match ty {
            Type::Var(tv) => {
                if let Some(t) = self.subst.get(tv) {
                    self.resolve(t)
                } else {
                    ty.clone()
                }
            }
            Type::Con(_) => ty.clone(),
            Type::App(name, args) => {
                Type::App(name.clone(), args.iter().map(|a| self.resolve(a)).collect())
            }
            Type::Arrow(params, ret) => Type::Arrow(
                params.iter().map(|p| self.resolve(p)).collect(),
                Box::new(self.resolve(ret)),
            ),
            Type::Record(row) => Type::Record(Box::new(self.resolve(row))),
            Type::RowEmpty => Type::RowEmpty,
            Type::RowExtend(label, field_ty, rest) => Type::RowExtend(
                label.clone(),
                Box::new(self.resolve(field_ty)),
                Box::new(self.resolve(rest)),
            ),
            Type::Tuple(elems) => Type::Tuple(elems.iter().map(|e| self.resolve(e)).collect()),
        }
    }

    fn occurs_in(&self, tv: TypeVar, ty: &Type) -> bool {
        let resolved = self.resolve(ty);
        match &resolved {
            Type::Var(v) => *v == tv,
            Type::Con(_) | Type::RowEmpty => false,
            Type::App(_, args) => args.iter().any(|a| self.occurs_in(tv, a)),
            Type::Arrow(params, ret) => {
                params.iter().any(|p| self.occurs_in(tv, p)) || self.occurs_in(tv, ret)
            }
            Type::Record(row) => self.occurs_in(tv, row),
            Type::RowExtend(_, field_ty, rest) => {
                self.occurs_in(tv, field_ty) || self.occurs_in(tv, rest)
            }
            Type::Tuple(elems) => elems.iter().any(|e| self.occurs_in(tv, e)),
        }
    }

    // ---- Unification ----

    fn unify(&mut self, t1: &Type, t2: &Type) {
        let lhs = self.resolve(t1);
        let rhs = self.resolve(t2);

        match (&lhs, &rhs) {
            (Type::Var(a), Type::Var(b)) if a == b => {}
            (Type::Var(a), _) => {
                assert!(
                    !self.occurs_in(*a, &rhs),
                    "infinite type: {a:?} occurs in {rhs:?}"
                );
                self.subst.insert(*a, rhs);
            }
            (_, Type::Var(_)) => self.unify(&rhs, &lhs),
            (Type::Con(a), Type::Con(b)) => {
                if a != b {
                    self.type_error(self.current_span, &format!("cannot unify {a} with {b}"));
                }
            }
            (Type::App(n1, a1), Type::App(n2, a2)) => {
                if n1 != n2 || a1.len() != a2.len() {
                    self.type_error(self.current_span, &format!("cannot unify {n1} with {n2}"));
                }
                for (x, y) in a1.iter().zip(a2.iter()) {
                    self.unify(x, y);
                }
            }
            (Type::Arrow(p1, r1), Type::Arrow(p2, r2)) => {
                if p1.len() != p2.len() {
                    self.type_error(
                        self.current_span,
                        &format!("function arity mismatch: {} vs {}", p1.len(), p2.len()),
                    );
                }
                for (x, y) in p1.iter().zip(p2.iter()) {
                    self.unify(x, y);
                }
                self.unify(r1, r2);
            }
            (Type::Tuple(a), Type::Tuple(b)) => {
                if a.len() != b.len() {
                    self.type_error(
                        self.current_span,
                        &format!("tuple length mismatch: {} vs {}", a.len(), b.len()),
                    );
                }
                for (x, y) in a.iter().zip(b.iter()) {
                    self.unify(x, y);
                }
            }
            (Type::Record(r1), Type::Record(r2)) => self.unify(r1, r2),
            (Type::RowEmpty, Type::RowEmpty) => {}
            (Type::RowExtend(label, ty, rest), _) => {
                let (other_ty, other_rest) = self.rewrite_row(&rhs, label);
                self.unify(ty, &other_ty);
                self.unify(rest, &other_rest);
            }
            (_, Type::RowExtend(..)) => self.unify(&rhs, &lhs),
            _ => {
                self.type_error(
                    self.current_span,
                    &format!(
                        "cannot unify {} with {}",
                        self.display_type(&lhs),
                        self.display_type(&rhs)
                    ),
                );
            }
        }
    }

    // ---- Row rewriting ----

    fn rewrite_row(&mut self, row: &Type, label: &str) -> (Type, Type) {
        let resolved = self.resolve(row);
        match resolved {
            Type::RowEmpty => panic!("type error: record has no field '{label}'"),
            Type::RowExtend(l, ty, rest) if l == label => (*ty, *rest),
            Type::RowExtend(l, ty, rest) => {
                let (field_ty, new_rest) = self.rewrite_row(&rest, label);
                (field_ty, Type::RowExtend(l, ty, Box::new(new_rest)))
            }
            Type::Var(tv) => {
                let field_ty = self.fresh();
                let new_rest = self.fresh();
                let new_row = Type::RowExtend(
                    label.to_owned(),
                    Box::new(field_ty.clone()),
                    Box::new(new_rest.clone()),
                );
                assert!(!self.occurs_in(tv, &new_row), "infinite row type");
                self.subst.insert(tv, new_row);
                (field_ty, new_rest)
            }
            _ => panic!(
                "type error: expected row, got {}",
                self.display_type(&resolved)
            ),
        }
    }

    // ---- Generalization & Instantiation ----

    fn free_vars(&self, ty: &Type) -> HashSet<TypeVar> {
        let resolved = self.resolve(ty);
        match &resolved {
            Type::Var(v) => HashSet::from([*v]),
            Type::Con(_) | Type::RowEmpty => HashSet::new(),
            Type::App(_, args) => args.iter().flat_map(|a| self.free_vars(a)).collect(),
            Type::Arrow(params, ret) => {
                let mut fvs: HashSet<TypeVar> =
                    params.iter().flat_map(|p| self.free_vars(p)).collect();
                fvs.extend(self.free_vars(ret));
                fvs
            }
            Type::Record(row) => self.free_vars(row),
            Type::RowExtend(_, field_ty, rest) => {
                let mut fvs = self.free_vars(field_ty);
                fvs.extend(self.free_vars(rest));
                fvs
            }
            Type::Tuple(elems) => elems.iter().flat_map(|e| self.free_vars(e)).collect(),
        }
    }

    fn free_vars_in_env(&self) -> HashSet<TypeVar> {
        self.env
            .values()
            .flat_map(|scheme| {
                let fvs = self.free_vars(&scheme.ty);
                let bound: HashSet<TypeVar> = scheme.vars.iter().copied().collect();
                fvs.into_iter().filter(move |v| !bound.contains(v))
            })
            .collect()
    }

    fn generalize(&self, ty: &Type) -> Scheme {
        let fvs = self.free_vars(ty);
        let env_fvs = self.free_vars_in_env();
        let vars: Vec<TypeVar> = fvs.into_iter().filter(|v| !env_fvs.contains(v)).collect();
        Scheme {
            vars,
            ty: self.resolve(ty),
        }
    }

    fn instantiate(&mut self, scheme: &Scheme) -> Type {
        let mapping: HashMap<TypeVar, Type> =
            scheme.vars.iter().map(|&v| (v, self.fresh())).collect();
        Self::apply_mapping(&scheme.ty, &mapping)
    }

    fn apply_mapping(ty: &Type, mapping: &HashMap<TypeVar, Type>) -> Type {
        match ty {
            Type::Var(v) => mapping.get(v).cloned().unwrap_or_else(|| ty.clone()),
            Type::Con(_) => ty.clone(),
            Type::App(name, args) => Type::App(
                name.clone(),
                args.iter()
                    .map(|a| Self::apply_mapping(a, mapping))
                    .collect(),
            ),
            Type::Arrow(params, ret) => Type::Arrow(
                params
                    .iter()
                    .map(|p| Self::apply_mapping(p, mapping))
                    .collect(),
                Box::new(Self::apply_mapping(ret, mapping)),
            ),
            Type::Record(row) => Type::Record(Box::new(Self::apply_mapping(row, mapping))),
            Type::RowEmpty => Type::RowEmpty,
            Type::RowExtend(label, field_ty, rest) => Type::RowExtend(
                label.clone(),
                Box::new(Self::apply_mapping(field_ty, mapping)),
                Box::new(Self::apply_mapping(rest, mapping)),
            ),
            Type::Tuple(elems) => Type::Tuple(
                elems
                    .iter()
                    .map(|e| Self::apply_mapping(e, mapping))
                    .collect(),
            ),
        }
    }

    // ---- Convert surface TypeExpr to inference Type ----

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
                    self.instantiate(&scheme)
                } else if name.starts_with(|c: char| c.is_ascii_lowercase()) {
                    // Lowercase names are implicit type variables
                    let tv = self.fresh();
                    let Type::Var(tv_id) = tv else { unreachable!() };
                    tvar_env.insert(name.to_owned(), tv_id);
                    tv
                } else {
                    Type::Con(name.to_owned())
                }
            }
            TypeExpr::App(name, args) => {
                let name = *name;
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
                self.fresh()
            }
            TypeExpr::Record(fields) => {
                let mut row = Type::RowEmpty;
                for (name, field_texpr) in fields.iter().rev() {
                    let field_ty = self.type_expr_to_type(field_texpr, tvar_env);
                    row = Type::RowExtend((*name).to_owned(), Box::new(field_ty), Box::new(row));
                }
                Type::Record(Box::new(row))
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
        // Create type variables for each type parameter
        let mut tvar_env: HashMap<String, TypeVar> = type_params
            .iter()
            .map(|p| {
                let tv = self.fresh();
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

    // ---- Expression inference ----

    #[expect(
        clippy::too_many_lines,
        reason = "expression inference handles all forms"
    )]
    fn infer_expr(&mut self, expr: &Expr<'src>) -> Type {
        self.current_span = expr.span;
        match &expr.kind {
            ExprKind::IntLit(_) => Type::Con("I64".to_owned()),

            ExprKind::Name(name) => {
                let name = *name;
                if let Some(scheme) = self.env.get(name).cloned() {
                    return self.instantiate(&scheme);
                }
                if let Some(scheme) = self.constructors.get(name).cloned() {
                    return self.instantiate(&scheme);
                }
                self.type_error(expr.span, &format!("undefined name '{name}'"));
            }

            ExprKind::BinOp { op, lhs, rhs } => {
                let lt = self.infer_expr(lhs);
                let rt = self.infer_expr(rhs);
                let i64_ty = Type::Con("I64".to_owned());
                match op {
                    BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Rem => {
                        self.unify(&lt, &i64_ty);
                        self.unify(&rt, &i64_ty);
                        i64_ty
                    }
                    BinOp::Eq | BinOp::Neq => {
                        self.unify(&lt, &rt);
                        Type::Con("Bool".to_owned())
                    }
                }
            }

            ExprKind::Call { func, args } => {
                let func = *func;
                self.infer_call(func, args)
            }

            ExprKind::QualifiedCall {
                owner,
                method,
                args,
            } => {
                let mangled = format!("{owner}.{method}");
                self.infer_call(&mangled, args)
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
                                let hint_ty = self.type_expr_to_type(&hint, &mut HashMap::new());
                                self.unify(&val_ty, &hint_ty);
                            }
                            let scheme = self.generalize(&val_ty);
                            self.env.insert(name.to_owned(), scheme);
                        }
                        Stmt::Destructure { pattern, val } => {
                            let val_ty = self.infer_expr(val);
                            let bindings = self.infer_pattern(pattern, &val_ty);
                            for (name, ty) in bindings {
                                let scheme = self.generalize(&ty);
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
                let result_ty = self.fresh();
                for arm in arms {
                    let bindings = self.infer_pattern(&arm.pattern, &scrutinee_ty);
                    let saved_env = self.env.clone();
                    for (name, ty) in bindings {
                        self.env.insert(name, Scheme::mono(ty));
                    }
                    let body_ty = self.infer_expr(&arm.body);
                    self.unify(&result_ty, &body_ty);
                    self.env = saved_env;
                }
                result_ty
            }

            ExprKind::Fold {
                expr: scrutinee,
                arms,
            } => {
                let scrutinee_ty = self.infer_expr(scrutinee);
                let result_ty = self.fresh();
                for arm in arms {
                    // In fold, recursive fields bind to the result type, not the scrutinee type
                    let bindings = self.infer_fold_pattern(&arm.pattern, &scrutinee_ty, &result_ty);
                    let saved_env = self.env.clone();
                    for (name, ty) in bindings {
                        self.env.insert(name, Scheme::mono(ty));
                    }
                    let body_ty = self.infer_expr(&arm.body);
                    self.unify(&result_ty, &body_ty);
                    self.env = saved_env;
                }
                result_ty
            }

            ExprKind::Record { fields } => {
                let mut row = Type::RowEmpty;
                for (name, field_expr) in fields.iter().rev() {
                    let field_ty = self.infer_expr(field_expr);
                    row = Type::RowExtend((*name).to_owned(), Box::new(field_ty), Box::new(row));
                }
                Type::Record(Box::new(row))
            }

            ExprKind::FieldAccess { record, field } => {
                let field = *field;
                let record_ty = self.infer_expr(record);
                let field_ty = self.fresh();
                let rest_row = self.fresh();
                let expected = Type::Record(Box::new(Type::RowExtend(
                    field.to_owned(),
                    Box::new(field_ty.clone()),
                    Box::new(rest_row),
                )));
                self.unify(&record_ty, &expected);
                field_ty
            }

            ExprKind::Lambda { params, body } => {
                let saved_env = self.env.clone();
                let param_types: Vec<Type> = params
                    .iter()
                    .map(|p| {
                        let ty = self.fresh();
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
        }
    }

    fn infer_call(&mut self, func: &str, args: &[Expr<'src>]) -> Type {
        let arg_types: Vec<Type> = args.iter().map(|a| self.infer_expr(a)).collect();
        let ret = self.fresh();

        if let Some(scheme) = self.constructors.get(func).cloned() {
            let con_ty = self.instantiate(&scheme);
            if arg_types.is_empty() {
                // Nullary constructor called with parens
                return con_ty;
            }
            let expected = Type::Arrow(arg_types, Box::new(ret.clone()));
            self.unify(&con_ty, &expected);
            return ret;
        }

        if let Some(scheme) = self.env.get(func).cloned() {
            let func_ty = self.instantiate(&scheme);
            let expected = Type::Arrow(arg_types, Box::new(ret.clone()));
            self.unify(&func_ty, &expected);
            return ret;
        }

        panic!("type error: undefined function '{func}'");
    }

    // ---- Pattern inference ----

    fn infer_pattern(&mut self, pat: &ast::Pattern<'src>, expected: &Type) -> Vec<(String, Type)> {
        match pat {
            ast::Pattern::Constructor { name, fields } => {
                let name = *name;
                let scheme = self
                    .constructors
                    .get(name)
                    .unwrap_or_else(|| panic!("type error: unknown constructor '{name}'"))
                    .clone();
                let con_ty = self.instantiate(&scheme);

                if fields.is_empty() {
                    // Nullary constructor
                    self.unify(&con_ty, expected);
                    vec![]
                } else {
                    // Constructor with fields
                    let field_types: Vec<Type> = fields.iter().map(|_| self.fresh()).collect();
                    let con_ret = self.fresh();
                    let arrow = Type::Arrow(field_types.clone(), Box::new(con_ret.clone()));
                    self.unify(&con_ty, &arrow);
                    self.unify(&con_ret, expected);

                    let mut bindings = Vec::new();
                    for (field_pat, field_ty) in fields.iter().zip(field_types.iter()) {
                        match field_pat {
                            ast::Pattern::Binding(n) => {
                                bindings.push(((*n).to_owned(), field_ty.clone()));
                            }
                            ast::Pattern::Wildcard => {}
                            ast::Pattern::Constructor { .. }
                            | ast::Pattern::Record { .. }
                            | ast::Pattern::Tuple(_) => {
                                bindings.extend(self.infer_pattern(field_pat, field_ty));
                            }
                        }
                    }
                    bindings
                }
            }
            ast::Pattern::Record { fields } => {
                let mut row = self.fresh(); // open rest
                let mut bindings = Vec::new();
                for (field_name, field_pat) in fields.iter().rev() {
                    let field_ty = self.fresh();
                    row = Type::RowExtend(
                        (*field_name).to_owned(),
                        Box::new(field_ty.clone()),
                        Box::new(row),
                    );
                    bindings.extend(self.infer_pattern(field_pat, &field_ty));
                }
                let expected_record = Type::Record(Box::new(row));
                self.unify(&expected_record, expected);
                bindings
            }
            ast::Pattern::Tuple(elems) => {
                let elem_types: Vec<Type> = elems.iter().map(|_| self.fresh()).collect();
                let tuple_ty = Type::Tuple(elem_types.clone());
                self.unify(&tuple_ty, expected);
                let mut bindings = Vec::new();
                for (elem_pat, elem_ty) in elems.iter().zip(elem_types.iter()) {
                    bindings.extend(self.infer_pattern(elem_pat, elem_ty));
                }
                bindings
            }
            ast::Pattern::Binding(name) => {
                vec![((*name).to_owned(), expected.clone())]
            }
            ast::Pattern::Wildcard => vec![],
        }
    }

    /// Like `infer_pattern` but for fold arms: recursive fields get the result type.
    fn infer_fold_pattern(
        &mut self,
        pat: &ast::Pattern<'src>,
        scrutinee_ty: &Type,
        result_ty: &Type,
    ) -> Vec<(String, Type)> {
        match pat {
            ast::Pattern::Constructor { name, fields } => {
                let name = *name;
                let scheme = self
                    .constructors
                    .get(name)
                    .unwrap_or_else(|| panic!("type error: unknown constructor '{name}'"))
                    .clone();
                let con_ty = self.instantiate(&scheme);

                if fields.is_empty() {
                    self.unify(&con_ty, scrutinee_ty);
                    vec![]
                } else {
                    let field_types: Vec<Type> = fields.iter().map(|_| self.fresh()).collect();
                    let con_ret = self.fresh();
                    let arrow = Type::Arrow(field_types.clone(), Box::new(con_ret.clone()));
                    self.unify(&con_ty, &arrow);
                    self.unify(&con_ret, scrutinee_ty);

                    // Determine which fields are recursive (same type as the scrutinee)
                    let mut bindings = Vec::new();
                    for (field_pat, field_ty) in fields.iter().zip(field_types.iter()) {
                        let resolved = self.resolve(field_ty);
                        let scrutinee_resolved = self.resolve(scrutinee_ty);
                        // If the field type unifies with the scrutinee type, it is recursive —
                        // bind to the result type instead.
                        let bind_ty = if self.types_match(&resolved, &scrutinee_resolved) {
                            result_ty.clone()
                        } else {
                            field_ty.clone()
                        };
                        match field_pat {
                            ast::Pattern::Binding(n) => {
                                bindings.push(((*n).to_owned(), bind_ty));
                            }
                            ast::Pattern::Wildcard => {}
                            ast::Pattern::Constructor { .. } => {
                                panic!("nested constructor patterns not supported in fold");
                            }
                            ast::Pattern::Record { .. } | ast::Pattern::Tuple(_) => {
                                bindings.extend(self.infer_pattern(field_pat, &bind_ty));
                            }
                        }
                    }
                    bindings
                }
            }
            _ => panic!("fold arms must use constructor patterns"),
        }
    }

    /// Check if two resolved types are structurally equal (without unifying).
    fn types_match(&self, a: &Type, b: &Type) -> bool {
        let a_resolved = self.resolve(a);
        let b_resolved = self.resolve(b);
        match (&a_resolved, &b_resolved) {
            (Type::Var(x), Type::Var(y)) => x == y,
            (Type::Con(x), Type::Con(y)) => x == y,
            (Type::App(n1, a1), Type::App(n2, a2)) => {
                n1 == n2
                    && a1.len() == a2.len()
                    && a1
                        .iter()
                        .zip(a2.iter())
                        .all(|(x, y)| self.types_match(x, y))
            }
            _ => false,
        }
    }

    // ---- Display helpers ----

    fn display_type(&self, ty: &Type) -> String {
        let resolved = self.resolve(ty);
        match &resolved {
            Type::Var(tv) => format!("t{}", tv.0),
            Type::Con(name) => name.clone(),
            Type::App(name, args) => {
                let arg_strs: Vec<String> = args.iter().map(|a| self.display_type(a)).collect();
                format!("{name}({})", arg_strs.join(", "))
            }
            Type::Arrow(params, ret) => {
                let param_strs: Vec<String> = params.iter().map(|p| self.display_type(p)).collect();
                format!("{} -> {}", param_strs.join(", "), self.display_type(ret))
            }
            Type::Record(row) => {
                let mut field_strs = Vec::new();
                let mut current = self.resolve(row);
                loop {
                    match current {
                        Type::RowExtend(label, field_ty, rest) => {
                            field_strs.push(format!("{label}: {}", self.display_type(&field_ty)));
                            current = self.resolve(&rest);
                        }
                        Type::RowEmpty => break,
                        _ => {
                            field_strs.push("..".to_owned());
                            break;
                        }
                    }
                }
                format!("{{ {} }}", field_strs.join(", "))
            }
            Type::RowEmpty => "{}".to_owned(),
            Type::RowExtend(label, field_ty, rest) => {
                format!(
                    "{{ {label}: {} | {} }}",
                    self.display_type(field_ty),
                    self.display_type(rest)
                )
            }
            Type::Tuple(elems) => {
                let elem_strs: Vec<String> = elems.iter().map(|e| self.display_type(e)).collect();
                format!("({})", elem_strs.join(", "))
            }
        }
    }
}

// ---- Public API ----

#[expect(
    clippy::too_many_lines,
    reason = "multi-pass type checking orchestration"
)]
pub fn check<'src>(source: &'src str, module: &Module<'src>) {
    let mut ctx = InferCtx::new(source);

    // Register prelude: Bool : [True, False]
    ctx.register_type_decl(
        "Bool",
        &[],
        &[
            ast::TagDecl {
                name: "True",
                fields: vec![],
            },
            ast::TagDecl {
                name: "False",
                fields: vec![],
            },
        ],
    );

    // Pass 1: register all type declarations and function signatures
    for decl in &module.decls {
        match decl {
            Decl::TypeAnno {
                name,
                type_params,
                ty: TypeExpr::TagUnion(tags),
                methods,
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
                            let mangled = format!("{name}.{method_name}");
                            let param_types: Vec<Type> =
                                params.iter().map(|_| ctx.fresh()).collect();
                            let ret = ctx.fresh();
                            let func_ty = Type::Arrow(param_types, Box::new(ret));
                            ctx.env.insert(mangled, Scheme::mono(func_ty));
                        }
                        Decl::TypeAnno {
                            name: method_name,
                            ty,
                            ..
                        } => {
                            let method_name = *method_name;
                            let mangled = format!("{name}.{method_name}");
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
                            let t = ctx.fresh();
                            let Type::Var(tv) = t else { unreachable!() };
                            ((*p).to_owned(), tv)
                        })
                        .collect();
                    let tvars: Vec<TypeVar> = type_params.iter().map(|p| tvar_env[*p]).collect();
                    let alias_ty = ctx.type_expr_to_type(ty, &mut tvar_env);
                    ctx.type_aliases.insert(
                        name.to_owned(),
                        Scheme {
                            vars: tvars,
                            ty: alias_ty,
                        },
                    );
                } else {
                    // snake_case: value/function annotation (e.g. get_x : I64 -> I64)
                    ctx.type_annos.insert(name.to_owned(), ty.clone());
                }
            }
            Decl::FuncDef { name, params, .. } => {
                let name = *name;
                let param_types: Vec<Type> = params.iter().map(|_| ctx.fresh()).collect();
                let ret = ctx.fresh();
                let func_ty = Type::Arrow(param_types, Box::new(ret));
                ctx.env.insert(name.to_owned(), Scheme::mono(func_ty));
            }
        }
    }

    // Pass 2: infer all function bodies
    for decl in &module.decls {
        match decl {
            Decl::FuncDef { name, params, body } => {
                let name = *name;
                let saved_env = ctx.env.clone();
                let pre_scheme = ctx.env[name].clone();
                let func_ty = ctx.instantiate(&pre_scheme);

                let param_types: Vec<Type> = params.iter().map(|_| ctx.fresh()).collect();
                let ret = ctx.fresh();
                let expected = Type::Arrow(param_types.clone(), Box::new(ret.clone()));
                ctx.unify(&func_ty, &expected);

                for (p, ty) in params.iter().zip(param_types.iter()) {
                    ctx.env.insert((*p).to_owned(), Scheme::mono(ty.clone()));
                }
                let body_ty = ctx.infer_expr(body);
                ctx.unify(&ret, &body_ty);

                if let Some(anno) = ctx.type_annos.get(name).cloned() {
                    let anno_ty = ctx.type_expr_to_type(&anno, &mut HashMap::new());
                    ctx.unify(&func_ty, &anno_ty);
                }

                ctx.env = saved_env;
                ctx.env.remove(name); // remove monomorphic binding before generalizing

                let resolved = ctx.resolve(&func_ty);
                let generalized = ctx.generalize(&resolved);
                ctx.env.insert(name.to_owned(), generalized);
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
                        let method_name = *method_name;
                        let mangled = format!("{name}.{method_name}");
                        let saved_env = ctx.env.clone();
                        let pre_scheme = ctx.env[&mangled].clone();
                        let func_ty = ctx.instantiate(&pre_scheme);

                        let param_types: Vec<Type> = params.iter().map(|_| ctx.fresh()).collect();
                        let ret = ctx.fresh();
                        let expected = Type::Arrow(param_types.clone(), Box::new(ret.clone()));
                        ctx.unify(&func_ty, &expected);

                        for (p, ty) in params.iter().zip(param_types.iter()) {
                            ctx.env.insert((*p).to_owned(), Scheme::mono(ty.clone()));
                        }
                        let body_ty = ctx.infer_expr(body);
                        ctx.unify(&ret, &body_ty);

                        if let Some(anno) = ctx.type_annos.get(&mangled).cloned() {
                            let anno_ty = ctx.type_expr_to_type(&anno, &mut HashMap::new());
                            ctx.unify(&func_ty, &anno_ty);
                        }

                        ctx.env = saved_env;
                        ctx.env.remove(&mangled);

                        let resolved = ctx.resolve(&func_ty);
                        let generalized = ctx.generalize(&resolved);
                        ctx.env.insert(mangled, generalized);
                    }
                }
            }
        }
    }
}
