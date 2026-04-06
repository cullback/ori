use std::collections::{HashMap, HashSet};

use crate::core::builder::Builder;
use crate::core::{
    Builtin, ConstructorDef, Core, FieldDef, FoldArm, FuncDef, FuncId, Pattern, Program, VarId,
};
use crate::stdlib;
use crate::syntax::ast::{self, BinOp, Decl, Expr, ExprKind, Module, Stmt, TypeExpr};
use crate::syntax::parse;

/// Build a mangled key for a method on a type, e.g. `method_key("List", "sum")` -> `"List.sum"`.
fn method_key(type_name: &str, method: &str) -> String {
    format!("{type_name}.{method}")
}

/// Lower a parsed AST module into a Core IR program.
///
/// Returns the program and the `VarId` of `main`'s input parameter
/// (a free variable that the runtime must bind before evaluation).
#[expect(clippy::too_many_lines, reason = "multi-pass lowering orchestration")]
pub fn lower(
    module: &Module<'_>,
    scope: &crate::resolve::ModuleScope,
    lit_types: &HashMap<ast::Span, crate::types::infer::NumType>,
) -> (Program, VarId) {
    let mut ctx = LowerCtx::new(lit_types.clone());

    // Register stdlib modules
    let bool_stdlib = ctx.register_stdlib_module("Bool");
    ctx.register_comparison_builtins();
    let result_stdlib = ctx.register_stdlib_module("Result");
    let maybe_stdlib = ctx.register_stdlib_module("Maybe");
    let list_stdlib = ctx.register_stdlib_module("List");
    let bool_methods = LowerCtx::extract_methods(&bool_stdlib);
    let result_methods = LowerCtx::extract_methods(&result_stdlib);
    let maybe_methods = LowerCtx::extract_methods(&maybe_stdlib);
    let list_methods = LowerCtx::extract_methods(&list_stdlib);

    // Pass 1: register user type declarations and function names
    ctx.register_decls(&module.decls);

    // Register module-qualified aliases for imported types
    for decl in &module.decls {
        if let Decl::TypeAnno { name, methods, .. } = decl {
            let name = *name;
            if let Some(mod_name) = scope.qualified_types.get(name) {
                for method_decl in methods {
                    if let Decl::FuncDef {
                        name: method_name, ..
                    } = method_decl
                    {
                        let method_name = *method_name;
                        let internal = method_key(name, method_name);
                        let qualified = format!("{mod_name}.{internal}");
                        if let Some(&func_id) = ctx.funcs.get(&internal) {
                            ctx.funcs.insert(qualified.clone(), func_id);
                        }
                        if let Some(&arity) = ctx.func_arities.get(&internal) {
                            ctx.func_arities.insert(qualified, arity);
                        }
                    }
                }
            }
        }
    }

    // Register module-qualified aliases for imported free functions
    for decl in &module.decls {
        if let Decl::FuncDef { name, .. } = decl {
            let name = *name;
            if let Some(mod_name) = scope.qualified_funcs.get(name) {
                let qualified = format!("{mod_name}.{name}");
                if let Some(&func_id) = ctx.funcs.get(name) {
                    ctx.funcs.insert(qualified.clone(), func_id);
                }
                if let Some(&arity) = ctx.func_arities.get(name) {
                    ctx.func_arities.insert(qualified, arity);
                }
            }
        }
    }

    // Compute reachable functions from main (skip dead code)
    let mut all_stdlib_methods = bool_methods;
    all_stdlib_methods.extend(&result_methods);
    all_stdlib_methods.extend(&maybe_methods);
    all_stdlib_methods.extend(&list_methods);
    ctx.compute_reachable_with_stdlib(&module.decls, &all_stdlib_methods);

    // Pass 1.5: scan reachable bodies to collect lambdas for defunctionalization
    ctx.collect_lambdas(&module.decls);
    // Also scan stdlib method bodies for lambdas
    for &(type_name, method) in &all_stdlib_methods {
        if let Decl::FuncDef {
            name, params, body, ..
        } = method
        {
            let mangled = method_key(type_name, name);
            if ctx.reachable.contains(&mangled) {
                // Mark higher-order params so captured closures are tracked
                for (i, p) in params.iter().enumerate() {
                    let key = (mangled.clone(), i);
                    if let Some(&ls_idx) = ctx.ho_param_sets.get(&key) {
                        ctx.ho_vars.insert((*p).to_owned(), ls_idx);
                    }
                }
                ctx.scan_expr(body);
                for p in params {
                    ctx.ho_vars.remove(*p);
                }
            }
        }
    }

    // Duplicate ho_param_sets entries for qualified aliases
    let alias_entries: Vec<((String, usize), usize)> = ctx
        .ho_param_sets
        .iter()
        .filter_map(|((name, idx), &ls_idx)| {
            // If this is a qualified name like "list.List.map", also register "List.map"
            ctx.funcs.iter().find_map(|(other_key, &other_fid)| {
                (other_key != name && ctx.funcs.get(name).is_some_and(|&fid| fid == other_fid))
                    .then(|| ((other_key.clone(), *idx), ls_idx))
            })
        })
        .collect();
    for (key, ls_idx) in alias_entries {
        ctx.ho_param_sets.entry(key).or_insert(ls_idx);
    }

    ctx.register_lambda_types();

    // Pass 2: lower all function bodies
    let mut main_params = None;
    let mut main_body = None;

    for decl in &module.decls {
        let Decl::FuncDef { name, params, body } = decl else {
            continue;
        };
        let name = *name;

        if name == "main" {
            main_params = Some(params.clone());
            main_body = Some(body.clone());
            continue;
        }

        if !ctx.reachable.contains(name) {
            continue;
        }

        let func_id = ctx.funcs[name];
        let param_vars: Vec<VarId> = params
            .iter()
            .map(|p| {
                let v = ctx.builder.var();
                ctx.vars.insert((*p).to_owned(), v);
                v
            })
            .collect();

        // Mark higher-order parameters
        for (i, p) in params.iter().enumerate() {
            let key = (name.to_owned(), i);
            if let Some(&ls_idx) = ctx.ho_param_sets.get(&key) {
                ctx.ho_vars.insert((*p).to_owned(), ls_idx);
            }
        }

        let body_core = ctx.lower_expr(body);
        for p in params {
            ctx.vars.remove(*p);
            ctx.ho_vars.remove(*p);
        }
        ctx.builder.add_func(FuncDef {
            name: func_id,
            params: param_vars,
            body: body_core,
        });
    }

    // Lower associated function bodies
    for decl in &module.decls {
        let Decl::TypeAnno {
            name: type_name,
            methods,
            ..
        } = decl
        else {
            continue;
        };
        let type_name = *type_name;
        for method_decl in methods {
            let Decl::FuncDef {
                name: method_name,
                params,
                body,
            } = method_decl
            else {
                continue;
            };
            let method_name = *method_name;
            let mangled = method_key(type_name, method_name);
            if !ctx.reachable.contains(&mangled) {
                continue;
            }
            let func_id = ctx.funcs[&mangled];
            let param_vars: Vec<VarId> = params
                .iter()
                .map(|p| {
                    let v = ctx.builder.var();
                    ctx.vars.insert((*p).to_owned(), v);
                    v
                })
                .collect();

            for (i, p) in params.iter().enumerate() {
                let key = (mangled.clone(), i);
                if let Some(&ls_idx) = ctx.ho_param_sets.get(&key) {
                    ctx.ho_vars.insert((*p).to_owned(), ls_idx);
                }
            }

            let body_core = ctx.lower_expr(body);
            for p in params {
                ctx.vars.remove(*p);
                ctx.ho_vars.remove(*p);
            }
            ctx.builder.add_func(FuncDef {
                name: func_id,
                params: param_vars,
                body: body_core,
            });
        }
    }

    // Lower stdlib method bodies
    ctx.lower_stdlib_methods(&all_stdlib_methods);

    // Lower main
    let params = main_params.expect("no 'main' function defined");
    let body = main_body.unwrap();
    assert!(
        params.len() == 1,
        "main must take exactly one parameter, got {}",
        params.len()
    );

    let input_var = ctx.builder.var();
    ctx.vars.insert(params[0].to_owned(), input_var);

    // Mark main's higher-order params (unlikely but consistent)
    for (i, p) in params.iter().enumerate() {
        let key = ("main".to_owned(), i);
        if let Some(&ls_idx) = ctx.ho_param_sets.get(&key) {
            ctx.ho_vars.insert((*p).to_owned(), ls_idx);
        }
    }

    let main_core = ctx.lower_expr(&body);

    // Generate apply functions from collected lambda sets
    ctx.generate_apply_functions();

    let program = ctx.builder.build(main_core);
    (program, input_var)
}

// ---- Defunctionalization data structures ----

#[derive(Clone)]
struct LambdaEntry<'src> {
    tag: FuncId,
    captures: Vec<&'src str>,
    /// For each capture, if it's a higher-order variable, the lambda set index.
    capture_ho: Vec<Option<usize>>,
    params: Vec<&'src str>,
    body: Option<Expr<'src>>,
    func_ref: Option<FuncId>,
}

#[derive(Clone)]
struct LambdaSet<'src> {
    apply_func: FuncId,
    entries: Vec<LambdaEntry<'src>>,
    arity: usize,
}

// ---- Lowering context ----

struct LowerCtx<'src> {
    builder: Builder,
    vars: HashMap<String, VarId>,
    funcs: HashMap<String, FuncId>,
    func_arities: HashMap<String, usize>,
    constructors: HashMap<String, FuncId>,
    /// Per-field recursive flags for each constructor (e.g. Cons -> [false, true]).
    constructor_fields: HashMap<String, Vec<bool>>,
    binops: HashMap<BinOp, FuncId>,

    /// Built-in List function IDs.
    list_builtins: HashMap<String, FuncId>,

    // Defunctionalization state
    lambda_sets: Vec<LambdaSet<'src>>,
    /// Maps (callee, param index) to lambda set index.
    ho_param_sets: HashMap<(String, usize), usize>,
    /// Maps higher-order parameter names to their lambda set index.
    ho_vars: HashMap<String, usize>,
    /// Counter to match lambdas between collect and lower passes
    lambda_arg_counters: HashMap<(String, usize), usize>,
    /// Functions reachable from main (dead code is not lowered).
    reachable: HashSet<String>,
    /// Resolved literal types from type inference.
    lit_types: HashMap<ast::Span, crate::types::infer::NumType>,
}

impl<'src> LowerCtx<'src> {
    fn new(lit_types: HashMap<ast::Span, crate::types::infer::NumType>) -> Self {
        let mut builder = Builder::new();
        let mut binops = HashMap::new();

        binops.insert(BinOp::Add, builder.builtin(Builtin::Add));
        binops.insert(BinOp::Sub, builder.builtin(Builtin::Sub));
        binops.insert(BinOp::Mul, builder.builtin(Builtin::Mul));
        binops.insert(BinOp::Div, builder.builtin(Builtin::Div));
        binops.insert(BinOp::Rem, builder.builtin(Builtin::Rem));
        // Eq and Neq are registered after the prelude defines Bool

        let mut list_builtins = HashMap::new();
        list_builtins.insert("List.len".to_owned(), builder.builtin(Builtin::ListLen));
        list_builtins.insert("List.get".to_owned(), builder.builtin(Builtin::ListGet));
        list_builtins.insert(
            "List.append".to_owned(),
            builder.builtin(Builtin::ListAppend),
        );
        list_builtins.insert(
            "List.reverse".to_owned(),
            builder.builtin(Builtin::ListReverse),
        );

        Self {
            builder,
            vars: HashMap::new(),
            funcs: HashMap::new(),
            func_arities: HashMap::new(),
            constructors: HashMap::new(),
            constructor_fields: HashMap::new(),
            binops,
            list_builtins,
            lambda_sets: Vec::new(),
            ho_param_sets: HashMap::new(),
            ho_vars: HashMap::new(),
            lambda_arg_counters: HashMap::new(),
            reachable: HashSet::new(),
            lit_types,
        }
    }

    /// Parse a stdlib module and register its types, constructors, and method signatures.
    fn register_stdlib_module(&mut self, module_name: &str) -> Module<'static> {
        let stdlib = parse::parse(stdlib::get(module_name).unwrap_or(""));
        self.register_decls(&stdlib.decls);
        stdlib
    }

    /// Extract `(type_name, method_decl)` pairs from a parsed stdlib module.
    fn extract_methods<'a>(stdlib: &'a Module<'static>) -> Vec<(&'static str, &'a Decl<'static>)> {
        let mut methods = Vec::new();
        for decl in &stdlib.decls {
            if let Decl::TypeAnno {
                name,
                methods: type_methods,
                ..
            } = decl
            {
                for m in type_methods {
                    methods.push((*name, m));
                }
            }
        }
        methods
    }

    // ---- Pass 1: Register declarations ----

    fn register_decls(&mut self, decls: &[Decl<'src>]) {
        for decl in decls {
            match decl {
                Decl::TypeAnno {
                    name,
                    ty: TypeExpr::TagUnion(tags),
                    methods,
                    ..
                } => {
                    let name = *name;
                    self.register_tag_union(name, tags);
                    for method_decl in methods {
                        if let Decl::FuncDef {
                            name: method_name,
                            params,
                            ..
                        } = method_decl
                        {
                            let method_name = *method_name;
                            let mangled = method_key(name, method_name);
                            let func_id = self.builder.func();
                            self.funcs.insert(mangled.clone(), func_id);
                            self.func_arities.insert(mangled, params.len());
                        }
                    }
                }
                Decl::TypeAnno { name, methods, .. } => {
                    // Non-TagUnion type with methods (e.g. List)
                    let name = *name;
                    for method_decl in methods {
                        if let Decl::FuncDef {
                            name: method_name,
                            params,
                            ..
                        } = method_decl
                        {
                            let method_name = *method_name;
                            let mangled = method_key(name, method_name);
                            if !self.funcs.contains_key(&mangled) {
                                let func_id = self.builder.func();
                                self.funcs.insert(mangled.clone(), func_id);
                                self.func_arities.insert(mangled, params.len());
                            }
                        }
                    }
                }
                Decl::FuncDef { name, params, .. } => {
                    let name = *name;
                    let func_id = self.builder.func();
                    self.funcs.insert(name.to_owned(), func_id);
                    self.func_arities.insert(name.to_owned(), params.len());
                }
            }
        }
    }

    /// Lower the bodies of stdlib methods that are reachable.
    fn lower_stdlib_methods(&mut self, methods: &[(&str, &Decl<'src>)]) {
        for &(type_name, method) in methods {
            if let Decl::FuncDef { name, params, body } = method {
                let mangled = method_key(type_name, name);
                if !self.reachable.contains(&mangled) {
                    continue;
                }
                let func_id = self.funcs[&mangled];
                let param_vars: Vec<VarId> = params
                    .iter()
                    .map(|p| {
                        let v = self.builder.var();
                        self.vars.insert((*p).to_owned(), v);
                        v
                    })
                    .collect();
                for (i, p) in params.iter().enumerate() {
                    let key = (mangled.clone(), i);
                    if let Some(&ls_idx) = self.ho_param_sets.get(&key) {
                        self.ho_vars.insert((*p).to_owned(), ls_idx);
                    }
                }
                let body_core = self.lower_expr(body);
                for p in params {
                    self.vars.remove(*p);
                    self.ho_vars.remove(*p);
                }
                self.builder.add_func(FuncDef {
                    name: func_id,
                    params: param_vars,
                    body: body_core,
                });
            }
        }
    }

    fn register_comparison_builtins(&mut self) {
        let true_con = *self
            .constructors
            .get("True")
            .expect("prelude must define True");
        let false_con = *self
            .constructors
            .get("False")
            .expect("prelude must define False");
        let eq = self.builder.builtin(Builtin::Eq {
            true_con,
            false_con,
        });
        let neq = self.builder.builtin(Builtin::Eq {
            true_con: false_con,
            false_con: true_con,
        });
        self.binops.insert(BinOp::Eq, eq);
        self.binops.insert(BinOp::Neq, neq);
    }

    fn compute_reachable_with_stdlib(
        &mut self,
        decls: &[Decl<'src>],
        stdlib_methods: &[(&str, &Decl<'static>)],
    ) {
        // Build function name → body index
        let mut bodies: HashMap<String, &Expr<'_>> = HashMap::new();
        // Add stdlib method bodies under Type.method
        for &(type_name, method) in stdlib_methods {
            if let Decl::FuncDef { name, body, .. } = method {
                bodies.insert(method_key(type_name, name), body);
            }
        }
        for decl in decls {
            match decl {
                Decl::FuncDef { name, body, .. } => {
                    bodies.insert((*name).to_owned(), body);
                }
                Decl::TypeAnno {
                    name: type_name,
                    methods,
                    ..
                } => {
                    for m in methods {
                        if let Decl::FuncDef {
                            name: method_name,
                            body,
                            ..
                        } = m
                        {
                            bodies.insert(method_key(type_name, method_name), body);
                        }
                    }
                }
            }
        }

        let mut worklist = vec!["main".to_owned()];
        while let Some(name) = worklist.pop() {
            if !self.reachable.insert(name.clone()) {
                continue;
            }
            if let Some(body) = bodies.get(&name) {
                Self::collect_refs(body, &mut worklist);
            }
        }

        // Expand reachable: if a qualified name is reachable, its internal alias is too
        let aliases: Vec<String> = self
            .funcs
            .iter()
            .filter_map(|(key, &fid)| {
                // If this key is reachable, find all other keys with the same FuncId
                if self.reachable.contains(key) {
                    self.funcs.iter().find_map(|(other_key, &other_fid)| {
                        (other_fid == fid && other_key != key).then(|| other_key.clone())
                    })
                } else {
                    None
                }
            })
            .collect();
        self.reachable.extend(aliases);
    }

    fn collect_refs(expr: &Expr<'_>, refs: &mut Vec<String>) {
        match &expr.kind {
            ExprKind::Call { func, args } => {
                refs.push((*func).to_owned());
                for a in args {
                    Self::collect_refs(a, refs);
                }
            }
            ExprKind::QualifiedCall { segments, args } => {
                refs.push(segments.join("."));
                for a in args {
                    Self::collect_refs(a, refs);
                }
            }
            ExprKind::Name(name) => {
                refs.push((*name).to_owned());
            }
            ExprKind::BinOp { lhs, rhs, .. } => {
                Self::collect_refs(lhs, refs);
                Self::collect_refs(rhs, refs);
            }
            ExprKind::Block(stmts, result) => {
                for stmt in stmts {
                    match stmt {
                        Stmt::Let { val, .. } | Stmt::Destructure { val, .. } => {
                            Self::collect_refs(val, refs);
                        }
                        Stmt::TypeHint { .. } => {}
                    }
                }
                Self::collect_refs(result, refs);
            }
            ExprKind::If {
                expr: e,
                arms,
                else_body,
            } => {
                Self::collect_refs(e, refs);
                for arm in arms {
                    Self::collect_refs(&arm.body, refs);
                }
                if let Some(eb) = else_body {
                    Self::collect_refs(eb, refs);
                }
            }
            ExprKind::Fold { expr: e, arms } => {
                Self::collect_refs(e, refs);
                for arm in arms {
                    Self::collect_refs(&arm.body, refs);
                }
            }
            ExprKind::Lambda { body, .. } => Self::collect_refs(body, refs),
            ExprKind::Record { fields } => {
                for (_, e) in fields {
                    Self::collect_refs(e, refs);
                }
            }
            ExprKind::FieldAccess { record, .. } => Self::collect_refs(record, refs),
            ExprKind::Tuple(elems) | ExprKind::ListLit(elems) => {
                for e in elems {
                    Self::collect_refs(e, refs);
                }
            }
            ExprKind::IntLit(_) | ExprKind::FloatLit(_) => {}
        }
    }

    fn register_tag_union(&mut self, type_name: &str, tags: &[ast::TagDecl<'src>]) {
        let mut con_defs = Vec::new();
        for tag in tags {
            let con_id = self.builder.func();
            self.constructors.insert(tag.name.to_owned(), con_id);
            let recursive_flags: Vec<bool> = tag
                .fields
                .iter()
                .map(|field_ty| {
                    matches!(field_ty, TypeExpr::Named(name) | TypeExpr::App(name, _) if *name == type_name)
                })
                .collect();
            self.constructor_fields
                .insert(tag.name.to_owned(), recursive_flags.clone());
            con_defs.push(ConstructorDef {
                tag: con_id,
                fields: recursive_flags
                    .iter()
                    .map(|&recursive| FieldDef { recursive })
                    .collect(),
            });
        }
        self.builder.add_type(con_defs);
    }

    // ---- Pass 1.5: Collect lambdas for defunctionalization ----

    fn collect_lambdas(&mut self, decls: &[Decl<'src>]) {
        for decl in decls {
            match decl {
                Decl::FuncDef { name, body, .. } => {
                    if self.reachable.contains(*name) {
                        self.scan_expr(body);
                    }
                }
                Decl::TypeAnno {
                    name: type_name,
                    methods,
                    ..
                } => {
                    for method_decl in methods {
                        if let Decl::FuncDef {
                            name: method_name,
                            body,
                            ..
                        } = method_decl
                        {
                            let mangled = method_key(type_name, method_name);
                            if self.reachable.contains(&mangled) {
                                self.scan_expr(body);
                            }
                        }
                    }
                }
            }
        }
    }

    fn scan_expr(&mut self, expr: &Expr<'src>) {
        match &expr.kind {
            ExprKind::Call { func, args } if self.funcs.contains_key(*func) => {
                self.scan_call_args(func, args);
            }
            ExprKind::Call { args, .. } => {
                for arg in args {
                    self.scan_expr(arg);
                }
            }
            ExprKind::BinOp { lhs, rhs, .. } => {
                self.scan_expr(lhs);
                self.scan_expr(rhs);
            }
            ExprKind::Block(stmts, result) => {
                for stmt in stmts {
                    match stmt {
                        Stmt::Let { val, .. } | Stmt::Destructure { val, .. } => {
                            self.scan_expr(val);
                        }
                        Stmt::TypeHint { .. } => {}
                    }
                }
                self.scan_expr(result);
            }
            ExprKind::If {
                expr: scrutinee,
                arms,
                else_body,
                ..
            } => {
                self.scan_expr(scrutinee);
                for arm in arms {
                    self.scan_expr(&arm.body);
                }
                if let Some(eb) = else_body {
                    self.scan_expr(eb);
                }
            }
            ExprKind::Fold {
                expr: scrutinee,
                arms,
            } => {
                self.scan_expr(scrutinee);
                for arm in arms {
                    self.scan_expr(&arm.body);
                }
            }
            ExprKind::QualifiedCall { segments, args } => {
                let mangled = segments.join(".");
                let is_list_ho = mangled == "List.walk" || mangled.ends_with(".List.walk");
                if is_list_ho || self.funcs.contains_key(&mangled) {
                    self.scan_call_args(&mangled, args);
                } else {
                    for arg in args {
                        self.scan_expr(arg);
                    }
                }
            }
            ExprKind::Lambda { body, .. } => {
                self.scan_expr(body);
            }
            ExprKind::Record { fields } => {
                for (_, field_expr) in fields {
                    self.scan_expr(field_expr);
                }
            }
            ExprKind::FieldAccess { record, .. } => {
                self.scan_expr(record);
            }
            ExprKind::Tuple(elems) | ExprKind::ListLit(elems) => {
                for e in elems {
                    self.scan_expr(e);
                }
            }
            ExprKind::IntLit(_) | ExprKind::FloatLit(_) | ExprKind::Name(_) => {}
        }
    }

    fn scan_call_args(&mut self, func_name: &str, args: &[Expr<'src>]) {
        for (i, arg) in args.iter().enumerate() {
            match &arg.kind {
                ExprKind::Lambda { params, body } => {
                    let free = self.compute_free_vars(body, params);
                    self.register_lambda(func_name, i, params.clone(), Some(body), free, None);
                }
                ExprKind::Name(name) => {
                    let name = *name;
                    if self.funcs.contains_key(name) && !self.constructors.contains_key(name) {
                        let func_id = self.funcs[name];
                        let arity = self.func_arities[name];
                        self.register_lambda(
                            func_name,
                            i,
                            Vec::new(),
                            None,
                            Vec::new(),
                            Some((func_id, arity)),
                        );
                    }
                }
                _ => {}
            }
            self.scan_expr(arg);
        }
    }

    fn register_lambda(
        &mut self,
        callee_func: &str,
        arg_index: usize,
        params: Vec<&'src str>,
        body: Option<&Expr<'src>>,
        captures: Vec<&'src str>,
        func_ref: Option<(FuncId, usize)>,
    ) {
        let key = (callee_func.to_owned(), arg_index);
        let arity = if let Some((_, a)) = func_ref {
            a
        } else {
            params.len()
        };

        let ls_idx = if let Some(&idx) = self.ho_param_sets.get(&key) {
            assert!(
                self.lambda_sets[idx].arity == arity,
                "arity mismatch in lambda set for {callee_func} arg {arg_index}"
            );
            idx
        } else {
            let apply_func = self.builder.func();
            let idx = self.lambda_sets.len();
            self.lambda_sets.push(LambdaSet {
                apply_func,
                entries: Vec::new(),
                arity,
            });
            self.ho_param_sets.insert(key, idx);
            idx
        };

        let capture_ho: Vec<Option<usize>> = captures
            .iter()
            .map(|name| self.ho_vars.get(*name).copied())
            .collect();
        let tag = self.builder.func();
        self.lambda_sets[ls_idx].entries.push(LambdaEntry {
            tag,
            capture_ho,
            captures,
            params,
            body: body.cloned(),
            func_ref: func_ref.map(|(fid, _)| fid),
        });
    }

    fn compute_free_vars(&self, body: &Expr<'src>, params: &[&'src str]) -> Vec<&'src str> {
        let mut free = Vec::new();
        let mut seen = HashSet::new();
        let bound: HashSet<&str> = params.iter().copied().collect();
        self.collect_free(body, &bound, &mut seen, &mut free);
        free
    }

    fn collect_free(
        &self,
        expr: &Expr<'src>,
        bound: &HashSet<&'src str>,
        seen: &mut HashSet<&'src str>,
        free: &mut Vec<&'src str>,
    ) {
        match &expr.kind {
            ExprKind::Name(name) => {
                let name = *name;
                if !bound.contains(name)
                    && !self.constructors.contains_key(name)
                    && !self.funcs.contains_key(name)
                    && !seen.contains(name)
                {
                    seen.insert(name);
                    free.push(name);
                }
            }
            ExprKind::IntLit(_) | ExprKind::FloatLit(_) => {}
            ExprKind::BinOp { lhs, rhs, .. } => {
                self.collect_free(lhs, bound, seen, free);
                self.collect_free(rhs, bound, seen, free);
            }
            ExprKind::Call { func, args } => {
                // func might be a captured variable used as a function
                if !bound.contains(func)
                    && !self.constructors.contains_key(*func)
                    && !self.funcs.contains_key(*func)
                    && !self.list_builtins.contains_key(&method_key("List", func))
                    && !seen.contains(func)
                {
                    seen.insert(func);
                    free.push(func);
                }
                for arg in args {
                    self.collect_free(arg, bound, seen, free);
                }
            }
            ExprKind::QualifiedCall { args, .. } => {
                for arg in args {
                    self.collect_free(arg, bound, seen, free);
                }
            }
            ExprKind::Record { fields } => {
                for (_, field_expr) in fields {
                    self.collect_free(field_expr, bound, seen, free);
                }
            }
            ExprKind::FieldAccess { record, .. } => {
                self.collect_free(record, bound, seen, free);
            }
            ExprKind::Lambda { params, body } => {
                let mut inner = bound.clone();
                for p in params {
                    inner.insert(p);
                }
                self.collect_free(body, &inner, seen, free);
            }
            ExprKind::Tuple(elems) | ExprKind::ListLit(elems) => {
                for e in elems {
                    self.collect_free(e, bound, seen, free);
                }
            }
            ExprKind::Block(stmts, result) => {
                let mut inner = bound.clone();
                for stmt in stmts {
                    match stmt {
                        Stmt::Let { name, val } => {
                            self.collect_free(val, &inner, seen, free);
                            inner.insert(name);
                        }
                        Stmt::Destructure { pattern, val } => {
                            self.collect_free(val, &inner, seen, free);
                            Self::pattern_names(pattern, &mut inner);
                        }
                        Stmt::TypeHint { .. } => {}
                    }
                }
                self.collect_free(result, &inner, seen, free);
            }
            ExprKind::If {
                expr: scrutinee,
                arms,
                else_body,
            } => {
                self.collect_free(scrutinee, bound, seen, free);
                for arm in arms {
                    let mut arm_bound = bound.clone();
                    Self::pattern_names(&arm.pattern, &mut arm_bound);
                    self.collect_free(&arm.body, &arm_bound, seen, free);
                }
                if let Some(eb) = else_body {
                    self.collect_free(eb, bound, seen, free);
                }
            }
            ExprKind::Fold {
                expr: scrutinee,
                arms,
            } => {
                self.collect_free(scrutinee, bound, seen, free);
                for arm in arms {
                    let mut arm_bound = bound.clone();
                    Self::pattern_names(&arm.pattern, &mut arm_bound);
                    self.collect_free(&arm.body, &arm_bound, seen, free);
                }
            }
        }
    }

    fn pattern_names(pat: &ast::Pattern<'src>, bound: &mut HashSet<&'src str>) {
        match pat {
            ast::Pattern::Constructor { fields, .. } => {
                for f in fields {
                    Self::pattern_names(f, bound);
                }
            }
            ast::Pattern::Record { fields } => {
                for (_, field_pat) in fields {
                    Self::pattern_names(field_pat, bound);
                }
            }
            ast::Pattern::Tuple(elems) => {
                for e in elems {
                    Self::pattern_names(e, bound);
                }
            }
            ast::Pattern::Binding(name) => {
                bound.insert(name);
            }
            ast::Pattern::Wildcard => {}
        }
    }

    /// Register constructor types for all lambda sets (after collection, before lowering).
    fn register_lambda_types(&mut self) {
        for ls in &self.lambda_sets {
            let con_defs: Vec<ConstructorDef> = ls
                .entries
                .iter()
                .map(|entry| ConstructorDef {
                    tag: entry.tag,
                    fields: entry
                        .captures
                        .iter()
                        .map(|_| FieldDef { recursive: false })
                        .collect(),
                })
                .collect();
            self.builder.add_type(con_defs);
        }
    }

    // ---- Pass 2: Lower expressions ----

    #[expect(clippy::too_many_lines, reason = "handles all expression forms")]
    fn lower_expr(&mut self, expr: &Expr<'src>) -> Core {
        match &expr.kind {
            #[expect(
                clippy::cast_sign_loss,
                clippy::cast_precision_loss,
                clippy::cast_possible_truncation
            )]
            ExprKind::IntLit(n) => match self.lit_types.get(&expr.span) {
                Some(crate::types::infer::NumType::U8) => Core::u8(*n as u8),
                Some(crate::types::infer::NumType::I8) => Core::i8(*n as i8),
                Some(crate::types::infer::NumType::U64) => Core::u64(*n as u64),
                Some(crate::types::infer::NumType::F64) => Core::f64(*n as f64),
                _ => Core::i64(*n),
            },
            ExprKind::FloatLit(n) => Core::f64(*n),

            ExprKind::Name(name) => {
                let name = *name;
                if let Some(&var_id) = self.vars.get(name) {
                    return Core::var(var_id);
                }
                if let Some(&con_id) = self.constructors.get(name) {
                    return Core::app(con_id, vec![]);
                }
                panic!("undefined name: {name}");
            }

            ExprKind::BinOp { op, lhs, rhs } => {
                let func_id = self.binops[op];
                Core::app(func_id, vec![self.lower_expr(lhs), self.lower_expr(rhs)])
            }

            ExprKind::Call { func, args } => self.lower_call(func, args),

            ExprKind::Block(stmts, result) => {
                let mut bindings = Vec::new();
                for stmt in stmts {
                    match stmt {
                        Stmt::Let { name, val } => {
                            let name = *name;
                            let val_core = self.lower_expr(val);
                            let var_id = self.builder.var();
                            self.vars.insert(name.to_owned(), var_id);
                            bindings.push((var_id, val_core));
                        }
                        Stmt::TypeHint { .. } => {} // handled by type checker
                        Stmt::Destructure { pattern, val } => {
                            let val_core = self.lower_expr(val);
                            let src_var = self.builder.var();
                            bindings.push((src_var, val_core));
                            self.lower_destructure(pattern, src_var, &mut bindings);
                        }
                    }
                }

                let mut result_core = self.lower_expr(result);
                for (var_id, val_core) in bindings.into_iter().rev() {
                    result_core = Core::let_(var_id, val_core, result_core);
                }
                result_core
            }

            ExprKind::If {
                expr: scrutinee_expr,
                arms,
                ..
            } => {
                let scrutinee = self.lower_expr(scrutinee_expr);
                let core_arms: Vec<(Pattern, Core)> = arms
                    .iter()
                    .map(|arm| {
                        let (pat, var_bindings) = self.lower_pattern(&arm.pattern);
                        for (name, var_id) in &var_bindings {
                            self.vars.insert(name.clone(), *var_id);
                        }
                        let body = self.lower_expr(&arm.body);
                        for (name, _) in &var_bindings {
                            self.vars.remove(name);
                        }
                        (pat, body)
                    })
                    .collect();
                Core::match_(scrutinee, core_arms)
            }

            ExprKind::Fold {
                expr: scrutinee_expr,
                arms,
            } => {
                let scrutinee = self.lower_expr(scrutinee_expr);
                let core_arms = arms.iter().map(|arm| self.lower_fold_arm(arm)).collect();
                Core::fold(scrutinee, core_arms)
            }

            ExprKind::QualifiedCall { segments, args } => {
                let mangled = segments.join(".");
                self.lower_call(&mangled, args)
            }

            ExprKind::Record { fields } => {
                let core_fields: Vec<(String, Core)> = fields
                    .iter()
                    .map(|(name, field_expr)| ((*name).to_owned(), self.lower_expr(field_expr)))
                    .collect();
                Core::record(core_fields)
            }

            ExprKind::FieldAccess { record, field } => {
                Core::field_access(self.lower_expr(record), (*field).to_owned())
            }

            ExprKind::Tuple(elems) => {
                let core_fields: Vec<(String, Core)> = elems
                    .iter()
                    .enumerate()
                    .map(|(i, e)| (i.to_string(), self.lower_expr(e)))
                    .collect();
                Core::record(core_fields)
            }

            ExprKind::Lambda { .. } => {
                panic!("lambdas are only supported as direct arguments to function calls");
            }

            ExprKind::ListLit(elems) => {
                let cores: Vec<Core> = elems.iter().map(|e| self.lower_expr(e)).collect();
                Core::list_lit(cores)
            }
        }
    }

    fn lower_call(&mut self, func: &str, args: &[Expr<'src>]) -> Core {
        // List.walk is special: emits Core::ListWalk with closure + apply_func
        if func == "List.walk" || func.ends_with(".List.walk") {
            assert!(args.len() >= 3, "List.walk takes 3 arguments");
            let list_core = self.lower_expr(&args[0]);
            let init_core = self.lower_expr(&args[1]);
            let key = (func.to_owned(), 2);
            let closure_core = if self.ho_param_sets.contains_key(&key) {
                self.lower_lambda_arg(&args[2], func, 2)
            } else {
                self.lower_expr(&args[2])
            };
            let ls_idx = self.ho_param_sets[&key];
            let apply_func = self.lambda_sets[ls_idx].apply_func;
            return Core::list_walk(list_core, init_core, closure_core, apply_func);
        }

        // Other List builtins
        if let Some(&builtin_id) = self.list_builtins.get(func) {
            let arg_cores: Vec<Core> = args.iter().map(|a| self.lower_expr(a)).collect();
            return Core::app(builtin_id, arg_cores);
        }

        if let Some(&con_id) = self.constructors.get(func) {
            let arg_cores: Vec<Core> = args.iter().map(|a| self.lower_expr(a)).collect();
            Core::app(con_id, arg_cores)
        } else if self.funcs.contains_key(func) {
            let fn_id = self.funcs[func];
            let arg_cores: Vec<Core> = args
                .iter()
                .enumerate()
                .map(|(i, a)| {
                    let key = (func.to_owned(), i);
                    if self.ho_param_sets.contains_key(&key) {
                        self.lower_lambda_arg(a, func, i)
                    } else {
                        self.lower_expr(a)
                    }
                })
                .collect();
            Core::app(fn_id, arg_cores)
        } else if let Some(&var_id) = self.vars.get(func) {
            if let Some(&ls_idx) = self.ho_vars.get(func) {
                let apply_func = self.lambda_sets[ls_idx].apply_func;
                let arg_cores: Vec<Core> = args.iter().map(|a| self.lower_expr(a)).collect();
                let mut full_args = vec![Core::var(var_id)];
                full_args.extend(arg_cores);
                Core::app(apply_func, full_args)
            } else {
                panic!("variable '{func}' called as function but has no lambda set");
            }
        } else {
            panic!("undefined function or constructor: {func}");
        }
    }

    #[expect(
        clippy::arithmetic_side_effects,
        reason = "index counter for lambda matching"
    )]
    fn lower_lambda_arg(&mut self, arg: &Expr<'src>, callee: &str, arg_idx: usize) -> Core {
        let key = (callee.to_owned(), arg_idx);
        let ls_idx = self.ho_param_sets[&key];
        let counter = self.lambda_arg_counters.entry(key).or_insert(0);
        let entry_idx = *counter;
        *counter += 1;

        let entry = &self.lambda_sets[ls_idx].entries[entry_idx];
        let tag = entry.tag;
        let captures: Vec<&'src str> = entry.captures.clone();

        match &arg.kind {
            ExprKind::Lambda { .. } => {
                let capture_vals: Vec<Core> = captures
                    .iter()
                    .map(|name| {
                        let &var_id = self
                            .vars
                            .get(*name)
                            .unwrap_or_else(|| panic!("captured variable '{name}' not in scope"));
                        Core::var(var_id)
                    })
                    .collect();
                Core::app(tag, capture_vals)
            }
            ExprKind::Name(_) => {
                // Function reference — nullary constructor
                Core::app(tag, vec![])
            }
            _ => panic!("expected lambda or function reference in higher-order argument"),
        }
    }

    // ---- Generate apply functions ----

    fn generate_apply_functions(&mut self) {
        // Clone lambda sets — we need them accessible during body lowering
        let sets: Vec<LambdaSet<'src>> = self.lambda_sets.clone();

        for ls in &sets {
            let closure_var = self.builder.var();
            let arg_vars: Vec<VarId> = std::iter::repeat_with(|| self.builder.var())
                .take(ls.arity)
                .collect();

            let match_arms: Vec<(Pattern, Core)> = ls
                .entries
                .iter()
                .map(|entry| {
                    if let Some(fid) = entry.func_ref {
                        let cap_vars: Vec<VarId> = std::iter::repeat_with(|| self.builder.var())
                            .take(entry.captures.len())
                            .collect();
                        let pattern = Pattern::con(entry.tag, cap_vars);
                        let dispatch =
                            Core::app(fid, arg_vars.iter().map(|&v| Core::var(v)).collect());
                        (pattern, dispatch)
                    } else {
                        let cap_vars: Vec<VarId> = std::iter::repeat_with(|| self.builder.var())
                            .take(entry.captures.len())
                            .collect();
                        let pattern = Pattern::con(entry.tag, cap_vars.clone());

                        for (cap_name, &cap_var) in entry.captures.iter().zip(&cap_vars) {
                            self.vars.insert((*cap_name).to_owned(), cap_var);
                        }
                        // Wire up ho_vars for captured higher-order variables
                        for (cap_name, ho_idx) in entry.captures.iter().zip(entry.capture_ho.iter())
                        {
                            if let Some(ls_idx) = ho_idx {
                                self.ho_vars.insert((*cap_name).to_owned(), *ls_idx);
                            }
                        }
                        for (param_name, &arg_var) in entry.params.iter().zip(&arg_vars) {
                            self.vars.insert((*param_name).to_owned(), arg_var);
                        }

                        let body_core = self.lower_expr(entry.body.as_ref().unwrap());

                        for cap_name in &entry.captures {
                            self.vars.remove(*cap_name);
                            self.ho_vars.remove(*cap_name);
                        }
                        for param_name in &entry.params {
                            self.vars.remove(*param_name);
                        }

                        (pattern, body_core)
                    }
                })
                .collect();

            let apply_body = Core::match_(Core::var(closure_var), match_arms);
            let mut all_params = vec![closure_var];
            all_params.extend(arg_vars);

            self.builder.add_func(FuncDef {
                name: ls.apply_func,
                params: all_params,
                body: apply_body,
            });
        }

        self.lambda_sets = sets;
    }

    // ---- Destructure lowering ----

    fn lower_destructure(
        &mut self,
        pattern: &ast::Pattern<'src>,
        source_var: VarId,
        bindings: &mut Vec<(VarId, Core)>,
    ) {
        match pattern {
            ast::Pattern::Tuple(elems) => {
                for (i, elem) in elems.iter().enumerate() {
                    let field_var = self.builder.var();
                    let access = Core::field_access(Core::var(source_var), i.to_string());
                    bindings.push((field_var, access));
                    self.lower_destructure_elem(elem, field_var, bindings);
                }
            }
            ast::Pattern::Record { fields } => {
                for (name, elem) in fields {
                    let field_var = self.builder.var();
                    let access = Core::field_access(Core::var(source_var), (*name).to_owned());
                    bindings.push((field_var, access));
                    self.lower_destructure_elem(elem, field_var, bindings);
                }
            }
            _ => panic!("expected tuple or record pattern in destructure"),
        }
    }

    fn lower_destructure_elem(
        &mut self,
        elem: &ast::Pattern<'src>,
        var: VarId,
        bindings: &mut Vec<(VarId, Core)>,
    ) {
        match elem {
            ast::Pattern::Binding(name) => {
                self.vars.insert((*name).to_owned(), var);
            }
            ast::Pattern::Tuple(_) | ast::Pattern::Record { .. } => {
                self.lower_destructure(elem, var, bindings);
            }
            ast::Pattern::Wildcard => {}
            ast::Pattern::Constructor { .. } => panic!("unsupported pattern in destructure"),
        }
    }

    // ---- Fold lowering ----

    fn lower_fold_arm(&mut self, arm: &ast::MatchArm<'src>) -> FoldArm {
        let ast::Pattern::Constructor { name: con_name, .. } = &arm.pattern else {
            panic!("fold arms must use constructor patterns");
        };
        let con_name = *con_name;
        let recursive_flags = self
            .constructor_fields
            .get(con_name)
            .unwrap_or_else(|| panic!("unknown constructor in fold: {con_name}"))
            .clone();

        let (pat, var_bindings) = self.lower_pattern(&arm.pattern);
        let Pattern::Constructor {
            fields: field_vars, ..
        } = &pat;

        // For recursive fields, create rec_bind vars and shadow the
        // user's name so the body references the fold result.
        let mut rec_binds = Vec::new();
        for (i, &is_rec) in recursive_flags.iter().enumerate() {
            if is_rec {
                let rec_var = self.builder.var();
                rec_binds.push(rec_var);
                if let Some((name, _)) = var_bindings.iter().find(|(_, vid)| *vid == field_vars[i])
                {
                    self.vars.insert(name.clone(), rec_var);
                }
            }
        }

        // Bind non-recursive field names
        for (name, var_id) in &var_bindings {
            self.vars.entry(name.clone()).or_insert(*var_id);
        }

        let body = self.lower_expr(&arm.body);

        for (name, _) in &var_bindings {
            self.vars.remove(name);
        }

        FoldArm {
            pattern: pat,
            rec_binds,
            body,
        }
    }

    // ---- Pattern lowering ----

    fn lower_pattern(&mut self, pat: &ast::Pattern<'src>) -> (Pattern, Vec<(String, VarId)>) {
        match pat {
            ast::Pattern::Constructor { name, fields } => {
                let name = *name;
                let con_id = *self
                    .constructors
                    .get(name)
                    .unwrap_or_else(|| panic!("unknown constructor in pattern: {name}"));
                let mut field_vars = Vec::new();
                let mut bindings = Vec::new();
                for field_pat in fields {
                    match field_pat {
                        ast::Pattern::Binding(binding_name) => {
                            let var_id = self.builder.var();
                            field_vars.push(var_id);
                            bindings.push(((*binding_name).to_owned(), var_id));
                        }
                        ast::Pattern::Wildcard => {
                            let var_id = self.builder.var();
                            field_vars.push(var_id);
                        }
                        ast::Pattern::Constructor { .. } => {
                            panic!("nested constructor patterns not yet supported");
                        }
                        ast::Pattern::Record { .. } => {
                            panic!("record patterns inside constructor patterns not yet supported");
                        }
                        ast::Pattern::Tuple(_) => {
                            panic!("tuple patterns inside constructor patterns not yet supported");
                        }
                    }
                }
                (Pattern::con(con_id, field_vars), bindings)
            }
            ast::Pattern::Record { .. } => {
                panic!("record patterns in match arms not yet supported in lowering");
            }
            ast::Pattern::Tuple(_) => {
                panic!("tuple patterns in match arms not yet supported in lowering");
            }
            ast::Pattern::Wildcard | ast::Pattern::Binding(_) => {
                panic!("top-level wildcard/binding patterns not yet supported in match arms");
            }
        }
    }
}
