use std::collections::{HashMap, HashSet};

use crate::ast::{self, BinOp, Decl, Expr, Module, Stmt, TypeExpr};
use crate::builder::Builder;
use crate::ir::{
    Builtin, ConstructorDef, Core, FieldDef, FoldArm, FuncDef, FuncId, Pattern, Program, VarId,
};
use crate::parse;

const PRELUDE: &str = "Bool : [True, False]\n";

/// Lower a parsed AST module into a Core IR program.
///
/// Returns the program and the `VarId` of `main`'s input parameter
/// (a free variable that the runtime must bind before evaluation).
#[expect(clippy::too_many_lines, reason = "multi-pass lowering orchestration")]
pub fn lower(module: &Module) -> (Program, VarId) {
    let mut ctx = LowerCtx::new();

    // Parse and register the prelude
    let prelude = parse::parse(PRELUDE);
    ctx.register_decls(&prelude.decls);

    // Now that Bool is known, register comparison builtins
    ctx.register_comparison_builtins();

    // Pass 1: register user type declarations and function names
    ctx.register_decls(&module.decls);

    // Pass 1.5: scan all bodies to collect lambdas for defunctionalization
    ctx.collect_lambdas(&module.decls);
    ctx.register_lambda_types();

    // Pass 2: lower all function bodies
    let mut main_params = None;
    let mut main_body = None;

    for decl in &module.decls {
        let Decl::FuncDef { name, params, body } = decl else {
            continue;
        };

        if name == "main" {
            main_params = Some(params.clone());
            main_body = Some(body.clone());
            continue;
        }

        let func_id = ctx.funcs[name];
        let param_vars: Vec<VarId> = params
            .iter()
            .map(|p| {
                let v = ctx.builder.var();
                ctx.vars.insert(p.clone(), v);
                v
            })
            .collect();

        // Mark higher-order parameters
        for (i, p) in params.iter().enumerate() {
            let key = (name.clone(), i);
            if let Some(&ls_idx) = ctx.ho_param_sets.get(&key) {
                ctx.ho_vars.insert(p.clone(), ls_idx);
            }
        }

        let body_core = ctx.lower_expr(body);
        for p in params {
            ctx.vars.remove(p);
            ctx.ho_vars.remove(p);
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
        for method_decl in methods {
            let Decl::FuncDef {
                name: method_name,
                params,
                body,
            } = method_decl
            else {
                continue;
            };
            let mangled = format!("{type_name}.{method_name}");
            let func_id = ctx.funcs[&mangled];
            let param_vars: Vec<VarId> = params
                .iter()
                .map(|p| {
                    let v = ctx.builder.var();
                    ctx.vars.insert(p.clone(), v);
                    v
                })
                .collect();

            for (i, p) in params.iter().enumerate() {
                let key = (mangled.clone(), i);
                if let Some(&ls_idx) = ctx.ho_param_sets.get(&key) {
                    ctx.ho_vars.insert(p.clone(), ls_idx);
                }
            }

            let body_core = ctx.lower_expr(body);
            for p in params {
                ctx.vars.remove(p);
                ctx.ho_vars.remove(p);
            }
            ctx.builder.add_func(FuncDef {
                name: func_id,
                params: param_vars,
                body: body_core,
            });
        }
    }

    // Lower main
    let params = main_params.expect("no 'main' function defined");
    let body = main_body.unwrap();
    assert!(
        params.len() == 1,
        "main must take exactly one parameter, got {}",
        params.len()
    );

    let input_var = ctx.builder.var();
    ctx.vars.insert(params[0].clone(), input_var);

    // Mark main's higher-order params (unlikely but consistent)
    for (i, p) in params.iter().enumerate() {
        let key = ("main".to_owned(), i);
        if let Some(&ls_idx) = ctx.ho_param_sets.get(&key) {
            ctx.ho_vars.insert(p.clone(), ls_idx);
        }
    }

    let main_core = ctx.lower_expr(&body);

    // Generate apply functions from collected lambda sets
    ctx.generate_apply_functions();

    let program = ctx.builder.build(main_core);
    (program, input_var)
}

// ---- Defunctionalization data structures ----

struct LambdaEntry {
    tag: FuncId,
    captures: Vec<String>,
    params: Vec<String>,
    body: Option<Expr>,
    func_ref: Option<FuncId>,
}

struct LambdaSet {
    apply_func: FuncId,
    entries: Vec<LambdaEntry>,
    arity: usize,
}

// ---- Lowering context ----

struct LowerCtx {
    builder: Builder,
    vars: HashMap<String, VarId>,
    funcs: HashMap<String, FuncId>,
    func_arities: HashMap<String, usize>,
    constructors: HashMap<String, FuncId>,
    /// Per-field recursive flags for each constructor (e.g. Cons -> [false, true]).
    constructor_fields: HashMap<String, Vec<bool>>,
    binops: HashMap<BinOp, FuncId>,

    // Defunctionalization state
    lambda_sets: Vec<LambdaSet>,
    /// Maps (callee, param index) to lambda set index.
    ho_param_sets: HashMap<(String, usize), usize>,
    /// Maps higher-order parameter names to their lambda set index.
    ho_vars: HashMap<String, usize>,
    /// Counter to match lambdas between collect and lower passes
    lambda_arg_counters: HashMap<(String, usize), usize>,
}

impl LowerCtx {
    fn new() -> Self {
        let mut builder = Builder::new();
        let mut binops = HashMap::new();

        binops.insert(BinOp::Add, builder.builtin(Builtin::Add));
        binops.insert(BinOp::Sub, builder.builtin(Builtin::Sub));
        binops.insert(BinOp::Mul, builder.builtin(Builtin::Mul));
        binops.insert(BinOp::Div, builder.builtin(Builtin::Mul)); // TODO: add Div builtin
        binops.insert(BinOp::Rem, builder.builtin(Builtin::Rem));
        // Eq and Neq are registered after the prelude defines Bool

        Self {
            builder,
            vars: HashMap::new(),
            funcs: HashMap::new(),
            func_arities: HashMap::new(),
            constructors: HashMap::new(),
            constructor_fields: HashMap::new(),
            binops,
            lambda_sets: Vec::new(),
            ho_param_sets: HashMap::new(),
            ho_vars: HashMap::new(),
            lambda_arg_counters: HashMap::new(),
        }
    }

    // ---- Pass 1: Register declarations ----

    fn register_decls(&mut self, decls: &[Decl]) {
        for decl in decls {
            match decl {
                Decl::TypeAnno {
                    name,
                    ty: TypeExpr::TagUnion(tags),
                    methods,
                    ..
                } => {
                    self.register_tag_union(name, tags);
                    for method_decl in methods {
                        if let Decl::FuncDef {
                            name: method_name,
                            params,
                            ..
                        } = method_decl
                        {
                            let mangled = format!("{name}.{method_name}");
                            let func_id = self.builder.func();
                            self.funcs.insert(mangled.clone(), func_id);
                            self.func_arities.insert(mangled, params.len());
                        }
                    }
                }
                Decl::TypeAnno { .. } => {}
                Decl::FuncDef { name, params, .. } => {
                    let func_id = self.builder.func();
                    self.funcs.insert(name.clone(), func_id);
                    self.func_arities.insert(name.clone(), params.len());
                }
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

    fn register_tag_union(&mut self, type_name: &str, tags: &[ast::TagDecl]) {
        let mut con_defs = Vec::new();
        for tag in tags {
            let con_id = self.builder.func();
            self.constructors.insert(tag.name.clone(), con_id);
            let recursive_flags: Vec<bool> = tag
                .fields
                .iter()
                .map(|field_ty| {
                    matches!(field_ty, TypeExpr::Named(name) | TypeExpr::App(name, _) if name == type_name)
                })
                .collect();
            self.constructor_fields
                .insert(tag.name.clone(), recursive_flags.clone());
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

    fn collect_lambdas(&mut self, decls: &[Decl]) {
        for decl in decls {
            match decl {
                Decl::FuncDef { body, .. } => self.scan_expr(body),
                Decl::TypeAnno { methods, .. } => {
                    for method_decl in methods {
                        if let Decl::FuncDef { body, .. } = method_decl {
                            self.scan_expr(body);
                        }
                    }
                }
            }
        }
    }

    fn scan_expr(&mut self, expr: &Expr) {
        match expr {
            Expr::Call { func, args } if self.funcs.contains_key(func) => {
                self.scan_call_args(func, args);
            }
            Expr::Call { args, .. } => {
                for arg in args {
                    self.scan_expr(arg);
                }
            }
            Expr::BinOp { lhs, rhs, .. } => {
                self.scan_expr(lhs);
                self.scan_expr(rhs);
            }
            Expr::Block(stmts, result) => {
                for stmt in stmts {
                    let Stmt::Let { val, .. } = stmt;
                    self.scan_expr(val);
                }
                self.scan_expr(result);
            }
            Expr::If {
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
            Expr::Fold {
                expr: scrutinee,
                arms,
            } => {
                self.scan_expr(scrutinee);
                for arm in arms {
                    self.scan_expr(&arm.body);
                }
            }
            Expr::QualifiedCall {
                owner,
                method,
                args,
            } => {
                let mangled = format!("{owner}.{method}");
                if self.funcs.contains_key(&mangled) {
                    self.scan_call_args(&mangled, args);
                } else {
                    for arg in args {
                        self.scan_expr(arg);
                    }
                }
            }
            Expr::Lambda { body, .. } => {
                self.scan_expr(body);
            }
            Expr::Record { fields } => {
                for (_, field_expr) in fields {
                    self.scan_expr(field_expr);
                }
            }
            Expr::FieldAccess { record, .. } => {
                self.scan_expr(record);
            }
            Expr::IntLit(_) | Expr::Name(_) => {}
        }
    }

    fn scan_call_args(&mut self, func_name: &str, args: &[Expr]) {
        for (i, arg) in args.iter().enumerate() {
            match arg {
                Expr::Lambda { params, body } => {
                    let free = self.compute_free_vars(body, params);
                    self.register_lambda(func_name, i, params.clone(), Some(body), free, None);
                }
                Expr::Name(name)
                    if self.funcs.contains_key(name) && !self.constructors.contains_key(name) =>
                {
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
                _ => {}
            }
            self.scan_expr(arg);
        }
    }

    fn register_lambda(
        &mut self,
        callee_func: &str,
        arg_index: usize,
        params: Vec<String>,
        body: Option<&Expr>,
        captures: Vec<String>,
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

        let tag = self.builder.func();
        self.lambda_sets[ls_idx].entries.push(LambdaEntry {
            tag,
            captures,
            params,
            body: body.cloned(),
            func_ref: func_ref.map(|(fid, _)| fid),
        });
    }

    fn compute_free_vars(&self, body: &Expr, params: &[String]) -> Vec<String> {
        let mut free = Vec::new();
        let mut seen = HashSet::new();
        let bound: HashSet<&str> = params.iter().map(String::as_str).collect();
        self.collect_free(body, &bound, &mut seen, &mut free);
        free
    }

    fn collect_free<'a>(
        &self,
        expr: &'a Expr,
        bound: &HashSet<&str>,
        seen: &mut HashSet<&'a str>,
        free: &mut Vec<String>,
    ) {
        match expr {
            Expr::Name(name) => {
                if !bound.contains(name.as_str())
                    && !self.constructors.contains_key(name)
                    && !self.funcs.contains_key(name)
                    && !seen.contains(name.as_str())
                {
                    seen.insert(name);
                    free.push(name.clone());
                }
            }
            Expr::IntLit(_) => {}
            Expr::BinOp { lhs, rhs, .. } => {
                self.collect_free(lhs, bound, seen, free);
                self.collect_free(rhs, bound, seen, free);
            }
            Expr::Call { args, .. } | Expr::QualifiedCall { args, .. } => {
                for arg in args {
                    self.collect_free(arg, bound, seen, free);
                }
            }
            Expr::Record { fields } => {
                for (_, field_expr) in fields {
                    self.collect_free(field_expr, bound, seen, free);
                }
            }
            Expr::FieldAccess { record, .. } => {
                self.collect_free(record, bound, seen, free);
            }
            Expr::Lambda { params, body } => {
                let mut inner = bound.clone();
                for p in params {
                    inner.insert(p);
                }
                self.collect_free(body, &inner, seen, free);
            }
            Expr::Block(stmts, result) => {
                let mut inner = bound.clone();
                for stmt in stmts {
                    let Stmt::Let { name, val } = stmt;
                    self.collect_free(val, &inner, seen, free);
                    inner.insert(name);
                }
                self.collect_free(result, &inner, seen, free);
            }
            Expr::If {
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
            Expr::Fold {
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

    fn pattern_names<'a>(pat: &'a ast::Pattern, bound: &mut HashSet<&'a str>) {
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

    fn lower_expr(&mut self, expr: &Expr) -> Core {
        match expr {
            Expr::IntLit(n) => Core::i64(*n),

            Expr::Name(name) => {
                if let Some(&var_id) = self.vars.get(name) {
                    return Core::var(var_id);
                }
                if let Some(&con_id) = self.constructors.get(name) {
                    return Core::app(con_id, vec![]);
                }
                panic!("undefined name: {name}");
            }

            Expr::BinOp { op, lhs, rhs } => {
                let func_id = self.binops[op];
                Core::app(func_id, vec![self.lower_expr(lhs), self.lower_expr(rhs)])
            }

            Expr::Call { func, args } => self.lower_call(func, args),

            Expr::Block(stmts, result) => {
                let mut bindings = Vec::new();
                for stmt in stmts {
                    let Stmt::Let { name, val } = stmt;
                    let val_core = self.lower_expr(val);
                    let var_id = self.builder.var();
                    self.vars.insert(name.clone(), var_id);
                    bindings.push((var_id, val_core));
                }

                let mut result_core = self.lower_expr(result);
                for (var_id, val_core) in bindings.into_iter().rev() {
                    result_core = Core::let_(var_id, val_core, result_core);
                }
                result_core
            }

            Expr::If {
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

            Expr::Fold {
                expr: scrutinee_expr,
                arms,
            } => {
                let scrutinee = self.lower_expr(scrutinee_expr);
                let core_arms = arms.iter().map(|arm| self.lower_fold_arm(arm)).collect();
                Core::fold(scrutinee, core_arms)
            }

            Expr::QualifiedCall {
                owner,
                method,
                args,
            } => {
                let mangled = format!("{owner}.{method}");
                self.lower_call(&mangled, args)
            }

            Expr::Record { fields } => {
                let core_fields: Vec<(String, Core)> = fields
                    .iter()
                    .map(|(name, field_expr)| (name.clone(), self.lower_expr(field_expr)))
                    .collect();
                Core::record(core_fields)
            }

            Expr::FieldAccess { record, field } => {
                Core::field_access(self.lower_expr(record), field.clone())
            }

            Expr::Lambda { .. } => {
                panic!("lambdas are only supported as direct arguments to function calls");
            }
        }
    }

    fn lower_call(&mut self, func: &str, args: &[Expr]) -> Core {
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
    fn lower_lambda_arg(&mut self, arg: &Expr, callee: &str, arg_idx: usize) -> Core {
        let key = (callee.to_owned(), arg_idx);
        let ls_idx = self.ho_param_sets[&key];
        let counter = self.lambda_arg_counters.entry(key).or_insert(0);
        let entry_idx = *counter;
        *counter += 1;

        let entry = &self.lambda_sets[ls_idx].entries[entry_idx];
        let tag = entry.tag;
        let captures: Vec<String> = entry.captures.clone();

        match arg {
            Expr::Lambda { .. } => {
                let capture_vals: Vec<Core> = captures
                    .iter()
                    .map(|name| {
                        let &var_id = self
                            .vars
                            .get(name)
                            .unwrap_or_else(|| panic!("captured variable '{name}' not in scope"));
                        Core::var(var_id)
                    })
                    .collect();
                Core::app(tag, capture_vals)
            }
            Expr::Name(_) => {
                // Function reference — nullary constructor
                Core::app(tag, vec![])
            }
            _ => panic!("expected lambda or function reference in higher-order argument"),
        }
    }

    // ---- Generate apply functions ----

    fn generate_apply_functions(&mut self) {
        // Clone lambda sets to avoid borrow conflict with self.lower_expr
        let sets: Vec<LambdaSet> = std::mem::take(&mut self.lambda_sets);

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
                            self.vars.insert(cap_name.clone(), cap_var);
                        }
                        for (param_name, &arg_var) in entry.params.iter().zip(&arg_vars) {
                            self.vars.insert(param_name.clone(), arg_var);
                        }

                        let body_core = self.lower_expr(entry.body.as_ref().unwrap());

                        for cap_name in &entry.captures {
                            self.vars.remove(cap_name);
                        }
                        for param_name in &entry.params {
                            self.vars.remove(param_name);
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

    // ---- Fold lowering ----

    fn lower_fold_arm(&mut self, arm: &ast::MatchArm) -> FoldArm {
        let ast::Pattern::Constructor { name: con_name, .. } = &arm.pattern else {
            panic!("fold arms must use constructor patterns");
        };
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

    fn lower_pattern(&mut self, pat: &ast::Pattern) -> (Pattern, Vec<(String, VarId)>) {
        match pat {
            ast::Pattern::Constructor { name, fields } => {
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
                            bindings.push((binding_name.clone(), var_id));
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
                    }
                }
                (Pattern::con(con_id, field_vars), bindings)
            }
            ast::Pattern::Record { .. } => {
                panic!("record patterns in match arms not yet supported in lowering");
            }
            ast::Pattern::Wildcard | ast::Pattern::Binding(_) => {
                panic!("top-level wildcard/binding patterns not yet supported in match arms");
            }
        }
    }
}
