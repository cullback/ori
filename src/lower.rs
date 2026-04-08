use std::collections::{HashMap, HashSet};

use crate::core::builder::Builder;
use crate::core::{
    Builtin, ConstructorDef, Core, FieldDef, FoldArm, FuncDef, FuncId, MonoType, Pattern, Program,
    VarId,
};
use crate::error::CompileError;
use crate::source::SourceArena;
use crate::syntax::ast::{self, BinOp, Decl, Expr, ExprKind, Module, Stmt, TypeExpr};
use crate::syntax::parse;

/// Build a mangled key for a method on a type, e.g. `method_key("List", "sum")` -> `"List.sum"`.
fn method_key(type_name: &str, method: &str) -> String {
    format!("{type_name}.{method}")
}

/// Lower a parsed AST module into a Core IR program.
///
/// Returns the program and `VarId`s for `main`'s parameters
/// (free variables that the runtime must bind before evaluation).
#[expect(clippy::too_many_lines, reason = "multi-pass lowering orchestration")]
pub fn lower<'src>(
    arena: &'src SourceArena,
    module: &Module<'src>,
    scope: &crate::resolve::ModuleScope,
    infer_result: &crate::types::infer::InferResult,
) -> Result<(Program, Vec<VarId>), CompileError> {
    let mut ctx = LowerCtx::new(infer_result);

    // Register stdlib modules
    let bool_stdlib = ctx.register_stdlib_module(arena, "Bool");
    ctx.register_comparison_builtins();
    ctx.register_num_to_str();
    let result_stdlib = ctx.register_stdlib_module(arena, "Result");
    let list_stdlib = ctx.register_stdlib_module(arena, "List");
    let str_stdlib = ctx.register_stdlib_module(arena, "Str");
    let bool_methods = LowerCtx::extract_methods(&bool_stdlib);
    let result_methods = LowerCtx::extract_methods(&result_stdlib);
    let list_methods = LowerCtx::extract_methods(&list_stdlib);
    let str_methods = LowerCtx::extract_methods(&str_stdlib);

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
    all_stdlib_methods.extend(&list_methods);
    all_stdlib_methods.extend(&str_methods);
    ctx.compute_reachable_with_stdlib(&module.decls, &all_stdlib_methods);

    // Add method-resolved functions to reachable set
    let resolved_methods: Vec<String> = ctx.method_resolutions.values().cloned().collect();
    ctx.reachable.extend(resolved_methods);

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

    // Pass 1.75: populate constructor field types from concrete instantiations
    ctx.populate_constructor_field_types();

    // Store constructor schemes in builder for SSA lowering
    #[expect(
        clippy::iter_over_hash_type,
        reason = "constructor insertion order does not matter"
    )]
    for (con_name, con_id) in &ctx.constructors {
        if let Some(scheme) = ctx.constructor_schemes.get(con_name.as_str()) {
            ctx.builder.set_constructor_scheme(*con_id, scheme.clone());
        }
    }

    // Pass 2: lower all function bodies
    let mut main_params = None;
    let mut main_body = None;

    for decl in &module.decls {
        let Decl::FuncDef {
            name, params, body, ..
        } = decl
        else {
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
        let param_monos = ctx.func_param_monos(name);
        let param_vars: Vec<VarId> = params
            .iter()
            .enumerate()
            .map(|(i, p)| {
                let v = ctx.builder.var();
                if let Some(mono) = param_monos.get(i) {
                    ctx.builder.set_var_type(v, mono.clone());
                }
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
            param_types: param_monos,
            return_type: ctx.func_return_mono(name),
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
                ..
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
                param_types: ctx.func_param_monos(&mangled),
                return_type: ctx.func_return_mono(&mangled),
            });
        }
    }

    // Lower stdlib method bodies
    ctx.lower_stdlib_methods(&all_stdlib_methods);

    // Lower main
    let params = main_params.ok_or_else(|| CompileError::new("no 'main' function defined"))?;
    let body = main_body.unwrap();
    let main_param_monos = ctx.func_param_monos("main");
    let mut input_vars = Vec::new();
    for (i, p) in params.iter().enumerate() {
        let var = ctx.builder.var();
        if let Some(mono) = main_param_monos.get(i) {
            ctx.builder.set_var_type(var, mono.clone());
        }
        ctx.vars.insert((*p).to_owned(), var);
        input_vars.push(var);
    }

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

    // Populate lambda capture field types from var_types
    ctx.populate_lambda_capture_types();

    let program = ctx.builder.build(main_core);
    Ok((program, input_vars))
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
    method_resolutions: HashMap<ast::Span, String>,
    /// Fully-resolved concrete type for every expression (by span).
    expr_types: HashMap<ast::Span, crate::types::engine::Type>,
    /// Generalized type schemes for all functions/methods.
    func_schemes: HashMap<String, crate::types::engine::Scheme>,
    /// Constructor type schemes (e.g., Ok → forall ok err. ok -> Result(ok, err)).
    constructor_schemes: HashMap<String, crate::types::engine::Scheme>,
}

impl<'src> LowerCtx<'src> {
    fn new(infer_result: &crate::types::infer::InferResult) -> Self {
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
        list_builtins.insert("List.set".to_owned(), builder.builtin(Builtin::ListSet));
        list_builtins.insert(
            "List.append".to_owned(),
            builder.builtin(Builtin::ListAppend),
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
            lit_types: infer_result.lit_types.clone(),
            method_resolutions: infer_result.method_resolutions.clone(),
            expr_types: infer_result.expr_types.clone(),
            func_schemes: infer_result.func_schemes.clone(),
            constructor_schemes: infer_result.constructor_schemes.clone(),
        }
    }

    /// Convert an inference `Type` to a concrete `MonoType` for layout computation.
    fn type_to_mono(ty: &crate::types::engine::Type) -> MonoType {
        use crate::types::engine::Type;
        match ty {
            Type::Con(name) => match name.as_str() {
                "I8" => MonoType::I8,
                "U8" => MonoType::U8,
                "I64" => MonoType::I64,
                "U64" => MonoType::U64,
                "F64" => MonoType::F64,
                "Bool" => MonoType::Bool,
                // All other named types (user-defined tag unions, Str, etc.) are heap-allocated
                _ => MonoType::Ptr,
            },
            // Everything else (App, Record, Tuple, Arrow, Var) is heap-allocated
            _ => MonoType::Ptr,
        }
    }

    /// Compute the slot index for a field access on a record/tuple type.
    /// Fields are stored in alphabetical order, so the slot is the alphabetical position.
    fn field_slot(ty: &crate::types::engine::Type, field: &str) -> usize {
        use crate::types::engine::Type;
        match ty {
            Type::Record { fields, .. } => {
                let mut names: Vec<&str> = fields.iter().map(|(n, _)| n.as_str()).collect();
                names.sort_unstable();
                names
                    .iter()
                    .position(|n| *n == field)
                    .unwrap_or_else(|| panic!("field '{field}' not found in record type"))
            }
            Type::Tuple(elems) => {
                // Tuple fields are named "0", "1", "2", ...
                // When stored alphabetically, single-digit names sort correctly.
                let mut names: Vec<String> = (0..elems.len()).map(|i| i.to_string()).collect();
                names.sort_unstable();
                names
                    .iter()
                    .position(|n| n == field)
                    .unwrap_or_else(|| panic!("field '{field}' not found in tuple type"))
            }
            _ => panic!("field access on non-record type: {ty:?}"),
        }
    }

    /// Get the `MonoType` for an expression from its span.
    fn expr_mono_type(&self, span: ast::Span) -> MonoType {
        self.expr_types
            .get(&span)
            .map_or(MonoType::Ptr, Self::type_to_mono)
    }

    /// Get the return `MonoType` for a function from its scheme.
    fn func_return_mono(&self, name: &str) -> MonoType {
        self.func_schemes.get(name).map_or(MonoType::Ptr, |scheme| {
            if let crate::types::engine::Type::Arrow(_, ret) = &scheme.ty {
                Self::type_to_mono(ret)
            } else {
                Self::type_to_mono(&scheme.ty)
            }
        })
    }

    /// Get the parameter `MonoType`s for a function from its scheme.
    fn func_param_monos(&self, name: &str) -> Vec<MonoType> {
        self.func_schemes
            .get(name)
            .and_then(|scheme| {
                if let crate::types::engine::Type::Arrow(params, _) = &scheme.ty {
                    Some(params.iter().map(Self::type_to_mono).collect())
                } else {
                    None
                }
            })
            .unwrap_or_default()
    }

    /// Structurally match a type pattern (with Vars) against a concrete type,
    /// extracting bindings for each type variable.
    fn match_type_params(
        pattern: &crate::types::engine::Type,
        concrete: &crate::types::engine::Type,
        bindings: &mut HashMap<crate::types::engine::TypeVar, crate::types::engine::Type>,
    ) {
        use crate::types::engine::Type;
        match (pattern, concrete) {
            (Type::Var(tv), _) => {
                bindings.insert(*tv, concrete.clone());
            }
            (Type::App(n1, a1), Type::App(n2, a2)) if n1 == n2 && a1.len() == a2.len() => {
                for (p, c) in a1.iter().zip(a2.iter()) {
                    Self::match_type_params(p, c, bindings);
                }
            }
            (Type::Arrow(p1, r1), Type::Arrow(p2, r2)) if p1.len() == p2.len() => {
                for (p, c) in p1.iter().zip(p2.iter()) {
                    Self::match_type_params(p, c, bindings);
                }
                Self::match_type_params(r1, r2, bindings);
            }
            _ => {}
        }
    }

    /// Given a constructor name and the concrete type it produces (from `expr_types`),
    /// compute the `MonoType` of each field.
    fn constructor_field_monos(
        &self,
        con_name: &str,
        concrete_result_type: &crate::types::engine::Type,
    ) -> Vec<MonoType> {
        use crate::types::engine::{Type, TypeEngine};

        let Some(scheme) = self.constructor_schemes.get(con_name) else {
            return vec![];
        };

        // Extract the return type and field types from the scheme
        let (field_types, return_type) = match &scheme.ty {
            Type::Arrow(params, ret) => (params.clone(), (**ret).clone()),
            other => (vec![], other.clone()),
        };

        // Match the scheme's return type against the concrete type to get bindings
        let mut bindings = HashMap::new();
        Self::match_type_params(&return_type, concrete_result_type, &mut bindings);

        // Apply bindings to each field type and convert to MonoType
        field_types
            .iter()
            .map(|ft| {
                let concrete = TypeEngine::apply_mapping(ft, &bindings);
                Self::type_to_mono(&concrete)
            })
            .collect()
    }

    /// Scan `expr_types` for concrete type instantiations and populate `FieldDef.mono_type`
    /// for constructors of single-instantiation parameterized types.
    #[expect(
        clippy::iter_over_hash_type,
        reason = "iteration order does not affect results"
    )]
    fn populate_constructor_field_types(&mut self) {
        use crate::types::engine::Type;

        // Collect all concrete App(name, args) types from expr_types
        let mut type_instantiations: HashMap<String, Vec<Vec<crate::types::engine::Type>>> =
            HashMap::new();
        for ty in self.expr_types.values() {
            Self::collect_app_types(ty, &mut type_instantiations);
        }

        // For each type with exactly one instantiation, populate constructor field types
        for (type_name, instantiations) in &type_instantiations {
            // Deduplicate and filter out instantiations with unresolved type variables
            // (these come from polymorphic function bodies, not real usage sites)
            let unique: Vec<&Vec<Type>> = {
                let mut seen = Vec::new();
                for inst in instantiations {
                    let has_vars = inst.iter().any(Self::contains_type_var);
                    if !has_vars && !seen.contains(&inst) {
                        seen.push(inst);
                    }
                }
                seen
            };

            if unique.len() != 1 {
                continue; // Multiple instantiations — leave as None (Ptr fallback)
            }

            let concrete_args = unique[0];
            let concrete_type = Type::App(type_name.clone(), concrete_args.clone());

            // Find constructors that belong to this type and populate their field types
            for (con_name, con_id) in &self.constructors {
                let Some(scheme) = self.constructor_schemes.get(con_name.as_str()) else {
                    continue;
                };
                // Check if this constructor's return type matches the current type
                let ret_ty = match &scheme.ty {
                    Type::Arrow(_, ret) => ret.as_ref(),
                    other => other,
                };
                let ret_type_name = match ret_ty {
                    Type::App(n, _) | Type::Con(n) => Some(n.as_str()),
                    _ => None,
                };
                if ret_type_name != Some(type_name.as_str()) {
                    continue; // This constructor doesn't belong to this type
                }
                let field_monos = self.constructor_field_monos(con_name, &concrete_type);
                if !field_monos.is_empty() {
                    self.builder
                        .update_constructor_field_types(*con_id, &field_monos);
                }
            }
        }

        // Also handle non-parameterized constructors (like Bool := [True, False])
        // These have no type params, so field types come directly from the scheme
        for (con_name, con_id) in &self.constructors {
            let Some(scheme) = self.constructor_schemes.get(con_name) else {
                continue;
            };
            if !scheme.vars.is_empty() {
                continue; // Parameterized — handled above
            }
            let field_types = match &scheme.ty {
                Type::Arrow(params, _) => params.iter().map(Self::type_to_mono).collect(),
                _ => vec![], // Nullary constructor
            };
            if !field_types.is_empty() {
                self.builder
                    .update_constructor_field_types(*con_id, &field_types);
            }
        }
    }

    /// Check if a type contains any unresolved type variables.
    fn contains_type_var(ty: &crate::types::engine::Type) -> bool {
        use crate::types::engine::Type;
        match ty {
            Type::Var(_) => true,
            Type::Con(_) => false,
            Type::App(_, args) => args.iter().any(Self::contains_type_var),
            Type::Arrow(params, ret) => {
                params.iter().any(Self::contains_type_var) || Self::contains_type_var(ret)
            }
            Type::Record { fields, rest } => {
                fields.iter().any(|(_, t)| Self::contains_type_var(t))
                    || rest.as_ref().is_some_and(|r| Self::contains_type_var(r))
            }
            Type::Tuple(elems) => elems.iter().any(Self::contains_type_var),
        }
    }

    /// Recursively collect all App(name, args) types from a type expression.
    fn collect_app_types(
        ty: &crate::types::engine::Type,
        map: &mut HashMap<String, Vec<Vec<crate::types::engine::Type>>>,
    ) {
        use crate::types::engine::Type;
        match ty {
            Type::App(name, args) => {
                map.entry(name.clone()).or_default().push(args.clone());
                for arg in args {
                    Self::collect_app_types(arg, map);
                }
            }
            Type::Arrow(params, ret) => {
                for p in params {
                    Self::collect_app_types(p, map);
                }
                Self::collect_app_types(ret, map);
            }
            Type::Record { fields, rest } => {
                for (_, ft) in fields {
                    Self::collect_app_types(ft, map);
                }
                if let Some(r) = rest {
                    Self::collect_app_types(r, map);
                }
            }
            Type::Tuple(elems) => {
                for e in elems {
                    Self::collect_app_types(e, map);
                }
            }
            Type::Con(_) | Type::Var(_) => {}
        }
    }

    /// Populate lambda closure constructor field types from captured variables' known types.
    fn populate_lambda_capture_types(&mut self) {
        for ls in &self.lambda_sets {
            for entry in &ls.entries {
                let capture_monos: Vec<MonoType> = entry
                    .captures
                    .iter()
                    .map(|name| {
                        self.vars
                            .get(*name)
                            .and_then(|var_id| self.builder.get_var_type(*var_id).cloned())
                            .unwrap_or(MonoType::Ptr)
                    })
                    .collect();
                if !capture_monos.is_empty() {
                    self.builder
                        .update_constructor_field_types(entry.tag, &capture_monos);
                }
            }
        }
    }

    /// Parse a stdlib module and register its types, constructors, and method signatures.
    fn register_stdlib_module(
        &mut self,
        arena: &'src SourceArena,
        module_name: &str,
    ) -> Module<'src> {
        let file_id = arena
            .find_by_path(&format!("<stdlib:{module_name}>"))
            .unwrap_or_else(|| panic!("stdlib module '{module_name}' not loaded in arena"));
        let stdlib = parse::parse(arena.content(file_id), file_id)
            .expect("stdlib module should always parse successfully");
        self.register_decls(&stdlib.decls);
        stdlib
    }

    /// Extract `(type_name, method_decl)` pairs from a parsed stdlib module.
    fn extract_methods<'a, 'b>(stdlib: &'a Module<'b>) -> Vec<(&'b str, &'a Decl<'b>)> {
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
                            self.builder.debug_name_func(func_id, mangled.clone());
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
                                self.builder.debug_name_func(func_id, mangled.clone());
                                self.funcs.insert(mangled.clone(), func_id);
                                self.func_arities.insert(mangled, params.len());
                            }
                        }
                    }
                }
                Decl::FuncDef { name, params, .. } => {
                    let name = *name;
                    let func_id = self.builder.func();
                    self.builder.debug_name_func(func_id, name.to_owned());
                    self.funcs.insert(name.to_owned(), func_id);
                    self.func_arities.insert(name.to_owned(), params.len());
                }
            }
        }
    }

    /// Lower the bodies of stdlib methods that are reachable.
    fn lower_stdlib_methods(&mut self, methods: &[(&str, &Decl<'src>)]) {
        for &(type_name, method) in methods {
            if let Decl::FuncDef {
                name, params, body, ..
            } = method
            {
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
                    param_types: self.func_param_monos(&mangled),
                    return_type: self.func_return_mono(&mangled),
                });
            }
        }
    }

    fn register_num_to_str(&mut self) {
        let to_str_id = self.builder.builtin(Builtin::NumToStr);
        for ty in &["I64", "U64", "F64", "U8", "I8"] {
            let key = format!("{ty}.to_str");
            self.funcs.insert(key.clone(), to_str_id);
            self.func_arities.insert(key, 1);
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
        stdlib_methods: &[(&'src str, &Decl<'src>)],
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
            ExprKind::MethodCall { receiver, args, .. } => {
                Self::collect_refs(receiver, refs);
                for a in args {
                    Self::collect_refs(a, refs);
                }
            }
            ExprKind::Tuple(elems) | ExprKind::ListLit(elems) => {
                for e in elems {
                    Self::collect_refs(e, refs);
                }
            }
            ExprKind::IntLit(_) | ExprKind::FloatLit(_) | ExprKind::StrLit(_) => {}
        }
    }

    fn register_tag_union(&mut self, type_name: &str, tags: &[ast::TagDecl<'src>]) {
        let mut con_defs = Vec::new();
        for tag in tags {
            let con_id = self.builder.func();
            self.builder.debug_name_func(con_id, tag.name.to_owned());
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
                    .map(|&recursive| FieldDef {
                        recursive,
                        mono_type: None,
                    })
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

    #[expect(clippy::too_many_lines, reason = "traverses all expression forms")]
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
                let is_list_ho = mangled == "List.walk"
                    || mangled.ends_with(".List.walk")
                    || mangled == "List.walk_backwards"
                    || mangled.ends_with(".List.walk_backwards");
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
            ExprKind::MethodCall { receiver, args, .. } => {
                self.scan_expr(receiver);
                // Check if resolved method is higher-order (e.g. List.walk)
                if let Some(resolved) = self.method_resolutions.get(&expr.span).cloned() {
                    let is_ho = resolved == "List.walk"
                        || resolved.ends_with(".List.walk")
                        || resolved == "List.walk_backwards"
                        || resolved.ends_with(".List.walk_backwards")
                        || self.funcs.contains_key(&resolved);
                    if is_ho {
                        // Offset arg indices by 1 (receiver is arg 0)
                        self.scan_call_args_offset(&resolved, args, 1);
                    } else {
                        for a in args {
                            self.scan_expr(a);
                        }
                    }
                } else {
                    for a in args {
                        self.scan_expr(a);
                    }
                }
            }
            ExprKind::Tuple(elems) | ExprKind::ListLit(elems) => {
                for e in elems {
                    self.scan_expr(e);
                }
            }
            ExprKind::IntLit(_)
            | ExprKind::FloatLit(_)
            | ExprKind::StrLit(_)
            | ExprKind::Name(_) => {}
        }
    }

    fn scan_call_args(&mut self, func_name: &str, args: &[Expr<'src>]) {
        self.scan_call_args_offset(func_name, args, 0);
    }

    /// Scan function call args for lambdas, with an index offset
    /// (e.g. offset=1 for method calls where receiver is arg 0).
    fn scan_call_args_offset(&mut self, func_name: &str, args: &[Expr<'src>], offset: usize) {
        for (i, arg) in args.iter().enumerate() {
            let idx = i + offset;
            match &arg.kind {
                ExprKind::Lambda { params, body } => {
                    let free = self.compute_free_vars(body, params);
                    self.register_lambda(func_name, idx, params.clone(), Some(body), free, None);
                }
                ExprKind::Name(name) => {
                    let name = *name;
                    if self.funcs.contains_key(name) && !self.constructors.contains_key(name) {
                        let func_id = self.funcs[name];
                        let arity = self.func_arities[name];
                        self.register_lambda(
                            func_name,
                            idx,
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
            let apply_name = format!("__apply_{callee_func}_{arg_index}");
            self.builder.debug_name_func(apply_func, apply_name);
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

    #[expect(clippy::too_many_lines, reason = "traverses all expression forms")]
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
            ExprKind::IntLit(_) | ExprKind::FloatLit(_) | ExprKind::StrLit(_) => {}
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
            ExprKind::MethodCall { receiver, args, .. } => {
                self.collect_free(receiver, bound, seen, free);
                for a in args {
                    self.collect_free(a, bound, seen, free);
                }
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
                        .map(|_| FieldDef {
                            recursive: false,
                            mono_type: None,
                        })
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

            ExprKind::StrLit(bytes) => {
                let elements: Vec<Core> = bytes.iter().map(|&b| Core::u8(b)).collect();
                Core::list_lit(elements)
            }

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
                            let mono = self.expr_mono_type(val.span);
                            let val_core = self.lower_expr(val);
                            let var_id = self.builder.var();
                            self.builder.set_var_type(var_id, mono);
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
                let scrutinee_type = self.expr_types.get(&scrutinee_expr.span).cloned();
                let core_arms: Vec<(Pattern, Core)> = arms
                    .iter()
                    .map(|arm| {
                        let (pat, var_bindings) = self.lower_pattern(&arm.pattern);
                        // Annotate pattern-bound variables with concrete types
                        self.annotate_pattern_vars(
                            &arm.pattern,
                            &var_bindings,
                            scrutinee_type.as_ref(),
                        );
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
                let scrutinee_type = self.expr_types.get(&scrutinee_expr.span).cloned();
                let core_arms = arms
                    .iter()
                    .map(|arm| self.lower_fold_arm(arm, scrutinee_type.as_ref()))
                    .collect();
                Core::fold(scrutinee, core_arms)
            }

            ExprKind::QualifiedCall { segments, args } => {
                // Check if inference resolved this to a method call (e.g., b.not → Bool.not)
                if let Some(resolved) = self.method_resolutions.get(&expr.span).cloned() {
                    let receiver_name = segments[0];
                    let receiver_core = if let Some(&var_id) = self.vars.get(receiver_name) {
                        Core::var(var_id)
                    } else if let Some(&con_id) = self.constructors.get(receiver_name) {
                        Core::app(con_id, vec![])
                    } else {
                        panic!("undefined receiver: {receiver_name}");
                    };
                    if let Some(builtin_name) = resolved.strip_prefix("__builtin.") {
                        // Builtin arithmetic: x.add(y) → Add(x, y)
                        let op = match builtin_name {
                            "add" => BinOp::Add,
                            "sub" => BinOp::Sub,
                            "mul" => BinOp::Mul,
                            "div" => BinOp::Div,
                            "rem" => BinOp::Rem,
                            "eq" => BinOp::Eq,
                            "neq" => BinOp::Neq,
                            _ => panic!("unknown builtin: {builtin_name}"),
                        };
                        let func_id = self.binops[&op];
                        let mut full_args = vec![receiver_core];
                        full_args.extend(args.iter().map(|a| self.lower_expr(a)));
                        Core::app(func_id, full_args)
                    } else {
                        // Method call: receiver.method(args) → Type.method(receiver, args)
                        let mut full_args = vec![receiver_core];
                        full_args.extend(args.iter().map(|a| self.lower_expr(a)));
                        let func_id = self.funcs[&resolved];
                        Core::app(func_id, full_args)
                    }
                } else {
                    let mangled = segments.join(".");
                    self.lower_call(&mangled, args)
                }
            }

            ExprKind::Record { fields } => {
                let core_fields: Vec<(String, Core)> = fields
                    .iter()
                    .map(|(name, field_expr)| ((*name).to_owned(), self.lower_expr(field_expr)))
                    .collect();
                Core::record(core_fields)
            }

            ExprKind::FieldAccess { record, field } => {
                let slot = self
                    .expr_types
                    .get(&record.span)
                    .map_or(0, |ty| Self::field_slot(ty, field));
                Core::field_access(self.lower_expr(record), (*field).to_owned(), slot)
            }

            ExprKind::MethodCall {
                receiver,
                method,
                args,
            } => {
                // Look up resolved method from type inference
                let resolved = self.method_resolutions.get(&expr.span).cloned();
                if let Some(mangled) = resolved {
                    // List.walk / walk_backwards: special Core node
                    let is_walk = mangled == "List.walk" || mangled.ends_with(".List.walk");
                    let is_walk_back = mangled == "List.walk_backwards"
                        || mangled.ends_with(".List.walk_backwards");
                    if is_walk || is_walk_back {
                        let list_core = self.lower_expr(receiver);
                        let init_core = self.lower_expr(&args[0]);
                        let key = (mangled.clone(), 2); // step is arg 2 (after receiver + init)
                        let closure_core = if self.ho_param_sets.contains_key(&key) {
                            self.lower_lambda_arg(&args[1], &mangled, 2)
                        } else {
                            self.lower_expr(&args[1])
                        };
                        let ls_idx = self.ho_param_sets[&key];
                        let apply_func = self.lambda_sets[ls_idx].apply_func;
                        return Core::list_walk(
                            list_core,
                            init_core,
                            closure_core,
                            apply_func,
                            is_walk_back,
                        );
                    }

                    // Build full args: receiver + method args (with lambda handling)
                    let recv_core = self.lower_expr(receiver);
                    let mut full_args = vec![recv_core];
                    for (i, a) in args.iter().enumerate() {
                        let idx = i + 1; // offset for receiver
                        let key = (mangled.clone(), idx);
                        if self.ho_param_sets.contains_key(&key) {
                            full_args.push(self.lower_lambda_arg(a, &mangled, idx));
                        } else {
                            full_args.push(self.lower_expr(a));
                        }
                    }
                    // Check for builtin
                    if let Some(op_name) = mangled.strip_prefix("__builtin.") {
                        let binop_id = self.binops[&match op_name {
                            "add" => BinOp::Add,
                            "sub" => BinOp::Sub,
                            "mul" => BinOp::Mul,
                            "div" => BinOp::Div,
                            "rem" => BinOp::Rem,
                            "eq" => BinOp::Eq,
                            "neq" => BinOp::Neq,
                            _ => panic!("unknown builtin: {op_name}"),
                        }];
                        return Core::app(binop_id, full_args);
                    }
                    // Check list builtins
                    if let Some(&builtin_id) = self.list_builtins.get(&mangled) {
                        return Core::app(builtin_id, full_args);
                    }
                    // Regular method
                    if let Some(&func_id) = self.funcs.get(&mangled) {
                        return Core::app(func_id, full_args);
                    }
                    panic!("unresolved method: {mangled}");
                }
                panic!("no method resolution for .{method}() at {:?}", expr.span);
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
        // List.walk / List.walk_backwards: emits Core::ListWalk with closure + apply_func
        let is_walk = func == "List.walk" || func.ends_with(".List.walk");
        let is_walk_back = func == "List.walk_backwards" || func.ends_with(".List.walk_backwards");
        if is_walk || is_walk_back {
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
            return Core::list_walk(list_core, init_core, closure_core, apply_func, is_walk_back);
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
                param_types: vec![],
                return_type: MonoType::Ptr,
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
                    let access = Core::field_access(Core::var(source_var), i.to_string(), i);
                    bindings.push((field_var, access));
                    self.lower_destructure_elem(elem, field_var, bindings);
                }
            }
            ast::Pattern::Record { fields } => {
                // Compute slot indices: fields are stored in alphabetical order.
                let mut all_names: Vec<&str> = fields.iter().map(|(n, _)| *n).collect();
                all_names.sort_unstable();
                for (name, elem) in fields {
                    let slot = all_names.iter().position(|n| n == name).unwrap();
                    let field_var = self.builder.var();
                    let access =
                        Core::field_access(Core::var(source_var), (*name).to_owned(), slot);
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

    fn lower_fold_arm(
        &mut self,
        arm: &ast::MatchArm<'src>,
        scrutinee_type: Option<&crate::types::engine::Type>,
    ) -> FoldArm {
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
        self.annotate_pattern_vars(&arm.pattern, &var_bindings, scrutinee_type);
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

    /// Annotate pattern-bound variables with their concrete `MonoType`s
    /// using the scrutinee type and the constructor's type scheme.
    fn annotate_pattern_vars(
        &mut self,
        pat: &ast::Pattern<'src>,
        var_bindings: &[(String, VarId)],
        scrutinee_type: Option<&crate::types::engine::Type>,
    ) {
        let ast::Pattern::Constructor { name, .. } = pat else {
            return;
        };
        let Some(scr_ty) = scrutinee_type else {
            return;
        };
        let field_monos = self.constructor_field_monos(name, scr_ty);
        for (i, (_name, var_id)) in var_bindings.iter().enumerate() {
            if let Some(mono) = field_monos.get(i) {
                self.builder.set_var_type(*var_id, mono.clone());
            }
        }
    }

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
