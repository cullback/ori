use std::collections::{HashMap, HashSet};

use crate::source::SourceArena;
use crate::ssa::ScalarType;
use crate::syntax::ast::{self, Decl, TypeExpr};
use crate::types::engine::{Scheme, Type};
use crate::types::infer::InferResult;

/// Build a mangled key for a method on a type, e.g. `method_key("List", "sum")` -> `"List.sum"`.
pub fn method_key(type_name: &str, method: &str) -> String {
    format!("{type_name}.{method}")
}

/// Map a resolved concrete type to the SSA scalar type used at runtime.
pub fn type_to_scalar(ty: &Type) -> ScalarType {
    match ty {
        Type::Con(name) => match name.as_str() {
            "I8" => ScalarType::I8,
            "U8" => ScalarType::U8,
            "I64" => ScalarType::I64,
            "U64" => ScalarType::U64,
            "F64" => ScalarType::F64,
            "Bool" => ScalarType::Bool,
            _ => ScalarType::Ptr,
        },
        _ => ScalarType::Ptr,
    }
}

/// Extract the return type from a function type scheme.
pub fn scheme_return_type(scheme: &Scheme) -> ScalarType {
    match &scheme.ty {
        Type::Arrow(_, ret) => type_to_scalar(ret),
        other => type_to_scalar(other),
    }
}

/// Constructor metadata for tag union variants and closure types.
#[derive(Clone, Debug)]
#[allow(dead_code)]
pub struct ConstructorMeta {
    pub tag_index: u64,
    pub num_fields: usize,
    pub max_fields: usize,
    pub recursive_flags: Vec<bool>,
    pub field_types: Vec<ScalarType>,
}

/// Registration data about all declared functions, constructors, and builtins.
pub struct DeclInfo {
    pub funcs: HashSet<String>,
    pub func_arities: HashMap<String, usize>,
    pub constructors: HashMap<String, ConstructorMeta>,
    pub list_builtins: HashSet<String>,
    pub num_to_str_methods: HashSet<String>,
    pub func_aliases: HashMap<String, Vec<String>>,
    pub func_return_types: HashMap<String, ScalarType>,
    pub func_schemes: HashMap<String, Scheme>,
    pub constructor_schemes: HashMap<String, Scheme>,
}

/// Build `DeclInfo` from the resolved module declarations.
pub fn build<'src>(
    _arena: &'src SourceArena,
    module: &ast::Module<'src>,
    scope: &crate::resolve::ModuleScope,
    infer_result: &InferResult,
) -> DeclInfo {
    let mut info = DeclInfo {
        funcs: HashSet::new(),
        func_arities: HashMap::new(),
        constructors: HashMap::new(),
        list_builtins: HashSet::new(),
        num_to_str_methods: HashSet::new(),
        func_aliases: HashMap::new(),
        func_return_types: HashMap::new(),
        func_schemes: infer_result.func_schemes.clone(),
        constructor_schemes: infer_result.constructor_schemes.clone(),
    };

    register_comparison_info();
    register_num_to_str(&mut info);

    // Register user declarations
    register_decls(&mut info, &module.decls);

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
                        if info.funcs.contains(&internal) {
                            info.funcs.insert(qualified.clone());
                            info.func_aliases
                                .entry(internal.clone())
                                .or_default()
                                .push(qualified.clone());
                            info.func_aliases
                                .entry(qualified.clone())
                                .or_default()
                                .push(internal.clone());
                        }
                        if let Some(&arity) = info.func_arities.get(&internal) {
                            info.func_arities.insert(qualified, arity);
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
                if info.funcs.contains(name) {
                    info.funcs.insert(qualified.clone());
                    info.func_aliases
                        .entry(name.to_owned())
                        .or_default()
                        .push(qualified.clone());
                    info.func_aliases
                        .entry(qualified.clone())
                        .or_default()
                        .push(name.to_owned());
                }
                if let Some(&arity) = info.func_arities.get(name) {
                    info.func_arities.insert(qualified, arity);
                }
            }
        }
    }

    info
}

/// Register all declarations (types, constructors, functions) into `DeclInfo`.
pub fn register_decls(info: &mut DeclInfo, decls: &[Decl<'_>]) {
    for decl in decls {
        match decl {
            Decl::TypeAnno {
                name,
                ty: TypeExpr::TagUnion(tags),
                methods,
                ..
            } => {
                let name = *name;
                register_tag_union(info, name, tags);
                for method_decl in methods {
                    if let Decl::FuncDef {
                        name: method_name,
                        params,
                        ..
                    } = method_decl
                    {
                        let method_name = *method_name;
                        let mangled = method_key(name, method_name);
                        info.funcs.insert(mangled.clone());
                        info.func_arities.insert(mangled.clone(), params.len());
                        if let Some(scheme) = info.func_schemes.get(&mangled) {
                            info.func_return_types
                                .insert(mangled, scheme_return_type(scheme));
                        }
                    }
                }
            }
            Decl::TypeAnno { name, methods, .. } => {
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
                        if !info.funcs.contains(&mangled) {
                            info.funcs.insert(mangled.clone());
                            info.func_arities.insert(mangled.clone(), params.len());
                            if let Some(scheme) = info.func_schemes.get(&mangled) {
                                info.func_return_types
                                    .insert(mangled, scheme_return_type(scheme));
                            }
                        }
                    }
                }
            }
            Decl::FuncDef { name, params, .. } => {
                let name = *name;
                info.funcs.insert(name.to_owned());
                info.func_arities.insert(name.to_owned(), params.len());
                if let Some(scheme) = info.func_schemes.get(name) {
                    info.func_return_types
                        .insert(name.to_owned(), scheme_return_type(scheme));
                }
            }
        }
    }
}

/// Register tag union constructors into `DeclInfo`.
fn register_tag_union(info: &mut DeclInfo, type_name: &str, tags: &[ast::TagDecl<'_>]) {
    let max_fields = tags.iter().map(|t| t.fields.len()).max().unwrap_or(0);
    for (i, tag) in tags.iter().enumerate() {
        let recursive_flags: Vec<bool> = tag
            .fields
            .iter()
            .map(|field_ty| {
                matches!(field_ty, TypeExpr::Named(name) | TypeExpr::App(name, _) if *name == type_name)
            })
            .collect();
        let field_types: Vec<ScalarType> = info.constructor_schemes.get(tag.name).map_or_else(
            || vec![ScalarType::Ptr; tag.fields.len()],
            |scheme| match &scheme.ty {
                Type::Arrow(params, _) => params.iter().map(type_to_scalar).collect(),
                _ => vec![ScalarType::Ptr; tag.fields.len()],
            },
        );
        info.constructors.insert(
            tag.name.to_owned(),
            ConstructorMeta {
                tag_index: i as u64,
                num_fields: tag.fields.len(),
                max_fields,
                recursive_flags,
                field_types,
            },
        );
    }
}

const fn register_comparison_info() {
    // Bool's True/False constructors are already registered from the Bool stdlib.
    // lower_eq handles emission directly — no separate registration needed.
}

fn register_num_to_str(info: &mut DeclInfo) {
    for ty in &["I64", "U64", "F64", "U8", "I8"] {
        let key = format!("{ty}.to_str");
        info.funcs.insert(key.clone());
        info.num_to_str_methods.insert(key.clone());
        info.func_arities.insert(key, 1);
    }
}
