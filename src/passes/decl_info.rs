//! Post-lower registration data: flat lookups for functions,
//! constructors, and builtin methods that `ssa::lower` needs while
//! walking the AST.
//!
//! Step 10 stripped this module down from 9 overlapping lookup tables
//! to just the ones the streamlined lowerer actually reads:
//! `funcs` / `func_return_types` / `constructors` /
//! `num_to_str_methods`. The `list_builtins`, `func_aliases`,
//! `func_arities`, and `func_schemes` / `constructor_schemes` maps
//! were either never populated or only used by machinery that's gone
//! now (reachability aliases, defunc HO-arg lookup, etc.).

use std::collections::{HashMap, HashSet};

use crate::ast::{self, Decl, TypeExpr};
use crate::passes::mono::Monomorphized;
use crate::ssa::ScalarType;
use crate::symbol::SymbolTable;
use crate::types::engine::{Scheme, Type};
use crate::types::infer::InferResult;

/// Build a mangled key for a method on a type, e.g. `method_key("List", "sum")` -> `"List.sum"`.
pub fn method_key(type_name: &str, method: &str) -> String {
    format!("{type_name}.{method}")
}

/// Map a resolved concrete type to the SSA scalar type used at runtime.
pub fn type_to_scalar(ty: &Type) -> ScalarType {
    match ty {
        Type::Con(name) => {
            if let Some(num) = crate::numeric::NumericType::from_name(name) {
                num.scalar_type()
            } else if name == "Bool" {
                ScalarType::Bool
            } else {
                ScalarType::Ptr
            }
        }
        _ => ScalarType::Ptr,
    }
}

/// Extract the return type from a function type scheme.
fn scheme_return_type(scheme: &Scheme) -> ScalarType {
    match &scheme.ty {
        Type::Arrow(_, ret) => type_to_scalar(ret),
        other => type_to_scalar(other),
    }
}

/// Constructor metadata for tag union variants and closure types.
#[derive(Clone, Debug)]
#[allow(dead_code, reason = "fields read at lower time")]
pub struct ConstructorMeta {
    pub tag_index: u64,
    pub num_fields: usize,
    pub max_fields: usize,
    pub recursive_flags: Vec<bool>,
    pub field_types: Vec<ScalarType>,
}

/// Registration data about all declared functions, constructors, and
/// builtins. Populated by [`build`] and consumed by `ssa::lower`.
pub struct DeclInfo {
    /// Every known callable, keyed by its mangled display name
    /// (e.g. `main`, `List.sum__I64`, `__apply_List.walk_2`).
    pub funcs: HashSet<String>,
    /// Number of parameters per callable. Defunc reads this when
    /// registering named-function-reference lambda entries.
    pub func_arities: HashMap<String, usize>,
    /// Concrete return type per callable. Missing entries default to
    /// `Ptr` at lookup time (for synthesized apply functions).
    pub func_return_types: HashMap<String, ScalarType>,
    /// Per-constructor tag index and field layout. Populated from
    /// user tag unions AND synthesized closure types from defunc.
    pub constructors: HashMap<String, ConstructorMeta>,
    /// Raw constructor schemes from inference, used to compute the
    /// field-type layout during tag-union registration.
    pub constructor_schemes: HashMap<String, Scheme>,
}

/// Build `DeclInfo` from the resolved module declarations.
pub fn build(mono: &Monomorphized<'_>) -> DeclInfo {
    let (module, infer_result, symbols) = (&mono.module, &mono.infer, &mono.symbols);
    let mut info = DeclInfo {
        funcs: HashSet::new(),
        func_arities: HashMap::new(),
        func_return_types: HashMap::new(),
        constructors: HashMap::new(),
        constructor_schemes: infer_result.constructor_schemes.clone(),
    };

    // Register the num-to-str intrinsic method names as known
    // callables so higher-order references (e.g. `List.map(xs,
    // I64.to_str)`) can resolve their target.
    for num in crate::numeric::ALL {
        let key = format!("{}.to_str", num.name());
        info.funcs.insert(key.clone());
        info.func_arities.insert(key, 1);
    }

    for decl in &module.decls {
        register_decl(&mut info, decl, infer_result, symbols);
    }

    info
}

fn register_decl(
    info: &mut DeclInfo,
    decl: &Decl<'_>,
    infer_result: &InferResult,
    symbols: &SymbolTable,
) {
    match decl {
        Decl::TypeAnno {
            name,
            ty: TypeExpr::TagUnion(tags, _),
            methods,
            ..
        } => {
            let type_name = symbols.display(*name);
            register_tag_union(info, type_name, tags);
            for method_decl in methods {
                register_method(info, type_name, method_decl, infer_result, symbols);
            }
        }
        Decl::TypeAnno { name, methods, .. } => {
            let type_name = symbols.display(*name);
            for method_decl in methods {
                register_method(info, type_name, method_decl, infer_result, symbols);
            }
        }
        Decl::FuncDef { name, params, .. } => {
            let name_str = symbols.display(*name);
            info.funcs.insert(name_str.to_owned());
            info.func_arities.insert(name_str.to_owned(), params.len());
            if let Some(scheme) = infer_result.func_schemes.get(name_str) {
                info.func_return_types
                    .insert(name_str.to_owned(), scheme_return_type(scheme));
            }
        }
    }
}

fn register_method(
    info: &mut DeclInfo,
    type_name: &str,
    method_decl: &Decl<'_>,
    infer_result: &InferResult,
    symbols: &SymbolTable,
) {
    if let Decl::FuncDef {
        name: method_name,
        params,
        ..
    } = method_decl
    {
        let method_name_str = symbols.display(*method_name);
        let mangled = method_key(type_name, method_name_str);
        info.funcs.insert(mangled.clone());
        info.func_arities.insert(mangled.clone(), params.len());
        if let Some(scheme) = infer_result.func_schemes.get(&mangled) {
            info.func_return_types
                .insert(mangled, scheme_return_type(scheme));
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

