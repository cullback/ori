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
use crate::types::engine::{Scheme, Type, TypeVar};
use crate::types::infer::InferResult;

/// Build a mangled key for a method on a type, e.g. `method_key("List", "sum")` -> `"List.sum"`.
pub fn method_key(type_name: &str, method: &str) -> String {
    format!("{type_name}.{method}")
}

/// Map a resolved concrete type to the SSA scalar type used at runtime.
/// This is the basic version without fieldless-tag awareness — use
/// [`resolve_scalar_type`] when `DeclInfo` is available.
pub fn type_to_scalar(ty: &Type) -> ScalarType {
    match ty {
        Type::Con(name) => {
            if let Some(num) = crate::numeric::NumericType::from_name(name) {
                num.scalar_type()
            } else {
                ScalarType::Ptr
            }
        }
        _ => ScalarType::Ptr,
    }
}

/// Like [`type_to_scalar`] but also maps fieldless tag unions to their
/// discriminant type (U8/U16/U32/U64) instead of Ptr.
pub fn resolve_scalar_type(ty: &Type, fieldless: &HashMap<String, ScalarType>) -> ScalarType {
    let base = type_to_scalar(ty);
    if base == ScalarType::Ptr {
        match ty {
            Type::Con(name) => {
                if let Some(&disc) = fieldless.get(name.as_str()) {
                    return disc;
                }
            }
            Type::TagUnion { tags, .. } => {
                if tags.iter().all(|(_, fields)| fields.is_empty()) {
                    return discriminant_type(tags.len());
                }
            }
            _ => {}
        }
    }
    base
}

/// Choose the smallest unsigned integer type that can represent
/// `num_variants` distinct values.
pub fn discriminant_type(num_variants: usize) -> ScalarType {
    if num_variants <= 256 {
        ScalarType::U8
    } else if num_variants <= 65536 {
        ScalarType::U16
    } else {
        ScalarType::U64
    }
}

/// Extract the return type from a function type scheme, unwrapping
/// transparent aliases so a `Foo := I64`-declared return surfaces as
/// `I64` rather than `Ptr`.
fn scheme_return_type(
    scheme: &Scheme,
    fieldless: &HashMap<String, ScalarType>,
    transparent: &HashMap<String, (Vec<TypeVar>, Type)>,
) -> ScalarType {
    let ret = match &scheme.ty {
        Type::Arrow(_, ret) => ret.as_ref().clone(),
        other => other.clone(),
    };
    let unwrapped = unwrap_transparent(&ret, transparent);
    resolve_scalar_type(&unwrapped, fieldless)
}

/// Resolve transparent type aliases (types declared with `:=`) to
/// their underlying representation. Mirrors `LowerCtx::resolve_transparent`.
fn unwrap_transparent(
    ty: &Type,
    transparent: &HashMap<String, (Vec<TypeVar>, Type)>,
) -> Type {
    match ty {
        Type::App(name, args) => {
            if let Some((params, underlying)) = transparent.get(name) {
                let mut result = underlying.clone();
                for (p, a) in params.iter().zip(args) {
                    result = substitute_type_var(&result, *p, a);
                }
                unwrap_transparent(&result, transparent)
            } else {
                ty.clone()
            }
        }
        Type::Con(name) => transparent
            .get(name)
            .map_or_else(|| ty.clone(), |(_, under)| unwrap_transparent(under, transparent)),
        _ => ty.clone(),
    }
}

fn substitute_type_var(ty: &Type, var: TypeVar, replacement: &Type) -> Type {
    match ty {
        Type::Var(v) if *v == var => replacement.clone(),
        Type::App(name, args) => Type::App(
            name.clone(),
            args.iter().map(|a| substitute_type_var(a, var, replacement)).collect(),
        ),
        Type::Arrow(params, ret) => Type::Arrow(
            params.iter().map(|p| substitute_type_var(p, var, replacement)).collect(),
            Box::new(substitute_type_var(ret, var, replacement)),
        ),
        Type::Tuple(elems) => Type::Tuple(
            elems.iter().map(|e| substitute_type_var(e, var, replacement)).collect(),
        ),
        Type::Record { fields, rest } => Type::Record {
            fields: fields.iter().map(|(n, t)| (n.clone(), substitute_type_var(t, var, replacement))).collect(),
            rest: rest.clone(),
        },
        Type::TagUnion { tags, rest } => Type::TagUnion {
            tags: tags.iter().map(|(n, ps)| {
                (n.clone(), ps.iter().map(|p| substitute_type_var(p, var, replacement)).collect())
            }).collect(),
            rest: rest.clone(),
        },
        _ => ty.clone(),
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
    /// Type names that are fieldless tag unions (all variants have 0
    /// payload fields), mapped to their discriminant SSA type.
    /// These are represented as a bare integer tag index at runtime.
    pub fieldless_tags: HashMap<String, ScalarType>,
}

/// Build `DeclInfo` from the resolved module declarations.
pub fn build(mono: &Monomorphized<'_>) -> DeclInfo {
    let (module, infer_result, symbols) = (&mono.module, &mono.infer, &mono.symbols);

    // Phase 1: identify fieldless tag unions so `resolve_scalar_type`
    // can use the correct discriminant types during registration.
    let mut fieldless_tags: HashMap<String, ScalarType> = HashMap::new();
    for decl in &module.decls {
        if let Decl::TypeAnno {
            name,
            ty: TypeExpr::TagUnion(tags, _),
            ..
        } = decl
        {
            let max_fields = tags.iter().map(|t| t.fields.len()).max().unwrap_or(0);
            if max_fields == 0 {
                let disc = discriminant_type(tags.len());
                fieldless_tags.insert(symbols.display(*name).to_owned(), disc);
            }
        }
    }

    let mut info = DeclInfo {
        funcs: HashSet::new(),
        func_arities: HashMap::new(),
        func_return_types: HashMap::new(),
        constructors: HashMap::new(),
        constructor_schemes: infer_result.constructor_schemes.clone(),
        fieldless_tags,
    };

    // Register the num-to-str intrinsic method names as known
    // callables so higher-order references (e.g. `List.map(xs,
    // I64.to_str)`) can resolve their target.
    for num in crate::numeric::ALL {
        let key = format!("{}.to_str", num.name());
        info.funcs.insert(key.clone());
        info.func_arities.insert(key, 1);
    }

    // Phase 2: register all declarations with fieldless-tag awareness.
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
                let ret = scheme_return_type(scheme, &info.fieldless_tags, &infer_result.transparent);
                info.func_return_types.insert(name_str.to_owned(), ret);
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
            let ret = scheme_return_type(scheme, &info.fieldless_tags, &infer_result.transparent);
            info.func_return_types.insert(mangled, ret);
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
        let fieldless = &info.fieldless_tags;
        let field_types: Vec<ScalarType> = info.constructor_schemes.get(tag.name).map_or_else(
            || vec![ScalarType::Ptr; tag.fields.len()],
            |scheme| match &scheme.ty {
                Type::Arrow(params, _) => {
                    params.iter().map(|t| resolve_scalar_type(t, fieldless)).collect()
                }
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

