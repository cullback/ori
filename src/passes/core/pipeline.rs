//! Whole-module AST → Core → SSA pipeline.
//!
//! Top-level entry: `lower_module(mono, fields, decls)` produces an
//! SSA module by lowering every `Decl::FuncDef` through Core. Returns
//! `Err(reason)` if any function can't be lowered (typically because
//! Core or to_ssa hit an unsupported AST/Core variant). The caller
//! decides whether to fall back to the existing direct AST→SSA path.
//!
//! ## Status
//!
//! Works for multi-function programs whose every function body is
//! within the AST→Core + Core→SSA support set today (scalar
//! arithmetic, `if`/`match` over fieldless tag unions, calls between
//! user functions). Fails (returns Err) for anything outside that
//! coverage: list operations that go through stdlib, payload-carrying
//! constructors needing field binders, `Lit::Str`, etc.
//!
//! Not yet wired into `src/main.rs::compile()`. Stays opt-in via
//! tests until coverage is comprehensive enough for hybrid lowering
//! (Core-where-possible, existing-lower-otherwise) to be tractable.

use std::collections::HashMap;

use crate::ast::{Decl, Expr as AstExpr};
use crate::passes::decl_info::DeclInfo;
use crate::passes::mono::Monomorphized;
use crate::ssa::instruction::ScalarType;
use crate::ssa::{Builder, Module, Value};
use crate::symbol::{FieldInterner, SymbolId, SymbolKind};
use crate::types::engine::Type;

use super::lower::{expand_slots, lower_expr_slots, LowerCtx, TransparentTable};
use super::to_ssa;

/// Lower a whole monomorphized AST module to SSA via the Core IR.
///
/// Renames the user's `main` to `__main` (matches existing-lower SSA
/// naming convention).
pub fn lower_module(
    mono: &mut Monomorphized<'_>,
    fields: &FieldInterner,
    decls: &DeclInfo,
) -> Result<Module, String> {
    // Snapshot the function decls (name, params, body) so we don't
    // hold `mono.module` immutably while we borrow `mono.symbols`
    // mutably for slot-symbol minting during lowering.
    let funcs: Vec<(SymbolId, Vec<SymbolId>, AstExpr<'_>)> = mono
        .module
        .decls
        .iter()
        .filter_map(|d| match d {
            Decl::FuncDef {
                name, params, body, ..
            } => Some((*name, params.clone(), body.clone())),
            _ => None,
        })
        .collect();

    let mut builder = Builder::new();

    // Build transparent table from infer (clone the relevant subset
    // — InferResult.transparent has the right shape already).
    let transparent: TransparentTable = mono.infer.transparent.clone();

    // Build payload-carrying-union name set from decl_info.constructors.
    // For each constructor with max_fields > 0, find its return type's
    // name (Ok → Result, Cons → List, etc.) by walking the constructor
    // scheme's Arrow → return type → App/Con name.
    let mut payload_unions: std::collections::HashSet<String> = std::collections::HashSet::new();
    for (con_name, meta) in &decls.constructors {
        if meta.max_fields == 0 { continue; }
        if let Some(scheme) = decls.constructor_schemes.get(con_name) {
            let ret_ty = match &scheme.ty {
                Type::Arrow(_, ret) => ret.as_ref(),
                other => other,
            };
            if let Some(name) = union_name_of(ret_ty) {
                payload_unions.insert(name);
            }
        }
    }

    for (name, params, body) in funcs {
        let name_str = mono.symbols.display(name).to_owned();

        // Per-param slot expansion from the function's declared
        // scheme. Synth functions without schemes default to single
        // RcPtr per source param.
        let per_param_slots = param_slot_types(mono, &name_str, &params, &decls.fieldless_tags, &transparent);

        // Add SSA function params + build locals for both passes.
        // - to_ssa_locals: SymbolId → SSA Value (used by Core→SSA).
        // - core_locals: SymbolId → slot SymbolIds (used by AST→Core
        //   when an AST Name needs to expand to multi-slot Vars).
        let mut to_ssa_locals: HashMap<SymbolId, Value> = HashMap::new();
        let mut core_locals: HashMap<SymbolId, Vec<SymbolId>> = HashMap::new();
        for (param_sym, slot_tys) in params.iter().zip(&per_param_slots) {
            add_function_param(
                &mut builder,
                mono,
                *param_sym,
                slot_tys,
                &mut to_ssa_locals,
                &mut core_locals,
            );
        }

        let entry = builder.create_block();
        builder.switch_to(entry);

        // AST → Core (mut borrows mono.symbols).
        let core_body = {
            let mut ctx = LowerCtx::new(fields, &mut mono.symbols);
            ctx.fieldless = decls.fieldless_tags.clone();
            ctx.transparent = transparent.clone();
            ctx.constructors = decls.constructors.keys().cloned().collect();
            ctx.payload_unions = payload_unions.clone();
            ctx.locals = core_locals;
            lower_expr_slots(&mut ctx, &body).map_err(|e| {
                format!("function `{name_str}`: AST→Core: {e}")
            })?
        };

        // Apply Core-level rewrite rules. Currently algebraic
        // identities only (x + 0, x * 1); fusion rules land here.
        let core_body: Vec<_> = core_body.into_iter().map(super::rules::simplify).collect();

        // Core → SSA via lower_slots so payload Con / multi-result
        // App / multi-slot Match return their full slot list.
        // Concatenating each core_body slot's lowered values gives
        // the function's return slot list.
        let result_vals: Vec<Value> = {
            let mut ctx = to_ssa::Ctx {
                builder: &mut builder,
                symbols: &mono.symbols,
                decls,
                locals: to_ssa_locals,
                fieldless: decls.fieldless_tags.clone(),
                transparent: transparent.clone(),
            };
            let mut all = Vec::new();
            for e in &core_body {
                all.extend(
                    to_ssa::lower_slots(&mut ctx, e)
                        .map_err(|e| format!("function `{name_str}`: Core→SSA: {e}"))?,
                );
            }
            all
        };

        // Reconcile body-slot count with declared-return-slot count.
        // The body's lowering may produce multi-slot (e.g., payload
        // Con returning [tag, payload]) while the function's declared
        // return shape is single-slot (e.g., `Result(I64, I64)` which
        // expand_slots treats as 1 RcPtr because tag-union `:=` types
        // aren't in `infer.transparent`). Materialize Multi → Single
        // by emitting alloc + sequential stores + return the shell
        // pointer — matches existing-lower's convention exactly.
        let ret_slots = expand_slots(&body.ty, &decls.fieldless_tags, &transparent);
        let result_vals = if result_vals.len() == ret_slots.len() {
            result_vals
        } else if ret_slots.len() == 1 && result_vals.len() > 1 {
            let shell = builder.alloc(result_vals.len() * 8);
            for (i, v) in result_vals.iter().enumerate() {
                builder.store(shell, i * 8, *v);
            }
            vec![shell]
        } else {
            return Err(format!(
                "function `{name_str}`: slot count mismatch — body produced {}, return declares {}",
                result_vals.len(),
                ret_slots.len()
            ));
        };

        if result_vals.len() == 1 {
            builder.ret(result_vals[0]);
        } else {
            builder.ret_multi(result_vals);
        }
        let ssa_name = if name_str == "main" { "__main".to_string() } else { name_str.clone() };
        if ret_slots.len() == 1 {
            builder.finish_function(&ssa_name, ret_slots[0]);
        } else {
            builder.finish_function_multi(&ssa_name, ret_slots);
        }
    }

    Ok(builder.build("__main"))
}

/// Resolve a function's per-param slot type expansion. Reads
/// `infer.func_schemes` (authoritative for declared functions);
/// falls back to one RcPtr per source param for synth functions
/// without schemes.
/// Extract the type name for `App(name, _)` or `Con(name)` — used to
/// reverse-look-up a constructor's parent union. Returns None for
/// non-named types (Record, Tuple, function arrows, etc.).
fn union_name_of(ty: &Type) -> Option<String> {
    match ty {
        Type::App(name, _) => Some(name.clone()),
        Type::Con(name) => Some(name.clone()),
        _ => None,
    }
}

fn param_slot_types(
    mono: &Monomorphized<'_>,
    name_str: &str,
    params: &[SymbolId],
    fieldless: &HashMap<String, ScalarType>,
    transparent: &TransparentTable,
) -> Vec<Vec<ScalarType>> {
    mono.infer
        .func_schemes
        .get(name_str)
        .map(|s| match &s.ty {
            Type::Arrow(ps, _) => ps.iter().map(|t| expand_slots(t, fieldless, transparent)).collect(),
            _ => vec![vec![ScalarType::RcPtr]; params.len()],
        })
        .unwrap_or_else(|| vec![vec![ScalarType::RcPtr]; params.len()])
}

/// Add SSA function parameter(s) for a single source-level param.
/// Scalar params: one `add_func_param` + bind sym directly. Multi-
/// slot params (records, tuples): mint slot symbols, add one
/// function param per slot, track slot syms in `core_locals` so
/// AST→Core resolves `Name(p)` to a Vec of slot Vars.
fn add_function_param(
    builder: &mut Builder,
    mono: &mut Monomorphized<'_>,
    param_sym: SymbolId,
    slot_tys: &[ScalarType],
    to_ssa_locals: &mut HashMap<SymbolId, Value>,
    core_locals: &mut HashMap<SymbolId, Vec<SymbolId>>,
) {
    if slot_tys.len() == 1 {
        let v = builder.add_func_param(slot_tys[0]);
        to_ssa_locals.insert(param_sym, v);
    } else {
        let base_name = mono.symbols.display(param_sym).to_owned();
        let span = mono.symbols.get(param_sym).span;
        let slot_syms: Vec<SymbolId> = (0..slot_tys.len())
            .map(|i| mono.symbols.fresh(format!("{base_name}.{i}"), span, SymbolKind::Func))
            .collect();
        for (sym, &ty) in slot_syms.iter().zip(slot_tys) {
            let v = builder.add_func_param(ty);
            to_ssa_locals.insert(*sym, v);
        }
        core_locals.insert(param_sym, slot_syms);
    }
}
