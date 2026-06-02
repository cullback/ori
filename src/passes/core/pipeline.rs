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

use super::lower::{expand_slots, lower_expr_slots, LowerCtx};
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

    for (name, params, body) in funcs {
        let name_str = mono.symbols.display(name).to_owned();

        // Per-param slot expansion from the function's declared
        // scheme. Synth functions without schemes default to single
        // RcPtr per source param.
        let per_param_slots = param_slot_types(mono, &name_str, &params, &decls.fieldless_tags);

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
            ctx.constructors = decls.constructors.keys().cloned().collect();
            ctx.locals = core_locals;
            lower_expr_slots(&mut ctx, &body).map_err(|e| {
                format!("function `{name_str}`: AST→Core: {e}")
            })?
        };

        // Core → SSA (immutable borrow on mono.symbols).
        let result_vals: Vec<Value> = {
            let mut ctx = to_ssa::Ctx {
                builder: &mut builder,
                symbols: &mono.symbols,
                decls,
                locals: to_ssa_locals,
                fieldless: decls.fieldless_tags.clone(),
            };
            core_body
                .iter()
                .map(|e| to_ssa::lower(&mut ctx, e))
                .collect::<Result<_, _>>()
                .map_err(|e| format!("function `{name_str}`: Core→SSA: {e}"))?
        };

        // Emit return + finish.
        if result_vals.len() == 1 {
            builder.ret(result_vals[0]);
        } else {
            builder.ret_multi(result_vals);
        }
        let ret_slots = expand_slots(&body.ty, &decls.fieldless_tags);
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
fn param_slot_types(
    mono: &Monomorphized<'_>,
    name_str: &str,
    params: &[SymbolId],
    fieldless: &HashMap<String, ScalarType>,
) -> Vec<Vec<ScalarType>> {
    mono.infer
        .func_schemes
        .get(name_str)
        .map(|s| match &s.ty {
            Type::Arrow(ps, _) => ps.iter().map(|t| expand_slots(t, fieldless)).collect(),
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
