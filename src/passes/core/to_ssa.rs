//! Core → SSA lowering.
//!
//! Translates Core expressions into SSA via the existing `ssa::Builder`.
//! Each Core primitive maps to a small SSA sequence — `BinOp` to one
//! `Inst::BinOp`, `Lit` to `Inst::Const`, `Let` to a binding + nested
//! lowering, `Var` to a lookup in the locals map.
//!
//! ## Status
//!
//! Minimal slice: `Var`, `Lit::Int`, `Let`, `BinOp`. Enough to round-trip
//! `let x = 1 + 2 in x + 3`-shaped programs end-to-end. Other Core
//! variants error out until needed — same convention as the AST→Core
//! lowering.
//!
//! ## Lowering context
//!
//! `Ctx` carries:
//! - A `Builder` for emitting instructions / managing blocks.
//! - A `locals` map from `SymbolId` → current SSA `Value`. Every
//!   `Var` lookup goes through this map. `Let` extends it.
//! - A `fieldless` map for scalar-type resolution of tag unions (today
//!   unused in this slice but required by `resolve_scalar_type`).

use std::collections::HashMap;

use crate::passes::decl_info::structural_con_layout;
use crate::passes::decl_info::{DeclInfo, resolve_scalar_type};
use crate::ssa::instruction::ScalarType;
use crate::ssa::{Builder, Value};
use crate::symbol::{SymbolId, SymbolTable};
use crate::types::engine::Type;

use super::expr::{Expr, Literal, MatchArm, Pattern};

/// Lowering context. Mutable: tracks the current locals map as `Let`s
/// extend it; the `Builder` is borrowed mutably and accumulates the
/// emitted instructions in its current block. The `SymbolTable` is
/// borrowed to resolve `App` targets to mangled name strings (SSA
/// `Call.target` is a string, by design — keeps codegen independent
/// of the symbol-ID allocator).
pub struct Ctx<'b> {
    pub builder: &'b mut Builder,
    pub symbols: &'b SymbolTable,
    pub decls: &'b DeclInfo,
    /// Local binding → its SSA value(s). Single-slot bindings have
    /// a 1-element Vec; multi-slot bindings (records, tuples,
    /// payload-union destructures bound by a single source name)
    /// have an N-element Vec carrying every slot. `lower` (single-
    /// slot lookup) requires the Vec to be exactly 1 element;
    /// `lower_slots` (multi-slot lookup) returns the full Vec.
    pub locals: HashMap<SymbolId, Vec<Value>>,
    pub fieldless: HashMap<String, ScalarType>,
    pub transparent: super::lower::TransparentTable,
    /// Used by `lower(Let)` to unbox a single-shell value into N slots
    /// when binders > value slot count. NOT used for App return-type
    /// decisions — those follow the existing-lower single-shell
    /// convention to keep call-result compatibility.
    pub payload_unions: std::collections::HashSet<String>,
    /// Builtin op SymbolIds. App's whose `target` matches one of
    /// these dispatch to inline ops (`Inst::BinOp`, `Inst::Cast`,
    /// inline range loop) instead of regular function calls.
    pub builtins: crate::symbol::BuiltinRegistry,
    /// Memo for shared-evaluation `Let`s. When `bind_multi_slot` or
    /// `lower_block`'s wrap-with-Lets emits N `Let`s with the same
    /// `binders` (because all N reference the same multi-slot value
    /// at different slot indices), we lower `value` only on the
    /// first encounter and reuse the resulting `Value`s thereafter.
    /// Keyed by `binders[0]` — slot syms are minted fresh per
    /// binding site, so the first binder uniquely identifies the
    /// group. Empty for `Let`s introduced outside the fan-out
    /// pattern (e.g. a regular block-level scalar let).
    pub bind_cache: HashMap<SymbolId, Vec<Value>>,
}

/// Lower a Core expression as a multi-slot SSA result. Returns
/// `Vec<Value>` whose length matches `expand_slots(expr.ty)`.
///
/// Most Core variants are single-slot; we delegate to `lower` and
/// wrap in a 1-element vec. The variants that are intrinsically
/// multi-slot (payload `Con`, multi-result `App`, multi-slot
/// `Match` result) have their own handlers.
pub fn lower_slots(ctx: &mut Ctx<'_>, expr: &Expr) -> Result<Vec<Value>, String> {
    match expr {
        // Payload-carrying Con: (tag, payload_ptr) two slots. We
        // allocate the payload, store each arg's slots at consecutive
        // offsets, return [tag, payload].
        Expr::Con { tag, args, field_slot_counts, ty } => {
            // Lower each arg's slots — already flattened to one
            // Core Expr per slot upstream (lower_call_args), so
            // each arg contributes one Value at this layer.
            let mut all_slots: Vec<Value> = Vec::new();
            for arg in args {
                all_slots.extend(lower_slots(ctx, arg)?);
            }
            // Phase E: single-variant payload union decomposes to
            // exactly the variant's fields — no tag, no payload heap.
            // Only applies when the Con's type is genuinely single-
            // variant. For multi-variant unions like
            // `Nat : [Zero, Succ(Nat)]`, `Succ(Zero)`'s args happen
            // to produce the same 2-slot shape as the parent union
            // (Zero unboxes to (tag, payload) == [U64, RcPtr] which
            // matches Nat's expand_slots), but that's a coincidence
            // — the union still needs the (tag, payload) shell.
            let is_single_variant = is_single_variant_union(ty, &ctx.transparent);
            let con_slots = super::lower::expand_slots_with(
                ty,
                &ctx.fieldless,
                &ctx.transparent,
                &ctx.payload_unions,
            );
            if is_single_variant && con_slots.len() == all_slots.len() && !all_slots.is_empty() {
                return Ok(all_slots);
            }
            let disc = resolve_scalar_type(ty, &ctx.fieldless);
            if !disc.is_heap_ptr() {
                // Fieldless — single-slot. Delegate to the scalar Con
                // path. all_slots should be empty for fieldless cons.
                return Ok(vec![lower(ctx, expr)?]);
            }
            // Multi-variant payload-carrying: payload holds one RcPtr
            // per source-level field. Multi-slot source fields (Str,
            // List, nested unions) get materialized into a 1-RcPtr
            // shell containing their N slots, matching existing-lower's
            // runtime contract. Re-group the per-slot Core args back
            // into source fields via the constructor's field-type
            // expansion.
            let tag_idx = if let Some(meta) = ctx.decls.constructors.get(tag) {
                meta.tag_index
            } else {
                structural_con_layout(ty, tag, &ctx.fieldless).0
            };
            let field_groups = group_args_by_field(
                field_slot_counts,
                &all_slots,
            );
            let arg_vals: Vec<Value> = field_groups
                .iter()
                .map(|slots| {
                    if slots.len() == 1 {
                        slots[0]
                    } else {
                        let wrapper = ctx.builder.alloc(slots.len() * 8);
                        for (i, v) in slots.iter().enumerate() {
                            ctx.builder.store(wrapper, i * 8, *v);
                        }
                        wrapper
                    }
                })
                .collect();
            let payload = ctx.builder.alloc(arg_vals.len() * 8);
            for (i, v) in arg_vals.iter().enumerate() {
                ctx.builder.store(payload, i * 8, *v);
            }
            let tag_v = ctx.builder.const_u64(tag_idx);
            Ok(vec![tag_v, payload])
        }

        // App where the return type is multi-slot — emit call_multi
        // and return the result slot list directly.
        Expr::App { target, args, ty } => {
            // Builtin dispatch: `Range` is the only currently-defined
            // builtin with a multi-slot return (the buffer trio).
            // Binary / Cast / Bitcast return a scalar — delegate
            // through `lower` so we hit the single-slot dispatch.
            if let Some(kind) = ctx.builtins.classify(*target) {
                return match kind {
                    crate::symbol::BuiltinKind::Range => emit_builtin_range(ctx, args, ty),
                    crate::symbol::BuiltinKind::Binary(_)
                    | crate::symbol::BuiltinKind::Cast
                    | crate::symbol::BuiltinKind::Bitcast => {
                        Ok(vec![emit_builtin_single_slot(ctx, kind, args, ty)?])
                    }
                };
            }
            let ret_slots = super::lower::expand_slots_with(ty, &ctx.fieldless, &ctx.transparent, &ctx.payload_unions);
            if ret_slots.len() == 1 {
                return Ok(vec![lower(ctx, expr)?]);
            }
            // Multi-result call. Spread each arg's slots, emit call_multi.
            let mut arg_vals: Vec<Value> = Vec::new();
            for a in args {
                arg_vals.extend(lower_slots(ctx, a)?);
            }
            let target_name = ctx.symbols.display(*target);
            Ok(ctx.builder.call_multi(target_name, arg_vals, &ret_slots))
        }

        // Match's natural multi-slot return — the merge block has
        // one param per result slot, and each arm jumps with N values
        // directly. Callers that need only one slot pick out of the
        // returned Vec; callers that need all (multi-slot Result
        // unbox) get them straight. No shell, no per-slot loads.
        Expr::Match { scrutinee_slots, scrutinee_ty, arms, ty } => {
            lower_match(ctx, scrutinee_slots, scrutinee_ty, arms, ty)
        }

        // Cata dispatches on target's source type:
        //   - target_ty unwraps to `List(T)` → emit a counter loop
        //     (`lower_list_cata`). `early_exit=true` adds
        //     Continue/Break dispatch on each step return.
        //   - Otherwise → emit a recursive helper Call. The
        //     fold-helper's body (from `fold_lift`) holds the
        //     structural recursion.
        Expr::Cata { fold_fn, target_slots, target_ty, init, captures, elem_ty, early_exit, ty } => {
            let unwrapped = super::lower::resolve_transparent(target_ty, &ctx.transparent);
            let is_list = matches!(&unwrapped, Type::App(n, ts) if n == "List" && ts.len() == 1);
            let fold_name = ctx.symbols.display(*fold_fn);
            if is_list {
                return lower_list_cata(ctx, target_slots, init, captures, elem_ty, *early_exit, fold_name, ty);
            }
            // Helper-call path: Call(fold_fn, target_slots ++ init ++ captures).
            let ret_slots = super::lower::expand_slots_with(ty, &ctx.fieldless, &ctx.transparent, &ctx.payload_unions);
            let mut arg_vals: Vec<Value> = Vec::new();
            for s in target_slots {
                arg_vals.extend(lower_slots(ctx, s)?);
            }
            for a in init {
                arg_vals.extend(lower_slots(ctx, a)?);
            }
            for a in captures {
                arg_vals.extend(lower_slots(ctx, a)?);
            }
            if ret_slots.len() == 1 {
                let ret_ty = resolve_scalar_type(ty, &ctx.fieldless);
                Ok(vec![ctx.builder.call(fold_name, arg_vals, ret_ty)])
            } else {
                Ok(ctx.builder.call_multi(fold_name, arg_vals, &ret_slots))
            }
        }

        // List literals fan out to (len, cap, data) directly so
        // App args, function returns, Con payloads receive the
        // trio without an intermediate header alloc. The single-
        // slot `lower` path wraps to a header when the caller
        // needs one RcPtr (boundary cases only).
        Expr::BufLit { elements, elem_ty, .. } => {
            let slot_count = super::lower::expand_slots_with(
                elem_ty,
                &ctx.fieldless,
                &ctx.transparent,
                &ctx.payload_unions,
            )
            .len()
            .max(1);
            let total_slots = elements.len();
            let n = total_slots / slot_count;
            let data = ctx.builder.alloc(total_slots * 8);
            for (i, elem) in elements.iter().enumerate() {
                let v = lower(ctx, elem)?;
                ctx.builder.store(data, i * 8, v);
            }
            let len_val = ctx.builder.const_u64(n as u64);
            Ok(vec![len_val, len_val, data])
        }


        // List.set: cow_store_dyn val into the data buffer at
        // index `idx`. Multi-slot elements stride at
        // `val_slots.len() * 8` bytes; each slot is a separate
        // cow_store_dyn call (the first cow-preps the buffer; the
        // result feeds the next call so the entire element lands
        // in one cloned/unique buffer). Returns the new
        // (len, cap, new_data) trio.
        Expr::BufSet { buf_slots, idx, val_slots, .. } => {
            use crate::ssa::{BinaryOp, ScalarType};
            let list_vals: Vec<Value> = {
                let mut all = Vec::new();
                for e in buf_slots {
                    all.extend(lower_slots(ctx, e)?);
                }
                all
            };
            if list_vals.len() != 3 {
                return Err(format!(
                    "core::to_ssa: ListSet expects 3-slot list trio, got {} slots",
                    list_vals.len()
                ));
            }
            let len = list_vals[0];
            let cap = list_vals[1];
            let data = list_vals[2];
            let idx_v = lower(ctx, idx)?;
            let val_vals: Vec<Value> = {
                let mut all = Vec::new();
                for e in val_slots {
                    all.extend(lower_slots(ctx, e)?);
                }
                all
            };
            let stride_units = val_vals.len().max(1) as u64;
            let stride_units_const = ctx.builder.const_u64(stride_units);
            let elem_unit_base = ctx.builder.binop(BinaryOp::Mul, idx_v, stride_units_const, ScalarType::U64);

            let mut current = data;
            for (j, v) in val_vals.iter().enumerate() {
                let target_idx = if j == 0 {
                    elem_unit_base
                } else {
                    let j_const = ctx.builder.const_u64(j as u64);
                    ctx.builder.binop(BinaryOp::Add, elem_unit_base, j_const, ScalarType::U64)
                };
                current = ctx.builder.cow_store_dyn(current, target_idx, *v);
            }
            Ok(vec![len, cap, current])
        }

        // List.append: cow_resize_dyn the data buffer to fit one
        // more element, write val slots at index `len`, return the
        // new (new_len, new_len, new_data) trio. Multi-slot
        // elements (records, Str, nested lists) store N slots at
        // consecutive 8-byte offsets within the element's stride
        // bucket.
        Expr::BufAppend { buf_slots, val_slots, .. } => {
            use crate::ssa::{BinaryOp, ScalarType};
            let list_vals: Vec<Value> = {
                let mut all = Vec::new();
                for e in buf_slots {
                    all.extend(lower_slots(ctx, e)?);
                }
                all
            };
            if list_vals.len() != 3 {
                return Err(format!(
                    "core::to_ssa: ListAppend expects 3-slot list trio, got {} slots",
                    list_vals.len()
                ));
            }
            let len = list_vals[0];
            let data = list_vals[2];

            let val_vals: Vec<Value> = {
                let mut all = Vec::new();
                for e in val_slots {
                    all.extend(lower_slots(ctx, e)?);
                }
                all
            };
            let stride_units = val_vals.len().max(1) as u64;
            let stride_bytes = stride_units * 8;

            let one = ctx.builder.const_u64(1);
            let new_len = ctx.builder.binop(BinaryOp::Add, len, one, ScalarType::U64);
            let stride_bytes_const = ctx.builder.const_u64(stride_bytes);
            let new_byte_len = ctx.builder.binop(BinaryOp::Mul, new_len, stride_bytes_const, ScalarType::U64);
            let new_data = ctx.builder.cow_resize_dyn(data, new_byte_len);

            // Element-unit base: `len * stride_units` (in 8-byte
            // index units, matching `store_dyn`'s convention).
            let stride_units_const = ctx.builder.const_u64(stride_units);
            let elem_unit_base = ctx.builder.binop(BinaryOp::Mul, len, stride_units_const, ScalarType::U64);
            for (j, v) in val_vals.iter().enumerate() {
                if j == 0 {
                    ctx.builder.store_dyn(new_data, elem_unit_base, *v);
                } else {
                    let j_const = ctx.builder.const_u64(j as u64);
                    let idx = ctx.builder.binop(BinaryOp::Add, elem_unit_base, j_const, ScalarType::U64);
                    ctx.builder.store_dyn(new_data, idx, *v);
                }
            }
            Ok(vec![new_len, new_len, new_data])
        }

        // Var with multi-slot binding: return all slot values
        // directly. `lower` errors on multi-slot Vars; this is the
        // multi-slot read path. Single-slot Vars also flow through
        // here because the fallback `_ =>` would call `lower` which
        // returns a 1-element Vec from a 1-element locals entry.
        Expr::Var { sym, .. } => {
            ctx.locals.get(sym).cloned().ok_or_else(|| {
                let name = ctx
                    .symbols
                    .try_get(*sym)
                    .map(|info| info.display.as_str())
                    .unwrap_or("?");
                format!("core::to_ssa: unbound Var #{} ({name})", sym.0)
            })
        }
        // All other variants are single-slot today; delegate.
        _ => Ok(vec![lower(ctx, expr)?]),
    }
}

/// Lower a Core expression into SSA, returning the `Value` holding
/// the result. Errors when the Core variant isn't yet supported by
/// this slice.
pub fn lower(ctx: &mut Ctx<'_>, expr: &Expr) -> Result<Value, String> {
    match expr {
        Expr::Var { sym, .. } => {
            let vals = ctx
                .locals
                .get(sym)
                .cloned()
                .ok_or_else(|| {
                    let name = ctx
                        .symbols
                        .try_get(*sym)
                        .map(|info| info.display.as_str())
                        .unwrap_or("?");
                    format!("core::to_ssa: unbound Var #{} ({name})", sym.0)
                })?;
            if vals.len() != 1 {
                return Err(format!(
                    "core::to_ssa: multi-slot Var #{} accessed via single-slot lower (use lower_slots)",
                    sym.0
                ));
            }
            Ok(vals[0])
        }

        Expr::Lit { value: Literal::Int(n), ty } => {
            // Type-directed const emission. Programs with U64, U8, I32,
            // etc. integer literals need the right const_* method or
            // SSA validation rejects the type mismatch.
            let scalar = resolve_scalar_type(ty, &ctx.fieldless);
            Ok(emit_int_const(ctx.builder, *n, scalar))
        }

        Expr::Lit { value: Literal::Float(f), .. } => Ok(ctx.builder.const_f64(*f)),

        Expr::Let { binders, value, body, .. } => {
            // Shared-Let memoization. When N `Let`s share the same
            // `binders` (the `bind_multi_slot` pattern, or
            // `lower_block`'s wrap-with-Lets across body slots),
            // lower `value` exactly once and reuse the result for
            // each subsequent Let. `binders[0]` keys the cache —
            // slot syms are minted fresh per binding site, so a
            // shared first binder uniquely identifies the group.
            let cache_key = binders.first().copied();
            let mut vals = if let Some(key) = cache_key {
                if let Some(cached) = ctx.bind_cache.get(&key) {
                    cached.clone()
                } else {
                    let computed = lower_slots(ctx, value)?;
                    ctx.bind_cache.insert(key, computed.clone());
                    computed
                }
            } else {
                lower_slots(ctx, value)?
            };
            // If value returned a single Value (heap shell from a Call
            // to a payload-union-returning function) but binders want
            // multiple slots, unbox by loading N values from the shell
            // at consecutive offsets. The slot types come from
            // expand_slots on the value's type — needs payload_unions
            // so App-form unions resolve correctly.
            if vals.len() == 1 && binders.len() > 1 {
                let slot_tys = super::lower::expand_slots_with(
                    value.ty(),
                    &ctx.fieldless,
                    &ctx.transparent,
                    &ctx.payload_unions,
                );
                if slot_tys.len() == binders.len() {
                    let shell = vals[0];
                    vals = slot_tys
                        .iter()
                        .enumerate()
                        .map(|(i, &ty)| ctx.builder.load(shell, i * 8, ty))
                        .collect();
                    if let Some(key) = cache_key {
                        ctx.bind_cache.insert(key, vals.clone());
                    }
                }
            }
            // Value returned multiple slots but the binder is a
            // single source name (e.g. `w = MkWrap(...)` where MkWrap
            // is single-variant and its tuple field fans out to 2
            // slots). Bind the source name to the full slot list as
            // a multi-slot local.
            if vals.len() > 1 && binders.len() == 1 {
                let binder = binders[0];
                let prev = vec![(binder, ctx.locals.insert(binder, vals))];
                let result_slots = lower_slots(ctx, body);
                for (binder, p) in prev.into_iter().rev() {
                    match p {
                        Some(prev_val) => { ctx.locals.insert(binder, prev_val); }
                        None => { ctx.locals.remove(&binder); }
                    }
                }
                let result_slots = result_slots?;
                if result_slots.len() == 1 {
                    return Ok(result_slots[0]);
                } else {
                    let shell = ctx.builder.alloc(result_slots.len() * 8);
                    for (i, v) in result_slots.iter().enumerate() {
                        ctx.builder.store(shell, i * 8, *v);
                    }
                    return Ok(shell);
                }
            }
            if vals.len() != binders.len() {
                return Err(format!(
                    "core::to_ssa: Let value produced {} slots but binders.len()={}",
                    vals.len(),
                    binders.len()
                ));
            }
            let mut prev = Vec::with_capacity(binders.len());
            for (binder, val) in binders.iter().zip(vals) {
                prev.push((*binder, ctx.locals.insert(*binder, vec![val])));
            }
            let result_slots = lower_slots(ctx, body);
            for (binder, p) in prev.into_iter().rev() {
                match p {
                    Some(prev_val) => { ctx.locals.insert(binder, prev_val); }
                    None => { ctx.locals.remove(&binder); }
                }
            }
            let result_slots = result_slots?;
            if result_slots.len() == 1 {
                Ok(result_slots[0])
            } else {
                let shell = ctx.builder.alloc(result_slots.len() * 8);
                for (i, v) in result_slots.iter().enumerate() {
                    ctx.builder.store(shell, i * 8, *v);
                }
                Ok(shell)
            }
        }


        Expr::App { target, args, ty } => {
            // Builtin dispatch: primitive arithmetic / cast / range
            // are App-shaped at Core but lower to inline ops, not
            // function calls.
            if let Some(kind) = ctx.builtins.classify(*target) {
                return emit_builtin_single_slot(ctx, kind, args, ty);
            }
            // Use lower_slots for args so multi-slot args (records,
            // payload Cons, multi-result Calls) spread into multiple
            // SSA call args. Single-result return; multi-result goes
            // through lower_slots's own App handler.
            let mut arg_vals: Vec<Value> = Vec::new();
            for a in args {
                arg_vals.extend(lower_slots(ctx, a)?);
            }
            // Use expand_slots for the return scalar so single-slot
            // Phase-E TagUnions ([Wrapped(I64)] → I64) match the
            // callee's actual SSA return. resolve_scalar_type alone
            // would give RcPtr (TagUnion default) where the callee
            // returns I64.
            let ret_slots = super::lower::expand_slots_with(ty, &ctx.fieldless, &ctx.transparent, &ctx.payload_unions);
            let ret_ty = if ret_slots.len() == 1 {
                ret_slots[0]
            } else {
                resolve_scalar_type(ty, &ctx.fieldless)
            };
            let target_name = ctx.symbols.display(*target);
            Ok(ctx.builder.call(target_name, arg_vals, ret_ty))
        }

        // Single-slot Cata path: defer to the multi-slot lowering
        // and materialize the result. List-shaped Catas emit a
        // counter loop; recursive-helper Catas emit a Call. Either
        // way `lower_slots` returns the slot list; we shell-wrap
        // multi-slot results so the single-slot caller sees one
        // RcPtr.
        Expr::Cata { .. } => {
            let slots = lower_slots(ctx, expr)?;
            if slots.len() == 1 {
                Ok(slots[0])
            } else {
                let shell = ctx.builder.alloc(slots.len() * 8);
                for (i, v) in slots.iter().enumerate() {
                    ctx.builder.store(shell, i * 8, *v);
                }
                Ok(shell)
            }
        }

        Expr::BufLit { elements, elem_ty, .. } => {
            // Element layout: each source-level element occupies
            // `slot_count` consecutive 8-byte slots in the data
            // buffer. `elements` is already flat (AST→Core
            // concatenated each element's slot list), so the
            // source-level element count is `elements.len() /
            // slot_count` and stores fan out in source order.
            let slot_count = super::lower::expand_slots_with(
                elem_ty,
                &ctx.fieldless,
                &ctx.transparent,
                &ctx.payload_unions,
            )
            .len()
            .max(1);
            let total_slots = elements.len();
            let n = total_slots / slot_count;
            let data = ctx.builder.alloc(total_slots * 8);
            for (i, elem) in elements.iter().enumerate() {
                let v = lower(ctx, elem)?;
                ctx.builder.store(data, i * 8, v);
            }
            let header = ctx.builder.alloc(24);
            let len_val = ctx.builder.const_u64(n as u64);
            ctx.builder.store(header, 0, len_val);
            ctx.builder.store(header, 8, len_val);
            ctx.builder.store(header, 16, data);
            Ok(header)
        }

        Expr::Match { scrutinee_slots, scrutinee_ty, arms, ty } => {
            // Single-value caller: Match naturally returns its full
            // slot list. If the result type is single-slot, take the
            // one value; if multi-slot, materialize a shell so this
            // single-value callsite still gets one RcPtr. (Multi-slot
            // callers go through `lower_slots`'s Match arm below,
            // which avoids the shell entirely.)
            let slots = lower_match(ctx, scrutinee_slots, scrutinee_ty, arms, ty)?;
            if slots.len() == 1 {
                Ok(slots[0])
            } else {
                let shell = ctx.builder.alloc(slots.len() * 8);
                for (i, v) in slots.iter().enumerate() {
                    ctx.builder.store(shell, i * 8, *v);
                }
                Ok(shell)
            }
        }

        // Unchecked indexed load from a buffer pointer. Lowers to
        // SSA `load_dyn(buf, idx, scalar_ty)` — one instruction.
        // The bounds check that makes `List.get` safe lives in the
        // surrounding `Match` synthesized at AST→Core time.
        Expr::BufLoad { buf, idx, ty } => {
            let buf_val = lower(ctx, buf)?;
            let idx_val = lower(ctx, idx)?;
            let scalar = resolve_scalar_type(ty, &ctx.fieldless);
            Ok(ctx.builder.load_dyn(buf_val, idx_val, scalar))
        }

        Expr::Con { tag, args, field_slot_counts: _, ty } => {
            // Only fieldless unions handled in the single-slot path
            // today. Payload Cons that the caller actually wants as
            // a multi-slot result are lowered through lower_slots
            // and the caller would have invoked that directly.
            if !args.is_empty() {
                // Fall through to lower_slots and materialize as
                // shell — needed when a single-slot caller wants
                // the Con's value but we'd otherwise produce a
                // multi-slot Phase-E fanout. Single-slot caller
                // gets back the shell; multi-slot caller would
                // have used lower_slots directly.
                let slots = lower_slots(ctx, expr)?;
                if slots.len() == 1 {
                    return Ok(slots[0]);
                }
                let shell = ctx.builder.alloc(slots.len() * 8);
                for (i, v) in slots.iter().enumerate() {
                    ctx.builder.store(shell, i * 8, *v);
                }
                return Ok(shell);
            }
            let disc = resolve_scalar_type(ty, &ctx.fieldless);
            if disc.is_heap_ptr() {
                return Err(format!(
                    "core::to_ssa: Con `{tag}` of payload-carrying union (disc resolves to {disc:?}); only fieldless unions supported"
                ));
            }
            let tag_idx = if let Some(meta) = ctx.decls.constructors.get(tag) {
                meta.tag_index
            } else {
                structural_con_layout(ty, tag, &ctx.fieldless).0
            };
            emit_tag_const(ctx.builder, tag_idx, disc)
                .ok_or_else(|| format!(
                    "core::to_ssa: Con `{tag}` has unsupported discriminant type {disc:?}"
                ))
        }

        // ListSet single-slot caller: materialize the trio.
        Expr::BufSet { .. } => {
            let slots = lower_slots(ctx, expr)?;
            let shell = ctx.builder.alloc(slots.len() * 8);
            for (i, v) in slots.iter().enumerate() {
                ctx.builder.store(shell, i * 8, *v);
            }
            Ok(shell)
        }

        // ListAppend single-slot caller: materialize the trio
        // into a shell. Multi-slot callers go through `lower_slots`.
        Expr::BufAppend { .. } => {
            let slots = lower_slots(ctx, expr)?;
            let shell = ctx.builder.alloc(slots.len() * 8);
            for (i, v) in slots.iter().enumerate() {
                ctx.builder.store(shell, i * 8, *v);
            }
            Ok(shell)
        }

    }
}

/// Lower a `Match` to SSA. Supported shapes:
///
/// 1. **Single-arm Wildcard / Binding** — trivial: the arm always runs.
/// 2. **Multi-arm Constructor** dispatch over **fieldless** tag unions
///    — emits a `SwitchInt` on the scalar discriminant; each arm has
///    its own block; results merge into a block-param of the result
///    type.
///
/// Lower a List-shaped Cata to a counter loop. Shared by both the
/// plain walk (`early_exit=false`) and walk-until (`early_exit=
/// true`) paths — the only structural difference is whether the
/// step's result needs Continue/Break tag-dispatch before being
/// fed back as the next accumulator.
///
/// SSA shape:
/// ```text
///   entry → header(0, init..., len, data, caps...)
///   header: i == len ? done(acc..., data, caps...) : body(...)
///   body: load elem at i (multi-slot stride); step(caps, acc, elem)
///         early_exit=false: jump header(i+1, new_acc, ...)
///         early_exit=true:  branch on Step tag — Continue → header(...);
///                                                Break    → done(new_acc, ...)
///   done(acc..., _data, _caps): yield acc
/// ```
fn lower_list_cata(
    ctx: &mut Ctx<'_>,
    target_slots: &[Expr],
    init: &[Expr],
    captures: &[Expr],
    elem_ty: &Type,
    early_exit: bool,
    fold_fn: &str,
    walk_ty: &Type,
) -> Result<Vec<Value>, String> {
    use crate::ssa::{BinaryOp, ScalarType};

    let list_vals: Vec<Value> = {
        let mut all = Vec::new();
        for e in target_slots {
            all.extend(lower_slots(ctx, e)?);
        }
        all
    };
    if list_vals.len() != 3 {
        return Err(format!(
            "core::to_ssa: List-Cata expects 3-slot list trio, got {} slots",
            list_vals.len()
        ));
    }
    let len_val = list_vals[0];
    let data_ptr = list_vals[2];

    let acc_slots: Vec<ScalarType> = super::lower::expand_slots_with(
        walk_ty,
        &ctx.fieldless,
        &ctx.transparent,
        &ctx.payload_unions,
    );
    let init_vals: Vec<Value> = {
        let mut all = Vec::new();
        for e in init {
            all.extend(lower_slots(ctx, e)?);
        }
        all
    };
    if init_vals.len() != acc_slots.len() {
        return Err(format!(
            "core::to_ssa: List-Cata init slot count {} != acc_slots {}",
            init_vals.len(),
            acc_slots.len()
        ));
    }

    // Captures flow as parallel "step values" through the loop
    // block params.
    let mut cap_vals: Vec<Value> = Vec::new();
    let mut cap_tys: Vec<ScalarType> = Vec::new();
    for c in captures {
        let slots = lower_slots(ctx, c)?;
        let ty_expanded = super::lower::expand_slots_with(
            c.ty(),
            &ctx.fieldless,
            &ctx.transparent,
            &ctx.payload_unions,
        );
        if slots.len() == ty_expanded.len() {
            cap_vals.extend(slots);
            cap_tys.extend(ty_expanded);
        } else {
            for v in slots {
                cap_vals.push(v);
                cap_tys.push(ScalarType::RcPtr);
            }
        }
    }

    let elem_tys: Vec<ScalarType> = super::lower::expand_slots_with(
        elem_ty,
        &ctx.fieldless,
        &ctx.transparent,
        &ctx.payload_unions,
    );

    let header = ctx.builder.create_block();
    let i_param = ctx.builder.add_block_param(header, ScalarType::U64);
    let acc_params: Vec<Value> = acc_slots
        .iter()
        .map(|&ty| ctx.builder.add_block_param(header, ty))
        .collect();
    let len_param = ctx.builder.add_block_param(header, ScalarType::U64);
    let data_param = ctx.builder.add_block_param(header, ScalarType::RcPtr);
    let cap_params: Vec<Value> = cap_tys
        .iter()
        .map(|&ty| ctx.builder.add_block_param(header, ty))
        .collect();

    let body_block = ctx.builder.create_block();
    let body_i = ctx.builder.add_block_param(body_block, ScalarType::U64);
    let body_acc: Vec<Value> = acc_slots
        .iter()
        .map(|&ty| ctx.builder.add_block_param(body_block, ty))
        .collect();
    let body_len = ctx.builder.add_block_param(body_block, ScalarType::U64);
    let body_data = ctx.builder.add_block_param(body_block, ScalarType::RcPtr);
    let body_cap_vals: Vec<Value> = cap_tys
        .iter()
        .map(|&ty| ctx.builder.add_block_param(body_block, ty))
        .collect();

    let done = ctx.builder.create_block();
    let done_acc: Vec<Value> = acc_slots
        .iter()
        .map(|&ty| ctx.builder.add_block_param(done, ty))
        .collect();
    let _done_data = ctx.builder.add_block_param(done, ScalarType::RcPtr);
    for &ty in &cap_tys {
        ctx.builder.add_block_param(done, ty);
    }

    // Entry → header(0, init..., len, data, caps...).
    let zero = ctx.builder.const_u64(0);
    let mut entry_args = Vec::with_capacity(1 + init_vals.len() + 2 + cap_vals.len());
    entry_args.push(zero);
    entry_args.extend(init_vals);
    entry_args.push(len_val);
    entry_args.push(data_ptr);
    entry_args.extend(cap_vals);
    ctx.builder.jump(header, entry_args);

    // Header: i == len ? done(acc, data, caps) : body(i, acc, len, data, caps).
    ctx.builder.switch_to(header);
    let cmp = ctx.builder.binop(BinaryOp::Eq, i_param, len_param, ScalarType::U8);
    let mut done_args: Vec<Value> = acc_params.clone();
    done_args.push(data_param);
    done_args.extend(cap_params.iter().copied());
    let mut body_args: Vec<Value> = Vec::new();
    body_args.push(i_param);
    body_args.extend(acc_params.iter().copied());
    body_args.push(len_param);
    body_args.push(data_param);
    body_args.extend(cap_params.iter().copied());
    ctx.builder.branch(cmp, done, done_args, body_block, body_args);

    // Body: load elem slot(s) from data buffer; call step.
    ctx.builder.switch_to(body_block);
    let elem_vals: Vec<Value> = if elem_tys.len() == 1 {
        vec![ctx.builder.load_dyn(body_data, body_i, elem_tys[0])]
    } else {
        let stride = ctx.builder.const_u64(elem_tys.len() as u64);
        let base = ctx.builder.binop(BinaryOp::Mul, body_i, stride, ScalarType::U64);
        elem_tys
            .iter()
            .enumerate()
            .map(|(k, &t)| {
                if k == 0 {
                    ctx.builder.load_dyn(body_data, base, t)
                } else {
                    let k_const = ctx.builder.const_u64(k as u64);
                    let off = ctx.builder.binop(BinaryOp::Add, base, k_const, ScalarType::U64);
                    ctx.builder.load_dyn(body_data, off, t)
                }
            })
            .collect()
    };

    let mut call_args: Vec<Value> = Vec::new();
    call_args.extend(body_cap_vals.iter().copied());
    call_args.extend(body_acc.iter().copied());
    call_args.extend(elem_vals);

    let one = ctx.builder.const_u64(1);
    let next_i = ctx.builder.binop(BinaryOp::Add, body_i, one, ScalarType::U64);

    if !early_exit {
        // Plain walk: step returns acc directly. Jump back to header.
        let new_acc: Vec<Value> = if acc_slots.len() == 1 {
            vec![ctx.builder.call(fold_fn, call_args, acc_slots[0])]
        } else {
            ctx.builder.call_multi(fold_fn, call_args, &acc_slots)
        };
        let mut jump_args: Vec<Value> = Vec::with_capacity(1 + new_acc.len() + 2 + body_cap_vals.len());
        jump_args.push(next_i);
        jump_args.extend(new_acc);
        jump_args.push(body_len);
        jump_args.push(body_data);
        jump_args.extend(body_cap_vals.iter().copied());
        ctx.builder.jump(header, jump_args);
    } else {
        // Walk-until: step returns Step(b) = (tag, payload). Dispatch
        // on the tag — Continue → header(i+1, ...), Break → done(...).
        let step_ret_tys = vec![ScalarType::U64, ScalarType::RcPtr];
        let step_result = ctx.builder.call_multi(fold_fn, call_args, &step_ret_tys);
        let tag_v = step_result[0];
        let payload_ptr = step_result[1];

        let new_acc: Vec<Value> = if acc_slots.len() == 1 {
            vec![ctx.builder.load(payload_ptr, 0, acc_slots[0])]
        } else {
            let wrapper = ctx.builder.load(payload_ptr, 0, ScalarType::RcPtr);
            acc_slots
                .iter()
                .enumerate()
                .map(|(i, &ty)| ctx.builder.load(wrapper, i * 8, ty))
                .collect()
        };

        let break_tag_idx = ctx
            .decls
            .constructors
            .get("Break")
            .map(|m| m.tag_index)
            .ok_or_else(|| "core::to_ssa: walk_until needs `Break` constructor in decl_info".to_string())?;
        let break_val = ctx.builder.const_u64(break_tag_idx);
        let is_break = ctx.builder.binop(BinaryOp::Eq, tag_v, break_val, ScalarType::U8);

        let mut break_done_args: Vec<Value> = new_acc.clone();
        break_done_args.push(body_data);
        break_done_args.extend(body_cap_vals.iter().copied());
        let mut continue_header_args: Vec<Value> = Vec::with_capacity(1 + new_acc.len() + 2 + body_cap_vals.len());
        continue_header_args.push(next_i);
        continue_header_args.extend(new_acc.iter().copied());
        continue_header_args.push(body_len);
        continue_header_args.push(body_data);
        continue_header_args.extend(body_cap_vals.iter().copied());
        ctx.builder.branch(is_break, done, break_done_args, header, continue_header_args);
    }

    ctx.builder.switch_to(done);
    Ok(done_acc)
}

/// Still unsupported in this slice:
/// - Non-fieldless unions (need to decompose into `(tag, payload)` and
///   bind field values from the payload).
/// - `IntLit` / `StrLit` patterns (chain of equality checks).
/// - Mixed pattern kinds in one Match.
fn lower_match(
    ctx: &mut Ctx<'_>,
    scrutinee_slots_exprs: &[Expr],
    scrutinee_ty: &Type,
    arms: &[MatchArm],
    ty: &Type,
) -> Result<Vec<Value>, String> {
    // Match.scrutinee_slots is a parallel slot-expr list (length 1 for
    // single-slot scrutinees, length > 1 for multi-slot decompositions).
    // The source-level type comes from `scrutinee_ty` — per-slot exprs
    // carry placeholder scalar types that lose the union shape.
    let scrutinee_ty = scrutinee_ty.clone();
    let mut scrutinee_slots: Vec<Value> = Vec::new();
    for e in scrutinee_slots_exprs {
        scrutinee_slots.extend(lower_slots(ctx, e)?);
    }


    // Determine union shape:
    // - 1 slot + multi-variant payload-carrying union (in App form
    //   that didn't unfold via transparent): unbox the heap shell
    //   via Load(shell, 0, U64) for tag + Load(shell, 8, RcPtr) for
    //   payload. Matches existing-lower's shell convention.
    // - 1 slot fieldless union: the slot IS the discriminant.
    // - 2 slots (tag, payload): use directly.
    let unwrapped_ty = super::lower::resolve_transparent(&scrutinee_ty, &ctx.transparent);
    // Two routes to "this scrutinee is a multi-variant payload union":
    // (1) Structural — the unwrapped type IS a TagUnion with multiple
    //     variants, at least one payload-carrying.
    // (2) Declared (Result, Maybe, user types) — the unwrapped type
    //     is still App(name, _) because `:=` tag unions aren't in
    //     `transparent`. Detect by checking if any arm's constructor
    //     name is in decl_info.constructors with max_fields > 0
    //     AND the constructor has at least one sibling (multi-variant).
    let is_structural_payload = matches!(
        &unwrapped_ty,
        Type::TagUnion { tags, .. } if tags.len() > 1 && tags.iter().any(|(_, fs)| !fs.is_empty())
    );
    // Look up the scrutinee's union name in payload_unions, which is
    // already filtered to (multi-variant AND payload-carrying). This
    // is more accurate than checking arm-by-arm — avoids false-
    // positives for single-variant unions that happen to have payload
    // constructors (where the scrutinee fans out directly, no shell).
    let scrutinee_union_name = match &unwrapped_ty {
        Type::App(name, _) => Some(name.as_str()),
        Type::Con(name) => Some(name.as_str()),
        _ => None,
    };
    let is_declared_payload = scrutinee_union_name
        .map(|n| ctx.payload_unions.contains(n))
        .unwrap_or(false);
    let is_payload_carrying_union = is_structural_payload || is_declared_payload;
    // Phase-E scrutinees: a single-variant union (typically a
    // closure with N captures) whose scrutinee_slots are *already*
    // the variant's fields fanned out — no tag, no payload heap.
    // When we see this, the multi-arm dispatch below would otherwise
    // misinterpret scrutinee_slots[1..] as a payload pointer and
    // emit RcPtr block params for it. Detect via the unwrapped
    // TagUnion's variant count: exactly one non-fieldless tag.
    let is_phase_e_scrutinee = matches!(
        &unwrapped_ty,
        Type::TagUnion { tags, .. } if tags.len() == 1 && tags.iter().any(|(_, fs)| !fs.is_empty())
    );
    // Phase-E single-variant scrutinee with N slots (N >= 1): the
    // scrutinee IS the variant's payload fanned out — no tag to
    // dispatch on. There's at most one matching arm (the
    // constructor pattern); bind its binders to the slots directly
    // and lower the body.
    if is_phase_e_scrutinee && !scrutinee_slots.is_empty() {
        // Find the single Constructor arm (or fall through to a
        // wildcard / binding arm). Pattern-matching a single-
        // variant union has exactly one tag, so any tag-equivalent
        // arm matches every value.
        let any_guarded = arms.iter().any(|a| !a.guards.is_empty());
        if any_guarded {
            return lower_phase_e_guarded(ctx, &scrutinee_slots, arms, ty);
        }
        {
        for arm in arms {
            let binders_opt: Option<&Vec<Vec<SymbolId>>> = match &arm.pattern {
                Pattern::Constructor { binders, .. } => Some(binders),
                Pattern::Wildcard | Pattern::Binding(_) => None,
                _ => continue,
            };
            // Bind each slot to the corresponding binder sym. For a
            // Constructor pattern, `binders` is per-field. Field
            // types may expand to N slots (e.g. List(I64) = 3); when
            // the field has only one source-level binder, that binder
            // absorbs all of the field's slots as a multi-slot local.
            // Otherwise binder_slots's syms each take one slot.
            let mut bound: Vec<(SymbolId, Option<Vec<Value>>)> = Vec::new();
            if let Some(binders) = binders_opt {
                let field_tys: Vec<Type> = match &unwrapped_ty {
                    Type::TagUnion { tags, .. } if tags.len() == 1 => {
                        tags[0].1.clone()
                    }
                    _ => Vec::new(),
                };
                let mut slot_idx = 0;
                for (field_i, binder_slots) in binders.iter().enumerate() {
                    let field_slot_count = field_tys
                        .get(field_i)
                        .map(|ft| {
                            super::lower::expand_slots_with(
                                ft,
                                &ctx.fieldless,
                                &ctx.transparent,
                                &ctx.payload_unions,
                            )
                            .len()
                            .max(1)
                        })
                        .unwrap_or(binder_slots.len().max(1));
                    if binder_slots.len() == 1 && field_slot_count > 1 {
                        let sym = binder_slots[0];
                        let end = (slot_idx + field_slot_count).min(scrutinee_slots.len());
                        let vals: Vec<Value> = scrutinee_slots[slot_idx..end].to_vec();
                        if sym.0 != u32::MAX {
                            bound.push((sym, ctx.locals.insert(sym, vals)));
                        }
                        slot_idx = end;
                    } else {
                        for &sym in binder_slots {
                            if slot_idx >= scrutinee_slots.len() {
                                break;
                            }
                            let v = scrutinee_slots[slot_idx];
                            if sym.0 != u32::MAX {
                                bound.push((sym, ctx.locals.insert(sym, vec![v])));
                            }
                            slot_idx += 1;
                        }
                    }
                }
            } else if let Pattern::Binding(sym) = &arm.pattern {
                // Bind the whole multi-slot scrutinee to the source
                // name (multi-slot locals carry all slots).
                bound.push((*sym, ctx.locals.insert(*sym, scrutinee_slots.clone())));
            }
            let result = lower_arm_body_slots(ctx, &arm.body);
            // Restore locals.
            for (sym, prev) in bound {
                match prev {
                    Some(p) => { ctx.locals.insert(sym, p); }
                    None => { ctx.locals.remove(&sym); }
                }
            }
            return result;
        }
        // No matching arm — fall through to error.
        }
    }
    // Whether any arm needs a real scrutinee-derived tag. Pure
    // Binding/Wildcard dispatches (literal-pattern desugar) don't —
    // a const-0 synth tag drives the SwitchInt's single arm. This
    // also lets multi-slot scrutinees (Str, List) match through
    // Binding patterns without a meaningful single-Value tag.
    let need_real_tag = arms
        .iter()
        .any(|a| matches!(a.pattern, Pattern::Constructor { .. }));
    let (tag_val, payload_val) = if need_real_tag {
        match scrutinee_slots.as_slice() {
            [v] => {
                if is_payload_carrying_union {
                    let shell = *v;
                    let tag = ctx.builder.load(shell, 0, ScalarType::U64);
                    let payload = ctx.builder.load(shell, 8, ScalarType::RcPtr);
                    (tag, Some(payload))
                } else {
                    (*v, None)
                }
            }
            [t, p] => (*t, Some(*p)),
            _ => return Err(format!(
                "core::to_ssa: Match scrutinee produced {} slots (expected 1 or 2)",
                scrutinee_slots.len()
            )),
        }
    } else {
        (ctx.builder.const_u64(0), None)
    };

    // Single-arm wildcard / binding — no dispatch.
    if arms.len() == 1 {
        let arm = &arms[0];
        match &arm.pattern {
            Pattern::Wildcard => return lower_arm_body_slots(ctx, &arm.body),
            Pattern::Binding(sym) => {
                // Bind to the full scrutinee slot list (multi-slot
                // for List/Str scrutinees post lit-pattern desugar).
                // Skip when the arm has guards — they need the
                // per-arm-block fall-through machinery, not the
                // single-arm fast path.
                if arm.guards.is_empty() {
                    let prev = ctx.locals.insert(*sym, scrutinee_slots.clone());
                    let result = lower_arm_body_slots(ctx, &arm.body);
                    match prev {
                        Some(p) => { ctx.locals.insert(*sym, p); }
                        None => { ctx.locals.remove(sym); }
                    }
                    return result;
                }
            }
            // Phase E shape: a single-variant union whose scrutinee
            // expanded to its captures directly (no tag, no payload
            // heap). The single Constructor arm binds each binder to
            // a scrutinee slot — no payload load, no dispatch. This
            // is how `apply__narrow0(f, ...)` deconstructs `f`'s
            // captures into registers. Each binder may itself be
            // multi-slot (a closure that captures a multi-slot
            // record), so iterate per-slot. Only applies when the
            // binder slot total matches the scrutinee's fan-out;
            // otherwise we fall through to the multi-arm dispatch
            // which handles fieldless single-arm matches via a
            // SwitchInt with one target.
            Pattern::Constructor { binders, .. }
                if (payload_val.is_none() || is_phase_e_scrutinee)
                    && !binders.is_empty()
                    && binders.iter().map(|b| b.len()).sum::<usize>() == scrutinee_slots.len() =>
            {
                let mut bound: Vec<(SymbolId, Option<Vec<Value>>)> = Vec::new();
                let mut idx = 0;
                for binder_slots in binders {
                    for &sym in binder_slots {
                        if sym.0 == u32::MAX {
                            idx += 1;
                            continue;
                        }
                        bound.push((sym, ctx.locals.insert(sym, vec![scrutinee_slots[idx]])));
                        idx += 1;
                    }
                }
                let result = lower_arm_body_slots(ctx, &arm.body);
                for (sym, prev) in bound.into_iter().rev() {
                    match prev {
                        Some(p) => { ctx.locals.insert(sym, p); }
                        None => { ctx.locals.remove(&sym); }
                    }
                }
                return result;
            }
            _ => {}
        }
    }

    let result_slot_tys = super::lower::expand_slots_with(
        ty,
        &ctx.fieldless,
        &ctx.transparent,
        &ctx.payload_unions,
    );

    let mut constructor_arms: Vec<(u64, &MatchArm, Vec<ScalarType>)> = Vec::new();
    let mut default_arm: Option<&MatchArm> = None;
    for arm in arms {
        match &arm.pattern {
            Pattern::Constructor { tag, binders } => {
                let (tag_idx, _max_fields, field_tys) =
                    if let Some(meta) = ctx.decls.constructors.get(tag) {
                        (meta.tag_index, meta.max_fields, meta.field_types.clone())
                    } else {
                        structural_con_layout(&scrutinee_ty, tag, &ctx.fieldless)
                    };
                if binders.len() != field_tys.len() {
                    return Err(format!(
                        "core::to_ssa: Match arm for `{tag}` has {} binders but constructor declares {} fields",
                        binders.len(),
                        field_tys.len()
                    ));
                }
                if !binders.is_empty() && payload_val.is_none() {
                    return Err(format!(
                        "core::to_ssa: Match arm for `{tag}` has binders but scrutinee is fieldless"
                    ));
                }
                constructor_arms.push((tag_idx, arm, field_tys));
            }
            // Binding arms come from literal-pattern desugar: each
            // such arm is `Binding(fresh_sym)` + a synthesized
            // `Eq(fresh_sym, lit)` guard. The binding itself always
            // succeeds; the guard chain handles fall-through. We
            // assign every Binding arm the same synthetic tag (0)
            // so they all share `next_same_tag` linkage — guard
            // failure on arm i flows to arm i+1, last falls through
            // to the default. The `SwitchInt` for this match emits
            // a single case (tag=0 → arm0_block) over a const-zero
            // tag value (computed below); semantically equivalent
            // to an unconditional jump to the chain head.
            Pattern::Binding(_) => {
                constructor_arms.push((0, arm, vec![]));
            }
            Pattern::Wildcard => {
                if default_arm.is_some() {
                    return Err("core::to_ssa: Match has multiple Wildcard arms".into());
                }
                default_arm = Some(arm);
            }
            other => {
                return Err(format!(
                    "core::to_ssa: Match pattern in multi-arm dispatch not yet supported: {other:?}"
                ));
            }
        }
    }

    let tag_block = ctx.builder.current_block.expect("expected current block");
    let merge = ctx.builder.create_block();
    // One merge param per result slot — Match returns its full slot
    // list, no shell-and-unbox. Each arm jumps to merge with N values
    // matching `result_slot_tys`.
    let merge_params: Vec<Value> = result_slot_tys
        .iter()
        .map(|&ty| ctx.builder.add_block_param(merge, ty))
        .collect();

    // Per-tag chain table: for each arm index, what's the next
    // arm with the *same* constructor tag? Guarded arms whose
    // guard fails fall through to this next arm's block (which
    // re-binds and tries its own guard); the last arm in a tag
    // chain falls through to the default block. Built once
    // upfront so the per-arm loop can look up its successor.
    let mut next_same_tag: Vec<Option<usize>> = vec![None; constructor_arms.len()];
    for i in 0..constructor_arms.len() {
        for j in (i + 1)..constructor_arms.len() {
            if constructor_arms[j].0 == constructor_arms[i].0 {
                next_same_tag[i] = Some(j);
                break;
            }
        }
    }

    // Pre-create default block (if any), so guarded arms can jump
    // to it on fall-through. Filled in after the arm loop.
    let default_block_id: Option<crate::ssa::BlockId> = default_arm.map(|_| ctx.builder.create_block());

    // For each arm: create body block. If the arm binds fields,
    // pass the payload through as a block-arg so the block can load
    // fields from it. Each binder is a single SSA slot from the
    // payload at its declared offset; bind locals before lowering
    // the arm body.
    let arm_block_ids: Vec<crate::ssa::BlockId> = (0..constructor_arms.len())
        .map(|_| ctx.builder.create_block())
        .collect();
    let mut arm_blocks: Vec<(u64, crate::ssa::BlockId, Vec<Value>)> = Vec::new();
    for (arm_i, (tag_idx, arm, field_tys)) in constructor_arms.iter().enumerate() {
        let b = arm_block_ids[arm_i];
        let payload_block_param = if !field_tys.is_empty() && payload_val.is_some() {
            Some(ctx.builder.add_block_param(b, ScalarType::RcPtr))
        } else {
            None
        };
        ctx.builder.switch_to(b);

        // Constructor arms with field binders: load each field's
        // slot list from the payload at consecutive 8-byte offsets,
        // binding every slot value to its slot sym in `ctx.locals`.
        // IntLit arms have no binders and no payload to load.
        //
        // Per-binder slot ScalarType comes from constructor_schemes
        // expanded with payload_unions. For synth lambda constructors
        // (no scheme recorded) we fall back to decl_info's per-binder
        // ScalarType — those constructors only carry scalar captures
        // by construction.
        // Multi-variant payload binding: payload holds one RcPtr per
        // source-level field. For multi-slot binder types
        // (Str/List/Tree/nested unions), load the RcPtr shell from
        // the payload then unwrap N values from the shell. Scalar
        // and single-slot binders bind one Value directly from the
        // payload slot.
        let mut bound: Vec<(SymbolId, Option<Vec<Value>>)> = Vec::new();
        // Binding arm (literal-pattern desugar): bind the fresh sym
        // to the full scrutinee slot list. The guard then references
        // it via `Var(fresh_sym)`.
        if let Pattern::Binding(sym) = &arm.pattern {
            bound.push((*sym, ctx.locals.insert(*sym, scrutinee_slots.clone())));
        }
        if let Pattern::Constructor { tag, binders } = &arm.pattern {
            if let Some(payload_param) = payload_block_param {
                // Resolve the per-field types by substituting the
                // constructor scheme's type vars against the
                // monomorphic scrutinee_ty — without this, polymorphic
                // constructors (`Ok : a -> Result(a, b)`) leave their
                // field types as bare `Var(a)` whose `expand_slots`
                // defaults to RcPtr, producing wrong-typed binder
                // loads at the SSA layer.
                let scheme_tys = ctx
                    .decls
                    .constructor_schemes
                    .get(tag)
                    .and_then(|s| match &s.ty {
                        Type::Arrow(ps, r, _) => {
                            let subst = collect_subst(r, &scrutinee_ty);
                            Some(ps.iter().map(|p| apply_subst(p, &subst)).collect::<Vec<_>>())
                        }
                        _ => None,
                    });
                let scalar_fallback: Vec<ScalarType> = ctx
                    .decls
                    .constructors
                    .get(tag)
                    .map(|m| m.field_types.clone())
                    .unwrap_or_else(|| vec![ScalarType::RcPtr; binders.len()]);
                for (i, binder_slots) in binders.iter().enumerate() {
                    let slot_tys: Vec<ScalarType> = if let Some(ref ps) = scheme_tys {
                        super::lower::expand_slots_with(
                            &ps[i],
                            &ctx.fieldless,
                            &ctx.transparent,
                            &ctx.payload_unions,
                        )
                    } else {
                        vec![scalar_fallback[i]]
                    };
                    let payload_offset = i * 8;
                    // Multi-slot field with single source binder:
                    // bind the binder to the wrapper RcPtr at the
                    // payload offset (the field's multi-slot data
                    // lives in a sub-heap object referenced there).
                    if binder_slots.len() == 1 && slot_tys.len() > 1 {
                        // Multi-slot field bound by a single source
                        // name. Load every slot from the wrapper
                        // heap object referenced at payload_offset
                        // and bind the source name to the full slot
                        // list (multi-slot locals).
                        let sym = binder_slots[0];
                        if sym.0 != u32::MAX {
                            let wrapper = ctx.builder.load(payload_param, payload_offset, ScalarType::RcPtr);
                            let slot_vals: Vec<Value> = slot_tys
                                .iter()
                                .enumerate()
                                .map(|(i, &t)| ctx.builder.load(wrapper, i * 8, t))
                                .collect();
                            bound.push((sym, ctx.locals.insert(sym, slot_vals)));
                        }
                        continue;
                    }
                    if binder_slots.len() != slot_tys.len() {
                        return Err(format!(
                            "core::to_ssa: Match arm binder for `{tag}` slot \
                             count mismatch — pattern has {} slot syms but type \
                             expands to {}",
                            binder_slots.len(),
                            slot_tys.len()
                        ));
                    }
                    if binder_slots.len() == 1 {
                        let sym = binder_slots[0];
                        if sym.0 == u32::MAX {
                            continue;
                        }
                        let v = ctx.builder.load(payload_param, payload_offset, slot_tys[0]);
                        bound.push((sym, ctx.locals.insert(sym, vec![v])));
                    } else {
                        let wrapper = ctx.builder.load(payload_param, payload_offset, ScalarType::RcPtr);
                        for (slot_i, (&sym, &slot_ty)) in binder_slots.iter().zip(&slot_tys).enumerate() {
                            if sym.0 == u32::MAX {
                                continue;
                            }
                            let v = ctx.builder.load(wrapper, slot_i * 8, slot_ty);
                            bound.push((sym, ctx.locals.insert(sym, vec![v])));
                        }
                    }
                }
            }
        }

        // Guards: each is a Bool (U8 discriminant) expression
        // evaluated in the arm's scope. If any is False, jump to
        // the next arm with the same tag (so it can try its own
        // bindings/guards) or to the default block. If no
        // fall-through target exists, bail to the fallback —
        // we'd need to synthesize an unreachable sink.
        if !arm.guards.is_empty() {
            let fallthrough_block = next_same_tag[arm_i]
                .and_then(|j| {
                    let next_target = arm_block_ids[j];
                    // The next-same-tag block expects a payload
                    // arg iff that arm has binders + payload_val.
                    let next_args = if !constructor_arms[j].2.is_empty() && payload_val.is_some() {
                        vec![payload_val.unwrap()]
                    } else {
                        vec![]
                    };
                    Some((next_target, next_args))
                })
                .or_else(|| default_block_id.map(|b| (b, vec![])));
            let Some((fail_block, fail_args)) = fallthrough_block else {
                return Err(format!(
                    "core::to_ssa: Match arm guards for `{:?}` have no fall-through target (no later same-tag arm, no default)",
                    arm.pattern
                ));
            };
            // Emit a body block to run guard-passed work; guards
            // chain via branch instructions in the current block.
            let body_block = ctx.builder.create_block();
            // Track bindings introduced by Is-guards so we can
            // restore the outer scope after the arm body lowers.
            let mut guard_bindings: Vec<(SymbolId, Option<Vec<Value>>)> = Vec::new();
            for guard in &arm.guards {
                // Special case: guard is an `Is { expr, pattern }`
                // (lowered to a 2-arm Match returning Bool with the
                // pattern's binders). flatten_patterns produces this
                // for nested patterns like `Boxed(Ok(x))`. We need
                // to BIND those binders in the surrounding scope —
                // not just check the bool — so the arm body can
                // reference `x`.
                if let Some((scrutinee_slots, scr_ty, pat)) = extract_is_guard(guard) {
                    let mut scrutinee_vals: Vec<Value> = Vec::new();
                    for slot in scrutinee_slots {
                        scrutinee_vals.extend(lower_slots(ctx, slot)?);
                    }
                    let next_check = ctx.builder.create_block();
                    emit_is_guard(
                        ctx,
                        &scrutinee_vals,
                        scr_ty,
                        pat,
                        next_check,
                        fail_block,
                        &fail_args,
                        &mut guard_bindings,
                    )?;
                    ctx.builder.switch_to(next_check);
                } else {
                    let g_val = lower(ctx, guard)?;
                    let next_check = ctx.builder.create_block();
                    ctx.builder.branch(g_val, next_check, vec![], fail_block, fail_args.clone());
                    ctx.builder.switch_to(next_check);
                }
            }
            // All guards passed: jump to body block (so the
            // unreachable bool-check trailing block above
            // terminates somewhere).
            ctx.builder.jump(body_block, vec![]);
            ctx.builder.switch_to(body_block);
            // Record guard bindings into the arm's `bound` list so
            // they restore alongside the regular pattern binders.
            bound.extend(guard_bindings);
        }

        // Lower the body's slot list. Each arm produces N values
        // matching `result_slot_tys.len()` (for merge arms) or the
        // enclosing function's return arity (for return arms).
        // Don't reconcile against `result_slot_tys` for return arms
        // — those short-circuit to the function boundary, where the
        // body's natural slot count is what matters.
        let arm_slots = lower_arm_body_slots(ctx, &arm.body)?;
        if arm.is_return {
            // Return arm: short-circuit the enclosing function
            // rather than merging into the Match's result. Used by
            // the `?` operator's Err arm and explicit `: pat return
            // body` syntax.
            if arm_slots.len() == 1 {
                ctx.builder.ret(arm_slots[0]);
            } else {
                ctx.builder.ret_multi(arm_slots.clone());
            }
        } else {
            let arm_body_ty = arm.body.first().map(|e| e.ty()).unwrap_or(&Type::Con("__none".to_string())).clone();
            let arm_slots = reconcile_arm_slots(ctx, arm_slots, &result_slot_tys, &arm_body_ty)?;
            if arm_slots.len() != merge_params.len() {
                return Err(format!(
                    "core::to_ssa: Match arm body produced {} slots but merge expects {}",
                    arm_slots.len(),
                    merge_params.len()
                ));
            }
            ctx.builder.jump(merge, arm_slots);
        }

        // Restore shadowed bindings.
        for (binder, prev) in bound.into_iter().rev() {
            match prev {
                Some(p) => { ctx.locals.insert(binder, p); }
                None => { ctx.locals.remove(&binder); }
            }
        }

        let switch_args = if payload_block_param.is_some() {
            vec![payload_val.unwrap()]
        } else {
            vec![]
        };
        arm_blocks.push((*tag_idx, b, switch_args));
    }
    let default_block = if let Some(arm) = default_arm {
        let b = default_block_id.expect("default_block_id pre-created when default_arm exists");
        ctx.builder.switch_to(b);
        let arm_slots = lower_arm_body_slots(ctx, &arm.body)?;
        let arm_body_ty = arm.body.first().map(|e| e.ty()).unwrap_or(&Type::Con("__none".to_string())).clone();
        let arm_slots = reconcile_arm_slots(ctx, arm_slots, &result_slot_tys, &arm_body_ty)?;
        if arm_slots.len() != merge_params.len() {
            return Err(format!(
                "core::to_ssa: Match default arm body produced {} slots but merge expects {}",
                arm_slots.len(),
                merge_params.len()
            ));
        }
        ctx.builder.jump(merge, arm_slots);
        Some(b)
    } else {
        None
    };

    ctx.builder.switch_to(tag_block);
    // All-Binding dispatch (literal-pattern desugar) uses synth tag=0
    // for every arm. The original `tag_val` is the scrutinee slot,
    // which for non-scalar scrutinees may not be a numeric Value the
    // SwitchInt can read. Replace it with a const-0 so the case-0
    // arm is always taken — the guard chain handles per-arm
    // dispatch from there.
    let all_binding = !constructor_arms.is_empty()
        && constructor_arms
            .iter()
            .all(|(_, a, _)| matches!(a.pattern, Pattern::Binding(_)));
    let dispatch_tag = if all_binding {
        ctx.builder.const_u64(0)
    } else {
        tag_val
    };
    ctx.builder.switch_int(
        dispatch_tag,
        arm_blocks,
        default_block.map(|b| (b, vec![])),
    );

    ctx.builder.switch_to(merge);
    Ok(merge_params)
}

/// Lower a builtin-target `App` whose result is single-slot
/// (every kind except `Range`). Dispatches to the matching SSA
/// op emission.
fn emit_builtin_single_slot(
    ctx: &mut Ctx<'_>,
    kind: crate::symbol::BuiltinKind,
    args: &[Expr],
    ty: &Type,
) -> Result<Value, String> {
    use crate::symbol::BuiltinKind;
    match kind {
        BuiltinKind::Binary(op) => emit_builtin_binop(ctx, op, args, ty),
        BuiltinKind::Cast => emit_builtin_cast(ctx, args, ty, false),
        BuiltinKind::Bitcast => emit_builtin_cast(ctx, args, ty, true),
        BuiltinKind::Range => Err(
            "core::to_ssa: __builtin.list.range result is multi-slot (use lower_slots)"
                .to_string(),
        ),
    }
}

/// Lower a binary builtin: `Add`, `Sub`, ..., `Eq`, `Neq`. For scalar
/// operands lowers to a single `Inst::BinOp`. For trio (`List` / `Str`)
/// operands `Eq` / `Neq` route through `buf_eq` (length check +
/// elementwise loop). Other ops on trios are an error.
fn emit_builtin_binop(
    ctx: &mut Ctx<'_>,
    op: crate::ssa::BinaryOp,
    args: &[Expr],
    ty: &Type,
) -> Result<Value, String> {
    use crate::ssa::BinaryOp;
    if args.len() != 2 {
        return Err(format!(
            "core::to_ssa: binary builtin expects 2 args, got {}",
            args.len()
        ));
    }
    let lhs = &args[0];
    let rhs = &args[1];
    if matches!(op, BinaryOp::Eq | BinaryOp::Neq) {
        let lhs_slots = lower_slots(ctx, lhs)?;
        let rhs_slots = lower_slots(ctx, rhs)?;
        if lhs_slots.len() == 3 && rhs_slots.len() == 3 {
            let lhs_ty_unwrapped =
                super::lower::resolve_transparent(lhs.ty(), &ctx.transparent);
            let elem_ty = match &lhs_ty_unwrapped {
                Type::App(n, ts) if n == "List" && ts.len() == 1 => ts[0].clone(),
                _ => return Err(format!(
                    "core::to_ssa: builtin Eq on 3-slot operands but lhs type \
                     isn't List(_): {lhs_ty_unwrapped:?}"
                )),
            };
            let elem_tys = super::lower::expand_slots_with(
                &elem_ty,
                &ctx.fieldless,
                &ctx.transparent,
                &ctx.payload_unions,
            );
            if elem_tys.len() != 1 {
                return Err(format!(
                    "core::to_ssa: builtin Eq on List({elem_ty:?}) — multi-slot \
                     elements not yet supported"
                ));
            }
            let result = buf_eq(ctx, &lhs_slots, &rhs_slots, elem_tys[0]);
            if matches!(op, BinaryOp::Neq) {
                let one = ctx.builder.const_u8(1);
                return Ok(ctx.builder.binop(BinaryOp::Xor, result, one, ScalarType::U8));
            }
            return Ok(result);
        }
        if lhs_slots.len() == 1 && rhs_slots.len() == 1 {
            let result_ty = resolve_scalar_type(ty, &ctx.fieldless);
            return Ok(ctx.builder.binop(op, lhs_slots[0], rhs_slots[0], result_ty));
        }
        return Err(format!(
            "core::to_ssa: builtin Eq operand slot mismatch — lhs={}, rhs={}",
            lhs_slots.len(),
            rhs_slots.len()
        ));
    }
    let l = lower(ctx, lhs)?;
    let r = lower(ctx, rhs)?;
    let result_ty = resolve_scalar_type(ty, &ctx.fieldless);
    Ok(ctx.builder.binop(op, l, r, result_ty))
}

/// Lower a cast / bitcast builtin: `dest_ty` is taken from the
/// `App`'s result type. Zero / sign-extend or truncate for `cast`;
/// bit-pattern preserving for `bitcast`.
fn emit_builtin_cast(
    ctx: &mut Ctx<'_>,
    args: &[Expr],
    ty: &Type,
    bitcast: bool,
) -> Result<Value, String> {
    if args.len() != 1 {
        return Err(format!(
            "core::to_ssa: cast builtin expects 1 arg, got {}",
            args.len()
        ));
    }
    let v = lower(ctx, &args[0])?;
    let dest_ty = resolve_scalar_type(ty, &ctx.fieldless);
    Ok(if bitcast {
        ctx.builder.bitcast(v, dest_ty)
    } else {
        ctx.builder.cast(v, dest_ty)
    })
}

/// Lower a `range(start, end)` builtin to the buffer-trio counter
/// loop. Result is `(len, cap, data)` — three SSA values.
fn emit_builtin_range(
    ctx: &mut Ctx<'_>,
    args: &[Expr],
    _ty: &Type,
) -> Result<Vec<Value>, String> {
    use crate::ssa::BinaryOp;
    if args.len() != 2 {
        return Err(format!(
            "core::to_ssa: range builtin expects 2 args, got {}",
            args.len()
        ));
    }
    let start_v = lower(ctx, &args[0])?;
    let end_v = lower(ctx, &args[1])?;

    let nonempty = ctx.builder.binop(BinaryOp::Gt, end_v, start_v, ScalarType::U8);
    let then_block = ctx.builder.create_block();
    let else_block = ctx.builder.create_block();
    let count_merge = ctx.builder.create_block();
    let count = ctx.builder.add_block_param(count_merge, ScalarType::U64);
    ctx.builder.branch(nonempty, then_block, vec![], else_block, vec![]);

    ctx.builder.switch_to(then_block);
    let diff = ctx.builder.binop(BinaryOp::Sub, end_v, start_v, ScalarType::U64);
    ctx.builder.jump(count_merge, vec![diff]);

    ctx.builder.switch_to(else_block);
    let zero = ctx.builder.const_u64(0);
    ctx.builder.jump(count_merge, vec![zero]);

    ctx.builder.switch_to(count_merge);
    let eight = ctx.builder.const_u64(8);
    let byte_len = ctx.builder.binop(BinaryOp::Mul, count, eight, ScalarType::U64);
    let data = ctx.builder.alloc_dyn(byte_len);

    let header = ctx.builder.create_block();
    let body = ctx.builder.create_block();
    let exit = ctx.builder.create_block();
    let header_i = ctx.builder.add_block_param(header, ScalarType::U64);
    let body_i = ctx.builder.add_block_param(body, ScalarType::U64);

    let zero2 = ctx.builder.const_u64(0);
    ctx.builder.jump(header, vec![zero2]);

    ctx.builder.switch_to(header);
    let cond = ctx.builder.binop(BinaryOp::Lt, header_i, count, ScalarType::U8);
    ctx.builder.branch(cond, body, vec![header_i], exit, vec![]);

    ctx.builder.switch_to(body);
    let val = ctx.builder.binop(BinaryOp::Add, start_v, body_i, ScalarType::U64);
    ctx.builder.store_dyn(data, body_i, val);
    let one = ctx.builder.const_u64(1);
    let next_i = ctx.builder.binop(BinaryOp::Add, body_i, one, ScalarType::U64);
    ctx.builder.jump(header, vec![next_i]);

    ctx.builder.switch_to(exit);
    Ok(vec![count, count, data])
}

/// Buffer-trio equality: `(l_len, _l_cap, l_data) == (r_len, _r_cap, r_data)`
/// is logical-content equality — same length and every element equal.
/// `cap` is an allocation detail and is intentionally ignored.
///
/// Emits a length check followed by an element-wise loop:
///
/// ```text
/// entry:    if l_len == r_len jump loop(0, false_block)
///           else              jump merge(false)
/// loop(i):  if i == l_len     jump merge(true)
///           else              jump body(i)
/// body(i):  l_e = load(l_data, i); r_e = load(r_data, i)
///           if l_e == r_e     jump loop(i + 1)
///           else              jump merge(false)
/// merge(r): r
/// ```
///
/// Returns a Bool Value (`U8`). Only supports single-slot element
/// types (every scalar — `U8` for `Str = List(U8)`, `I64` for
/// `List(I64)`, etc.). Multi-slot elements (lists of records) would
/// need per-slot recursion at the comparison site.
fn buf_eq(
    ctx: &mut Ctx<'_>,
    lhs_slots: &[Value],
    rhs_slots: &[Value],
    elem_scalar: ScalarType,
) -> Value {
    use crate::ssa::BinaryOp;

    let l_len = lhs_slots[0];
    let l_data = lhs_slots[2];
    let r_len = rhs_slots[0];
    let r_data = rhs_slots[2];

    let loop_block = ctx.builder.create_block();
    let i_param = ctx.builder.add_block_param(loop_block, ScalarType::U64);
    let body_block = ctx.builder.create_block();
    let merge = ctx.builder.create_block();
    let result_param = ctx.builder.add_block_param(merge, ScalarType::U8);

    // entry: length check.
    let len_eq = ctx.builder.binop(BinaryOp::Eq, l_len, r_len, ScalarType::U8);
    let zero = ctx.builder.const_u64(0);
    let false_v = ctx.builder.const_u8(0);
    ctx.builder.branch(len_eq, loop_block, vec![zero], merge, vec![false_v]);

    // loop(i): done check.
    ctx.builder.switch_to(loop_block);
    let done = ctx.builder.binop(BinaryOp::Eq, i_param, l_len, ScalarType::U8);
    let true_v = ctx.builder.const_u8(1);
    ctx.builder.branch(done, merge, vec![true_v], body_block, vec![]);

    // body: load both elements; compare.
    ctx.builder.switch_to(body_block);
    let l_e = ctx.builder.load_dyn(l_data, i_param, elem_scalar);
    let r_e = ctx.builder.load_dyn(r_data, i_param, elem_scalar);
    let elem_eq = ctx.builder.binop(BinaryOp::Eq, l_e, r_e, elem_scalar);
    let one = ctx.builder.const_u64(1);
    let next_i = ctx.builder.binop(BinaryOp::Add, i_param, one, ScalarType::U64);
    let false_v2 = ctx.builder.const_u8(0);
    ctx.builder.branch(elem_eq, loop_block, vec![next_i], merge, vec![false_v2]);

    ctx.builder.switch_to(merge);
    result_param
}

fn zero_value(ctx: &mut Ctx<'_>, ty: crate::ssa::ScalarType) -> Value {
    use crate::ssa::ScalarType;
    match ty {
        ScalarType::I8 => ctx.builder.const_i8(0),
        ScalarType::U8 => ctx.builder.const_u8(0),
        ScalarType::I16 => ctx.builder.const_i16(0),
        ScalarType::U16 => ctx.builder.const_u16(0),
        ScalarType::I32 => ctx.builder.const_i32(0),
        ScalarType::U32 => ctx.builder.const_u32(0),
        ScalarType::I64 => ctx.builder.const_i64(0),
        ScalarType::U64 => ctx.builder.const_u64(0),
        ScalarType::F64 => ctx.builder.const_f64(0.0),
        ScalarType::Ptr | ScalarType::RcPtr => ctx.builder.alloc(0),
    }
}

/// Lower a Phase-E (single-variant, fanned-out) Match where at
/// least one arm has guards. Without guards, the no-tag fast path
/// at the top of `lower_match` binds binders directly and lowers
/// the body. With guards, each arm needs a block so a failing
/// guard can fall through to the next arm — same Pair tag means
/// every arm matches every value, the guards disambiguate.
fn lower_phase_e_guarded(
    ctx: &mut Ctx<'_>,
    scrutinee_slots: &[Value],
    arms: &[MatchArm],
    ty: &Type,
) -> Result<Vec<Value>, String> {
    let result_slot_tys = super::lower::expand_slots_with(
        ty,
        &ctx.fieldless,
        &ctx.transparent,
        &ctx.payload_unions,
    );
    let merge = ctx.builder.create_block();
    let merge_params: Vec<Value> = result_slot_tys
        .iter()
        .map(|&t| ctx.builder.add_block_param(merge, t))
        .collect();
    let mut con_arms: Vec<&MatchArm> = Vec::new();
    let mut default_arm: Option<&MatchArm> = None;
    for arm in arms {
        match &arm.pattern {
            Pattern::Constructor { .. } | Pattern::Binding(_) => con_arms.push(arm),
            Pattern::Wildcard => default_arm = Some(arm),
            _ => return Err(format!(
                "core::to_ssa: Phase-E guarded Match unsupported arm pattern: {:?}",
                arm.pattern
            )),
        }
    }
    let arm_block_ids: Vec<crate::ssa::BlockId> = (0..con_arms.len())
        .map(|_| ctx.builder.create_block())
        .collect();
    let default_block_id = default_arm.map(|_| ctx.builder.create_block());
    let first_target = arm_block_ids.first().copied().or(default_block_id).ok_or_else(|| {
        "core::to_ssa: Phase-E guarded Match has no arms".to_string()
    })?;
    ctx.builder.jump(first_target, vec![]);

    for (arm_i, arm) in con_arms.iter().enumerate() {
        let b = arm_block_ids[arm_i];
        ctx.builder.switch_to(b);
        let mut bound: Vec<(SymbolId, Option<Vec<Value>>)> = Vec::new();
        match &arm.pattern {
            Pattern::Constructor { binders, .. } => {
                let mut slot_idx = 0;
                for binder_slots in binders {
                    for &sym in binder_slots {
                        if slot_idx >= scrutinee_slots.len() {
                            break;
                        }
                        let v = scrutinee_slots[slot_idx];
                        if sym.0 != u32::MAX {
                            bound.push((sym, ctx.locals.insert(sym, vec![v])));
                        }
                        slot_idx += 1;
                    }
                }
            }
            Pattern::Binding(sym) => {
                bound.push((*sym, ctx.locals.insert(*sym, scrutinee_slots.to_vec())));
            }
            _ => unreachable!(),
        }
        let fallthrough_explicit = arm_block_ids.get(arm_i + 1).copied().or(default_block_id);
        let mut guard_bindings: Vec<(SymbolId, Option<Vec<Value>>)> = Vec::new();
        if !arm.guards.is_empty() {
            // Last guarded arm with no default: exhaustive Match
            // semantics say the guard must succeed at runtime. Emit
            // a sink block that returns zero values matching the
            // function's return signature — never executed at
            // runtime, but gives the block a valid terminator.
            let fail_block = match fallthrough_explicit {
                Some(b) => b,
                None => {
                    let sink = ctx.builder.create_block();
                    let prev = ctx.builder.current_block;
                    ctx.builder.switch_to(sink);
                    let ret_tys: Vec<crate::ssa::ScalarType> = ctx
                        .builder
                        .func
                        .return_type
                        .clone()
                        .unwrap_or_else(|| vec![crate::ssa::ScalarType::I64]);
                    let zeros: Vec<Value> = ret_tys
                        .iter()
                        .map(|&t| zero_value(ctx, t))
                        .collect();
                    if zeros.len() == 1 {
                        ctx.builder.ret(zeros[0]);
                    } else {
                        ctx.builder.ret_multi(zeros);
                    }
                    if let Some(p) = prev {
                        ctx.builder.switch_to(p);
                    }
                    sink
                }
            };
            let fail_args: Vec<Value> = vec![];
            let body_block = ctx.builder.create_block();
            for guard in arm.guards.iter() {
                if let Some((scrutinee_slots_g, scr_ty, pat)) = extract_is_guard(guard) {
                    let mut svals: Vec<Value> = Vec::new();
                    for slot in scrutinee_slots_g {
                        svals.extend(lower_slots(ctx, slot)?);
                    }
                    let next_check = ctx.builder.create_block();
                    emit_is_guard(
                        ctx, &svals, scr_ty, pat, next_check,
                        fail_block, &fail_args, &mut guard_bindings,
                    )?;
                    ctx.builder.switch_to(next_check);
                } else {
                    let g_val = lower(ctx, guard)?;
                    let next_check = ctx.builder.create_block();
                    ctx.builder.branch(g_val, next_check, vec![], fail_block, fail_args.clone());
                    ctx.builder.switch_to(next_check);
                }
            }
            ctx.builder.jump(body_block, vec![]);
            ctx.builder.switch_to(body_block);
        }
        bound.extend(guard_bindings);

        let arm_slots = lower_arm_body_slots(ctx, &arm.body)?;
        if arm.is_return {
            if arm_slots.len() == 1 {
                ctx.builder.ret(arm_slots[0]);
            } else {
                ctx.builder.ret_multi(arm_slots.clone());
            }
        } else {
            let arm_body_ty = arm.body.first().map(|e| e.ty())
                .unwrap_or(&Type::Con("__none".to_string())).clone();
            let arm_slots = reconcile_arm_slots(ctx, arm_slots, &result_slot_tys, &arm_body_ty)?;
            if arm_slots.len() != merge_params.len() {
                return Err(format!(
                    "core::to_ssa: Phase-E arm body produced {} slots but merge expects {}",
                    arm_slots.len(),
                    merge_params.len()
                ));
            }
            ctx.builder.jump(merge, arm_slots);
        }
        for (binder, prev) in bound.into_iter().rev() {
            match prev {
                Some(p) => { ctx.locals.insert(binder, p); }
                None => { ctx.locals.remove(&binder); }
            }
        }
    }

    if let Some(arm) = default_arm {
        let b = default_block_id.expect("default_block_id pre-created");
        ctx.builder.switch_to(b);
        let arm_slots = lower_arm_body_slots(ctx, &arm.body)?;
        let arm_body_ty = arm.body.first().map(|e| e.ty())
            .unwrap_or(&Type::Con("__none".to_string())).clone();
        let arm_slots = reconcile_arm_slots(ctx, arm_slots, &result_slot_tys, &arm_body_ty)?;
        if arm_slots.len() != merge_params.len() {
            return Err(format!(
                "core::to_ssa: Phase-E Match default produced {} slots but merge expects {}",
                arm_slots.len(),
                merge_params.len()
            ));
        }
        ctx.builder.jump(merge, arm_slots);
    }

    ctx.builder.switch_to(merge);
    Ok(merge_params)
}

/// True when `ty` resolves (via transparent unfolding) to a
/// single-variant tag union — the Phase-E direct-fanout case where
/// a Con of this type produces only the variant's fields with no
/// Match a guard expression against the `Is`-with-binding-pattern
/// shape that `flatten_patterns` produces for nested patterns. The
/// `is` lowering at AST→Core time desugars to:
///
///   `Match { scrutinee, arms: [Constructor(tag, binders) → True,
///                              Wildcard → False] }`
///
/// Detecting that shape lets us bind the constructor's binders in
/// the surrounding scope when the guard succeeds, rather than
/// throwing the bindings away as the standard bool-evaluation would.
fn extract_is_guard<'g>(guard: &'g Expr) -> Option<(&'g [Expr], &'g Type, &'g Pattern)> {
    let Expr::Match { scrutinee_slots, scrutinee_ty, arms, .. } = guard else {
        return None;
    };
    if arms.len() != 2 {
        return None;
    }
    let true_arm = &arms[0];
    let false_arm = &arms[1];
    // True arm: Constructor(_, _) body == [Con("True", [], ...)]
    let con_pat = match &true_arm.pattern {
        Pattern::Constructor { .. } => &true_arm.pattern,
        _ => return None,
    };
    if !matches!(false_arm.pattern, Pattern::Wildcard) {
        return None;
    }
    // Confirm the bodies are True/False constants (the standard `is`
    // desugar) — otherwise we'd hijack a user-written Match.
    let is_bool_con = |body: &[Expr], target: &str| {
        body.len() == 1
            && matches!(
                &body[0],
                Expr::Con { tag, args, .. } if tag == target && args.is_empty()
            )
    };
    if !is_bool_con(&true_arm.body, "True") {
        return None;
    }
    if !is_bool_con(&false_arm.body, "False") {
        return None;
    }
    Some((scrutinee_slots.as_slice(), scrutinee_ty, con_pat))
}

/// Lower an Is-guard: dispatch on the scrutinee, bind the
/// constructor pattern's binders into ctx.locals on the success
/// branch, and continue to `next_check`. On mismatch, branch to
/// `fail_block` with `fail_args`. Records every binding in
/// `guard_bindings` so the caller can restore the outer scope after
/// the arm body lowers.
fn emit_is_guard(
    ctx: &mut Ctx<'_>,
    scrutinee_vals: &[Value],
    scrutinee_ty: &Type,
    pattern: &Pattern,
    next_check: crate::ssa::BlockId,
    fail_block: crate::ssa::BlockId,
    fail_args: &[Value],
    guard_bindings: &mut Vec<(SymbolId, Option<Vec<Value>>)>,
) -> Result<(), String> {
    use crate::ssa::{BinaryOp, ScalarType};
    let Pattern::Constructor { tag, binders } = pattern else {
        return Err("emit_is_guard: pattern must be Constructor".into());
    };
    // Resolve the tag's index.
    let tag_idx = ctx
        .decls
        .constructors
        .get(tag)
        .ok_or_else(|| format!("emit_is_guard: constructor `{tag}` not in decl_info"))?
        .tag_index;
    // Dispatch the scrutinee: for [tag, payload_ptr] D2 shape, the
    // tag is slot 0 and payload is slot 1. For single-variant Phase-E
    // scrutinees, scrutinee_vals IS the variant's fields fanned out
    // — no tag check needed (the pattern's constructor must match).
    let (tag_v, payload) = match scrutinee_vals {
        [t, p] => (*t, Some(*p)),
        [v] => (*v, None),
        _ => {
            // Phase-E: bind every binder directly from scrutinee_vals.
            let mut slot_idx = 0;
            for binder_slots in binders {
                for &sym in binder_slots {
                    if slot_idx >= scrutinee_vals.len() {
                        break;
                    }
                    let v = scrutinee_vals[slot_idx];
                    if sym.0 != u32::MAX {
                        guard_bindings.push((sym, ctx.locals.insert(sym, vec![v])));
                    }
                    slot_idx += 1;
                }
            }
            ctx.builder.jump(next_check, vec![]);
            return Ok(());
        }
    };
    // Compare tag against the expected constructor's index.
    let expected = ctx.builder.const_u64(tag_idx);
    let is_match = ctx.builder.binop(BinaryOp::Eq, tag_v, expected, ScalarType::U8);
    let success = ctx.builder.create_block();
    ctx.builder.branch(is_match, success, vec![], fail_block, fail_args.to_vec());
    ctx.builder.switch_to(success);
    // Bind binders by loading from the payload at i*8 offsets.
    if let Some(payload_ptr) = payload {
        let scheme_tys = ctx
            .decls
            .constructor_schemes
            .get(tag)
            .and_then(|s| match &s.ty {
                Type::Arrow(ps, r, _) => {
                    let subst = collect_subst(r, scrutinee_ty);
                    Some(ps.iter().map(|p| apply_subst(p, &subst)).collect::<Vec<_>>())
                }
                _ => None,
            });
        let scalar_fallback: Vec<ScalarType> = ctx
            .decls
            .constructors
            .get(tag)
            .map(|m| m.field_types.clone())
            .unwrap_or_else(|| vec![ScalarType::RcPtr; binders.len()]);
        for (i, binder_slots) in binders.iter().enumerate() {
            let slot_tys: Vec<ScalarType> = if let Some(ref ps) = scheme_tys {
                super::lower::expand_slots_with(
                    &ps[i],
                    &ctx.fieldless,
                    &ctx.transparent,
                    &ctx.payload_unions,
                )
            } else {
                vec![scalar_fallback[i]]
            };
            let offset = i * 8;
            if binder_slots.len() == 1 && slot_tys.len() > 1 {
                let sym = binder_slots[0];
                if sym.0 != u32::MAX {
                    let wrapper = ctx.builder.load(payload_ptr, offset, ScalarType::RcPtr);
                    let slot_vals: Vec<Value> = slot_tys
                        .iter()
                        .enumerate()
                        .map(|(j, &t)| ctx.builder.load(wrapper, j * 8, t))
                        .collect();
                    guard_bindings.push((sym, ctx.locals.insert(sym, slot_vals)));
                }
                continue;
            }
            if binder_slots.len() == 1 && slot_tys.len() == 1 {
                let sym = binder_slots[0];
                if sym.0 != u32::MAX {
                    let v = ctx.builder.load(payload_ptr, offset, slot_tys[0]);
                    guard_bindings.push((sym, ctx.locals.insert(sym, vec![v])));
                }
            } else if binder_slots.len() == slot_tys.len() {
                let wrapper = ctx.builder.load(payload_ptr, offset, ScalarType::RcPtr);
                for (k, (&sym, &t)) in binder_slots.iter().zip(&slot_tys).enumerate() {
                    if sym.0 == u32::MAX {
                        continue;
                    }
                    let v = ctx.builder.load(wrapper, k * 8, t);
                    guard_bindings.push((sym, ctx.locals.insert(sym, vec![v])));
                }
            }
        }
    }
    ctx.builder.jump(next_check, vec![]);
    Ok(())
}

/// tag and no payload heap object. Multi-variant and non-TagUnion
/// types return false; the caller's coincidence check (slot counts
/// match) alone isn't enough to distinguish them.
/// Lower a Match arm body — a slot-list of Core `Expr`s — into a
/// flat `Vec<Value>`. Each entry's `lower_slots` produces 1 or more
/// values; the concatenation is what flows to the merge block.
fn lower_arm_body_slots(
    ctx: &mut Ctx<'_>,
    body: &[Expr],
) -> Result<Vec<Value>, String> {
    let mut all = Vec::new();
    for e in body {
        all.extend(lower_slots(ctx, e)?);
    }
    Ok(all)
}

/// Reconcile a Match arm body's lowered slot count with the merge
/// block's expected slot count. Two cases worth handling at the
/// boundary:
///
/// - Body produced 1 value, merge expects N (because the body's
///   `lower_slots` returned the heap-shell single-Value form):
///   load N values from the shell at consecutive offsets.
/// - Body produced N values, merge expects 1 (a multi-slot value
///   flowing through a single-slot Match result — happens when the
///   result type's `expand_slots` collapses to one RcPtr):
///   materialize a heap shell holding the N values.
///
/// Identity case (N == N) passes through unchanged.
fn reconcile_arm_slots(
    ctx: &mut Ctx<'_>,
    arm_slots: Vec<Value>,
    result_slot_tys: &[crate::ssa::ScalarType],
    body_ty: &Type,
) -> Result<Vec<Value>, String> {
    use crate::ssa::ScalarType;
    if arm_slots.len() == result_slot_tys.len() {
        return Ok(arm_slots);
    }
    if arm_slots.len() == 1 && result_slot_tys.len() > 1 {
        // Body returned a single shell pointer; load N values from
        // its consecutive 8-byte offsets. The shell layout is
        // dictated by `expand_slots`'s ordering on `body_ty`.
        let _ = body_ty;
        let shell = arm_slots[0];
        let unboxed: Vec<Value> = result_slot_tys
            .iter()
            .enumerate()
            .map(|(i, &ty)| ctx.builder.load(shell, i * 8, ty))
            .collect();
        return Ok(unboxed);
    }
    if arm_slots.len() > 1 && result_slot_tys.len() == 1 {
        // Body returned N values but the merge takes a single
        // shell. Allocate a heap shell and store the N values into
        // it; pass the shell pointer through.
        let _ = body_ty;
        let shell = ctx.builder.alloc(arm_slots.len() * 8);
        for (i, v) in arm_slots.iter().enumerate() {
            ctx.builder.store(shell, i * 8, *v);
        }
        return Ok(vec![shell]);
    }
    Err(format!(
        "core::to_ssa: Match arm body slot count {} can't reconcile with merge's {} slots",
        arm_slots.len(),
        result_slot_tys.len()
    ))
}

fn is_single_variant_union(ty: &Type, transparent: &super::lower::TransparentTable) -> bool {
    let unwrapped = super::lower::resolve_transparent(ty, transparent);
    matches!(unwrapped, Type::TagUnion { tags, .. } if tags.len() == 1)
}

/// Re-group flat per-slot Con args into source-field slot lists,
/// driven by `field_slot_counts` computed at AST→Core time from the
/// source AST args (before per-slot flattening). When the sum of
/// counts doesn't match `all_slots.len()`, falls back to one slot per
/// arg — the caller treats this as no-wrapping needed.
/// Collect type-var substitutions by walking `scheme_ty` and
/// `mono_ty` in parallel. Each `Var` in `scheme_ty` pairs with the
/// concrete `Type` at the same position in `mono_ty`. Used by both
/// the Con's `group_args_by_field` and Match-arm binder loading
/// to instantiate polymorphic constructor schemes.
fn collect_subst(
    scheme_ty: &Type,
    mono_ty: &Type,
) -> Vec<(crate::types::engine::TypeVar, Type)> {
    let mut out: Vec<(crate::types::engine::TypeVar, Type)> = Vec::new();
    walk_for_subst(scheme_ty, mono_ty, &mut out);
    out
}

fn walk_for_subst(
    scheme: &Type,
    mono: &Type,
    out: &mut Vec<(crate::types::engine::TypeVar, Type)>,
) {
    match (scheme, mono) {
        (Type::Var(v), _) => out.push((*v, mono.clone())),
        (Type::App(_, a), Type::App(_, b)) | (Type::Tuple(a), Type::Tuple(b)) => {
            for (sa, mb) in a.iter().zip(b.iter()) {
                walk_for_subst(sa, mb, out);
            }
        }
        (Type::Arrow(ap, ar, _), Type::Arrow(bp, br, _)) => {
            for (sa, mb) in ap.iter().zip(bp.iter()) {
                walk_for_subst(sa, mb, out);
            }
            walk_for_subst(ar, br, out);
        }
        _ => {}
    }
}

fn apply_subst(
    ty: &Type,
    subst: &[(crate::types::engine::TypeVar, Type)],
) -> Type {
    let mut result = ty.clone();
    for (v, t) in subst {
        result = crate::passes::decl_info::substitute_type_var(&result, *v, t);
    }
    result
}

fn group_args_by_field(
    field_slot_counts: &[usize],
    all_slots: &[Value],
) -> Vec<Vec<Value>> {
    let total: usize = field_slot_counts.iter().sum();
    if total != all_slots.len() {
        return all_slots.iter().map(|v| vec![*v]).collect();
    }
    let mut out: Vec<Vec<Value>> = Vec::with_capacity(field_slot_counts.len());
    let mut idx = 0usize;
    for &n in field_slot_counts {
        out.push(all_slots[idx..idx + n].to_vec());
        idx += n;
    }
    out
}

/// Emit a constant of `disc` type holding `tag_idx`. Returns None if
/// the resolved discriminant type isn't an unsigned integer — caller
/// should propagate as Err to trigger fallback rather than emit a
/// wrong-typed const.
fn emit_tag_const(b: &mut Builder, tag_idx: u64, disc: ScalarType) -> Option<Value> {
    match disc {
        ScalarType::U8 => Some(b.const_u8(tag_idx as u8)),
        ScalarType::U16 => Some(b.const_u16(tag_idx as u16)),
        ScalarType::U32 => Some(b.const_u32(tag_idx as u32)),
        ScalarType::U64 => Some(b.const_u64(tag_idx)),
        _ => None,
    }
}

/// Emit an integer literal at the appropriate scalar width. Pure
/// type-directed dispatch over Builder's typed const_* methods.
fn emit_int_const(b: &mut Builder, n: i64, ty: ScalarType) -> Value {
    match ty {
        ScalarType::I8  => b.const_i8(n as i8),
        ScalarType::U8  => b.const_u8(n as u8),
        ScalarType::I16 => b.const_i16(n as i16),
        ScalarType::U16 => b.const_u16(n as u16),
        ScalarType::I32 => b.const_i32(n as i32),
        ScalarType::U32 => b.const_u32(n as u32),
        ScalarType::I64 => b.const_i64(n),
        ScalarType::U64 => b.const_u64(n as u64),
        // Floats / Ptr / RcPtr — invalid for an integer literal; the
        // type system should reject before this point. Treat as an
        // inference bug.
        other => panic!("core::to_ssa: integer literal can't have type {other:?}"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ssa::{BinaryOp as SsaBinaryOp, ScalarType};

    fn i64_ty() -> Type {
        Type::Con("I64".to_string())
    }

    /// Build the Core for `let x = 1 + 2 in x + 3`.
    fn build_test_core(builtins: &crate::symbol::BuiltinRegistry) -> (Expr, SymbolId) {
        let x = SymbolId(100);
        let one = Expr::Lit { value: Literal::Int(1), ty: i64_ty() };
        let two = Expr::Lit { value: Literal::Int(2), ty: i64_ty() };
        let one_plus_two = Expr::App {
            target: builtins.add,
            args: vec![one, two],
            ty: i64_ty(),
        };
        let x_ref = Expr::Var { sym: x, ty: i64_ty() };
        let three = Expr::Lit { value: Literal::Int(3), ty: i64_ty() };
        let x_plus_three = Expr::App {
            target: builtins.add,
            args: vec![x_ref, three],
            ty: i64_ty(),
        };
        let body = Expr::Let {
            binders: vec![x],
            value: Box::new(one_plus_two),
            body: Box::new(x_plus_three),
            ty: i64_ty(),
        };
        (body, x)
    }

    #[test]
    fn lowers_let_with_binops_to_ssa() {
        let mut symbols = SymbolTable::new();
        let builtins = crate::symbol::BuiltinRegistry::bootstrap(&mut symbols);
        let (core, _x) = build_test_core(&builtins);
        let mut builder = Builder::new();
        let _entry = builder.create_block();
        builder.switch_to(crate::ssa::BlockId(0));
        let decls = crate::passes::decl_info::DeclInfo::default();
        let mut ctx = Ctx {
            builder: &mut builder,
            symbols: &symbols,
            decls: &decls,
            locals: HashMap::new(),
            fieldless: HashMap::new(),
            transparent: HashMap::new(),
            payload_unions: std::collections::HashSet::new(),
            bind_cache: HashMap::new(),
            builtins,
        };
        let result = lower(&mut ctx, &core).expect("lowering should succeed");
        // Finalize so we can introspect the function.
        builder.ret(result);
        builder.finish_function("test", ScalarType::I64);
        let module = builder.build("test");
        let func = &module.functions["test"];

        // Expect: const 1, const 2, add, const 3, add, ret. Exactly
        // two BinOps in the entry block.
        let entry = &func.blocks[&crate::ssa::BlockId(0)];
        let binops = entry.insts.iter().filter(|i| matches!(i, crate::ssa::Inst::BinOp(..))).count();
        assert_eq!(binops, 2, "expected exactly 2 BinOps from two add expressions");
        let consts = entry.insts.iter().filter(|i| matches!(i, crate::ssa::Inst::Const(..))).count();
        assert_eq!(consts, 3, "expected 3 Const insts for 1, 2, 3");
    }

    #[test]
    fn end_to_end_let_with_binops_evaluates_correctly() {
        // Round-trip the Core `let x = 1 + 2 in x + 3` through SSA and
        // eval. Expected: 6.
        let mut symbols = SymbolTable::new();
        let builtins = crate::symbol::BuiltinRegistry::bootstrap(&mut symbols);
        let (core, _x) = build_test_core(&builtins);
        let mut builder = Builder::new();
        let _entry = builder.create_block();
        builder.switch_to(crate::ssa::BlockId(0));
        let decls = crate::passes::decl_info::DeclInfo::default();
        let mut ctx = Ctx {
            builder: &mut builder,
            symbols: &symbols,
            decls: &decls,
            locals: HashMap::new(),
            fieldless: HashMap::new(),
            transparent: HashMap::new(),
            payload_unions: std::collections::HashSet::new(),
            bind_cache: HashMap::new(),
            builtins,
        };
        let result = lower(&mut ctx, &core).expect("lowering should succeed");
        builder.ret(result);
        builder.finish_function("test", ScalarType::I64);
        let module = builder.build("test");

        let mut heap = crate::ssa::eval::new_heap();
        crate::ssa::eval::load_statics(&module, &mut heap);
        let result = crate::ssa::eval::eval(&module, &mut heap, &[]);
        match result {
            crate::ssa::eval::Scalar::I64(n) => assert_eq!(n, 6),
            other => panic!("expected I64(6), got {other:?}"),
        }
    }

    #[test]
    fn lowers_app_to_ssa_call() {
        // Build Core for `f(1, 2)` where `f` is a top-level function
        // named "myfunc" (registered in the symbol table).
        use crate::ast::Span;
        use crate::source::FileId;
        use crate::symbol::SymbolKind;
        let mut symbols = SymbolTable::new();
        let builtins = crate::symbol::BuiltinRegistry::bootstrap(&mut symbols);
        let f = symbols.fresh(
            "myfunc",
            Span { file: FileId(0), start: 0, end: 0 },
            SymbolKind::Func,
        );
        let core = Expr::App {
            target: f,
            args: vec![
                Expr::Lit { value: Literal::Int(1), ty: i64_ty() },
                Expr::Lit { value: Literal::Int(2), ty: i64_ty() },
            ],
            ty: i64_ty(),
        };
        let mut builder = Builder::new();
        let _entry = builder.create_block();
        builder.switch_to(crate::ssa::BlockId(0));
        let decls = crate::passes::decl_info::DeclInfo::default();
        let mut ctx = Ctx {
            builder: &mut builder,
            symbols: &symbols,
            decls: &decls,
            locals: HashMap::new(),
            fieldless: HashMap::new(),
            transparent: HashMap::new(),
            payload_unions: std::collections::HashSet::new(),
            bind_cache: HashMap::new(),
            builtins,
        };
        let result = lower(&mut ctx, &core).expect("lowering should succeed");
        builder.ret(result);
        builder.finish_function("test", ScalarType::I64);
        let module = builder.build("test");
        // Inspect the emitted Call instruction in the finished function.
        let func = &module.functions["test"];
        let entry = &func.blocks[&crate::ssa::BlockId(0)];
        let call = entry.insts.iter().find_map(|i| {
            if let crate::ssa::Inst::Call { target, args, .. } = i {
                Some((target.clone(), args.clone()))
            } else { None }
        }).expect("expected a Call inst");
        assert_eq!(call.0, "myfunc");
        assert_eq!(call.1.len(), 2, "two args");
    }

    #[test]
    fn lowers_match_with_binding_arm() {
        // Core: match (1 + 2) of x -> x * 10
        // Expected eval: 30.
        let mut symbols = SymbolTable::new();
        let builtins = crate::symbol::BuiltinRegistry::bootstrap(&mut symbols);
        let x = SymbolId(50);
        let one_plus_two = Expr::App {
            target: builtins.add,
            args: vec![
                Expr::Lit { value: Literal::Int(1), ty: i64_ty() },
                Expr::Lit { value: Literal::Int(2), ty: i64_ty() },
            ],
            ty: i64_ty(),
        };
        let body = Expr::App {
            target: builtins.mul,
            args: vec![
                Expr::Var { sym: x, ty: i64_ty() },
                Expr::Lit { value: Literal::Int(10), ty: i64_ty() },
            ],
            ty: i64_ty(),
        };
        let core = Expr::Match {
            scrutinee_slots: vec![one_plus_two],
            scrutinee_ty: i64_ty(),
            arms: vec![super::super::expr::MatchArm::plain(
                super::super::expr::Pattern::Binding(x),
                body,
            )],
            ty: i64_ty(),
        };
        let mut builder = Builder::new();
        let _entry = builder.create_block();
        builder.switch_to(crate::ssa::BlockId(0));
        let decls = crate::passes::decl_info::DeclInfo::default();
        let mut ctx = Ctx {
            builder: &mut builder,
            symbols: &symbols,
            decls: &decls,
            locals: HashMap::new(),
            fieldless: HashMap::new(),
            transparent: HashMap::new(),
            payload_unions: std::collections::HashSet::new(),
            bind_cache: HashMap::new(),
            builtins,
        };
        let result = lower(&mut ctx, &core).expect("lowering should succeed");
        builder.ret(result);
        builder.finish_function("test", ScalarType::I64);
        let module = builder.build("test");
        let mut heap = crate::ssa::eval::new_heap();
        crate::ssa::eval::load_statics(&module, &mut heap);
        let result = crate::ssa::eval::eval(&module, &mut heap, &[]);
        assert_eq!(result, crate::ssa::eval::Scalar::I64(30));
    }

    #[test]
    fn lowers_match_with_two_fieldless_constructor_arms() {
        // Core for: match (U8 = 1) of True -> 100; False -> 200
        // The scrutinee carries TagUnion type [True, False]; structural
        // layout sorts alphabetically (False=0, True=1) so the value 1
        // selects the True arm. Expected: 100.
        let bool_ty = Type::TagUnion {
            tags: vec![
                ("True".to_string(), vec![]),
                ("False".to_string(), vec![]),
            ],
            rest: None,
        };
        // The scrutinee Value type matches what fieldless unions
        // lower to — a U8 discriminant.
        let scrutinee = Expr::Lit {
            value: Literal::Int(1),  // True (after alphabetical sort: False=0, True=1)
            ty: bool_ty.clone(),
        };
        let arms = vec![
            MatchArm::plain(
                Pattern::Constructor { tag: "True".to_string(), binders: vec![] },
                Expr::Lit { value: Literal::Int(100), ty: i64_ty() },
            ),
            MatchArm::plain(
                Pattern::Constructor { tag: "False".to_string(), binders: vec![] },
                Expr::Lit { value: Literal::Int(200), ty: i64_ty() },
            ),
        ];
        let core = Expr::Match {
            scrutinee_slots: vec![scrutinee],
            scrutinee_ty: bool_ty.clone(),
            arms,
            ty: i64_ty(),
        };

        let mut symbols = SymbolTable::new();
        let builtins = crate::symbol::BuiltinRegistry::bootstrap(&mut symbols);
        let mut builder = Builder::new();
        let _entry = builder.create_block();
        builder.switch_to(crate::ssa::BlockId(0));
        // The scrutinee path through the Lit-Int lowering doesn't know
        // about U8 discriminant typing — emit a U8 const first and
        // bind it to a sentinel symbol, then have the Match reference
        // that symbol.
        let sentinel = SymbolId(9999);
        let one_u8 = builder.const_u8(1);

        let mut fieldless = HashMap::new();
        fieldless.insert("Bool".to_string(), ScalarType::U8);
        let mut locals = HashMap::new();
        locals.insert(sentinel, vec![one_u8]);
        let decls = crate::passes::decl_info::DeclInfo::default();
        let mut ctx = Ctx {
            builder: &mut builder,
            symbols: &symbols,
            decls: &decls,
            locals,
            fieldless,
            transparent: HashMap::new(),
            payload_unions: std::collections::HashSet::new(),
            bind_cache: HashMap::new(),
            builtins,
        };

        let core_with_var = Expr::Match {
            scrutinee_slots: vec![Expr::Var { sym: sentinel, ty: bool_ty.clone() }],
            scrutinee_ty: bool_ty,
            arms: match &core {
                Expr::Match { arms, .. } => arms.clone(),
                _ => unreachable!(),
            },
            ty: i64_ty(),
        };
        let result = lower(&mut ctx, &core_with_var).expect("lowering should succeed");
        // Re-borrow builder after ctx drops.
        drop(ctx);
        builder.ret(result);
        builder.finish_function("test", ScalarType::I64);
        let module = builder.build("test");
        crate::ssa::validate::check(&module, "match e2e");

        let mut heap = crate::ssa::eval::new_heap();
        crate::ssa::eval::load_statics(&module, &mut heap);
        let r = crate::ssa::eval::eval(&module, &mut heap, &[]);
        assert_eq!(r, crate::ssa::eval::Scalar::I64(100),
            "expected True arm (value 100) to fire; got {r:?}");
    }

    #[test]
    fn unbound_var_reports_symbol() {
        let core = Expr::Var { sym: SymbolId(42), ty: i64_ty() };
        let mut builder = Builder::new();
        let _entry = builder.create_block();
        builder.switch_to(crate::ssa::BlockId(0));
        let mut symbols = SymbolTable::new();
        let builtins = crate::symbol::BuiltinRegistry::bootstrap(&mut symbols);
        let decls = crate::passes::decl_info::DeclInfo::default();
        let mut ctx = Ctx {
            builder: &mut builder,
            symbols: &symbols,
            decls: &decls,
            locals: HashMap::new(),
            fieldless: HashMap::new(),
            transparent: HashMap::new(),
            payload_unions: std::collections::HashSet::new(),
            bind_cache: HashMap::new(),
            builtins,
        };
        let err = lower(&mut ctx, &core).unwrap_err();
        assert!(err.contains("#42"), "error should name the unbound symbol: {err}");
    }
}
