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

use crate::lower::constructor::structural_con_layout;
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
    pub locals: HashMap<SymbolId, Value>,
    pub fieldless: HashMap<String, ScalarType>,
    pub transparent: super::lower::TransparentTable,
    /// Used by `lower(Let)` to unbox a single-shell value into N slots
    /// when binders > value slot count. NOT used for App return-type
    /// decisions — those follow the existing-lower single-shell
    /// convention to keep call-result compatibility.
    pub payload_unions: std::collections::HashSet<String>,
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
            let ret_slots = super::lower::expand_slots_with(ty, &ctx.fieldless, &ctx.transparent, &ctx.payload_unions);
            if ret_slots.len() == 1 {
                return Ok(vec![lower(ctx, expr)?]);
            }
            // Multi-result call. Spread each arg's slots, emit call_multi.
            let mut arg_vals: Vec<Value> = Vec::new();
            for a in args {
                arg_vals.extend(lower_slots(ctx, a)?);
            }
            Ok(ctx.builder.call_multi(target, arg_vals, &ret_slots))
        }

        // Match's natural multi-slot return — the merge block has
        // one param per result slot, and each arm jumps with N values
        // directly. Callers that need only one slot pick out of the
        // returned Vec; callers that need all (multi-slot Result
        // unbox) get them straight. No shell, no per-slot loads.
        Expr::Match { scrutinee_slots, scrutinee_ty, arms, ty } => {
            lower_match(ctx, scrutinee_slots, scrutinee_ty, arms, ty)
        }

        // Cata lowers to the same SSA as the equivalent App — both
        // call the same `__fold_N` helper. Cata's value is purely at
        // the rewrite layer (rules.rs); to_ssa treats it as a labeled
        // App so the resulting SSA matches what existing-lower
        // produces from `fold_lift`'s output verbatim.
        Expr::Cata { fold_fn, target_slots, extra_args, ty } => {
            let ret_slots = super::lower::expand_slots_with(ty, &ctx.fieldless, &ctx.transparent, &ctx.payload_unions);
            let mut arg_vals: Vec<Value> = Vec::new();
            for s in target_slots {
                arg_vals.extend(lower_slots(ctx, s)?);
            }
            for a in extra_args {
                arg_vals.extend(lower_slots(ctx, a)?);
            }
            if ret_slots.len() == 1 {
                let ret_ty = resolve_scalar_type(ty, &ctx.fieldless);
                Ok(vec![ctx.builder.call(fold_fn, arg_vals, ret_ty)])
            } else {
                Ok(ctx.builder.call_multi(fold_fn, arg_vals, &ret_slots))
            }
        }

        // Str literals fan out to (len, cap, data) directly — the
        // canonical SROA shape, same as List(U8). Single-slot
        // callers re-materialize via `lower` below.
        Expr::Lit { value: Literal::Str(bytes), .. } => {
            let len = bytes.len();
            let data = ctx.builder.alloc(len * 8);
            for (i, &b) in bytes.iter().enumerate() {
                let v = ctx.builder.const_u8(b);
                ctx.builder.store(data, i * 8, v);
            }
            let len_val = ctx.builder.const_u64(len as u64);
            Ok(vec![len_val, len_val, data])
        }

        // List literals fan out to (len, cap, data) directly so
        // App args, function returns, Con payloads receive the
        // trio without an intermediate header alloc. The single-
        // slot `lower` path wraps to a header when the caller
        // needs one RcPtr (boundary cases only).
        Expr::ListLit { elements, elem_ty, .. } => {
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

        // List.walk: fold the list under a step function, threading
        // the accumulator. Singleton-closure direct-dispatch only
        // (Core lower only emits ListWalk when the closure's tag
        // resolves to a known apply target). Mirrors
        // existing-lower's `lower_list_walk` with the `until=false`
        // path.
        Expr::ListWalk { list_slots, init, target, captures, elem_ty, ty: walk_ty } => {
            use crate::ssa::{BinaryOp, ScalarType};

            let list_vals: Vec<Value> = {
                let mut all = Vec::new();
                for e in list_slots {
                    all.extend(lower_slots(ctx, e)?);
                }
                all
            };
            if list_vals.len() != 3 {
                return Err(format!(
                    "core::to_ssa: ListWalk expects 3-slot list trio, got {} slots",
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
                    "core::to_ssa: ListWalk init slot count {} != acc_slots {}",
                    init_vals.len(),
                    acc_slots.len()
                ));
            }

            // Captures flow as parallel "step values" through the
            // loop block params. Each capture expression is lowered
            // to its slots; we collect both values and types.
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
                    // Mismatch — fall back to a single RcPtr per
                    // capture (defensive; shouldn't happen for
                    // well-typed Core).
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

            // Build header / body / done blocks. Header threads
            // (i, acc..., len, data, caps...). Body adds element
            // load + step call. Done receives the final acc.
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
            // Threaded so the buffer's rc-release lands here.
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

            // Header: cmp i == len; done(acc, data, caps) :: body(i, acc, len, data, caps).
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

            // Body: load elem slot(s) from data buffer at body_i.
            // Element stride is sum(elem_slot_count) * 8 bytes;
            // for single-slot elements that's the simple `body_data[body_i]`
            // load_dyn. For multi-slot (Str/List/aggregate) we'd need
            // stride math — bail (return error) for those today.
            ctx.builder.switch_to(body_block);
            if elem_tys.len() != 1 {
                return Err(format!(
                    "core::to_ssa: ListWalk multi-slot elements ({} slots) not yet supported",
                    elem_tys.len()
                ));
            }
            let elem_v = ctx.builder.load_dyn(body_data, body_i, elem_tys[0]);

            // Step call: target(caps, acc, elem) → acc_slots.
            let mut call_args: Vec<Value> = Vec::new();
            call_args.extend(body_cap_vals.iter().copied());
            call_args.extend(body_acc.iter().copied());
            call_args.push(elem_v);
            let new_acc: Vec<Value> = if acc_slots.len() == 1 {
                vec![ctx.builder.call(target, call_args, acc_slots[0])]
            } else {
                ctx.builder.call_multi(target, call_args, &acc_slots)
            };

            // i+1 → header.
            let one = ctx.builder.const_u64(1);
            let next_i = ctx.builder.binop(BinaryOp::Add, body_i, one, ScalarType::U64);
            let mut jump_args: Vec<Value> = Vec::with_capacity(1 + new_acc.len() + 2 + body_cap_vals.len());
            jump_args.push(next_i);
            jump_args.extend(new_acc);
            jump_args.push(body_len);
            jump_args.push(body_data);
            jump_args.extend(body_cap_vals.iter().copied());
            ctx.builder.jump(header, jump_args);

            ctx.builder.switch_to(done);
            Ok(done_acc)
        }

        // List.set: cow_store_dyn val into the data buffer at
        // index `idx`. Multi-slot elements stride at
        // `val_slots.len() * 8` bytes; each slot is a separate
        // cow_store_dyn call (the first cow-preps the buffer; the
        // result feeds the next call so the entire element lands
        // in one cloned/unique buffer). Returns the new
        // (len, cap, new_data) trio.
        Expr::ListSet { list_slots, idx, val_slots, .. } => {
            use crate::ssa::{BinaryOp, ScalarType};
            let list_vals: Vec<Value> = {
                let mut all = Vec::new();
                for e in list_slots {
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
        Expr::ListAppend { list_slots, val_slots, .. } => {
            use crate::ssa::{BinaryOp, ScalarType};
            let list_vals: Vec<Value> = {
                let mut all = Vec::new();
                for e in list_slots {
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

        // List.range emits a counter-driven fill loop and returns
        // the resulting (len, cap, data) trio. Empty range
        // (`end <= start`) yields count=0 with a 0-byte data buffer.
        Expr::ListRange { start, end, .. } => {
            use crate::ssa::{BinaryOp, ScalarType};
            let start_v = lower(ctx, start)?;
            let end_v = lower(ctx, end)?;

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

        // All other variants are single-slot today; delegate.
        _ => Ok(vec![lower(ctx, expr)?]),
    }
}

/// Lower a Core expression into SSA, returning the `Value` holding
/// the result. Errors when the Core variant isn't yet supported by
/// this slice.
pub fn lower(ctx: &mut Ctx<'_>, expr: &Expr) -> Result<Value, String> {
    match expr {
        Expr::Var { sym, .. } => ctx
            .locals
            .get(sym)
            .copied()
            .ok_or_else(|| {
                let name = ctx
                    .symbols
                    .try_get(*sym)
                    .map(|info| info.display.as_str())
                    .unwrap_or("?");
                format!("core::to_ssa: unbound Var #{} ({name})", sym.0)
            }),

        Expr::Lit { value: Literal::Int(n), ty } => {
            // Type-directed const emission. Programs with U64, U8, I32,
            // etc. integer literals need the right const_* method or
            // SSA validation rejects the type mismatch.
            let scalar = resolve_scalar_type(ty, &ctx.fieldless);
            Ok(emit_int_const(ctx.builder, *n, scalar))
        }

        Expr::Lit { value: Literal::Float(f), .. } => Ok(ctx.builder.const_f64(*f)),

        Expr::Lit { value: Literal::Str(bytes), .. } => {
            // Same shape as existing-lower's lower_str_literal:
            // alloc bytes (U8 per slot at 8-byte stride) + alloc the
            // (len, cap, data) 24-byte header + return header ptr.
            // static_promote (opt pass) hoists this to a static when
            // the bytes are constant — we don't pre-promote here.
            let len = bytes.len();
            let data = ctx.builder.alloc(len * 8);
            for (i, &b) in bytes.iter().enumerate() {
                let v = ctx.builder.const_u8(b);
                ctx.builder.store(data, i * 8, v);
            }
            let header = ctx.builder.alloc(24);
            let len_val = ctx.builder.const_u64(len as u64);
            ctx.builder.store(header, 0, len_val);
            ctx.builder.store(header, 8, len_val);
            ctx.builder.store(header, 16, data);
            Ok(header)
        }

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
            if vals.len() != binders.len() {
                return Err(format!(
                    "core::to_ssa: Let value produced {} slots but binders.len()={}",
                    vals.len(),
                    binders.len()
                ));
            }
            let mut prev = Vec::with_capacity(binders.len());
            for (binder, val) in binders.iter().zip(vals) {
                prev.push((*binder, ctx.locals.insert(*binder, val)));
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

        Expr::BinOp { op, lhs, rhs, ty } => {
            // Core's BinOp uses ssa::BinaryOp directly — short-
            // circuit And/Or were desugared to Match at AST→Core
            // time and don't appear here.
            let l = lower(ctx, lhs)?;
            let r = lower(ctx, rhs)?;
            let result_ty = resolve_scalar_type(ty, &ctx.fieldless);
            Ok(ctx.builder.binop(*op, l, r, result_ty))
        }

        Expr::Cast { src, dest_ty, bitcast, .. } => {
            // Numeric conversion. `bitcast` preserves the bit
            // pattern (to_bits / from_bits); regular cast does
            // zero/sign-extend or truncate as the SSA op dictates.
            let v = lower(ctx, src)?;
            Ok(if *bitcast {
                ctx.builder.bitcast(v, *dest_ty)
            } else {
                ctx.builder.cast(v, *dest_ty)
            })
        }

        Expr::App { target, args, ty } => {
            // Use lower_slots for args so multi-slot args (records,
            // payload Cons, multi-result Calls) spread into multiple
            // SSA call args. Single-result return; multi-result goes
            // through lower_slots's own App handler.
            let mut arg_vals: Vec<Value> = Vec::new();
            for a in args {
                arg_vals.extend(lower_slots(ctx, a)?);
            }
            let ret_ty = resolve_scalar_type(ty, &ctx.fieldless);
            Ok(ctx.builder.call(target, arg_vals, ret_ty))
        }

        // Single-slot Cata path: identical SSA shape to App, since
        // Cata is just a labeled fold-shaped call at the IR level.
        Expr::Cata { fold_fn, target_slots, extra_args, ty } => {
            let mut arg_vals: Vec<Value> = Vec::new();
            for s in target_slots {
                arg_vals.extend(lower_slots(ctx, s)?);
            }
            for a in extra_args {
                arg_vals.extend(lower_slots(ctx, a)?);
            }
            let ret_ty = resolve_scalar_type(ty, &ctx.fieldless);
            Ok(ctx.builder.call(fold_fn, arg_vals, ret_ty))
        }

        Expr::ListLit { elements, elem_ty, .. } => {
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

        // Multi-slot primitives — single-slot caller asks for a
        // header pointer; materialize the trio into a 24-byte shell.
        Expr::ListRange { .. } => {
            let slots = lower_slots(ctx, expr)?;
            let shell = ctx.builder.alloc(slots.len() * 8);
            for (i, v) in slots.iter().enumerate() {
                ctx.builder.store(shell, i * 8, *v);
            }
            Ok(shell)
        }

        // ListSet single-slot caller: materialize the trio.
        Expr::ListSet { .. } => {
            let slots = lower_slots(ctx, expr)?;
            let shell = ctx.builder.alloc(slots.len() * 8);
            for (i, v) in slots.iter().enumerate() {
                ctx.builder.store(shell, i * 8, *v);
            }
            Ok(shell)
        }

        // ListAppend single-slot caller: materialize the trio
        // into a shell. Multi-slot callers go through `lower_slots`.
        Expr::ListAppend { .. } => {
            let slots = lower_slots(ctx, expr)?;
            let shell = ctx.builder.alloc(slots.len() * 8);
            for (i, v) in slots.iter().enumerate() {
                ctx.builder.store(shell, i * 8, *v);
            }
            Ok(shell)
        }

        // ListWalk's result is the acc type, which can be either
        // single-slot or multi-slot. Multi-slot callers go through
        // `lower_slots` directly; single-slot callers get the
        // acc value back.
        Expr::ListWalk { .. } => {
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
    if is_phase_e_scrutinee && scrutinee_slots.len() >= 3 {
        // Find the single Constructor arm (or fall through to a
        // wildcard / binding arm). Pattern-matching a single-
        // variant union has exactly one tag, so any tag-equivalent
        // arm matches every value.
        for arm in arms {
            let binders_opt: Option<&Vec<Vec<SymbolId>>> = match &arm.pattern {
                Pattern::Constructor { binders, .. } => Some(binders),
                Pattern::Wildcard | Pattern::Binding(_) => None,
                _ => continue,
            };
            // Bind each slot to the corresponding binder sym. For a
            // Constructor pattern, `binders` is per-field; for
            // Wildcard / Binding, just bind the whole thing.
            let mut bound: Vec<(SymbolId, Option<Value>)> = Vec::new();
            if let Some(binders) = binders_opt {
                let mut slot_idx = 0;
                for binder_slots in binders {
                    for &sym in binder_slots {
                        if slot_idx >= scrutinee_slots.len() {
                            break;
                        }
                        let v = scrutinee_slots[slot_idx];
                        if sym.0 != u32::MAX {
                            bound.push((sym, ctx.locals.insert(sym, v)));
                        }
                        slot_idx += 1;
                    }
                }
            } else if let Pattern::Binding(sym) = &arm.pattern {
                bound.push((*sym, ctx.locals.insert(*sym, scrutinee_slots[0])));
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
    let (tag_val, payload_val) = match scrutinee_slots.as_slice() {
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
    };

    // Single-arm wildcard / binding — no dispatch.
    if arms.len() == 1 {
        let arm = &arms[0];
        match &arm.pattern {
            Pattern::Wildcard => return lower_arm_body_slots(ctx, &arm.body),
            Pattern::Binding(sym) => {
                // For multi-slot scrutinee, binding binds to the
                // first slot (the discriminant). This is sufficient
                // for simple uses; multi-slot Binding requires the
                // multi-binder Let machinery.
                let prev = ctx.locals.insert(*sym, tag_val);
                let result = lower_arm_body_slots(ctx, &arm.body);
                match prev {
                    Some(p) => { ctx.locals.insert(*sym, p); }
                    None => { ctx.locals.remove(sym); }
                }
                return result;
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
                let mut bound: Vec<(SymbolId, Option<Value>)> = Vec::new();
                let mut idx = 0;
                for binder_slots in binders {
                    for &sym in binder_slots {
                        if sym.0 == u32::MAX {
                            idx += 1;
                            continue;
                        }
                        bound.push((sym, ctx.locals.insert(sym, scrutinee_slots[idx])));
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
            // IntLit patterns dispatch on the literal value as the
            // SwitchInt arm tag. Works because the scrutinee is itself
            // the integer being matched. No field binders.
            Pattern::IntLit(n) => {
                if payload_val.is_some() {
                    return Err(format!(
                        "core::to_ssa: IntLit pattern can't match a multi-slot scrutinee"
                    ));
                }
                constructor_arms.push((*n as u64, arm, vec![]));
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
        let mut bound: Vec<(SymbolId, Option<Value>)> = Vec::new();
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
                        let sym = binder_slots[0];
                        if sym.0 != u32::MAX {
                            let v = ctx.builder.load(payload_param, payload_offset, ScalarType::RcPtr);
                            bound.push((sym, ctx.locals.insert(sym, v)));
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
                        bound.push((sym, ctx.locals.insert(sym, v)));
                    } else {
                        let wrapper = ctx.builder.load(payload_param, payload_offset, ScalarType::RcPtr);
                        for (slot_i, (&sym, &slot_ty)) in binder_slots.iter().zip(&slot_tys).enumerate() {
                            if sym.0 == u32::MAX {
                                continue;
                            }
                            let v = ctx.builder.load(wrapper, slot_i * 8, slot_ty);
                            bound.push((sym, ctx.locals.insert(sym, v)));
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
            for guard in &arm.guards {
                let g_val = lower(ctx, guard)?;
                let next_check = ctx.builder.create_block();
                ctx.builder.branch(g_val, next_check, vec![], fail_block, fail_args.clone());
                ctx.builder.switch_to(next_check);
            }
            // All guards passed: jump to body block (so the
            // unreachable bool-check trailing block above
            // terminates somewhere).
            ctx.builder.jump(body_block, vec![]);
            ctx.builder.switch_to(body_block);
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
    ctx.builder.switch_int(
        tag_val,
        arm_blocks,
        default_block.map(|b| (b, vec![])),
    );

    ctx.builder.switch_to(merge);
    Ok(merge_params)
}

/// True when `ty` resolves (via transparent unfolding) to a
/// single-variant tag union — the Phase-E direct-fanout case where
/// a Con of this type produces only the variant's fields with no
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
    fn build_test_core() -> (Expr, SymbolId) {
        let x = SymbolId(100);
        let one = Expr::Lit { value: Literal::Int(1), ty: i64_ty() };
        let two = Expr::Lit { value: Literal::Int(2), ty: i64_ty() };
        let one_plus_two = Expr::BinOp {
            op: SsaBinaryOp::Add,
            lhs: Box::new(one),
            rhs: Box::new(two),
            ty: i64_ty(),
        };
        let x_ref = Expr::Var { sym: x, ty: i64_ty() };
        let three = Expr::Lit { value: Literal::Int(3), ty: i64_ty() };
        let x_plus_three = Expr::BinOp {
            op: SsaBinaryOp::Add,
            lhs: Box::new(x_ref),
            rhs: Box::new(three),
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
        let (core, _x) = build_test_core();
        let mut builder = Builder::new();
        let _entry = builder.create_block();
        builder.switch_to(crate::ssa::BlockId(0));
        let symbols = SymbolTable::new();
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
        let (core, _x) = build_test_core();
        let mut builder = Builder::new();
        let _entry = builder.create_block();
        builder.switch_to(crate::ssa::BlockId(0));
        let symbols = SymbolTable::new();
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
        let f = symbols.fresh(
            "myfunc",
            Span { file: FileId(0), start: 0, end: 0 },
            SymbolKind::Func,
        );
        let core = Expr::App {
            target: symbols.display(f).to_owned(),
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
        let x = SymbolId(50);
        let one_plus_two = Expr::BinOp {
            op: SsaBinaryOp::Add,
            lhs: Box::new(Expr::Lit { value: Literal::Int(1), ty: i64_ty() }),
            rhs: Box::new(Expr::Lit { value: Literal::Int(2), ty: i64_ty() }),
            ty: i64_ty(),
        };
        let body = Expr::BinOp {
            op: SsaBinaryOp::Mul,
            lhs: Box::new(Expr::Var { sym: x, ty: i64_ty() }),
            rhs: Box::new(Expr::Lit { value: Literal::Int(10), ty: i64_ty() }),
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

        let symbols = SymbolTable::new();
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

        let symbols = SymbolTable::new();
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
        locals.insert(sentinel, one_u8);
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
        let symbols = SymbolTable::new();
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
        };
        let err = lower(&mut ctx, &core).unwrap_err();
        assert!(err.contains("#42"), "error should name the unbound symbol: {err}");
    }
}
