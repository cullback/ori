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

use crate::ast::BinOp as AstBinOp;
use crate::lower::constructor::structural_con_layout;
use crate::passes::decl_info::{DeclInfo, resolve_scalar_type};
use crate::ssa::instruction::{BinaryOp, ScalarType};
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
        Expr::Con { tag, args, ty } => {
            let disc = resolve_scalar_type(ty, &ctx.fieldless);
            if !disc.is_heap_ptr() {
                // Fieldless — single-slot. Delegate.
                return Ok(vec![lower(ctx, expr)?]);
            }
            // Payload-carrying: emit alloc + stores + return (tag, payload).
            let tag_idx = if let Some(meta) = ctx.decls.constructors.get(tag) {
                meta.tag_index
            } else {
                structural_con_layout(ty, tag, &ctx.fieldless).0
            };
            // Lower each arg's slots and store at consecutive 8-byte offsets.
            let mut all_slots: Vec<Value> = Vec::new();
            for arg in args {
                all_slots.extend(lower_slots(ctx, arg)?);
            }
            let alloc_size = all_slots.len() * 8;
            let payload = ctx.builder.alloc(alloc_size);
            for (i, v) in all_slots.iter().enumerate() {
                ctx.builder.store(payload, i * 8, *v);
            }
            let tag_v = ctx.builder.const_u64(tag_idx);
            Ok(vec![tag_v, payload])
        }

        // App where the return type is multi-slot — emit call_multi
        // and return the result slot list directly.
        Expr::App { target, args, ty } => {
            let ret_slots = super::lower::expand_slots(ty, &ctx.fieldless, &ctx.transparent);
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
            .ok_or_else(|| format!("core::to_ssa: unbound Var #{}", sym.0)),

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
            // Lower body via lower_slots (so multi-slot results work)
            // and materialize to single if needed — same convention
            // as the function-return and match-arm boundaries.
            let vals = lower_slots(ctx, value)?;
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
            // Short-circuit booleans (And/Or) need to lower as Match
            // (left side conditional on right side's evaluation), not
            // as a strict binop. Not yet implemented at Core level —
            // bail so caller falls back to direct AST→SSA.
            if matches!(op, AstBinOp::And | AstBinOp::Or) {
                return Err(format!(
                    "core::to_ssa: short-circuit {op:?} needs Match-desugaring (not yet implemented)"
                ));
            }
            let l = lower(ctx, lhs)?;
            let r = lower(ctx, rhs)?;
            let result_ty = resolve_scalar_type(ty, &ctx.fieldless);
            let ssa_op = map_binop(*op);
            Ok(ctx.builder.binop(ssa_op, l, r, result_ty))
        }

        Expr::App { target, args, ty } => {
            // Lower each arg first (left-to-right per the language's
            // strict eval order). Then emit the SSA call.
            let arg_vals: Vec<Value> = args
                .iter()
                .map(|a| lower(ctx, a))
                .collect::<Result<_, _>>()?;
            let ret_ty = resolve_scalar_type(ty, &ctx.fieldless);
            Ok(ctx.builder.call(target, arg_vals, ret_ty))
        }

        Expr::ListLit { elements, .. } => {
            // Same shape as existing-lower's ListLit:
            //   data = alloc(n * 8)
            //   store each elem at data[i*8]
            //   header = alloc(24)
            //   store len, cap, data
            //   return header
            // Single-slot elements only; the AST→Core layer bails
            // before producing a ListLit with multi-slot elements.
            let n = elements.len();
            let data = ctx.builder.alloc(n * 8);
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

        Expr::Match { scrutinee, arms, ty } => lower_match(ctx, scrutinee, arms, ty),

        Expr::Con { tag, args, ty } => {
            // Only fieldless unions are supported in this slice —
            // emit the discriminant scalar. Payload-carrying unions
            // need the (tag, payload) representation, which requires
            // multi-slot Con lowering (returns 2 values). That ships
            // when Core→SSA grows multi-result semantics.
            //
            // The "args.is_empty()" check is insufficient — a variant
            // like Nil in `[Nil, Cons(a, List(a))]` has no args but
            // its union is payload-carrying, so the result type is
            // (tag, payload) not a bare discriminant. Cross-check
            // via the resolved scalar type: fieldless unions resolve
            // to an integer discriminant; payload-carrying ones
            // resolve to RcPtr.
            if !args.is_empty() {
                return Err(format!(
                    "core::to_ssa: Con `{tag}` carries {} payload args (not yet supported)",
                    args.len()
                ));
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
            Ok(emit_tag_const(ctx.builder, tag_idx, disc))
        }

        _ => Err(format!(
            "core::to_ssa: variant not yet supported: {}",
            variant_name(expr)
        )),
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
    scrutinee: &Expr,
    arms: &[MatchArm],
    ty: &Type,
) -> Result<Value, String> {
    let scrutinee_ty = scrutinee.ty().clone();
    let scrutinee_slots = lower_slots(ctx, scrutinee)?;

    // Determine union shape from scrutinee's slot count:
    // - 1 slot  = fieldless union (the slot IS the discriminant)
    // - 2 slots = (tag, payload_ptr) non-fieldless
    let (tag_val, payload_val) = match scrutinee_slots.as_slice() {
        [v] => (*v, None),
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
            Pattern::Wildcard => return lower(ctx, &arm.body),
            Pattern::Binding(sym) => {
                // For multi-slot scrutinee, binding binds to the
                // first slot (the discriminant). This is sufficient
                // for simple uses; multi-slot Binding requires the
                // multi-binder Let machinery.
                let prev = ctx.locals.insert(*sym, tag_val);
                let result = lower(ctx, &arm.body);
                match prev {
                    Some(p) => { ctx.locals.insert(*sym, p); }
                    None => { ctx.locals.remove(sym); }
                }
                return result;
            }
            _ => {}
        }
    }

    let result_scalar = resolve_scalar_type(ty, &ctx.fieldless);

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
    let merge_param = ctx.builder.add_block_param(merge, result_scalar);

    // For each arm: create body block. If the arm binds fields,
    // pass the payload through as a block-arg so the block can load
    // fields from it. Each binder is a single SSA slot from the
    // payload at its declared offset; bind locals before lowering
    // the arm body.
    let mut arm_blocks: Vec<(u64, crate::ssa::BlockId, Vec<Value>)> = Vec::new();
    for (tag_idx, arm, field_tys) in &constructor_arms {
        let b = ctx.builder.create_block();
        let payload_block_param = if !field_tys.is_empty() && payload_val.is_some() {
            Some(ctx.builder.add_block_param(b, ScalarType::RcPtr))
        } else {
            None
        };
        ctx.builder.switch_to(b);

        // Constructor arms with field binders: load each field from
        // the payload + bind to its binder. IntLit arms have no
        // binders and no payload to load from.
        let mut bound: Vec<(SymbolId, Option<Value>)> = Vec::new();
        if let Pattern::Constructor { binders, .. } = &arm.pattern {
            if let Some(payload_param) = payload_block_param {
                for (i, (binder, &field_ty)) in binders.iter().zip(field_tys).enumerate() {
                    if binder.0 == u32::MAX { continue; } // wildcard
                    let v = ctx.builder.load(payload_param, i * 8, field_ty);
                    bound.push((*binder, ctx.locals.insert(*binder, v)));
                }
            }
        }

        // Lower the body via lower_slots so payload Con works. If
        // the arm produces multiple slots but the Match result is
        // single-slot (which happens when the Match's result type is
        // a tag-union `:=` whose expand_slots returns 1), materialize
        // the slots into a single heap shell — same convention as
        // pipeline.rs uses for the function return boundary.
        let arm_slots = lower_slots(ctx, &arm.body)?;
        let body_val = if arm_slots.len() == 1 {
            arm_slots[0]
        } else {
            let shell = ctx.builder.alloc(arm_slots.len() * 8);
            for (i, v) in arm_slots.iter().enumerate() {
                ctx.builder.store(shell, i * 8, *v);
            }
            shell
        };
        ctx.builder.jump(merge, vec![body_val]);

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
        let b = ctx.builder.create_block();
        ctx.builder.switch_to(b);
        let arm_slots = lower_slots(ctx, &arm.body)?;
        let body_val = if arm_slots.len() == 1 {
            arm_slots[0]
        } else {
            let shell = ctx.builder.alloc(arm_slots.len() * 8);
            for (i, v) in arm_slots.iter().enumerate() {
                ctx.builder.store(shell, i * 8, *v);
            }
            shell
        };
        ctx.builder.jump(merge, vec![body_val]);
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
    Ok(merge_param)
}

/// Map AST-level `BinOp` to SSA-level `BinaryOp`. They're a 1:1
/// correspondence except for `And`/`Or` (short-circuit booleans),
/// which we error on here — they need lazy lowering that we'd handle
/// as `Match` at the Core layer rather than as binops.
fn map_binop(op: AstBinOp) -> BinaryOp {
    match op {
        AstBinOp::Add => BinaryOp::Add,
        AstBinOp::Sub => BinaryOp::Sub,
        AstBinOp::Mul => BinaryOp::Mul,
        AstBinOp::Div => BinaryOp::Div,
        AstBinOp::Rem => BinaryOp::Rem,
        AstBinOp::BitOr => BinaryOp::Or,
        AstBinOp::BitXor => BinaryOp::Xor,
        AstBinOp::Eq => BinaryOp::Eq,
        AstBinOp::Neq => BinaryOp::Neq,
        AstBinOp::Lt => BinaryOp::Lt,
        AstBinOp::Gt => BinaryOp::Gt,
        AstBinOp::Le => BinaryOp::Le,
        AstBinOp::Ge => BinaryOp::Ge,
        AstBinOp::And | AstBinOp::Or => {
            // Caller must check before calling map_binop — the
            // Expr::BinOp arm in `lower` short-circuits earlier with
            // an Err return for And/Or.
            unreachable!("And/Or should be handled before map_binop")
        }
    }
}

/// Emit a constant of `disc` type holding `tag_idx`. The width of the
/// discriminant determines which `const_*` Builder method to use.
fn emit_tag_const(b: &mut Builder, tag_idx: u64, disc: ScalarType) -> Value {
    match disc {
        ScalarType::U8 => b.const_u8(tag_idx as u8),
        ScalarType::U16 => b.const_u16(tag_idx as u16),
        ScalarType::U32 => b.const_u32(tag_idx as u32),
        ScalarType::U64 => b.const_u64(tag_idx),
        other => panic!("core::to_ssa: unexpected discriminant type {other:?}"),
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

fn variant_name(expr: &Expr) -> &'static str {
    match expr {
        Expr::Var { .. } => "Var",
        Expr::Lit { .. } => "Lit",
        Expr::App { .. } => "App",
        Expr::Let { .. } => "Let",
        Expr::Match { .. } => "Match",
        Expr::Cata { .. } => "Cata",
        Expr::Con { .. } => "Con",
        Expr::BinOp { .. } => "BinOp",
        Expr::ListLit { .. } => "ListLit",
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::BinOp as AstBinOp;
    use crate::ssa::ScalarType;

    fn i64_ty() -> Type {
        Type::Con("I64".to_string())
    }

    /// Build the Core for `let x = 1 + 2 in x + 3`.
    fn build_test_core() -> (Expr, SymbolId) {
        let x = SymbolId(100);
        let one = Expr::Lit { value: Literal::Int(1), ty: i64_ty() };
        let two = Expr::Lit { value: Literal::Int(2), ty: i64_ty() };
        let one_plus_two = Expr::BinOp {
            op: AstBinOp::Add,
            lhs: Box::new(one),
            rhs: Box::new(two),
            ty: i64_ty(),
        };
        let x_ref = Expr::Var { sym: x, ty: i64_ty() };
        let three = Expr::Lit { value: Literal::Int(3), ty: i64_ty() };
        let x_plus_three = Expr::BinOp {
            op: AstBinOp::Add,
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
            op: AstBinOp::Add,
            lhs: Box::new(Expr::Lit { value: Literal::Int(1), ty: i64_ty() }),
            rhs: Box::new(Expr::Lit { value: Literal::Int(2), ty: i64_ty() }),
            ty: i64_ty(),
        };
        let body = Expr::BinOp {
            op: AstBinOp::Mul,
            lhs: Box::new(Expr::Var { sym: x, ty: i64_ty() }),
            rhs: Box::new(Expr::Lit { value: Literal::Int(10), ty: i64_ty() }),
            ty: i64_ty(),
        };
        let core = Expr::Match {
            scrutinee: Box::new(one_plus_two),
            arms: vec![super::super::expr::MatchArm {
                pattern: super::super::expr::Pattern::Binding(x),
                body,
            }],
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
            MatchArm {
                pattern: Pattern::Constructor { tag: "True".to_string(), binders: vec![] },
                body: Expr::Lit { value: Literal::Int(100), ty: i64_ty() },
            },
            MatchArm {
                pattern: Pattern::Constructor { tag: "False".to_string(), binders: vec![] },
                body: Expr::Lit { value: Literal::Int(200), ty: i64_ty() },
            },
        ];
        let core = Expr::Match {
            scrutinee: Box::new(scrutinee),
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
        };

        let core_with_var = Expr::Match {
            scrutinee: Box::new(Expr::Var { sym: sentinel, ty: bool_ty }),
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
        };
        let err = lower(&mut ctx, &core).unwrap_err();
        assert!(err.contains("#42"), "error should name the unbound symbol: {err}");
    }
}
