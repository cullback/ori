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
use crate::passes::decl_info::resolve_scalar_type;
use crate::ssa::instruction::{BinaryOp, ScalarType};
use crate::ssa::{Builder, Value};
use crate::symbol::SymbolId;
use crate::types::engine::Type;

use super::expr::{Expr, Literal};

/// Lowering context. Mutable: tracks the current locals map as `Let`s
/// extend it; the `Builder` is borrowed mutably and accumulates the
/// emitted instructions in its current block.
pub struct Ctx<'b> {
    pub builder: &'b mut Builder,
    pub locals: HashMap<SymbolId, Value>,
    pub fieldless: HashMap<String, ScalarType>,
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

        Expr::Lit { value: Literal::Int(n), ty: _ty } => {
            // Type-aware: we'd ideally pick the const variant based on
            // the literal's resolved type. The minimal slice uses I64;
            // type-directed const selection lands when we grow.
            Ok(ctx.builder.const_i64(*n))
        }

        Expr::Lit { value: Literal::Float(f), .. } => Ok(ctx.builder.const_f64(*f)),

        Expr::Lit { value: Literal::Str(_), .. } => {
            Err("core::to_ssa: Lit::Str requires static promotion — not yet implemented".into())
        }

        Expr::Let { binder, value, body, .. } => {
            let v = lower(ctx, value)?;
            let prev = ctx.locals.insert(*binder, v);
            let result = lower(ctx, body);
            // Restore the shadowed binding so sibling scopes don't see
            // this binder (Core blocks are lexically scoped).
            match prev {
                Some(p) => { ctx.locals.insert(*binder, p); }
                None => { ctx.locals.remove(binder); }
            }
            result
        }

        Expr::BinOp { op, lhs, rhs, ty } => {
            let l = lower(ctx, lhs)?;
            let r = lower(ctx, rhs)?;
            let result_ty = resolve_scalar_type(ty, &ctx.fieldless);
            let ssa_op = map_binop(*op);
            Ok(ctx.builder.binop(ssa_op, l, r, result_ty))
        }

        _ => Err(format!(
            "core::to_ssa: variant not yet supported: {}",
            variant_name(expr)
        )),
    }
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
            // Short-circuit booleans lower as Match in Core, not BinOp.
            // If a Core::BinOp carries And/Or we have an upstream bug.
            panic!("core::to_ssa: And/Or should not appear as BinOp at Core level")
        }
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
        Expr::Record { .. } => "Record",
        Expr::BinOp { .. } => "BinOp",
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
            binder: x,
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
        let mut ctx = Ctx {
            builder: &mut builder,
            locals: HashMap::new(),
            fieldless: HashMap::new(),
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
        let mut ctx = Ctx {
            builder: &mut builder,
            locals: HashMap::new(),
            fieldless: HashMap::new(),
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
    fn unbound_var_reports_symbol() {
        let core = Expr::Var { sym: SymbolId(42), ty: i64_ty() };
        let mut builder = Builder::new();
        let _entry = builder.create_block();
        builder.switch_to(crate::ssa::BlockId(0));
        let mut ctx = Ctx {
            builder: &mut builder,
            locals: HashMap::new(),
            fieldless: HashMap::new(),
        };
        let err = lower(&mut ctx, &core).unwrap_err();
        assert!(err.contains("#42"), "error should name the unbound symbol: {err}");
    }
}
