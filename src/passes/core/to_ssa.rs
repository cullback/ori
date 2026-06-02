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
use crate::passes::decl_info::resolve_scalar_type;
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

        Expr::App { target, args, ty } => {
            // Lower each arg first (left-to-right per the language's
            // strict eval order). Then emit the SSA call.
            let arg_vals: Vec<Value> = args
                .iter()
                .map(|a| lower(ctx, a))
                .collect::<Result<_, _>>()?;
            let name = ctx.symbols.display(*target).to_owned();
            let ret_ty = resolve_scalar_type(ty, &ctx.fieldless);
            Ok(ctx.builder.call(&name, arg_vals, ret_ty))
        }

        Expr::Match { scrutinee, arms, ty } => lower_match(ctx, scrutinee, arms, ty),

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
    let scrutinee_val = lower(ctx, scrutinee)?;

    // Single-arm wildcard / binding: no dispatch needed.
    if arms.len() == 1 {
        let arm = &arms[0];
        match &arm.pattern {
            Pattern::Wildcard => return lower(ctx, &arm.body),
            Pattern::Binding(sym) => {
                let prev = ctx.locals.insert(*sym, scrutinee_val);
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

    // Multi-arm dispatch — require all arms to be Constructor with
    // no field binders (fieldless unions), or Wildcard (default).
    // Mixed patterns or payload-carrying constructors are deferred.
    let result_scalar = resolve_scalar_type(ty, &ctx.fieldless);

    let mut constructor_arms: Vec<(u64, &MatchArm)> = Vec::new();
    let mut default_arm: Option<&MatchArm> = None;
    for arm in arms {
        match &arm.pattern {
            Pattern::Constructor { tag, binders } => {
                if !binders.is_empty() {
                    return Err(format!(
                        "core::to_ssa: Match arm for `{tag}` carries field binders \
                         (non-fieldless union not yet supported)"
                    ));
                }
                let (tag_idx, _, _) =
                    structural_con_layout(&scrutinee_ty, tag, &ctx.fieldless);
                constructor_arms.push((tag_idx, arm));
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

    // Set up: merge block with a result block-param. Each arm gets
    // its own body block; from the body we jump to merge with its
    // result.
    let tag_block = ctx.builder.current_block.expect("expected current block");
    let merge = ctx.builder.create_block();
    let merge_param = ctx.builder.add_block_param(merge, result_scalar);

    // Materialize each arm's body block + lower its body, jumping
    // to merge with the body's result.
    let mut arm_blocks: Vec<(u64, crate::ssa::BlockId)> = Vec::new();
    for (tag_idx, arm) in &constructor_arms {
        let b = ctx.builder.create_block();
        ctx.builder.switch_to(b);
        let body_val = lower(ctx, &arm.body)?;
        ctx.builder.jump(merge, vec![body_val]);
        arm_blocks.push((*tag_idx, b));
    }
    let default_block = if let Some(arm) = default_arm {
        let b = ctx.builder.create_block();
        ctx.builder.switch_to(b);
        let body_val = lower(ctx, &arm.body)?;
        ctx.builder.jump(merge, vec![body_val]);
        Some(b)
    } else {
        None
    };

    // Back at the tag block: emit the dispatch.
    ctx.builder.switch_to(tag_block);
    let switch_arms: Vec<(u64, crate::ssa::BlockId, Vec<Value>)> = arm_blocks
        .iter()
        .map(|(idx, b)| (*idx, *b, vec![]))
        .collect();
    ctx.builder.switch_int(
        scrutinee_val,
        switch_arms,
        default_block.map(|b| (b, vec![])),
    );

    // Continue lowering in the merge block — its block-param is the
    // result Value.
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
        let symbols = SymbolTable::new();
        let mut ctx = Ctx {
            builder: &mut builder,
            symbols: &symbols,
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
        let symbols = SymbolTable::new();
        let mut ctx = Ctx {
            builder: &mut builder,
            symbols: &symbols,
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
        let mut ctx = Ctx {
            builder: &mut builder,
            symbols: &symbols,
            locals: HashMap::new(),
            fieldless: HashMap::new(),
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
        let mut ctx = Ctx {
            builder: &mut builder,
            symbols: &symbols,
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
        let mut ctx = Ctx {
            builder: &mut builder,
            symbols: &symbols,
            locals,
            fieldless,
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
        let mut ctx = Ctx {
            builder: &mut builder,
            symbols: &symbols,
            locals: HashMap::new(),
            fieldless: HashMap::new(),
        };
        let err = lower(&mut ctx, &core).unwrap_err();
        assert!(err.contains("#42"), "error should name the unbound symbol: {err}");
    }
}
