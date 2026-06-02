//! AST → Core lowering — slot-list semantics.
//!
//! Translates the post-mono, post-lambda-lift, post-pattern-flattened
//! AST into Core. The primary API is `lower_expr_slots(ctx, ast) ->
//! Vec<Expr>`, which returns one Core expression per slot of the AST
//! expression's type. Scalars produce a 1-element vec; aggregates
//! (records, tuples, multi-slot tag unions) produce N. The slot
//! count is `expand_slots(ast.ty)` — deterministic from type.
//!
//! `lower_expr(ctx, ast) -> Expr` is a convenience that asserts the
//! result is single-slot and unwraps. Use it from contexts where the
//! AST expression is known to be scalar (`BinOp` operand, scalar
//! arg, etc.).
//!
//! ## Mapping table
//!
//! | AST | Core |
//! |---|---|
//! | `IntLit/FloatLit/StrLit` | `[Lit]` |
//! | `Name` | `[Var]`, or N Vars if the binding is multi-slot |
//! | `Call/QualifiedCall/MethodCall` | `[App]` (or multiple, for multi-result) |
//! | `BinOp` | `[BinOp]` (always single-slot) |
//! | `Block(stmts, last)` | nested `Let`s; result is last's slot list |
//! | `If` | per-slot `[Match, Match, ...]` (duplicates condition) |
//! | `Tuple(elems)` | concatenation of each elem's slots |
//! | `Record { fields }` | concatenation of each field's slots |
//! | `FieldAccess { record, field }` | slice of record's slot list at field's offset |
//! | `Fold` | (already eliminated by `fold_lift`) |
//!
//! ## Aggregate SROA
//!
//! Records and tuples have no Core IR node. They lower to slot lists:
//!
//! - `Record { x: e1, y: e2 }` → `lower_slots(e1) ++ lower_slots(e2)`
//! - `r.x` → take `lower_slots(r)[x_offset..x_offset + x_slot_count]`
//! - `let r = e in body` (where `e` is multi-slot): mint fresh slot
//!   symbols for `r`, emit one `Let` per slot, track binding in
//!   `LowerCtx.locals`. Subsequent `Var(r)` references expand to
//!   `Vec<Var>` of the slot symbols.
//!
//! ## Aggregate-producing control flow
//!
//! For multi-slot `If`/`Match` results, each slot becomes a parallel
//! Core expression — the same scrutinee/condition is duplicated.
//! Sound under purity + totality; performance cost recovered by
//! future CSE/GVN. Not implemented yet beyond single-slot today.

use std::collections::HashMap;

use std::collections::HashSet;

use crate::ast::{Expr as AstExpr, ExprKind, MatchArm as AstMatchArm, Pattern as AstPattern, Stmt};
use crate::passes::decl_info::resolve_scalar_type;
use crate::ssa::instruction::ScalarType;
use crate::symbol::{FieldInterner, SymbolId, SymbolKind, SymbolTable};
use crate::types::engine::Type;

use super::expr::{Expr, Literal, MatchArm, Pattern};

/// Context for AST→Core lowering. Mutable: minting fresh slot
/// symbols requires `&mut SymbolTable`; tracking per-binding slot
/// expansions and slot debug names happens during lowering.
pub struct LowerCtx<'a> {
    pub fields: &'a FieldInterner,
    pub symbols: &'a mut SymbolTable,
    /// `fieldless_tags` from decl_info, needed for `expand_slots`
    /// type queries. Kept as an owned clone to avoid the lifetime
    /// gymnastics of borrowing through `&Monomorphized`.
    pub fieldless: HashMap<String, ScalarType>,
    /// Names of declared constructors (`"Ok"`, `"Cons"`, `"True"`, ...).
    /// A `Call` whose target's display name is in this set lowers to
    /// `Core::Con`, not `Core::App` — keeps constructor dispatch
    /// visible to `Match` and avoids generating "call to unknown
    /// function 'Ok'" SSA.
    pub constructors: HashSet<String>,
    /// Per-binding slot expansion. An AST `SymbolId` for a binding
    /// of multi-slot type maps to its synthesized per-slot symbols.
    /// Single-slot bindings either don't appear here (the AST sym
    /// is used directly) or appear with a 1-element vec.
    pub locals: HashMap<SymbolId, Vec<SymbolId>>,
    /// Debug names: slot SymbolId → source-derived dotted path
    /// (`r.x`, `r.b.c`, `t.0`). Read by the SSA display layer when
    /// printing Values for debug output / error messages.
    pub slot_paths: HashMap<SymbolId, String>,
}

impl<'a> LowerCtx<'a> {
    pub fn new(fields: &'a FieldInterner, symbols: &'a mut SymbolTable) -> Self {
        Self {
            fields,
            symbols,
            fieldless: HashMap::new(),
            constructors: HashSet::new(),
            locals: HashMap::new(),
            slot_paths: HashMap::new(),
        }
    }
}

/// Lower an AST expression into Core slot list. The vec's length
/// equals `expand_slots(ast.ty).len()` — one Core expression per slot.
pub fn lower_expr_slots(ctx: &mut LowerCtx<'_>, ast: &AstExpr<'_>) -> Result<Vec<Expr>, String> {
    match &ast.kind {
        ExprKind::IntLit(n) => Ok(vec![Expr::Lit {
            value: Literal::Int(*n),
            ty: ast.ty.clone(),
        }]),

        ExprKind::FloatLit(f) => Ok(vec![Expr::Lit {
            value: Literal::Float(*f),
            ty: ast.ty.clone(),
        }]),

        ExprKind::StrLit(bytes) => Ok(vec![Expr::Lit {
            value: Literal::Str(bytes.clone()),
            ty: ast.ty.clone(),
        }]),

        ExprKind::Name(sym) => {
            // If the binding has been slot-expanded (e.g., its value
            // was a multi-slot record), return Vars over the slot
            // symbols. Otherwise treat the AST sym as itself a
            // single SSA value (function params, scalar lets).
            if let Some(slot_syms) = ctx.locals.get(sym).cloned() {
                let slot_tys = expand_slots(&ast.ty, &ctx.fieldless);
                Ok(slot_syms
                    .into_iter()
                    .zip(slot_tys)
                    .map(|(s, ty)| Expr::Var { sym: s, ty: type_for_scalar(ty) })
                    .collect())
            } else {
                Ok(vec![Expr::Var { sym: *sym, ty: ast.ty.clone() }])
            }
        }

        ExprKind::Block(stmts, last) => lower_block(ctx, stmts, last),

        ExprKind::BinOp { op, lhs, rhs } => {
            // Short-circuit booleans desugar to Match — left side
            // evaluated first; right side conditional on it. This
            // is semantically equivalent to `if lhs : True then rhs
            // : False then <False/True default>` and produces the
            // same SSA as the existing AST→SSA path.
            use crate::ast::BinOp;
            match op {
                BinOp::And => {
                    // a && b ≡ match a of True -> b | False -> False
                    let scrutinee = lower_expr(ctx, lhs)?;
                    let body_true = lower_expr(ctx, rhs)?;
                    let body_false = Expr::Con {
                        tag: "False".to_string(),
                        args: vec![],
                        ty: ast.ty.clone(),
                    };
                    Ok(vec![Expr::Match {
                        scrutinee: Box::new(scrutinee),
                        arms: vec![
                            MatchArm {
                                pattern: Pattern::Constructor {
                                    tag: "True".to_string(),
                                    binders: vec![],
                                },
                                body: body_true,
                            },
                            MatchArm {
                                pattern: Pattern::Constructor {
                                    tag: "False".to_string(),
                                    binders: vec![],
                                },
                                body: body_false,
                            },
                        ],
                        ty: ast.ty.clone(),
                    }])
                }
                BinOp::Or => {
                    // a || b ≡ match a of True -> True | False -> b
                    let scrutinee = lower_expr(ctx, lhs)?;
                    let body_true = Expr::Con {
                        tag: "True".to_string(),
                        args: vec![],
                        ty: ast.ty.clone(),
                    };
                    let body_false = lower_expr(ctx, rhs)?;
                    Ok(vec![Expr::Match {
                        scrutinee: Box::new(scrutinee),
                        arms: vec![
                            MatchArm {
                                pattern: Pattern::Constructor {
                                    tag: "True".to_string(),
                                    binders: vec![],
                                },
                                body: body_true,
                            },
                            MatchArm {
                                pattern: Pattern::Constructor {
                                    tag: "False".to_string(),
                                    binders: vec![],
                                },
                                body: body_false,
                            },
                        ],
                        ty: ast.ty.clone(),
                    }])
                }
                _ => Ok(vec![Expr::BinOp {
                    op: *op,
                    lhs: Box::new(lower_expr(ctx, lhs)?),
                    rhs: Box::new(lower_expr(ctx, rhs)?),
                    ty: ast.ty.clone(),
                }]),
            }
        }

        ExprKind::Call { target, args } => {
            let name = ctx.symbols.display(*target).to_owned();
            let arg_exprs = lower_call_args(ctx, args)?;
            if ctx.constructors.contains(&name) {
                Ok(vec![Expr::Con {
                    tag: name,
                    args: arg_exprs,
                    ty: ast.ty.clone(),
                }])
            } else {
                Ok(vec![Expr::App {
                    target: name,
                    args: arg_exprs,
                    ty: ast.ty.clone(),
                }])
            }
        }

        ExprKind::QualifiedCall { resolved, args, .. } => {
            let name = resolved
                .as_ref()
                .ok_or_else(|| "core::lower_expr: QualifiedCall unresolved".to_string())?;
            let arg_exprs = lower_call_args(ctx, args)?;
            if ctx.constructors.contains(name) {
                Ok(vec![Expr::Con {
                    tag: name.clone(),
                    args: arg_exprs,
                    ty: ast.ty.clone(),
                }])
            } else {
                Ok(vec![Expr::App {
                    target: name.clone(),
                    args: arg_exprs,
                    ty: ast.ty.clone(),
                }])
            }
        }

        ExprKind::MethodCall { receiver, args, resolved, .. } => {
            let name = resolved
                .as_ref()
                .ok_or_else(|| "core::lower_expr: MethodCall unresolved".to_string())?;
            let mut arg_exprs: Vec<Expr> = Vec::new();
            arg_exprs.extend(lower_expr_slots(ctx, receiver)?);
            for a in args {
                arg_exprs.extend(lower_expr_slots(ctx, a)?);
            }
            Ok(vec![Expr::App {
                target: name.clone(),
                args: arg_exprs,
                ty: ast.ty.clone(),
            }])
        }

        ExprKind::Tuple(elems) => {
            // SROA: concatenate each element's slot list. No Core
            // node produced — the tuple exists only as its component
            // expressions.
            let mut slots = Vec::new();
            for e in elems {
                slots.extend(lower_expr_slots(ctx, e)?);
            }
            Ok(slots)
        }

        ExprKind::Record { fields } => {
            // SROA: same as Tuple. Field order is the source order.
            // (Layout normalization can reorder for packing; that's
            // a Core→SSA concern.)
            let mut slots = Vec::new();
            for (_fsym, e) in fields {
                slots.extend(lower_expr_slots(ctx, e)?);
            }
            Ok(slots)
        }

        ExprKind::FieldAccess { record, field } => {
            // Slot picking: take the record's slot list, slice at
            // the field's slot offset for its slot count.
            let record_slots = lower_expr_slots(ctx, record)?;
            let (offset, count) = field_slice(&record.ty, *field, ctx.fields, &ctx.fieldless);
            if offset + count > record_slots.len() {
                return Err(format!(
                    "core::lower_expr: FieldAccess offset {offset}..{} exceeds record's {} slots",
                    offset + count,
                    record_slots.len()
                ));
            }
            Ok(record_slots[offset..offset + count].to_vec())
        }

        ExprKind::If { expr, arms, else_body } => {
            // Single-slot If only for now — multi-slot If requires
            // per-slot duplication, deferred to a follow-on commit.
            let scrutinee = lower_expr(ctx, expr)?;
            let mut core_arms: Vec<MatchArm> = arms
                .iter()
                .map(|a| lower_match_arm(ctx, a))
                .collect::<Result<_, _>>()?;
            if let Some(else_expr) = else_body {
                let body = lower_expr(ctx, else_expr)?;
                core_arms.push(MatchArm { pattern: Pattern::Wildcard, body });
            }
            Ok(vec![Expr::Match {
                scrutinee: Box::new(scrutinee),
                arms: core_arms,
                ty: ast.ty.clone(),
            }])
        }

        other => Err(format!(
            "core::lower_expr_slots: unsupported ExprKind: {}",
            ast_kind_name(other)
        )),
    }
}

/// Convenience: lower an AST expression that's known to be single-
/// slot. Asserts the result has exactly one slot and unwraps.
pub fn lower_expr(ctx: &mut LowerCtx<'_>, ast: &AstExpr<'_>) -> Result<Expr, String> {
    let mut slots = lower_expr_slots(ctx, ast)?;
    if slots.len() != 1 {
        return Err(format!(
            "core::lower_expr: expected single slot for ExprKind {}, got {}",
            ast_kind_name(&ast.kind),
            slots.len()
        ));
    }
    Ok(slots.pop().unwrap())
}

/// Lower call args, spreading multi-slot args into the flat App args
/// list. A call `f(record, scalar)` where `record` has 2 slots and
/// `scalar` has 1 slot produces a 3-element args vec.
fn lower_call_args(ctx: &mut LowerCtx<'_>, args: &[AstExpr<'_>]) -> Result<Vec<Expr>, String> {
    let mut out = Vec::new();
    for a in args {
        out.extend(lower_expr_slots(ctx, a)?);
    }
    Ok(out)
}

fn lower_block(
    ctx: &mut LowerCtx<'_>,
    stmts: &[Stmt<'_>],
    last: &AstExpr<'_>,
) -> Result<Vec<Expr>, String> {
    // Lower body first so we know its slot count.
    let body_slots = lower_expr_slots(ctx, last)?;

    // Right-to-left fold: wrap each body slot in the Let chain.
    // Each Stmt::Let may produce multiple slot Lets if the bound
    // value is multi-slot. The same Let chain wraps every body slot
    // — sharing the bindings.
    let mut wrap_with_lets: Vec<(SymbolId, Expr)> = Vec::new();
    for stmt in stmts {
        match stmt {
            Stmt::Let { name, val } => {
                let value_slots = lower_expr_slots(ctx, val)?;
                if value_slots.len() == 1 {
                    // Scalar binding: just bind to the AST sym
                    // directly; no slot synthesis needed.
                    wrap_with_lets.push((*name, value_slots.into_iter().next().unwrap()));
                } else {
                    // Multi-slot binding: mint a slot symbol per
                    // value, record in locals + slot_paths.
                    let base_name = ctx.symbols.display(*name).to_owned();
                    let slot_syms: Vec<SymbolId> = (0..value_slots.len())
                        .map(|i| {
                            ctx.symbols.fresh(
                                format!("{base_name}.{i}"),
                                ctx.symbols.get(*name).span,
                                SymbolKind::Func,  // placeholder; not used for slot syms
                            )
                        })
                        .collect();
                    for (i, sym) in slot_syms.iter().enumerate() {
                        ctx.slot_paths.insert(*sym, format!("{base_name}.{i}"));
                    }
                    ctx.locals.insert(*name, slot_syms.clone());
                    for (sym, val) in slot_syms.into_iter().zip(value_slots) {
                        wrap_with_lets.push((sym, val));
                    }
                }
            }
            Stmt::TypeHint { .. } => {}
            Stmt::Destructure { .. } => {
                return Err("core::lower_block: Stmt::Destructure not yet supported".into());
            }
            Stmt::Guard { .. } => {
                return Err("core::lower_block: Stmt::Guard not yet supported".into());
            }
        }
    }

    // Wrap each body slot in the Let chain (innermost let wraps
    // body slot; outer lets wrap the result). Same chain for each
    // body slot — Lets are shared by sym id, not by tree position,
    // so this is correct semantically even though the Let tree is
    // duplicated.
    let wrapped: Vec<Expr> = body_slots
        .into_iter()
        .map(|body| {
            let mut out = body;
            for (sym, val) in wrap_with_lets.iter().rev() {
                out = Expr::Let {
                    binder: *sym,
                    value: Box::new(val.clone()),
                    body: Box::new(out),
                    ty: last.ty.clone(),
                };
            }
            out
        })
        .collect();
    Ok(wrapped)
}

/// Compute `(offset, count)` for a field access — the slice of the
/// record's slot list that corresponds to `field`. `offset` is the
/// sum of slot counts of preceding fields; `count` is the field's
/// slot count.
fn field_slice(
    record_ty: &Type,
    field: crate::symbol::FieldSym,
    fields: &FieldInterner,
    fieldless: &HashMap<String, ScalarType>,
) -> (usize, usize) {
    let Type::Record { fields: record_fields, .. } = record_ty else {
        panic!(
            "core::field_slice: expected Record type for FieldAccess, got {:?}",
            record_ty
        );
    };
    let target_name = fields.get(field);
    let mut offset = 0;
    for (fname, fty) in record_fields {
        let count = expand_slots(fty, fieldless).len();
        if fname == target_name {
            return (offset, count);
        }
        offset += count;
    }
    panic!(
        "core::field_slice: field `{target_name}` not in record type {record_ty:?}"
    );
}

/// Compute the slot list (per-slot ScalarType) for a type. Records,
/// tuples expand recursively; scalars and pointer types are
/// 1-element; multi-variant tag unions are (tag, payload) → 2.
pub fn expand_slots(ty: &Type, fieldless: &HashMap<String, ScalarType>) -> Vec<ScalarType> {
    match ty {
        Type::Record { fields, .. } => {
            let mut out = Vec::new();
            for (_, fty) in fields {
                out.extend(expand_slots(fty, fieldless));
            }
            out
        }
        Type::Tuple(elems) => {
            let mut out = Vec::new();
            for e in elems {
                out.extend(expand_slots(e, fieldless));
            }
            out
        }
        Type::TagUnion { tags, .. } => {
            let all_fieldless = tags.iter().all(|(_, fs)| fs.is_empty());
            if all_fieldless {
                vec![crate::passes::decl_info::discriminant_type(tags.len())]
            } else {
                // (tag: U64, payload: RcPtr)
                vec![ScalarType::U64, ScalarType::RcPtr]
            }
        }
        _ => vec![resolve_scalar_type(ty, fieldless)],
    }
}

/// Build a placeholder Type from a single ScalarType — used to
/// stamp the type on per-slot `Var` exprs synthesized for multi-
/// slot bindings. The Type is the lowest-fidelity representation
/// of the scalar's source-level type; downstream consumers only
/// use it for scalar-type resolution via `resolve_scalar_type`.
fn type_for_scalar(s: ScalarType) -> Type {
    match s {
        ScalarType::I8 => Type::Con("I8".into()),
        ScalarType::U8 => Type::Con("U8".into()),
        ScalarType::I16 => Type::Con("I16".into()),
        ScalarType::U16 => Type::Con("U16".into()),
        ScalarType::I32 => Type::Con("I32".into()),
        ScalarType::U32 => Type::Con("U32".into()),
        ScalarType::I64 => Type::Con("I64".into()),
        ScalarType::U64 => Type::Con("U64".into()),
        ScalarType::F64 => Type::Con("F64".into()),
        ScalarType::Ptr => Type::Con("__Ptr".into()),
        ScalarType::RcPtr => Type::Con("__RcPtr".into()),
    }
}

fn lower_match_arm(ctx: &mut LowerCtx<'_>, arm: &AstMatchArm<'_>) -> Result<MatchArm, String> {
    if !arm.guards.is_empty() {
        return Err("core::lower_match_arm: guarded arms not yet supported".into());
    }
    if arm.is_return {
        return Err("core::lower_match_arm: return arms not yet supported".into());
    }
    let pattern = lower_pattern(&arm.pattern)?;
    let body = lower_expr(ctx, &arm.body)?;
    Ok(MatchArm { pattern, body })
}

fn lower_pattern(pat: &AstPattern<'_>) -> Result<Pattern, String> {
    match pat {
        AstPattern::Constructor { name, fields } => {
            let mut binders = Vec::with_capacity(fields.len());
            for f in fields {
                match f {
                    AstPattern::Binding(sym) => binders.push(*sym),
                    AstPattern::Wildcard => {
                        binders.push(SymbolId(u32::MAX));
                    }
                    other => {
                        return Err(format!(
                            "core::lower_pattern: nested pattern field not supported \
                             (post-flatten should have left only Binding/Wildcard, \
                             saw {other:?})"
                        ));
                    }
                }
            }
            Ok(Pattern::Constructor {
                tag: (*name).to_owned(),
                binders,
            })
        }
        AstPattern::IntLit(n) => Ok(Pattern::IntLit(*n)),
        AstPattern::StrLit(bytes) => Ok(Pattern::StrLit(bytes.clone())),
        AstPattern::Wildcard => Ok(Pattern::Wildcard),
        AstPattern::Binding(sym) => Ok(Pattern::Binding(*sym)),
        AstPattern::Record { .. } | AstPattern::List(_) | AstPattern::Tuple(_) => {
            Err(format!(
                "core::lower_pattern: nested pattern shape not supported \
                 (post-flatten should have eliminated these): {pat:?}"
            ))
        }
    }
}

fn ast_kind_name(kind: &ExprKind<'_>) -> &'static str {
    match kind {
        ExprKind::IntLit(_) => "IntLit",
        ExprKind::FloatLit(_) => "FloatLit",
        ExprKind::StrLit(_) => "StrLit",
        ExprKind::Name(_) => "Name",
        ExprKind::BinOp { .. } => "BinOp",
        ExprKind::Call { .. } => "Call",
        ExprKind::Block(..) => "Block",
        ExprKind::If { .. } => "If",
        ExprKind::Fold { .. } => "Fold",
        ExprKind::Lambda { .. } => "Lambda",
        ExprKind::QualifiedCall { .. } => "QualifiedCall",
        ExprKind::Record { .. } => "Record",
        ExprKind::RecordUpdate { .. } => "RecordUpdate",
        ExprKind::FieldAccess { .. } => "FieldAccess",
        ExprKind::Tuple(_) => "Tuple",
        ExprKind::ListLit(_) => "ListLit",
        ExprKind::MethodCall { .. } => "MethodCall",
        ExprKind::Is { .. } => "Is",
        ExprKind::Closure { .. } => "Closure",
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{ExprKind, Span};
    use crate::source::FileId;

    fn dummy_span() -> Span {
        Span { file: FileId(0), start: 0, end: 0 }
    }

    fn i64_ty() -> Type {
        Type::Con("I64".to_string())
    }

    fn is_i64(ty: &Type) -> bool {
        matches!(ty, Type::Con(c) if c == "I64")
    }

    fn fresh_ctx<'a>(
        fields: &'a FieldInterner,
        symbols: &'a mut SymbolTable,
    ) -> LowerCtx<'a> {
        LowerCtx::new(fields, symbols)
    }

    #[test]
    fn lowers_int_literal() {
        let mut sym = SymbolTable::new();
        let fld = FieldInterner::new();
        let mut ctx = fresh_ctx(&fld, &mut sym);
        let ast = AstExpr::typed(ExprKind::IntLit(42), dummy_span(), i64_ty());
        let core = lower_expr(&mut ctx, &ast).unwrap();
        match core {
            Expr::Lit { value: Literal::Int(n), ty } => {
                assert_eq!(n, 42);
                assert!(is_i64(&ty));
            }
            other => panic!("expected Lit::Int, got {other:?}"),
        }
    }

    #[test]
    fn lowers_name_to_var() {
        let mut sym = SymbolTable::new();
        let fld = FieldInterner::new();
        let mut ctx = fresh_ctx(&fld, &mut sym);
        let ast = AstExpr::typed(ExprKind::Name(SymbolId(7)), dummy_span(), i64_ty());
        let core = lower_expr(&mut ctx, &ast).unwrap();
        match core {
            Expr::Var { sym: got, ty } => {
                assert_eq!(got, SymbolId(7));
                assert!(is_i64(&ty));
            }
            other => panic!("expected Var, got {other:?}"),
        }
    }

    #[test]
    fn tuple_lowers_to_slot_list() {
        let mut sym = SymbolTable::new();
        let fld = FieldInterner::new();
        let mut ctx = fresh_ctx(&fld, &mut sym);
        // AST `(1, 2, 3)` of type (I64, I64, I64) → 3 slot list
        let elems = vec![
            AstExpr::typed(ExprKind::IntLit(1), dummy_span(), i64_ty()),
            AstExpr::typed(ExprKind::IntLit(2), dummy_span(), i64_ty()),
            AstExpr::typed(ExprKind::IntLit(3), dummy_span(), i64_ty()),
        ];
        let tup_ty = Type::Tuple(vec![i64_ty(), i64_ty(), i64_ty()]);
        let ast = AstExpr::typed(ExprKind::Tuple(elems), dummy_span(), tup_ty);
        let slots = lower_expr_slots(&mut ctx, &ast).unwrap();
        assert_eq!(slots.len(), 3, "tuple of 3 → 3 slots");
        for (i, slot) in slots.iter().enumerate() {
            assert!(matches!(
                slot,
                Expr::Lit { value: Literal::Int(n), .. } if *n == (i + 1) as i64
            ), "slot {i} should be Lit({}); got {slot:?}", i + 1);
        }
    }
}
