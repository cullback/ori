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
use crate::passes::decl_info::{resolve_scalar_type, substitute_type_var};
use crate::ssa::instruction::ScalarType;
use crate::symbol::{FieldInterner, SymbolId, SymbolKind, SymbolTable};
use crate::types::engine::{Type, TypeVar};

/// Type alias table — maps transparent newtype names to their
/// (type-params, underlying type). Same shape as `InferResult.transparent`.
pub type TransparentTable = HashMap<String, (Vec<TypeVar>, Type)>;

/// Unfold transparent type aliases. `Result(I64, I64)` (declared as
/// `Result(ok, err) := [Ok(ok), Err(err)]`) becomes the structural
/// `[Ok(I64), Err(I64)]` TagUnion. Recursive aliases unfold to fixed
/// point. Non-alias types pass through unchanged.
pub fn resolve_transparent(ty: &Type, transparent: &TransparentTable) -> Type {
    match ty {
        Type::App(name, args) => {
            if let Some((param_vars, underlying)) = transparent.get(name) {
                let mut result = underlying.clone();
                for (var, arg) in param_vars.iter().zip(args) {
                    result = substitute_type_var(&result, *var, arg);
                }
                resolve_transparent(&result, transparent)
            } else {
                ty.clone()
            }
        }
        Type::Con(name) => {
            if let Some((_, underlying)) = transparent.get(name) {
                resolve_transparent(underlying, transparent)
            } else {
                ty.clone()
            }
        }
        _ => ty.clone(),
    }
}

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
    /// Transparent type alias table — `Result(a, e)` → `[Ok(a), Err(e)]`
    /// etc. Passed to `expand_slots` so transparent aliases get
    /// resolved before slot-shape computation.
    pub transparent: TransparentTable,
    /// Names of declared constructors (`"Ok"`, `"Cons"`, `"True"`, ...).
    /// A `Call` whose target's display name is in this set lowers to
    /// `Core::Con`, not `Core::App` — keeps constructor dispatch
    /// visible to `Match` and avoids generating "call to unknown
    /// function 'Ok'" SSA.
    pub constructors: HashSet<String>,
    /// Names of declared **payload-carrying** unions (`Result`, `Maybe`,
    /// custom user types with field-bearing variants). `expand_slots`
    /// for an `App(name, _)` whose `name` is in this set returns
    /// 2 slots `[U64, RcPtr]` even when the type doesn't unfold via
    /// `transparent` — these `:=` tag unions aren't in the transparent
    /// table by design (see `infer::Pass 2a`).
    pub payload_unions: HashSet<String>,
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
            transparent: HashMap::new(),
            constructors: HashSet::new(),
            payload_unions: HashSet::new(),
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
                let slot_tys = expand_slots_with(&ast.ty, &ctx.fieldless, &ctx.transparent, &ctx.payload_unions);
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
                        scrutinee_slots: vec![scrutinee],
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
                        scrutinee_slots: vec![scrutinee],
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

        ExprKind::QualifiedCall { resolved, args, segments, .. } => {
            // Mirror existing-lower's QualifiedCall fallback at the
            // very end: when `resolved` is None, fall back to the
            // joined segments as the call name. Most affected tests
            // are top-level qualified calls (`List.range`, `Type.method`)
            // that mono should have populated but in some shapes
            // didn't. Calls to local-variable receivers / __builtin
            // intrinsics keep their existing bail-out paths.
            let synthesized;
            let name: &String = match resolved.as_ref() {
                Some(n) => n,
                None => {
                    // Local-variable method-call form: segments[0] is
                    // a local. Existing-lower handles this via the
                    // receiver_lv code path; we don't.
                    if segments.len() >= 2
                        && ctx.locals.contains_key(&segments[0].parse::<u32>().map(crate::symbol::SymbolId).unwrap_or(crate::symbol::SymbolId(u32::MAX)))
                    {
                        return Err(format!(
                            "core::lower_expr: QualifiedCall on local receiver `{}` not yet handled",
                            segments[0]
                        ));
                    }
                    synthesized = segments.join(".");
                    &synthesized
                }
            };
            if name.starts_with("__builtin.") {
                return Err(format!(
                    "core::lower_expr: QualifiedCall to intrinsic `{name}` not yet handled"
                ));
            }
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
            if name.starts_with("__builtin.") {
                return Err(format!(
                    "core::lower_expr: MethodCall to intrinsic `{name}` not yet handled"
                ));
            }
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
            let (offset, count) = field_slice(&record.ty, *field, ctx.fields, &ctx.fieldless, &ctx.transparent);
            if offset + count > record_slots.len() {
                return Err(format!(
                    "core::lower_expr: FieldAccess offset {offset}..{} exceeds record's {} slots",
                    offset + count,
                    record_slots.len()
                ));
            }
            Ok(record_slots[offset..offset + count].to_vec())
        }

        ExprKind::ListLit(elems) => {
            // Element type from List(T) — unfold transparent first
            // (Str := List(U8)).
            let unwrapped = resolve_transparent(&ast.ty, &ctx.transparent);
            let elem_ty = match &unwrapped {
                Type::App(name, args) if name == "List" && args.len() == 1 => args[0].clone(),
                _ => return Err(format!(
                    "core::lower_expr: ListLit type not List(_): {:?}",
                    ast.ty
                )),
            };
            // Each element must be single-slot for now. Multi-slot
            // element types (records, tuples, lists-of-lists) need
            // inlined-slot layout — falls back.
            if expand_slots_with(&elem_ty, &ctx.fieldless, &ctx.transparent, &ctx.payload_unions).len() != 1 {
                return Err(format!(
                    "core::lower_expr: ListLit with multi-slot element type {elem_ty:?} not yet supported"
                ));
            }
            let elements: Vec<Expr> = elems
                .iter()
                .map(|e| lower_expr(ctx, e))
                .collect::<Result<_, _>>()?;
            Ok(vec![Expr::ListLit {
                elements,
                elem_ty,
                ty: ast.ty.clone(),
            }])
        }

        ExprKind::Is { expr, pattern } => {
            // `expr : pattern` is sugar for a 2-arm Match returning Bool.
            //   match expr of pattern -> True | _ -> False
            let scrutinee_slots = lower_expr_slots(ctx, expr)?;
            let pat = lower_pattern(pattern)?;
            let bool_ty = ast.ty.clone();
            let true_body = Expr::Con {
                tag: "True".to_string(),
                args: vec![],
                ty: bool_ty.clone(),
            };
            let false_body = Expr::Con {
                tag: "False".to_string(),
                args: vec![],
                ty: bool_ty.clone(),
            };
            Ok(vec![Expr::Match {
                scrutinee_slots,
                arms: vec![
                    MatchArm { pattern: pat, body: true_body },
                    MatchArm { pattern: Pattern::Wildcard, body: false_body },
                ],
                ty: bool_ty,
            }])
        }

        ExprKind::If { expr, arms, else_body } => {
            // The scrutinee may be multi-slot (e.g., matching on a
            // Maybe parameter whose params decomposed to (tag,
            // payload)). lower_expr_slots returns the parallel slot
            // list; to_ssa flattens it into the SSA Values it dispatches
            // on.
            let scrutinee_slots = lower_expr_slots(ctx, expr)?;
            let mut core_arms: Vec<MatchArm> = arms
                .iter()
                .map(|a| lower_match_arm(ctx, a))
                .collect::<Result<_, _>>()?;
            if let Some(else_expr) = else_body {
                let body = lower_expr(ctx, else_expr)?;
                core_arms.push(MatchArm { pattern: Pattern::Wildcard, body });
            }
            Ok(vec![Expr::Match {
                scrutinee_slots,
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
    let mut wrap_with_lets: Vec<(Vec<SymbolId>, Expr)> = Vec::new();
    for stmt in stmts {
        match stmt {
            Stmt::Let { name, val } => {
                let value_slots = lower_expr_slots(ctx, val)?;
                let expected_slot_count = expand_slots_with(&val.ty, &ctx.fieldless, &ctx.transparent, &ctx.payload_unions).len();

                if value_slots.len() == 1 && expected_slot_count == 1 {
                    // Scalar binding — bind to the AST sym directly.
                    wrap_with_lets.push((
                        vec![*name],
                        value_slots.into_iter().next().unwrap(),
                    ));
                } else if value_slots.len() == expected_slot_count {
                    // Aggregate literal — N parallel single-binder Lets.
                    let slot_syms = mint_slot_syms(ctx, *name, expected_slot_count);
                    ctx.locals.insert(*name, slot_syms.clone());
                    for (sym, val) in slot_syms.into_iter().zip(value_slots) {
                        wrap_with_lets.push((vec![sym], val));
                    }
                } else if value_slots.len() == 1 && expected_slot_count > 1 {
                    // One Core Expr producing N slots (multi-result
                    // Call, payload Con) — single multi-binder Let.
                    let slot_syms = mint_slot_syms(ctx, *name, expected_slot_count);
                    ctx.locals.insert(*name, slot_syms.clone());
                    wrap_with_lets.push((
                        slot_syms,
                        value_slots.into_iter().next().unwrap(),
                    ));
                } else {
                    return Err(format!(
                        "core::lower_block: slot count mismatch — value_slots={}, expected={}",
                        value_slots.len(),
                        expected_slot_count
                    ));
                }
            }
            Stmt::TypeHint { .. } => {}
            Stmt::Destructure { pattern, val } => {
                lower_destructure(ctx, pattern, val, &mut wrap_with_lets)?;
            }
            Stmt::Guard { .. } => {
                return Err("core::lower_block: Stmt::Guard not yet supported".into());
            }
        }
    }

    let wrapped: Vec<Expr> = body_slots
        .into_iter()
        .map(|body| {
            let mut out = body;
            for (binders, val) in wrap_with_lets.iter().rev() {
                out = Expr::Let {
                    binders: binders.clone(),
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

/// Lower a `let pat = val` destructure into one or more bindings in
/// `wrap_with_lets`. Today supports `Pattern::Tuple` with single-slot
/// Binding sub-patterns (no Wildcards, no nesting). The value is
/// either an aggregate literal (Vec<Expr> matching the sub-pattern
/// count) or a single multi-slot Core Expr (multi-binder Let).
fn lower_destructure(
    ctx: &mut LowerCtx<'_>,
    pattern: &AstPattern<'_>,
    val: &AstExpr<'_>,
    wrap_with_lets: &mut Vec<(Vec<SymbolId>, Expr)>,
) -> Result<(), String> {
    let value_slots = lower_expr_slots(ctx, val)?;
    let expected_slot_count = expand_slots_with(&val.ty, &ctx.fieldless, &ctx.transparent, &ctx.payload_unions).len();
    let sub_pats: &[AstPattern<'_>] = match pattern {
        AstPattern::Tuple(ps) => ps,
        other => return Err(format!(
            "core::lower_destructure: unsupported pattern shape: {other:?}"
        )),
    };
    // For simplicity, each sub-pattern must be a Binding. Nested
    // patterns + Wildcards land later.
    let binders: Vec<SymbolId> = sub_pats
        .iter()
        .map(|p| match p {
            AstPattern::Binding(sym) => Ok(*sym),
            other => Err(format!(
                "core::lower_destructure: only top-level Binding sub-patterns supported, got {other:?}"
            )),
        })
        .collect::<Result<_, _>>()?;
    if sub_pats.len() != expected_slot_count {
        return Err(format!(
            "core::lower_destructure: Tuple pattern has {} elements but value type expands to {} slots",
            sub_pats.len(),
            expected_slot_count
        ));
    }

    if value_slots.len() == binders.len() {
        // Aggregate literal — parallel single-binder Lets.
        for (sym, val) in binders.into_iter().zip(value_slots) {
            wrap_with_lets.push((vec![sym], val));
        }
    } else if value_slots.len() == 1 && binders.len() > 1 {
        // Multi-slot Call etc. — single multi-binder Let.
        wrap_with_lets.push((binders, value_slots.into_iter().next().unwrap()));
    } else {
        return Err(format!(
            "core::lower_destructure: slot count mismatch — value_slots={}, binders={}",
            value_slots.len(),
            binders.len()
        ));
    }
    Ok(())
}

fn mint_slot_syms(
    ctx: &mut LowerCtx<'_>,
    base: SymbolId,
    count: usize,
) -> Vec<SymbolId> {
    let base_name = ctx.symbols.display(base).to_owned();
    let span = ctx.symbols.get(base).span;
    let syms: Vec<SymbolId> = (0..count)
        .map(|i| ctx.symbols.fresh(format!("{base_name}.{i}"), span, SymbolKind::Func))
        .collect();
    for (i, sym) in syms.iter().enumerate() {
        ctx.slot_paths.insert(*sym, format!("{base_name}.{i}"));
    }
    syms
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
    transparent: &TransparentTable,
) -> (usize, usize) {
    let unwrapped = resolve_transparent(record_ty, transparent);
    let Type::Record { fields: record_fields, .. } = &unwrapped else {
        panic!(
            "core::field_slice: expected Record type for FieldAccess, got {:?}",
            record_ty
        );
    };
    let target_name = fields.get(field);
    let mut offset = 0;
    for (fname, fty) in record_fields {
        let count = expand_slots(fty, fieldless, transparent).len();
        if fname == target_name {
            return (offset, count);
        }
        offset += count;
    }
    panic!(
        "core::field_slice: field `{target_name}` not in record type {record_ty:?}"
    );
}

/// Compute the slot list (per-slot ScalarType) for a type, unfolding
/// transparent aliases first. Records and tuples fan out shallowly;
/// scalars and pointer types are 1-element; multi-variant tag unions
/// are (tag, payload) → 2.
pub fn expand_slots(
    ty: &Type,
    fieldless: &HashMap<String, ScalarType>,
    transparent: &TransparentTable,
) -> Vec<ScalarType> {
    expand_slots_with(ty, fieldless, transparent, &HashSet::new())
}

pub fn expand_slots_with(
    ty: &Type,
    fieldless: &HashMap<String, ScalarType>,
    transparent: &TransparentTable,
    payload_unions: &HashSet<String>,
) -> Vec<ScalarType> {
    let unwrapped = resolve_transparent(ty, transparent);
    // Named reference to a declared payload-carrying union (Result,
    // Maybe, custom user types) — return (tag, payload_ptr) shape even
    // though the type doesn't unfold via transparent. `:=` and `:`
    // declarations aren't in the transparent table; they appear in
    // schemes as Type::App or Type::Con by name.
    let union_name = match &unwrapped {
        Type::App(name, _) => Some(name.as_str()),
        Type::Con(name) => Some(name.as_str()),
        _ => None,
    };
    if let Some(name) = union_name {
        if payload_unions.contains(name) {
            return vec![ScalarType::U64, ScalarType::RcPtr];
        }
    }
    match &unwrapped {
        Type::Record { fields, .. } => {
            let mut out = Vec::new();
            for (_, fty) in fields {
                out.extend(expand_slots(fty, fieldless, transparent));
            }
            out
        }
        Type::Tuple(elems) => {
            let mut out = Vec::new();
            for e in elems {
                out.extend(expand_slots(e, fieldless, transparent));
            }
            out
        }
        Type::TagUnion { tags, .. } => {
            let all_fieldless = tags.iter().all(|(_, fs)| fs.is_empty());
            if all_fieldless {
                vec![crate::passes::decl_info::discriminant_type(tags.len())]
            } else if tags.len() == 1 {
                // Single non-fieldless variant (Phase E closure shape,
                // single-constructor newtypes): decompose directly to
                // the variant's fields — no tag, no payload heap.
                // Matches existing-lower's convention exactly so HOF
                // narrowing → register captures still works.
                tags[0].1.iter().flat_map(|t| expand_slots_with(t, fieldless, transparent, payload_unions)).collect()
            } else {
                // (tag: U64, payload: RcPtr)
                vec![ScalarType::U64, ScalarType::RcPtr]
            }
        }
        _ => vec![resolve_scalar_type(&unwrapped, fieldless)],
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
