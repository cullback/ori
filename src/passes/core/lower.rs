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
    /// Per-constructor source-level field types, projected from
    /// `decl_info.constructor_schemes`. Match arm binders consult
    /// this to decide whether a binder is multi-slot (and thus
    /// needs slot syms minted) — the AST itself only carries the
    /// surface binder names without enough type info.
    pub constructor_field_types: HashMap<String, Vec<Type>>,
    /// Per-constructor source-level *return* type (the parent
    /// union). Read when lowering `Name(constructor)` so the
    /// produced `Con` carries the union's type rather than the
    /// expression-level type of the AST node — for lambda
    /// constructors the latter is the closure's return type
    /// (`I64`), which loses the fieldless-discriminant shape
    /// to_ssa needs.
    pub constructor_return_types: HashMap<String, Type>,
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
    /// Closure-tag → lifted-apply target. Populated from
    /// `decl_info.tag_targets`. Walk lowering reads this to
    /// resolve the direct-call function for a fresh-closure
    /// `Call(closure_tag, captures)` at the walk call site.
    pub tag_targets: HashMap<String, String>,
}

impl<'a> LowerCtx<'a> {
    pub fn new(fields: &'a FieldInterner, symbols: &'a mut SymbolTable) -> Self {
        Self {
            fields,
            symbols,
            fieldless: HashMap::new(),
            transparent: HashMap::new(),
            constructors: HashSet::new(),
            constructor_field_types: HashMap::new(),
            constructor_return_types: HashMap::new(),
            payload_unions: HashSet::new(),
            locals: HashMap::new(),
            slot_paths: HashMap::new(),
            tag_targets: HashMap::new(),
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
                // `ast.ty` may be a `Type::Var` left unresolved by
                // inference (the __apply closure-param case), in
                // which case `expand_slots_with` returns fewer slots
                // than `ctx.locals[sym]` actually carries. The
                // binding's slot count is the authoritative source
                // here — pad the slot-type list with `__RcPtr`
                // placeholders so every minted slot sym surfaces as
                // its own `Var`. `Match`'s scrutinee_ty is what's
                // used for actual shape resolution downstream.
                let mut slot_tys = expand_slots_with(&ast.ty, &ctx.fieldless, &ctx.transparent, &ctx.payload_unions);
                while slot_tys.len() < slot_syms.len() {
                    slot_tys.push(ScalarType::RcPtr);
                }
                return Ok(slot_syms
                    .into_iter()
                    .zip(slot_tys)
                    .map(|(s, ty)| Expr::Var { sym: s, ty: type_for_scalar(ty) })
                    .collect());
            }
            // A Name referring to a constructor — used as a 0-arg
            // value, like `Nil` in `Cons(1, Nil)` — lowers to a Con
            // with no args. Without this branch the Name path produces
            // a Var into a SymbolId that to_ssa has no binding for.
            // Resolve via `SymbolKind::Constructor` rather than name
            // alone so we don't have to round-trip through display
            // (which panics for unallocated test-only sym IDs).
            //
            // The Con's stored type is the *constructor's* return type
            // (looked up via `constructor_field_types` — the parent
            // union from the scheme), not `ast.ty`. Lambda narrow
            // sometimes leaves `Name(__lambda_0)`'s expression-level
            // type as the lambda's *return* type (`I64`) rather than
            // the closure-set TagUnion; using ast.ty there would make
            // resolve_scalar_type return I64 at to_ssa, killing the
            // fieldless discriminant path.
            if sym_is_constructor(ctx.symbols, *sym) {
                let name = ctx.symbols.display(*sym).to_owned();
                let ty = ctx
                    .constructor_return_types
                    .get(&name)
                    .cloned()
                    .unwrap_or_else(|| ast.ty.clone());
                return Ok(vec![Expr::Con {
                    tag: name,
                    args: vec![],
                    field_slot_counts: vec![],
                    ty,
                }]);
            }
            Ok(vec![Expr::Var { sym: *sym, ty: ast.ty.clone() }])
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
                    let scrutinee_ty = lhs.ty.clone();
                    let scrutinee = lower_expr(ctx, lhs)?;
                    let body_true = lower_expr(ctx, rhs)?;
                    let body_false = Expr::Con {
                        tag: "False".to_string(),
                        args: vec![],
                        field_slot_counts: vec![],
                        ty: ast.ty.clone(),
                    };
                    Ok(vec![Expr::Match {
                        scrutinee_slots: vec![scrutinee],
                        scrutinee_ty,
                        arms: vec![
                            MatchArm::plain(
                                Pattern::Constructor { tag: "True".to_string(), binders: vec![] },
                                body_true,
                            ),
                            MatchArm::plain(
                                Pattern::Constructor { tag: "False".to_string(), binders: vec![] },
                                body_false,
                            ),
                        ],
                        ty: ast.ty.clone(),
                    }])
                }
                BinOp::Or => {
                    // a || b ≡ match a of True -> True | False -> b
                    let scrutinee_ty = lhs.ty.clone();
                    let scrutinee = lower_expr(ctx, lhs)?;
                    let body_true = Expr::Con {
                        tag: "True".to_string(),
                        args: vec![],
                        field_slot_counts: vec![],
                        ty: ast.ty.clone(),
                    };
                    let body_false = lower_expr(ctx, rhs)?;
                    Ok(vec![Expr::Match {
                        scrutinee_slots: vec![scrutinee],
                        scrutinee_ty,
                        arms: vec![
                            MatchArm::plain(
                                Pattern::Constructor { tag: "True".to_string(), binders: vec![] },
                                body_true,
                            ),
                            MatchArm::plain(
                                Pattern::Constructor { tag: "False".to_string(), binders: vec![] },
                                body_false,
                            ),
                        ],
                        ty: ast.ty.clone(),
                    }])
                }
                _ => Ok(vec![Expr::BinOp {
                    op: ast_binop_to_ssa(*op),
                    lhs: Box::new(lower_expr(ctx, lhs)?),
                    rhs: Box::new(lower_expr(ctx, rhs)?),
                    ty: ast.ty.clone(),
                }]),
            }
        }

        ExprKind::Call { target, args } => {
            let name = ctx.symbols.display(*target).to_owned();
            // Stdlib intrinsics (List.* / crash) get inlined by
            // existing-lower with direct knowledge of the
            // (len, cap, data) list decomposition. Core lowers
            // the ones it understands via direct slot-list
            // slicing for header reads + dedicated Core nodes
            // (`BufLoad`, `ListRange`, `ListWalk`, `ListAppend`,
            // `ListSet`) for buffer ops; the remainder bail so
            // fallback handles them.
            if let Some(prim) = try_lower_stdlib_intrinsic(ctx, &name, args, &ast.ty)? {
                return Ok(prim);
            }
            if is_stdlib_intrinsic(&name) {
                return Err(format!(
                    "core::lower_expr: stdlib intrinsic `{name}` needs existing-lower's expanded layout"
                ));
            }
            // Compute per-source-field slot counts from the AST args'
            // inferred types BEFORE flattening into Core args, so the
            // Con boundary (in to_ssa) can re-group the per-slot Core
            // args back into source fields when materializing a wrapper
            // per field.
            let field_slot_counts: Vec<usize> = args
                .iter()
                .map(|a| {
                    expand_slots_with(
                        &a.ty,
                        &ctx.fieldless,
                        &ctx.transparent,
                        &ctx.payload_unions,
                    )
                    .len()
                    .max(1)
                })
                .collect();
            let arg_exprs = lower_call_args(ctx, &name, args)?;
            if ctx.constructors.contains(&name) {
                // Same caveat as the Name path: inference / lambda
                // narrow can leave the Call's expression-level type
                // as the lambda's *return* type (`I64`) for
                // closure constructors. Use the constructor's
                // parent-union type from `constructor_return_types`
                // when registered.
                let ty = ctx
                    .constructor_return_types
                    .get(&name)
                    .cloned()
                    .unwrap_or_else(|| ast.ty.clone());
                Ok(vec![Expr::Con {
                    tag: name,
                    args: arg_exprs,
                    field_slot_counts,
                    ty,
                }])
            } else if name.starts_with(|c: char| c.is_ascii_uppercase()) {
                // Structural constructor (uppercase, no declared
                // TypeAnno). Inference produced a TagUnion type for
                // the call site (see infer.rs's `infer_call`
                // structural fallback); emit as Con so SSA sees a
                // tag-union value, not a phantom function call.
                Ok(vec![Expr::Con {
                    tag: name,
                    args: arg_exprs,
                    field_slot_counts,
                    ty: ast.ty.clone(),
                }])
            } else if name.starts_with("__fold_") && !args.is_empty() {
                // Recognize calls to fold_lift's synth helpers as
                // `Cata`. The first source-level arg is the
                // inductive value being folded (multi-slot for
                // recursive payload unions); remaining source args
                // are captured free variables threaded through
                // the original `fold` expression. Lower each
                // source arg separately so the boundary survives —
                // a flat `lower_call_args` spread would collapse
                // the target's slots into the extras vec.
                let target_slots = lower_expr_slots(ctx, &args[0])?;
                let mut extras: Vec<Expr> = Vec::new();
                for a in &args[1..] {
                    extras.extend(lower_expr_slots(ctx, a)?);
                }
                Ok(vec![Expr::Cata {
                    fold_fn: name,
                    target_slots,
                    extra_args: extras,
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
            if let Some(op) = builtin_to_binop(name) {
                if args.len() != 2 {
                    return Err(format!(
                        "core::lower_expr: __builtin binop `{name}` expects 2 args, got {}",
                        args.len()
                    ));
                }
                return Ok(vec![Expr::BinOp {
                    op,
                    lhs: Box::new(lower_expr(ctx, &args[0])?),
                    rhs: Box::new(lower_expr(ctx, &args[1])?),
                    ty: ast.ty.clone(),
                }]);
            }
            if name.starts_with("__builtin.") {
                // Unary numeric conversions (`__builtin.to_u8`,
                // `__builtin.from_u8`, `__builtin.to_bits`, etc.)
                // dispatch on `segments[0]` (the receiver type) for
                // the destination scalar. Mirrors existing-lower's
                // call.rs handling.
                if let Some(prim) = try_lower_unary_builtin(ctx, name, segments, args, &ast.ty)? {
                    return Ok(prim);
                }
                return Err(format!(
                    "core::lower_expr: QualifiedCall to intrinsic `{name}` not yet handled"
                ));
            }
            if let Some(prim) = try_lower_stdlib_intrinsic(ctx, name, args, &ast.ty)? {
                return Ok(prim);
            }
            if is_stdlib_intrinsic(name) {
                return Err(format!(
                    "core::lower_expr: stdlib intrinsic `{name}` needs existing-lower's expanded layout"
                ));
            }
            let field_slot_counts: Vec<usize> = args
                .iter()
                .map(|a| {
                    expand_slots_with(
                        &a.ty,
                        &ctx.fieldless,
                        &ctx.transparent,
                        &ctx.payload_unions,
                    )
                    .len()
                    .max(1)
                })
                .collect();
            let arg_exprs = lower_call_args(ctx, name, args)?;
            if ctx.constructors.contains(name) {
                Ok(vec![Expr::Con {
                    tag: name.clone(),
                    args: arg_exprs,
                    field_slot_counts,
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
            if let Some(op) = builtin_to_binop(name) {
                if args.len() != 1 {
                    return Err(format!(
                        "core::lower_expr: __builtin binop `{name}` expects 1 arg, got {}",
                        args.len()
                    ));
                }
                return Ok(vec![Expr::BinOp {
                    op,
                    lhs: Box::new(lower_expr(ctx, receiver)?),
                    rhs: Box::new(lower_expr(ctx, &args[0])?),
                    ty: ast.ty.clone(),
                }]);
            }
            if name.starts_with("__builtin.") {
                // Unary numeric conversions on a method receiver.
                // We pass the receiver as the single "arg" — the
                // helper inspects ast.ty (the call's result) to
                // determine the destination scalar.
                let combined = vec![(**receiver).clone()];
                if let Some(prim) = try_lower_unary_builtin(ctx, name, &[], &combined, &ast.ty)? {
                    return Ok(prim);
                }
                return Err(format!(
                    "core::lower_expr: MethodCall to intrinsic `{name}` not yet handled"
                ));
            }
            // Method form: synthesize a positional arg list with
            // the receiver in front, then try the standard intrinsic
            // lowering. Same primitive set as Call/QualifiedCall.
            if is_stdlib_intrinsic(name) {
                let mut combined = vec![(**receiver).clone()];
                combined.extend(args.iter().cloned());
                if let Some(prim) = try_lower_stdlib_intrinsic(ctx, name, &combined, &ast.ty)? {
                    return Ok(prim);
                }
                return Err(format!(
                    "core::lower_expr: stdlib intrinsic `{name}` (method form) needs existing-lower's expanded layout"
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
            // a Core→SSA concern.) For multi-slot fields whose
            // expression yields a single Core node (e.g. an App,
            // ListAppend, Cata returning multiple slots), mint a
            // Let to bind slot syms one-per-slot so the resulting
            // slot list has the right length and each slot is a
            // simple Var reference — no duplicated evaluation.
            let mut slots = Vec::new();
            for (_fsym, e) in fields {
                let lowered = lower_expr_slots(ctx, e)?;
                let expected = expand_slots_with(
                    &e.ty,
                    &ctx.fieldless,
                    &ctx.transparent,
                    &ctx.payload_unions,
                );
                if lowered.len() == 1 && expected.len() > 1 {
                    slots.extend(bind_multi_slot(ctx, lowered.into_iter().next().unwrap(), &expected, &e.ty));
                } else {
                    slots.extend(lowered);
                }
            }
            Ok(slots)
        }

        ExprKind::RecordUpdate { base, updates } => {
            // SROA: lower the base into slots, then replace each
            // updated field's slot range with the new value's slots.
            // field_slice gives (offset, count) into the base's slot
            // list — derived from the base's source type, which after
            // inference matches our `expand_slots`-shaped slot list.
            // `_expanded` fans out a multi-slot value that lowered to
            // a single Core Expr (App, ListLit, ...) so the splice
            // length matches `count`.
            let mut slots = lower_expr_slots_expanded(ctx, base)?;
            for (field, val) in updates {
                let (offset, count) = field_slice(
                    &base.ty, *field, ctx.fields, &ctx.fieldless, &ctx.transparent,
                );
                let new_slots = lower_expr_slots_expanded(ctx, val)?;
                if new_slots.len() != count {
                    return Err(format!(
                        "core::lower_expr: RecordUpdate field has {} slots, expected {}",
                        new_slots.len(), count
                    ));
                }
                slots.splice(offset..offset + count, new_slots);
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
            // Each element's slot list is concatenated into the
            // ListLit's flat element vec. to_ssa knows the
            // per-element slot count via `elem_ty` (looking up
            // expand_slots) and emits stores at the right stride.
            let mut elements: Vec<Expr> = Vec::new();
            for e in elems {
                elements.extend(lower_expr_slots(ctx, e)?);
            }
            Ok(vec![Expr::ListLit {
                elements,
                elem_ty,
                ty: ast.ty.clone(),
            }])
        }

        ExprKind::Is { expr, pattern } => {
            // `expr : pattern` is sugar for a 2-arm Match returning Bool.
            //   match expr of pattern -> True | _ -> False
            let scrutinee_ty = expr.ty.clone();
            let scrutinee_slots = lower_expr_slots(ctx, expr)?;
            let pat = lower_pattern(pattern)?;
            let bool_ty = ast.ty.clone();
            let true_body = Expr::Con {
                tag: "True".to_string(),
                args: vec![],
                field_slot_counts: vec![],
                ty: bool_ty.clone(),
            };
            let false_body = Expr::Con {
                tag: "False".to_string(),
                args: vec![],
                field_slot_counts: vec![],
                ty: bool_ty.clone(),
            };
            Ok(vec![Expr::Match {
                scrutinee_slots,
                scrutinee_ty,
                arms: vec![
                    MatchArm::plain(pat, true_body),
                    MatchArm::plain(Pattern::Wildcard, false_body),
                ],
                ty: bool_ty,
            }])
        }

        ExprKind::If { expr, arms, else_body } => {
            // `if (A is X(b)) and (b is Y(c)) then ... else ...`:
            // the bool-and path lowers each Is as a Bool-returning
            // Match, so binders from the first Is don't propagate
            // to the second. Rewrite to nested If:
            //   if A is X(b) then (if b is Y(c) then ... else f) else f
            // The inner if sits inside the outer if's True arm where
            // the outer Is's binders are in scope. Only fires when
            // arms are the canonical True/False boolean shape (i.e.
            // not a user pattern Match like `if x : Foo(a) then ...`).
            if let ExprKind::BinOp { op: crate::ast::BinOp::And, lhs, rhs } = &expr.kind {
                if let Some(rewritten) = rewrite_and_if_to_nested(
                    lhs, rhs, arms, else_body.as_deref(), ast.span, ast.id, &ast.ty,
                ) {
                    return lower_expr_slots(ctx, &rewritten);
                }
            }
            // `if (A is X(b)) then T else F`: rewrite to a pattern
            // Match on A so b's binding flows naturally to T. The
            // bool path would lose the binding.
            if let ExprKind::Is { expr: scrutinee, pattern } = &expr.kind {
                if let Some(rewritten) = rewrite_is_if_to_match(
                    scrutinee, pattern, arms, ast.span, ast.id, &ast.ty,
                ) {
                    return lower_expr_slots(ctx, &rewritten);
                }
            }
            // The scrutinee may be multi-slot (e.g., matching on a
            // Maybe parameter whose params decomposed to (tag,
            // payload)). lower_expr_slots returns the parallel slot
            // list; to_ssa flattens it into the SSA Values it dispatches
            // on.
            let scrutinee_ty = expr.ty.clone();
            let scrutinee_slots = lower_expr_slots(ctx, expr)?;
            let mut core_arms: Vec<MatchArm> = arms
                .iter()
                .map(|a| lower_match_arm(ctx, a, &scrutinee_ty))
                .collect::<Result<_, _>>()?;
            if let Some(else_expr) = else_body {
                let body = lower_expr_slots(ctx, else_expr)?;
                core_arms.push(MatchArm {
                    pattern: Pattern::Wildcard,
                    guards: vec![],
                    body,
                    is_return: false,
                });
            }
            Ok(vec![Expr::Match {
                scrutinee_slots,
                scrutinee_ty,
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
/// Return true if `sym` is registered in the SymbolTable as a
/// tag-union constructor (declared or structural). Returns false
/// when the symbol is missing — keeps the AST→Core entry point
/// usable from unit tests that hand-allocate SymbolIds without
/// populating the table.
fn sym_is_constructor(symbols: &SymbolTable, sym: SymbolId) -> bool {
    symbols
        .try_get(sym)
        .is_some_and(|info| matches!(info.kind, SymbolKind::Constructor))
}

/// Try to lower a stdlib intrinsic call as Core primitives.
/// Returns `Ok(Some(slots))` when the intrinsic has a Core
/// expansion, `Ok(None)` when the name isn't an intrinsic (caller
/// falls through to App), and `Err` for malformed calls.
///
/// Ported intrinsics today: `crash`, `List.len`, `List.get`,
/// `List.range`, `List.walk`, `List.append`, `List.set`. Single-
/// slot scalar element types only for `List.get`; multi-slot
/// elements (Str inside `List(Str)`) bail.
///
/// If `closure_expr` is a `Call(closure_tag_sym, captures)` whose
/// tag is registered in `tag_targets` (i.e. a fresh lambda at the
/// call site whose lambda-set entry has a known lifted apply
/// function), return the target function name. Otherwise return
/// None — the caller bails to existing-lower for the non-direct
/// dispatch case.
fn resolve_closure_target_name(
    ctx: &LowerCtx<'_>,
    closure_expr: &AstExpr<'_>,
) -> Option<String> {
    let ExprKind::Call { target, .. } = &closure_expr.kind else {
        return None;
    };
    let tag_name = ctx.symbols.display(*target).to_owned();
    ctx.tag_targets.get(&tag_name).cloned()
}

fn try_lower_stdlib_intrinsic(
    ctx: &mut LowerCtx<'_>,
    name: &str,
    args: &[AstExpr<'_>],
    ret_ty: &Type,
) -> Result<Option<Vec<Expr>>, String> {
    let base = name.split("__").next().unwrap_or(name);
    match base {
        "crash" => {
            // `crash(msg)` rewrites to a call to the runtime
            // `__crash` function. Diverging; whatever return type
            // surrounds it gets a dummy value here that the runtime
            // never produces (because __crash doesn't return).
            if args.len() != 1 {
                return Err(format!(
                    "core::lower_expr: crash expects 1 arg, got {}",
                    args.len()
                ));
            }
            let msg_slots = lower_expr_slots_expanded(ctx, &args[0])?;
            Ok(Some(vec![Expr::App {
                target: "__crash".to_string(),
                args: msg_slots,
                ty: ret_ty.clone(),
            }]))
        }
        "List.walk" => {
            // Method form: args == [xs, init, closure_expr].
            // Singleton-closure direct-call only — bail if the
            // closure flows in as something other than a fresh
            // `Call(closure_tag, captures)` whose tag we can resolve
            // in `tag_targets`. Non-singleton dispatch (`__apply_K`)
            // still uses existing-lower.
            if args.len() != 3 {
                return Err(format!(
                    "core::lower_expr: List.walk expects 3 args, got {}",
                    args.len()
                ));
            }
            let xs = &args[0];
            let init = &args[1];
            let closure_expr = &args[2];
            let Some(target_func) = resolve_closure_target_name(ctx, closure_expr) else {
                return Ok(None); // bail to fallback
            };
            let xs_ty = resolve_transparent(&xs.ty, &ctx.transparent);
            let elem_ty = match &xs_ty {
                Type::App(n, ts) if n == "List" && ts.len() == 1 => ts[0].clone(),
                _ => return Ok(None),
            };
            let list_slots = lower_expr_slots_expanded(ctx, xs)?;
            let init_slots = lower_expr_slots(ctx, init)?;
            // Captures: the closure_expr is Call(tag, captures);
            // lower each capture's slots so the loop can thread
            // them as parallel block params.
            let captures = match &closure_expr.kind {
                ExprKind::Call { args: cap_args, .. } => {
                    let mut all = Vec::new();
                    for a in cap_args {
                        all.extend(lower_expr_slots(ctx, a)?);
                    }
                    all
                }
                _ => return Ok(None),
            };
            Ok(Some(vec![Expr::ListWalk {
                list_slots,
                init: init_slots,
                target: target_func,
                captures,
                elem_ty,
                ty: ret_ty.clone(),
            }]))
        }
        "List.set" => {
            // Method form: args == [xs, idx, val].
            if args.len() != 3 {
                return Err(format!(
                    "core::lower_expr: List.set expects 3 args, got {}",
                    args.len()
                ));
            }
            let xs = &args[0];
            let idx_expr = &args[1];
            let val = &args[2];
            let xs_ty = resolve_transparent(&xs.ty, &ctx.transparent);
            let elem_ty = match &xs_ty {
                Type::App(n, ts) if n == "List" && ts.len() == 1 => ts[0].clone(),
                _ => return Ok(None),
            };
            let list_slots = lower_expr_slots_expanded(ctx, xs)?;
            let idx_lowered = lower_expr(ctx, idx_expr)?;
            let val_slots = lower_expr_slots(ctx, val)?;
            Ok(Some(vec![Expr::ListSet {
                list_slots,
                idx: Box::new(idx_lowered),
                val_slots,
                elem_ty,
                ty: ret_ty.clone(),
            }]))
        }
        "List.append" => {
            // Method form: args == [xs, val].
            if args.len() != 2 {
                return Err(format!(
                    "core::lower_expr: List.append expects 2 args, got {}",
                    args.len()
                ));
            }
            let xs = &args[0];
            let val = &args[1];
            // Unwrap transparent aliases (e.g. `Str := List(U8)`)
            // so the List-shape match below catches them.
            let xs_ty = resolve_transparent(&xs.ty, &ctx.transparent);
            let elem_ty = match &xs_ty {
                Type::App(n, ts) if n == "List" && ts.len() == 1 => ts[0].clone(),
                _ => return Ok(None),
            };
            let list_slots = lower_expr_slots_expanded(ctx, xs)?;
            let val_slots = lower_expr_slots(ctx, val)?;
            Ok(Some(vec![Expr::ListAppend {
                list_slots,
                val_slots,
                elem_ty,
                ty: ret_ty.clone(),
            }]))
        }
        "List.range" => {
            if args.len() != 2 {
                return Err(format!(
                    "core::lower_expr: List.range expects 2 args, got {}",
                    args.len()
                ));
            }
            let start = lower_expr(ctx, &args[0])?;
            let end = lower_expr(ctx, &args[1])?;
            Ok(Some(vec![Expr::ListRange {
                start: Box::new(start),
                end: Box::new(end),
                ty: ret_ty.clone(),
            }]))
        }
        "List.len" => {
            if args.len() != 1 {
                return Err(format!(
                    "core::lower_expr: List.len expects 1 arg, got {}",
                    args.len()
                ));
            }
            let source_slots = lower_expr_slots_expanded(ctx, &args[0])?;
            // The list's slot list is `[len, cap, data]`; pick the
            // first slot directly. Core lists are 3-slot SROA'd
            // everywhere internal to the IR, so a header read is
            // just a slot pick — no dedicated IR node.
            if source_slots.is_empty() {
                return Err("core::lower_expr: List.len received empty slot list".into());
            }
            Ok(Some(vec![source_slots.into_iter().next().unwrap()]))
        }
        "List.get" => {
            if args.len() != 2 {
                return Err(format!(
                    "core::lower_expr: List.get expects 2 args, got {}",
                    args.len()
                ));
            }
            // Desugar `List.get(xs, idx)` into a bounds-checked
            // `Match` over `idx < xs_slots[0]` whose arms build
            // `Ok(BufLoad(xs_slots[2], idx, T))` or
            // `Err(OutOfBounds)`. The Match returns the Result's
            // (tag, payload) directly as parallel block params at
            // its merge — `bind_multi_slot` binds them via a Let
            // so the caller sees a proper 2-slot decomposition
            // without a heap shell + load round-trip.
            let xs_slots = lower_expr_slots_expanded(ctx, &args[0])?;
            let idx_expr = lower_expr(ctx, &args[1])?;
            let u64_ty = Type::Con("U64".to_string());
            let bool_ty = Type::TagUnion {
                tags: vec![("True".to_string(), vec![]), ("False".to_string(), vec![])],
                rest: None,
            };
            let xs_ty_resolved = resolve_transparent(&args[0].ty, &ctx.transparent);
            let elem_ty = match &xs_ty_resolved {
                Type::App(n, ts) if n == "List" && ts.len() == 1 => ts[0].clone(),
                other => return Err(format!(
                    "core::lower_expr: List.get on non-List type {other:?}"
                )),
            };
            // Multi-slot inline elements (records, Str, nested List)
            // are stored at stride `N * 8` per element in the data
            // buffer, with slot j of element i at slot index
            // `i * N + j`. Emit N `BufLoad`s per source field, with
            // the slot list passed to `Ok`'s Con as `args` with
            // `field_slot_counts = [N]`.
            let elem_slots = expand_slots_with(
                &elem_ty,
                &ctx.fieldless,
                &ctx.transparent,
                &ctx.payload_unions,
            );
            // List trio is decomposed to 3 parallel slots in Core
            // (len, cap, data). Pick slot 0 for the bounds check
            // and slot 2 for the buffer; direct list indexing.
            if xs_slots.len() < 3 {
                return Err(format!(
                    "core::lower_expr: List.get on xs lowered to {} slots, expected 3",
                    xs_slots.len()
                ));
            }
            let len = xs_slots[0].clone();
            let data = xs_slots[2].clone();
            let bounds_check = Expr::BinOp {
                op: crate::ssa::BinaryOp::Lt,
                lhs: Box::new(idx_expr.clone()),
                rhs: Box::new(len),
                ty: bool_ty.clone(),
            };
            // Compute the per-slot indices: `idx * N + j` for j in
            // 0..N. The N=1 single-slot case reduces to a plain
            // `data[idx]` load (no multiplication).
            let n = elem_slots.len();
            let elem_args: Vec<Expr> = (0..n)
                .map(|j| {
                    let inner_idx = if n == 1 {
                        idx_expr.clone()
                    } else {
                        let n_const = Expr::Lit {
                            value: Literal::Int(n as i64),
                            ty: u64_ty.clone(),
                        };
                        let base = Expr::BinOp {
                            op: crate::ssa::BinaryOp::Mul,
                            lhs: Box::new(idx_expr.clone()),
                            rhs: Box::new(n_const),
                            ty: u64_ty.clone(),
                        };
                        if j == 0 {
                            base
                        } else {
                            let j_const = Expr::Lit {
                                value: Literal::Int(j as i64),
                                ty: u64_ty.clone(),
                            };
                            Expr::BinOp {
                                op: crate::ssa::BinaryOp::Add,
                                lhs: Box::new(base),
                                rhs: Box::new(j_const),
                                ty: u64_ty.clone(),
                            }
                        }
                    };
                    Expr::BufLoad {
                        buf: Box::new(data.clone()),
                        idx: Box::new(inner_idx),
                        ty: type_for_scalar(elem_slots[j]),
                    }
                })
                .collect();
            let ok_body = Expr::Con {
                tag: "Ok".to_string(),
                args: elem_args,
                field_slot_counts: vec![n],
                ty: ret_ty.clone(),
            };
            let oob_union_ty = Type::TagUnion {
                tags: vec![("OutOfBounds".to_string(), vec![])],
                rest: None,
            };
            let oob = Expr::Con {
                tag: "OutOfBounds".to_string(),
                args: vec![],
                field_slot_counts: vec![],
                ty: oob_union_ty,
            };
            let err_body = Expr::Con {
                tag: "Err".to_string(),
                args: vec![oob],
                field_slot_counts: vec![1],
                ty: ret_ty.clone(),
            };
            let match_result = Expr::Match {
                scrutinee_slots: vec![bounds_check],
                scrutinee_ty: bool_ty,
                arms: vec![
                    MatchArm::plain(
                        Pattern::Constructor { tag: "True".to_string(), binders: vec![] },
                        ok_body,
                    ),
                    MatchArm::plain(
                        Pattern::Constructor { tag: "False".to_string(), binders: vec![] },
                        err_body,
                    ),
                ],
                ty: ret_ty.clone(),
            };
            // Match now returns its full slot list natively — the
            // merge block has one param per Result slot (tag,
            // payload). Bind the 2-slot Match value once via a Let
            // and reference each slot via a fresh Var so the Match
            // SSA is emitted exactly once (no duplicate bounds-check
            // + arm allocation).
            let result_slots = expand_slots_with(
                &ret_ty,
                &ctx.fieldless,
                &ctx.transparent,
                &ctx.payload_unions,
            );
            Ok(Some(bind_multi_slot(ctx, match_result, &result_slots, ret_ty)))
        }
        _ => Ok(None),
    }
}

/// True if `name` is a stdlib intrinsic that existing-lower
/// implements inline (operating on the expanded (len, cap, data)
/// list shape) rather than via a registered SSA function.
/// Catches both bare names (`List.get`) and monomorphized
/// suffixes (`List.get__I64`).
/// Rewrite `if (lhs and rhs) then T else F` to
/// `if lhs then (if rhs then T else F) else F`. Only fires when the
/// arms are the canonical True/False boolean shape (not a typed
/// pattern Match) — otherwise we'd transform a user-written Match.
/// Returns None if the shape doesn't match.
fn rewrite_and_if_to_nested<'src>(
    lhs: &AstExpr<'src>,
    rhs: &AstExpr<'src>,
    arms: &[crate::ast::MatchArm<'src>],
    else_body: Option<&AstExpr<'src>>,
    span: crate::ast::Span,
    id: crate::ast::ExprId,
    ty: &Type,
) -> Option<AstExpr<'src>> {
    use crate::ast::{ExprKind as AstK, MatchArm, Pattern as AstPat};
    if arms.len() != 2 {
        return None;
    }
    let true_arm = arms.iter().find(|a| matches!(&a.pattern, AstPat::Constructor { name: "True", .. }))?;
    let false_arm = arms.iter().find(|a| matches!(&a.pattern, AstPat::Constructor { name: "False", .. }))?;
    if else_body.is_some() {
        return None;
    }
    let body_t = true_arm.body.clone();
    let body_f = false_arm.body.clone();
    let inner_if = {
        let mut e = AstExpr::new(
            AstK::If {
                expr: Box::new(rhs.clone()),
                arms: vec![
                    MatchArm {
                        pattern: AstPat::Constructor { name: "True", fields: vec![] },
                        guards: vec![],
                        body: body_t,
                        is_return: false,
                    },
                    MatchArm {
                        pattern: AstPat::Constructor { name: "False", fields: vec![] },
                        guards: vec![],
                        body: body_f.clone(),
                        is_return: false,
                    },
                ],
                else_body: None,
            },
            span,
        );
        e.id = id;
        e.ty = ty.clone();
        e
    };
    let outer_if = {
        let mut e = AstExpr::new(
            AstK::If {
                expr: Box::new(lhs.clone()),
                arms: vec![
                    MatchArm {
                        pattern: AstPat::Constructor { name: "True", fields: vec![] },
                        guards: vec![],
                        body: inner_if,
                        is_return: false,
                    },
                    MatchArm {
                        pattern: AstPat::Constructor { name: "False", fields: vec![] },
                        guards: vec![],
                        body: body_f,
                        is_return: false,
                    },
                ],
                else_body: None,
            },
            span,
        );
        e.id = id;
        e.ty = ty.clone();
        e
    };
    Some(outer_if)
}

/// Rewrite `if (scrutinee is pattern) then T else F` to a pattern
/// Match on the scrutinee with pattern → T, _ → F. Binders in the
/// pattern flow naturally into the True arm's body.
fn rewrite_is_if_to_match<'src>(
    scrutinee: &AstExpr<'src>,
    pattern: &crate::ast::Pattern<'src>,
    arms: &[crate::ast::MatchArm<'src>],
    span: crate::ast::Span,
    id: crate::ast::ExprId,
    ty: &Type,
) -> Option<AstExpr<'src>> {
    use crate::ast::{ExprKind as AstK, MatchArm, Pattern as AstPat};
    if arms.len() != 2 {
        return None;
    }
    let true_arm = arms.iter().find(|a| matches!(&a.pattern, AstPat::Constructor { name: "True", .. }))?;
    let false_arm = arms.iter().find(|a| matches!(&a.pattern, AstPat::Constructor { name: "False", .. }))?;
    let body_t = true_arm.body.clone();
    let body_f = false_arm.body.clone();
    let mut rewritten = AstExpr::new(
        AstK::If {
            expr: Box::new(scrutinee.clone()),
            arms: vec![
                MatchArm {
                    pattern: pattern.clone(),
                    guards: vec![],
                    body: body_t,
                    is_return: false,
                },
                MatchArm {
                    pattern: AstPat::Wildcard,
                    guards: vec![],
                    body: body_f,
                    is_return: false,
                },
            ],
            else_body: None,
        },
        span,
    );
    rewritten.id = id;
    rewritten.ty = ty.clone();
    Some(rewritten)
}

fn is_stdlib_intrinsic(name: &str) -> bool {
    let base = name.split("__").next().unwrap_or(name);
    // True intrinsics: declared in `standard/list.ori` *without* a
    // body (the lowering is inline at this layer, not via a normal
    // SSA function call). `reverse` / `repeat` / `map` etc. have
    // bodies in stdlib that use the true intrinsics — those flow
    // through the regular App path.
    matches!(
        base,
        "List.len" | "List.get" | "List.append" | "List.set"
        | "List.range" | "List.walk" | "List.walk_until"
        | "crash"
    )
}

/// Lower unary numeric conversion builtins (`__builtin.to_u8`,
/// `__builtin.from_u8`, `__builtin.to_u64`, `__builtin.to_i64`,
/// `__builtin.to_bits`, `__builtin.from_bits`) to a Core `Cast`
/// expression.
///
/// `segments` is the QualifiedCall's segments (e.g. `["U32",
/// "from_u8"]` — the receiver type lives in `segments[0]`). For
/// MethodCall form, `segments` is empty and the receiver type is
/// inferred from the receiver expression's type instead.
///
/// `result_ty` is the call expression's result type — for `to_u8`,
/// `to_u64`, `to_i64`, and `from_bits`, the destination scalar is
/// determined by it. For `from_u8` the destination is read from
/// `segments[0]` (QualifiedCall) or from `result_ty` (either form).
/// For `to_bits` the destination is the matching unsigned width of
/// the source signed type (or `U64` for `F64`).
fn try_lower_unary_builtin(
    ctx: &mut LowerCtx<'_>,
    name: &str,
    segments: &[&str],
    args: &[crate::ast::Expr<'_>],
    result_ty: &Type,
) -> Result<Option<Vec<Expr>>, String> {
    use crate::ssa::ScalarType;
    let Some(op_name) = name.strip_prefix("__builtin.") else {
        return Ok(None);
    };
    if args.len() != 1 {
        return Ok(None);
    }
    let src = lower_expr(ctx, &args[0])?;
    // Pick the destination scalar based on the builtin's name +
    // available type info.
    let result_scalar = scalar_type_of(result_ty);
    let (dest_ty, bitcast) = match op_name {
        "to_u8" => (ScalarType::U8, false),
        "to_u64" => (ScalarType::U64, false),
        "to_i64" => (ScalarType::I64, false),
        "from_u8" => {
            // U32.from_u8 vs U64.from_u8 — destination determined by
            // result type (or by segments[0] if available).
            let dest = if let Some(t) = segments.first().and_then(|s| scalar_from_type_name(s)) {
                t
            } else {
                result_scalar.unwrap_or(ScalarType::U64)
            };
            (dest, false)
        }
        "to_bits" => {
            // Map signed → unsigned of same width; F64 → U64.
            let recv_name = segments.first().copied().unwrap_or("");
            let dest = match recv_name {
                "I8" => ScalarType::U8,
                "I16" => ScalarType::U16,
                "I32" => ScalarType::U32,
                "I64" | "F64" => ScalarType::U64,
                _ => result_scalar.unwrap_or(ScalarType::U64),
            };
            (dest, true)
        }
        "from_bits" => (ScalarType::F64, true),
        _ => return Ok(None),
    };
    Ok(Some(vec![Expr::Cast {
        src: Box::new(src),
        dest_ty,
        bitcast,
        ty: result_ty.clone(),
    }]))
}

/// Scalar from a type-name string (e.g. `"U32"` → `ScalarType::U32`).
/// Returns `None` for non-numeric type names.
fn scalar_from_type_name(name: &str) -> Option<crate::ssa::ScalarType> {
    use crate::ssa::ScalarType;
    Some(match name {
        "I8" => ScalarType::I8,
        "U8" => ScalarType::U8,
        "I16" => ScalarType::I16,
        "U16" => ScalarType::U16,
        "I32" => ScalarType::I32,
        "U32" => ScalarType::U32,
        "I64" => ScalarType::I64,
        "U64" => ScalarType::U64,
        "F64" => ScalarType::F64,
        _ => return None,
    })
}

/// Scalar from a `Type::Con(name)`. Returns `None` for non-Con or
/// non-numeric types.
fn scalar_type_of(ty: &Type) -> Option<crate::ssa::ScalarType> {
    match ty {
        Type::Con(name) => scalar_from_type_name(name),
        _ => None,
    }
}

/// Map a `__builtin.<op>` intrinsic name to its Core `BinOp` if it
/// corresponds to a 2-input scalar binop. Builtins that need
/// special-case lowering (`equals` over polymorphic types,
/// `compare` producing an Order tag union, etc.) return None and
/// fall through to the fallback path.
fn builtin_to_binop(name: &str) -> Option<crate::ssa::BinaryOp> {
    use crate::ssa::BinaryOp;
    Some(match name {
        "__builtin.add" => BinaryOp::Add,
        "__builtin.sub" => BinaryOp::Sub,
        "__builtin.mul" => BinaryOp::Mul,
        "__builtin.div" => BinaryOp::Div,
        "__builtin.mod" => BinaryOp::Rem,
        "__builtin.bit_and" => BinaryOp::And,
        "__builtin.bit_or" => BinaryOp::Or,
        "__builtin.bit_xor" => BinaryOp::Xor,
        "__builtin.shl" => BinaryOp::Shl,
        "__builtin.shr" => BinaryOp::Shr,
        _ => return None,
    })
}

/// Map an AST surface `BinOp` to its SSA `BinaryOp`. The two enums
/// were near-1:1 before bit_and/shl/shr entered Core via builtin
/// intrinsics; this is the canonical join point.
fn ast_binop_to_ssa(op: crate::ast::BinOp) -> crate::ssa::BinaryOp {
    use crate::ast::BinOp as A;
    use crate::ssa::BinaryOp as S;
    match op {
        A::Add => S::Add,
        A::Sub => S::Sub,
        A::Mul => S::Mul,
        A::Div => S::Div,
        A::Rem => S::Rem,
        A::BitOr => S::Or,
        A::BitXor => S::Xor,
        A::Eq => S::Eq,
        A::Neq => S::Neq,
        A::Lt => S::Lt,
        A::Gt => S::Gt,
        A::Le => S::Le,
        A::Ge => S::Ge,
        // And/Or are short-circuit booleans — desugared to Match
        // upstream of this mapping. Hitting them here is a bug.
        A::And | A::Or => unreachable!(
            "ast_binop_to_ssa: short-circuit boolean reached the scalar path"
        ),
    }
}

fn lower_call_args(
    ctx: &mut LowerCtx<'_>,
    _callee: &str,
    args: &[AstExpr<'_>],
) -> Result<Vec<Expr>, String> {
    let mut out = Vec::new();
    for a in args {
        let lowered = lower_expr_slots(ctx, a)?;
        let expected = expand_slots_with(
            &a.ty,
            &ctx.fieldless,
            &ctx.transparent,
            &ctx.payload_unions,
        );
        // Multi-slot single-Expr fan-out: when a multi-slot arg
        // (closure value, Result, Maybe, record-typed arg) lowers
        // to one Core Expr (e.g. a single Match or App), expand
        // it into per-slot Var references so the call's positional
        // arg list matches the callee's per-slot signature. See
        // `bind_multi_slot` for the shared-Let convention.
        if lowered.len() == 1 && expected.len() > 1 {
            out.extend(bind_multi_slot(ctx, lowered.into_iter().next().unwrap(), &expected, &a.ty));
        } else {
            out.extend(lowered);
        }
    }
    Ok(out)
}

fn lower_block<'src>(
    ctx: &mut LowerCtx<'_>,
    stmts: &[Stmt<'src>],
    last: &AstExpr<'src>,
) -> Result<Vec<Expr>, String> {
    // Desugar the first `Stmt::Guard` we hit into a 2-arm `If`:
    // True arm returns the guard's value (`is_return: true` →
    // short-circuit the enclosing function); False arm carries the
    // remaining statements + `last` as its body. Recursing with
    // the prefix-of-stmts + synthesized If as the new `last` lets
    // the normal block lowering run unchanged.
    if let Some(guard_idx) = stmts.iter().position(|s| matches!(s, Stmt::Guard { .. })) {
        let Stmt::Guard { condition, return_val } = &stmts[guard_idx] else {
            unreachable!("position matched Stmt::Guard");
        };
        let rest_stmts = stmts[guard_idx + 1..].to_vec();
        let rest_block = AstExpr {
            kind: ExprKind::Block(rest_stmts, Box::new(last.clone())),
            span: last.span,
            id: last.id,
            ty: last.ty.clone(),
        };
        let true_arm = crate::ast::MatchArm {
            pattern: crate::ast::Pattern::Constructor { name: "True", fields: vec![] },
            guards: vec![],
            body: return_val.clone(),
            is_return: true,
        };
        let false_arm = crate::ast::MatchArm {
            pattern: crate::ast::Pattern::Constructor { name: "False", fields: vec![] },
            guards: vec![],
            body: rest_block,
            is_return: false,
        };
        let if_expr = AstExpr {
            kind: ExprKind::If {
                expr: Box::new(condition.clone()),
                arms: vec![true_arm, false_arm],
                else_body: None,
            },
            span: condition.span,
            id: condition.id,
            ty: last.ty.clone(),
        };
        return lower_block(ctx, &stmts[..guard_idx], &if_expr);
    }

    // Lower stmts in source order so multi-slot bindings (records,
    // tuples, payload-union calls) register their slot syms in
    // `ctx.locals` before the body — or before subsequent stmts —
    // dereference them via `Name(p)`. The body lowers last so it
    // sees the full local table.
    let mut wrap_with_lets: Vec<(Vec<SymbolId>, Expr)> = Vec::new();
    let mut shadowed: Vec<(SymbolId, Option<Vec<SymbolId>>)> = Vec::new();
    for stmt in stmts {
        match stmt {
            Stmt::Let { name, val } => {
                let value_slots = lower_expr_slots(ctx, val)?;
                let expected_slot_count = expand_slots_with(&val.ty, &ctx.fieldless, &ctx.transparent, &ctx.payload_unions).len();

                if value_slots.len() == 1 && expected_slot_count == 1 {
                    // Scalar binding — bind to the AST sym directly.
                    // If `name` was previously mapped to multi-slot
                    // syms by an outer scope (e.g. shadowed by
                    // fold_lift's recursive-result Let inside a
                    // Match arm whose pattern bound `name` to a
                    // multi-slot inductive), drop the old mapping
                    // so subsequent `Name(name)` references the new
                    // single-slot value, not the old slot Vars.
                    if let Some(prev) = ctx.locals.remove(name) {
                        shadowed.push((*name, Some(prev)));
                    }
                    wrap_with_lets.push((
                        vec![*name],
                        value_slots.into_iter().next().unwrap(),
                    ));
                } else if value_slots.len() == expected_slot_count {
                    // Aggregate literal — N parallel single-binder Lets.
                    let slot_syms = mint_slot_syms(ctx, *name, expected_slot_count);
                    shadowed.push((*name, ctx.locals.insert(*name, slot_syms.clone())));
                    for (sym, val) in slot_syms.into_iter().zip(value_slots) {
                        wrap_with_lets.push((vec![sym], val));
                    }
                } else if value_slots.len() == 1 && expected_slot_count > 1 {
                    // One Core Expr producing N slots (multi-result
                    // Call, payload Con) — single multi-binder Let.
                    let slot_syms = mint_slot_syms(ctx, *name, expected_slot_count);
                    shadowed.push((*name, ctx.locals.insert(*name, slot_syms.clone())));
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

    let body_slots = lower_expr_slots(ctx, last)?;

    // Restore outer scope's `ctx.locals` entries shadowed by this
    // block's bindings. The Lets we wrap with preserve the names for
    // the SSA layer; we only need to undo our changes to the lookup
    // table so siblings of this block don't see our slot syms.
    for (name, prev) in shadowed.into_iter().rev() {
        match prev {
            Some(p) => { ctx.locals.insert(name, p); }
            None => { ctx.locals.remove(&name); }
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
    // For Record patterns, reorder sub-patterns to match the
    // record's sorted-by-field-name slot order (expand_slots'
    // canonical order). Each pattern field's sub-pattern is the
    // binder for that slot.
    let owned_sub_pats: Vec<AstPattern<'_>>;
    let sub_pats: &[AstPattern<'_>] = match pattern {
        AstPattern::Tuple(ps) => ps,
        AstPattern::Record { fields, .. } => {
            // Resolve val's record type to get the canonical field
            // order (sorted alphabetically per expand_slots).
            let resolved = resolve_transparent(&val.ty, &ctx.transparent);
            let record_fields = match &resolved {
                Type::Record { fields: rf, .. } => rf.clone(),
                _ => {
                    return Err(format!(
                        "core::lower_destructure: Record pattern but val type isn't Record: {:?}",
                        val.ty
                    ));
                }
            };
            let mut sorted_fields: Vec<&str> = record_fields.iter().map(|(n, _)| n.as_str()).collect();
            sorted_fields.sort();
            // For each slot (in sorted order), find the pattern's
            // entry for that field, or insert Wildcard if absent.
            let mut ordered: Vec<AstPattern<'_>> = Vec::with_capacity(sorted_fields.len());
            for &slot_name in &sorted_fields {
                let entry = fields
                    .iter()
                    .find(|(fsym, _)| ctx.fields.get(*fsym) == slot_name)
                    .map(|(_, p)| p.clone())
                    .unwrap_or(AstPattern::Wildcard);
                ordered.push(entry);
            }
            owned_sub_pats = ordered;
            &owned_sub_pats
        }
        other => return Err(format!(
            "core::lower_destructure: unsupported pattern shape: {other:?}"
        )),
    };
    // Each sub-pattern must resolve to Binding or Wildcard at every
    // leaf. Wildcards get a sentinel SymbolId (`u32::MAX`). Nested
    // Tuple sub-patterns (e.g. `((a, b), (c, d)) = t`) flatten
    // recursively into a single binder list — the value's slot list
    // is already flat (SROA), so this mirrors that shape.
    fn flatten_sub_pats(pat: &AstPattern<'_>, out: &mut Vec<SymbolId>) -> Result<(), String> {
        match pat {
            AstPattern::Binding(sym) => { out.push(*sym); Ok(()) }
            AstPattern::Wildcard => { out.push(SymbolId(u32::MAX)); Ok(()) }
            AstPattern::Tuple(ps) => {
                for p in ps {
                    flatten_sub_pats(p, out)?;
                }
                Ok(())
            }
            other => Err(format!(
                "core::lower_destructure: only top-level Binding/Wildcard sub-patterns supported, got {other:?}"
            )),
        }
    }
    let mut binders: Vec<SymbolId> = Vec::new();
    for p in sub_pats {
        flatten_sub_pats(p, &mut binders)?;
    }
    if binders.len() != expected_slot_count {
        return Err(format!(
            "core::lower_destructure: Tuple pattern flattens to {} binders but value type expands to {} slots",
            binders.len(),
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

/// Bind a single multi-slot Core expression to N fresh slot symbols
/// via a `Let`, returning N `Var` references — one per slot. Each
/// returned `Var` carries the same shared `Let` wrapper, so when
/// `to_ssa::lower_slots` processes the slot list it lowers the
/// value ONCE (the first Var's Let-value evaluation registers the
/// slot syms in `ctx.locals`; subsequent Vars hit the registered
/// syms). Used by `Record` / `Tuple` / call-arg sites that
/// concatenate per-field slot lists when a field's expression is a
/// multi-slot operation (App, ListAppend, Cata) producing a single
/// Core node.
/// Walk `scheme_ret` and the monomorphic `mono_ty` in parallel,
/// pairing each `Type::Var` with the concrete `Type` at the same
/// position. Used by pattern lowering to monomorphize per-field
/// types from a polymorphic constructor scheme.
fn collect_pattern_subst(
    scheme_ret: &Type,
    mono_ty: &Type,
) -> Vec<(crate::types::engine::TypeVar, Type)> {
    let mut out: Vec<(crate::types::engine::TypeVar, Type)> = Vec::new();
    walk_pattern_subst(scheme_ret, mono_ty, &mut out);
    out
}

fn walk_pattern_subst(
    scheme: &Type,
    mono: &Type,
    out: &mut Vec<(crate::types::engine::TypeVar, Type)>,
) {
    match (scheme, mono) {
        (Type::Var(v), _) => out.push((*v, mono.clone())),
        (Type::App(_, a), Type::App(_, b)) | (Type::Tuple(a), Type::Tuple(b)) => {
            for (sa, mb) in a.iter().zip(b.iter()) {
                walk_pattern_subst(sa, mb, out);
            }
        }
        (Type::Arrow(ap, ar, _), Type::Arrow(bp, br, _)) => {
            for (sa, mb) in ap.iter().zip(bp.iter()) {
                walk_pattern_subst(sa, mb, out);
            }
            walk_pattern_subst(ar, br, out);
        }
        _ => {}
    }
}

fn apply_pattern_subst(
    ty: &Type,
    subst: &[(crate::types::engine::TypeVar, Type)],
) -> Type {
    let mut result = ty.clone();
    for (v, t) in subst {
        result = crate::passes::decl_info::substitute_type_var(&result, *v, t);
    }
    result
}

/// Lower an AST expression as a slot list, ensuring the result has
/// `expand_slots(ast.ty)` entries. If the natural lowering produces
/// a single Core Expr whose type is multi-slot (App, ListLit, Match,
/// nested Con returning a payload union, etc.), fan it out into per-
/// slot `Var` references via `bind_multi_slot` — one shared `Let`
/// binds N slot syms to the value, each entry references one sym.
/// `to_ssa`'s `bind_cache` ensures the value lowers exactly once.
pub fn lower_expr_slots_expanded(
    ctx: &mut LowerCtx<'_>,
    ast: &AstExpr<'_>,
) -> Result<Vec<Expr>, String> {
    let lowered = lower_expr_slots(ctx, ast)?;
    let expected = expand_slots_with(
        &ast.ty,
        &ctx.fieldless,
        &ctx.transparent,
        &ctx.payload_unions,
    );
    if lowered.len() == 1 && expected.len() > 1 {
        Ok(bind_multi_slot(
            ctx,
            lowered.into_iter().next().unwrap(),
            &expected,
            &ast.ty,
        ))
    } else {
        Ok(lowered)
    }
}

fn bind_multi_slot(
    ctx: &mut LowerCtx<'_>,
    value: Expr,
    slot_tys: &[ScalarType],
    value_ty: &Type,
) -> Vec<Expr> {
    use crate::symbol::SymbolKind;
    let span = crate::ast::Span { file: crate::source::FileId(0), start: 0, end: 0 };
    let slot_syms: Vec<SymbolId> = (0..slot_tys.len())
        .map(|i| ctx.symbols.fresh(format!("__rec_slot_{i}"), span, SymbolKind::Func))
        .collect();
    slot_syms
        .iter()
        .enumerate()
        .map(|(i, &sym)| Expr::Let {
            binders: slot_syms.clone(),
            value: Box::new(value.clone()),
            body: Box::new(Expr::Var {
                sym,
                ty: type_for_scalar(slot_tys[i]),
            }),
            ty: value_ty.clone(),
        })
        .collect()
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
    // `List(T)` (and `Str = List(U8)` via the transparent table)
    // decompose to (len: U64, cap: U64, data: RcPtr) at every
    // layer — the canonical SROA shape. Functions take and return
    // the slot trio; payload Cons store the trio inline; pattern
    // binders bind three SSA values. The only place the trio
    // collapses back into a single RcPtr header is the `__main`
    // ABI boundary, where it's an explicit materialization.
    if let Type::App(name, _) = &unwrapped {
        if name == "List" {
            return vec![ScalarType::U64, ScalarType::U64, ScalarType::RcPtr];
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

fn lower_match_arm(
    ctx: &mut LowerCtx<'_>,
    arm: &AstMatchArm<'_>,
    scrutinee_ty: &Type,
) -> Result<MatchArm, String> {
    let mut pattern = lower_pattern(&arm.pattern)?;

    // For each constructor binder whose source type expands to
    // multiple slots, mint slot syms and register them in
    // `ctx.locals` so `Name(binder)` in the arm body expands to the
    // per-slot Vars. Wildcards (sym = u32::MAX) skip the lookup.
    // Single-slot binders keep their AST sym — no minting needed.
    //
    // The scheme's `field_tys` may be polymorphic (e.g. `Err : b ->
    // Result(a, b)`); we substitute against the scrutinee_ty so the
    // monomorphic slot count is used. Without this, `Var(b)` falls
    // back to 1 slot (the default RcPtr) and we miss the case
    // where the Err payload is multi-slot like `Str` or `List(I64)`.
    let mut shadowed: Vec<(SymbolId, Option<Vec<SymbolId>>)> = Vec::new();
    if let Pattern::Constructor { tag, binders } = &mut pattern {
        let scheme_subst: Vec<(crate::types::engine::TypeVar, Type)> = ctx
            .constructor_return_types
            .get(tag)
            .map(|scheme_ret| collect_pattern_subst(scheme_ret, scrutinee_ty))
            .unwrap_or_default();
        if let Some(field_tys) = ctx.constructor_field_types.get(tag).cloned() {
            for (i, binder_slots) in binders.iter_mut().enumerate() {
                if i >= field_tys.len() {
                    break;
                }
                if binder_slots.len() != 1 {
                    continue;
                }
                let field_ty = apply_pattern_subst(&field_tys[i], &scheme_subst);
                let slot_tys = expand_slots_with(
                    &field_ty,
                    &ctx.fieldless,
                    &ctx.transparent,
                    &ctx.payload_unions,
                );
                if slot_tys.len() <= 1 {
                    continue;
                }
                if binder_slots[0].0 == u32::MAX {
                    // Wildcard binder over a multi-slot field —
                    // expand to N wildcard sentinels so the
                    // pattern's binder count matches the field's
                    // slot count (to_ssa's binder loader walks them
                    // in parallel with `slot_tys`).
                    *binder_slots = vec![SymbolId(u32::MAX); slot_tys.len()];
                    continue;
                }
                let ast_sym = binder_slots[0];
                let slot_syms = mint_slot_syms(ctx, ast_sym, slot_tys.len());
                shadowed.push((ast_sym, ctx.locals.insert(ast_sym, slot_syms.clone())));
                *binder_slots = slot_syms;
            }
        }
    }

    // Guards and body lower in the arm's scope (so they can see the
    // pattern binders). Each guard is a Bool-typed expression that
    // must evaluate to True for the arm to fire; to_ssa chains them
    // as branches that fall through to subsequent arms on False.
    let guards: Vec<Expr> = arm
        .guards
        .iter()
        .map(|g| lower_expr(ctx, g))
        .collect::<Result<_, _>>()?;
    let body = lower_expr_slots(ctx, &arm.body)?;

    // Restore the outer scope's `ctx.locals` so sibling arms don't
    // see this arm's slot syms. The Pattern still carries them so
    // to_ssa can load values at the right offsets.
    for (sym, prev) in shadowed.into_iter().rev() {
        match prev {
            Some(p) => { ctx.locals.insert(sym, p); }
            None => { ctx.locals.remove(&sym); }
        }
    }

    Ok(MatchArm { pattern, guards, body, is_return: arm.is_return })
}

fn lower_pattern(pat: &AstPattern<'_>) -> Result<Pattern, String> {
    match pat {
        AstPattern::Constructor { name, fields } => {
            let mut binders: Vec<Vec<SymbolId>> = Vec::with_capacity(fields.len());
            for f in fields {
                match f {
                    AstPattern::Binding(sym) => binders.push(vec![*sym]),
                    AstPattern::Wildcard => {
                        binders.push(vec![SymbolId(u32::MAX)]);
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
