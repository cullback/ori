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

use super::lower::{expand_slots_with, lower_expr_slots, LowerCtx, TransparentTable};
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

    // Lambda-set synth closure types (`__Closure_xxx`) are TagUnion
    // TypeAnnos in module.decls but their tags (`__lambda_N`) are
    // *not* in `constructor_schemes`. Harvest their return-type
    // shape directly so Name→Con can stamp the correct TagUnion
    // for closure values. Restrict to synth `__` prefixes to avoid
    // overriding the inference-recorded shapes for user-declared
    // tag unions (those carry App/Con references with type-param
    // arguments that the trivial TypeExpr→Type projection here
    // would drop).
    let mut synth_con_return_types: std::collections::HashMap<String, Type> =
        std::collections::HashMap::new();
    for decl in &mono.module.decls {
        if let Decl::TypeAnno {
            name,
            ty: crate::ast::TypeExpr::TagUnion(tags, _),
            ..
        } = decl
        {
            let union_name = mono.symbols.display(*name).to_owned();
            if !union_name.starts_with("__") {
                continue;
            }
            let tagged: Vec<(String, Vec<Type>)> = tags
                .iter()
                .map(|t| {
                    let fs: Vec<Type> = t.fields.iter().map(type_expr_to_type).collect();
                    (t.name.to_string(), fs)
                })
                .collect();
            let union_ty = Type::TagUnion { tags: tagged.clone(), rest: None };
            for (tag_name, _) in &tagged {
                synth_con_return_types
                    .entry(tag_name.clone())
                    .or_insert_with(|| union_ty.clone());
            }
        }
    }

    let mut builder = Builder::new();

    // Build transparent table from infer (clone the relevant subset
    // — InferResult.transparent has the right shape already).
    let mut transparent: TransparentTable = mono.infer.transparent.clone();
    // Push synth `__Closure_*` types and source-level `: alias`
    // TagUnion declarations into the transparent table.
    //
    // `__Closure_*` types come from the lambda passes' `Decl::TypeAnno`
    // synthesis but never reach `infer.transparent` — without unfolding,
    // `expand_slots(Con("__Closure_..."))` falls through to a heap-ptr
    // default and the `__apply_*` dispatcher's closure param gets a
    // single RcPtr instead of the fanned-out captures.
    //
    // `: alias` declarations (`Pair : [MkPair(I64, I64)]`) similarly
    // stay as `Type::Con("Pair")` at use sites — inference doesn't
    // eagerly substitute them. Adding them to `transparent` makes
    // `expand_slots` and friends see the underlying TagUnion shape,
    // which is required for matches like `if pair : MkPair(a, b) then …`
    // to recognize the scrutinee as a single-variant Phase-E fanout.
    for decl in &mono.module.decls {
        if let Decl::TypeAnno {
            name,
            ty: crate::ast::TypeExpr::TagUnion(tags, _),
            kind,
            ..
        } = decl
        {
            use crate::ast::TypeDeclKind;
            let union_name = mono.symbols.display(*name).to_owned();
            // Only `:` aliases and synth `__` types — `:=` is already
            // in `infer.transparent`, and `::` is opaque on purpose.
            let synth = union_name.starts_with("__");
            let alias = matches!(kind, TypeDeclKind::Alias);
            if !synth && !alias {
                continue;
            }
            let tagged: Vec<(String, Vec<Type>)> = tags
                .iter()
                .map(|t| {
                    let fs: Vec<Type> = t.fields.iter().map(type_expr_to_type).collect();
                    (t.name.to_string(), fs)
                })
                .collect();
            transparent
                .entry(union_name)
                .or_insert((vec![], Type::TagUnion { tags: tagged, rest: None }));
        }
    }

    // Build a map: union name → (variant count, any-payload-carrying).
    // The "payload_unions" set we expose is the subset that's
    // multi-variant AND has at least one payload-carrying constructor.
    // Single-variant unions (like `Wrapped(I64)`) are not treated as
    // (tag, payload) — their expand_slots fans out the variant's
    // fields directly per existing-lower's convention.
    let mut by_union: std::collections::HashMap<String, (usize, bool)> = std::collections::HashMap::new();
    for (con_name, meta) in &decls.constructors {
        if let Some(scheme) = decls.constructor_schemes.get(con_name) {
            let ret_ty = match &scheme.ty {
                Type::Arrow(_, ret, _) => ret.as_ref(),
                other => other,
            };
            if let Some(name) = union_name_of(ret_ty) {
                let entry = by_union.entry(name).or_insert((0, false));
                entry.0 += 1;
                if meta.max_fields > 0 { entry.1 = true; }
            }
        }
    }
    let mut payload_unions: std::collections::HashSet<String> = by_union
        .into_iter()
        .filter_map(|(name, (count, has_payload))| {
            if count > 1 && has_payload { Some(name) } else { None }
        })
        .collect();
    // Synth closure types (`__Closure_xxx`) declared by the lambda
    // passes aren't in `decl_info.constructors` because the
    // constructors are registered after inference. Walk the
    // TagUnion TypeAnnos directly so multi-variant payload-carrying
    // lambda sets land in `payload_unions` and `expand_slots` picks
    // them up as (tag, payload) — without this the __apply
    // dispatchers see their closure params as a bare discriminant.
    for decl in &mono.module.decls {
        if let Decl::TypeAnno {
            name,
            ty: crate::ast::TypeExpr::TagUnion(tags, _),
            ..
        } = decl
        {
            let union_name = mono.symbols.display(*name).to_owned();
            if !union_name.starts_with("__") {
                continue;
            }
            if tags.len() > 1 && tags.iter().any(|t| !t.fields.is_empty()) {
                payload_unions.insert(union_name);
            }
        }
    }

    for (name, params, body) in funcs {
        let name_str = mono.symbols.display(name).to_owned();
        // `main` is the ABI boundary to the Rust eval driver: its
        // params and return stay single-slot (RcPtr for aggregates),
        // matching existing-lower's __main convention. Multi-slot
        // expansion only applies inside user-to-user calls.
        let is_main = name_str == "main";

        // Per-param slot expansion from the function's declared
        // scheme. Synth functions without schemes default to single
        // RcPtr per source param.
        let param_payload_unions = if is_main { std::collections::HashSet::new() } else { payload_unions.clone() };
        let per_param_slots = param_slot_types(mono, &name_str, &params, &decls.fieldless_tags, &transparent, &param_payload_unions);

        // Add SSA function params + build locals for both passes.
        // - to_ssa_locals: SymbolId → SSA Value (used by Core→SSA).
        // - core_locals: SymbolId → slot SymbolIds (used by AST→Core
        //   when an AST Name needs to expand to multi-slot Vars).
        let mut to_ssa_locals: HashMap<SymbolId, Vec<Value>> = HashMap::new();
        let mut core_locals: HashMap<SymbolId, Vec<SymbolId>> = HashMap::new();
        // For __main's List params: the eval driver and CLI pass
        // one RcPtr header per arg, so the SSA param stays a single
        // RcPtr. Inside the body Core sees Lists as 3 slots, so we
        // need to emit `Load`s at the header's (0, 8, 16) byte
        // offsets in the entry block and bind the param sym to the
        // 3 minted slot syms. Track which params need this
        // boundary-unpacking; emit after entry is created.
        struct UnpackedListParam {
            param_sym: SymbolId,
            header_val: Value,
            slot_tys: Vec<ScalarType>,
        }
        let mut unpacked_lists: Vec<UnpackedListParam> = Vec::new();
        if is_main {
            // Look up each source param's declared type; if it's a
            // List trio, override slot_tys to a single RcPtr and
            // record the boundary unpack for later.
            let scheme_param_tys: Vec<Type> = mono
                .infer
                .func_schemes
                .get(&name_str)
                .and_then(|s| match &s.ty {
                    Type::Arrow(ps, _, _) => Some(ps.clone()),
                    _ => None,
                })
                .unwrap_or_default();
            for (i, (param_sym, slot_tys)) in params.iter().zip(&per_param_slots).enumerate() {
                let is_list_param = scheme_param_tys
                    .get(i)
                    .map(|t| is_list_trio(t, &transparent))
                    .unwrap_or(false);
                if is_list_param && slot_tys.len() == 3 {
                    // ABI: take one RcPtr header. Body: 3 slot syms.
                    let header_val = builder.add_func_param(ScalarType::RcPtr);
                    unpacked_lists.push(UnpackedListParam {
                        param_sym: *param_sym,
                        header_val,
                        slot_tys: slot_tys.clone(),
                    });
                } else {
                    add_function_param(
                        &mut builder,
                        mono,
                        *param_sym,
                        slot_tys,
                        &mut to_ssa_locals,
                        &mut core_locals,
                    );
                }
            }
        } else {
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
        }

        let entry = builder.create_block();
        builder.switch_to(entry);

        // Emit the header→trio unpacking for any __main List
        // params we recorded above. Three loads per param at the
        // canonical (0, 8, 16) byte offsets. Skip the unpack if
        // the body doesn't reference the param — the loads would
        // auto-rc the slots and force rc_dec balancing for values
        // nothing uses, which existing-lower avoids by never
        // emitting them in the first place. If we unpack, the
        // body uses are the only justification for the extra RC
        // traffic.
        for up in &unpacked_lists {
            if !body_uses_sym(&body, up.param_sym) {
                // Param header binds as a single RcPtr — no slot
                // unpacking. The body never references it; rc_emit
                // releases the param at the function boundary.
                to_ssa_locals.insert(up.param_sym, vec![up.header_val]);
                continue;
            }
            let base_name = mono.symbols.display(up.param_sym).to_owned();
            let span = mono.symbols.get(up.param_sym).span;
            let slot_syms: Vec<SymbolId> = (0..up.slot_tys.len())
                .map(|i| mono.symbols.fresh(format!("{base_name}.{i}"), span, SymbolKind::Func))
                .collect();
            for (i, (&sym, &ty)) in slot_syms.iter().zip(&up.slot_tys).enumerate() {
                let v = builder.load(up.header_val, i * 8, ty);
                to_ssa_locals.insert(sym, vec![v]);
            }
            core_locals.insert(up.param_sym, slot_syms);
        }

        // AST → Core (mut borrows mono.symbols).
        let core_body = {
            let mut ctx = LowerCtx::new(fields, &mut mono.symbols);
            ctx.fieldless = decls.fieldless_tags.clone();
            ctx.transparent = transparent.clone();
            ctx.constructors = decls.constructors.keys().cloned().collect();
            ctx.constructor_field_types = decls
                .constructor_schemes
                .iter()
                .filter_map(|(name, s)| match &s.ty {
                    Type::Arrow(ps, _, _) => Some((name.clone(), ps.clone())),
                    _ => None,
                })
                .collect();
            ctx.constructor_return_types = decls
                .constructor_schemes
                .iter()
                .map(|(name, s)| {
                    let ret = match &s.ty {
                        Type::Arrow(_, r, _) => (**r).clone(),
                        other => other.clone(),
                    };
                    (name.clone(), ret)
                })
                .collect();
            // Lambda-set synth constructors aren't in
            // constructor_schemes — pick them up from the
            // module-level TypeAnno harvest above so Con-from-Name
            // can stamp the proper TagUnion type.
            for (k, v) in &synth_con_return_types {
                ctx.constructor_return_types
                    .entry(k.clone())
                    .or_insert_with(|| v.clone());
            }
            ctx.payload_unions = payload_unions.clone();
            ctx.tag_targets = decls
                .tag_targets
                .iter()
                .map(|(k, v)| (k.clone(), v.target_func.clone()))
                .collect();
            ctx.funcs = decls.funcs.clone();
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
                payload_unions: payload_unions.clone(),
                bind_cache: std::collections::HashMap::new(),
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
        let ret_payload_unions = if is_main { std::collections::HashSet::new() } else { payload_unions.clone() };
        let ret_slots_natural = expand_slots_with(&body.ty, &decls.fieldless_tags, &transparent, &ret_payload_unions);
        // __main's ABI: a List return collapses to a single RcPtr
        // header. The body still produces (len, cap, data) — the
        // shell-materialize reconciliation below packs the trio
        // into an alloc'd header and returns one pointer.
        let ret_slots = if is_main && is_list_trio(&body.ty, &transparent) {
            vec![ScalarType::RcPtr]
        } else {
            ret_slots_natural
        };
        let result_vals = if result_vals.len() == ret_slots.len() {
            result_vals
        } else if ret_slots.len() == 1 && result_vals.len() > 1 {
            // Body produced multi-slot but the function's return
            // type is single-slot — materialize into an RcPtr shell.
            let shell = builder.alloc(result_vals.len() * 8);
            for (i, v) in result_vals.iter().enumerate() {
                builder.store(shell, i * 8, *v);
            }
            vec![shell]
        } else if result_vals.len() == 1 && ret_slots.len() > 1 {
            // Body produced a single RcPtr shell (typically because
            // the Core::Match lowering merges arms through a
            // single-slot block param) but the function's return
            // shape is multi-slot. Unbox by loading N values from
            // the shell at consecutive offsets, typed per ret_slots.
            let shell = result_vals[0];
            ret_slots
                .iter()
                .enumerate()
                .map(|(i, &ty)| builder.load(shell, i * 8, ty))
                .collect()
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

    let module = builder.build("__main");

    // Post-build sanity check: every `Call` must pass exactly as
    // many args as the callee has params. Mismatches here surface
    // higher-order lowering bugs (e.g. Core not expanding a
    // closure-shaped param into its (tag, payload) slot pair)
    // that downstream passes only catch post-inline. Bail
    // explicitly so the fallback is taken at boundary time
    // instead of panicking in `opt::inline`.
    for (fname, func) in &module.functions {
        let blocks: Vec<_> = func.blocks.values().collect();
        for block in &blocks {
            for inst in &block.insts {
                if let crate::ssa::Inst::Call { target: callee, args, .. } = inst {
                    if let Some(callee_func) = module.functions.get(callee) {
                        if callee_func.params.len() != args.len() {
                            return Err(format!(
                                "function `{fname}`: call to `{callee}` has {} args but callee declares {} params",
                                args.len(), callee_func.params.len()
                            ));
                        }
                    }
                }
            }
        }
    }

    Ok(module)
}

/// Resolve a function's per-param slot type expansion. Reads
/// `infer.func_schemes` (authoritative for declared functions);
/// falls back to one RcPtr per source param for synth functions
/// without schemes.
/// Minimal `TypeExpr` → `Type` projection sufficient for the
/// constructor-return-type harvest. We only need to handle the
/// shapes that appear in synth lambda type annotations: `Named`
/// (closure capture types, today always `I64`) and `App` (parametric
/// references). Anything else degrades to `Type::Con("__unknown")`
/// — downstream uses this only for `union_name_of` / `expand_slots`
/// shape queries, so a placeholder is safe.
fn type_expr_to_type(t: &crate::ast::TypeExpr<'_>) -> Type {
    use crate::ast::TypeExpr;
    match t {
        TypeExpr::Named(name) => Type::Con((*name).to_owned()),
        TypeExpr::App(name, args) => {
            Type::App((*name).to_owned(), args.iter().map(type_expr_to_type).collect())
        }
        TypeExpr::Tuple(elems) => Type::Tuple(elems.iter().map(type_expr_to_type).collect()),
        _ => Type::Con("__unknown".to_owned()),
    }
}

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
    payload_unions: &std::collections::HashSet<String>,
) -> Vec<Vec<ScalarType>> {
    // HO params still carry `Type::Arrow` in the scheme — Arrow
    // expands to 1 RcPtr slot via the default path below, which
    // keeps callee+caller consistent. existing-lower handles HO
    // values via shell-wrap materialization (`to_slots`'
    // Multi→Single).
    let _ = mono;
    mono.infer
        .func_schemes
        .get(name_str)
        .map(|s| match &s.ty {
            Type::Arrow(ps, _, _) => ps
                .iter()
                .map(|t| expand_slots_with(t, fieldless, transparent, payload_unions))
                .collect(),
            _ => vec![vec![ScalarType::RcPtr]; params.len()],
        })
        .unwrap_or_else(|| vec![vec![ScalarType::RcPtr]; params.len()])
}

/// True if `ty` resolves (via transparent unfolding) to a
/// `List(T)`-shaped reference — used by `__main`'s ABI boundary
/// to collapse the 3-slot (len, cap, data) trio back to a single
/// RcPtr header for the eval driver / CLI's calling convention.
/// Walk `body` looking for any `ExprKind::Name(target)` reference.
/// Used by the __main ABI carve-out to decide whether unpacking a
/// header into its slot trio is worth the loads — if the body
/// doesn't touch the param, we'd just be emitting auto-rc'd loads
/// that nothing reads and rc_dec'ing them at function end.
fn body_uses_sym(body: &AstExpr<'_>, target: SymbolId) -> bool {
    use crate::ast::{ExprKind, Pattern, Stmt};
    fn walk_expr(e: &AstExpr<'_>, t: SymbolId) -> bool {
        match &e.kind {
            ExprKind::Name(s) => *s == t,
            ExprKind::IntLit(_) | ExprKind::FloatLit(_) | ExprKind::StrLit(_) => false,
            ExprKind::BinOp { lhs, rhs, .. } => walk_expr(lhs, t) || walk_expr(rhs, t),
            ExprKind::Call { args, .. } => args.iter().any(|a| walk_expr(a, t)),
            ExprKind::QualifiedCall { args, .. } => args.iter().any(|a| walk_expr(a, t)),
            ExprKind::MethodCall { receiver, args, .. } => {
                walk_expr(receiver, t) || args.iter().any(|a| walk_expr(a, t))
            }
            ExprKind::Tuple(elems) | ExprKind::ListLit(elems) => {
                elems.iter().any(|a| walk_expr(a, t))
            }
            ExprKind::Record { fields } => fields.iter().any(|(_, e)| walk_expr(e, t)),
            ExprKind::RecordUpdate { base, updates } => {
                walk_expr(base, t) || updates.iter().any(|(_, e)| walk_expr(e, t))
            }
            ExprKind::FieldAccess { record, .. } => walk_expr(record, t),
            ExprKind::Is { expr, .. } => walk_expr(expr, t),
            ExprKind::If { expr, arms, else_body } => {
                walk_expr(expr, t)
                    || arms.iter().any(|a| walk_expr(&a.body, t) || a.guards.iter().any(|g| walk_expr(g, t)))
                    || else_body.as_ref().map(|b| walk_expr(b, t)).unwrap_or(false)
            }
            ExprKind::Fold { expr, arms } => {
                walk_expr(expr, t)
                    || arms.iter().any(|a| walk_expr(&a.body, t) || a.guards.iter().any(|g| walk_expr(g, t)))
            }
            ExprKind::Block(stmts, last) => {
                stmts.iter().any(|s| walk_stmt(s, t)) || walk_expr(last, t)
            }
            ExprKind::Lambda { .. } => {
                unreachable!("lift_pre_infer removes all Lambda nodes before Core lowering")
            }
            ExprKind::Closure { captures, .. } => captures.iter().any(|c| walk_expr(c, t)),
        }
    }
    fn walk_stmt(s: &Stmt<'_>, t: SymbolId) -> bool {
        match s {
            Stmt::Let { val, .. } => walk_expr(val, t),
            Stmt::Destructure { val, .. } => walk_expr(val, t),
            Stmt::Guard { condition, return_val } => {
                walk_expr(condition, t) || walk_expr(return_val, t)
            }
            Stmt::TypeHint { .. } => false,
        }
    }
    let _ = Pattern::Wildcard;
    walk_expr(body, target)
}

fn is_list_trio(ty: &Type, transparent: &TransparentTable) -> bool {
    use crate::passes::core::lower::resolve_transparent;
    matches!(resolve_transparent(ty, transparent), Type::App(ref name, _) if name == "List")
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
    to_ssa_locals: &mut HashMap<SymbolId, Vec<Value>>,
    core_locals: &mut HashMap<SymbolId, Vec<SymbolId>>,
) {
    if slot_tys.len() == 1 {
        let v = builder.add_func_param(slot_tys[0]);
        to_ssa_locals.insert(param_sym, vec![v]);
    } else {
        let base_name = mono.symbols.display(param_sym).to_owned();
        let span = mono.symbols.get(param_sym).span;
        let slot_syms: Vec<SymbolId> = (0..slot_tys.len())
            .map(|i| mono.symbols.fresh(format!("{base_name}.{i}"), span, SymbolKind::Func))
            .collect();
        for (sym, &ty) in slot_syms.iter().zip(slot_tys) {
            let v = builder.add_func_param(ty);
            to_ssa_locals.insert(*sym, vec![v]);
        }
        core_locals.insert(param_sym, slot_syms);
    }
}
