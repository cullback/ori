//! AST → SSA lowering.
//!
//! The single entry into the SSA pipeline. Walks each monomorphized
//! `FuncDef`, emitting straight-line SSA per body via the `Builder`.
//! Match compilation, intrinsic dispatch, constructor layout, and
//! built-in list operations are all handled here — no separate
//! method-resolution or layout pass downstream.
//!
//! ## How
//!
//! Per `ExprKind`, dispatch to an emitter that writes instructions
//! through `Builder`. Two side tables shape the output:
//! - `self.vars: HashMap<SymbolId, LoweredValue>` — the live local
//!   map for the current block. Updated as let-bindings introduce
//!   names. Bindings are `Single(v)` for scalars and (legacy)
//!   heap-pointer aggregates; `Multi(vs)` for tuples/records that
//!   decompose to N parallel slot Values.
//! - `decl_info::DeclInfo` — constructor layouts, function arities
//!   and return types, recursive-field flags.
//!
//! `if`/`match` arms each create their own blocks via `Builder`. Lower
//! threads the *scrutinee* through arm-block params explicitly, but
//! does **not** thread other locals — those are emitted as direct SSA
//! references to upstream block-local values. `ssa_construct` repairs
//! this immediately afterwards.
//!
//! ## Input invariants
//!
//! - `Module` is monomorphized (no type variables remain).
//! - Lambdas have been lifted and specialized — every `Call` has a
//!   known first-order target.
//! - Patterns are flattened — no nested constructor patterns, no
//!   `Pattern::List`.
//! - Folds are eliminated — every `Fold` is now a synthesized
//!   `__fold_N` helper.
//! - Reachability has been pruned — no orphan decls.
//!
//! ## Output invariants
//!
//! - One `ssa::Function` per `FuncDef`; one `ssa::Module` overall.
//! - Every SSA `Value` carries its `ScalarType` at creation.
//! - **Cross-block references via implicit scoping are permitted.**
//!   `ssa_construct` is the next pass and is responsible for
//!   establishing the explicit-block-params invariant.
//!
//! ## Notes
//!
//! - `__apply_K` dispatchers from `lambda_specialize` and `__list_*`
//!   intrinsics are referenced by name; lowering emits direct `Call`
//!   instructions for them.
//! - The interpreter (`eval.rs`) tolerates the implicit-scoping
//!   output via its flat register file, so dropping `ssa_construct`
//!   wouldn't surface as test failures — it'd surface as bugs in
//!   passes that trust the documented invariant.

pub mod boolean;
pub mod call;
pub mod constructor;
pub mod elim_dead_allocs;
pub mod eq;
pub mod hash;
pub mod lowered_value;
pub mod numeric;
pub mod rc_emit;
pub mod ssa_form;
pub mod pattern;
pub mod walk;

use std::collections::{HashMap, HashSet};

use crate::ast::{self, BinOp, Decl, Expr, ExprKind, Stmt};
use crate::passes::decl_info::{self, DeclInfo, method_key, resolve_scalar_type};
use crate::passes::mono::Monomorphized;
use crate::error::CompileError;
use crate::ssa::Module;
use crate::ssa::builder::Builder;
use crate::ssa::instruction::{BinaryOp, ScalarType, Value};
use crate::symbol::{FieldInterner, SymbolId, SymbolTable};
use crate::types::engine::{Type, TypeVar};
use crate::types::infer::InferResult;

use self::lowered_value::LoweredValue;

/// Lower a monomorphized AST module to SSA IR.
///
/// The output satisfies all of `lower/`'s established invariants:
/// - **block-param scoping** — every cross-block value reference is
///   threaded through explicit block-arg forwarding (no implicit
///   scoping). Established by `ssa_form`.
/// - **concrete types** — every `Value` carries its `ScalarType`.
///   Established by `lower_to_ssa` at value creation.
///
/// Per the architecture: optional invariants (naïve RC traffic,
/// per-Ptr layouts) are gated behind feature flags during the
/// canonical-Perceus migration and will be unconditional once
/// stable.
pub fn lower(
    mono: &Monomorphized<'_>,
    fields: &FieldInterner,
) -> Result<(Module, Vec<Value>), CompileError> {
    let decls = decl_info::build(mono);
    let (mut module, input_vals) = lower_to_ssa(
        &mono.module,
        &mono.infer,
        &decls,
        &mono.symbols,
        fields,
        &mono.singletons,
        &mono.tag_targets,
    )?;
    // Establish the explicit-block-params invariant. `lower_to_ssa`
    // emits cross-block references implicitly; downstream passes
    // require explicit block-arg threading.
    ssa_form::run(&mut module);
    // ORI_RC_EMIT_NAIVE: emit naïve Perceus RC traffic so the SSA is
    // leak-free by construction. Without this flag, the existing
    // emit_drops pass (in opt/) inserts the RC traffic later.
    rc_emit::run(&mut module);
    // Local lower-finalize: kill Alloc chains whose only uses are
    // Stores into them + rc traffic + final RcDec. After load-
    // forwarding, some intermediate aggregates have no observers
    // left and the whole construction is dead.
    elim_dead_allocs::run(&mut module);
    Ok((module, input_vals))
}

// ---- Free-variable analysis (for dead-let elimination) ----

/// `true` if `e` (or any sub-expression) references `target`. Used
/// by `lower_block` to drop let-bindings whose name is never used
/// in the rest of the block.
fn expr_uses(e: &Expr<'_>, target: SymbolId) -> bool {
    match &e.kind {
        ExprKind::Name(sym) => *sym == target,
        ExprKind::IntLit(..) | ExprKind::FloatLit(..) | ExprKind::StrLit(..) => false,
        ExprKind::BinOp { lhs, rhs, .. } => expr_uses(lhs, target) || expr_uses(rhs, target),
        ExprKind::Call { target: t, args } => {
            *t == target || args.iter().any(|a| expr_uses(a, target))
        }
        ExprKind::Block(stmts, result) => {
            stmts.iter().any(|s| stmt_uses(s, target)) || expr_uses(result, target)
        }
        ExprKind::If { expr, arms, else_body } => {
            expr_uses(expr, target)
                || arms.iter().any(|a| a.guards.iter().any(|g| expr_uses(g, target)) || expr_uses(&a.body, target))
                || else_body.as_ref().is_some_and(|e| expr_uses(e, target))
        }
        ExprKind::Fold { expr, arms } => {
            expr_uses(expr, target)
                || arms.iter().any(|a| a.guards.iter().any(|g| expr_uses(g, target)) || expr_uses(&a.body, target))
        }
        ExprKind::Lambda { body, .. } => expr_uses(body, target),
        ExprKind::QualifiedCall { args, .. } => args.iter().any(|a| expr_uses(a, target)),
        ExprKind::Record { fields } => fields.iter().any(|(_, e)| expr_uses(e, target)),
        ExprKind::RecordUpdate { base, updates } => {
            expr_uses(base, target) || updates.iter().any(|(_, e)| expr_uses(e, target))
        }
        ExprKind::FieldAccess { record, .. } => expr_uses(record, target),
        ExprKind::Tuple(elems) | ExprKind::ListLit(elems) => {
            elems.iter().any(|e| expr_uses(e, target))
        }
        ExprKind::MethodCall { receiver, args, .. } => {
            expr_uses(receiver, target) || args.iter().any(|a| expr_uses(a, target))
        }
        ExprKind::Is { expr, .. } => expr_uses(expr, target),
        ExprKind::Closure { captures, .. } => captures.iter().any(|c| expr_uses(c, target)),
    }
}

fn stmt_uses(s: &Stmt<'_>, target: SymbolId) -> bool {
    match s {
        Stmt::Let { val, .. } | Stmt::Destructure { val, .. } => expr_uses(val, target),
        Stmt::Guard { condition, return_val } => {
            expr_uses(condition, target) || expr_uses(return_val, target)
        }
        Stmt::TypeHint { .. } => false,
    }
}

// ---- SSA lowering context ----

use crate::passes::lambda_specialize::SingletonTarget;

struct LowerCtx<'a, 'src> {
    builder: Builder,
    /// Locals in scope: binding `SymbolId` → lowered value. Function
    /// parameters, let-bound names, lambda params, and pattern
    /// bindings all enter/exit this map as their scopes open and
    /// close. A binding may be `Multi` if the source value is a
    /// tuple or record and its construction site chose the
    /// decomposed shape.
    vars: HashMap<SymbolId, LoweredValue>,
    /// Generated equality functions, keyed by canonical name.
    /// Each entry is a real SSA function that compares two values
    /// of a concrete type field-by-field. Generated on first use
    /// by `ensure_eq_func`.
    eq_func_cache: HashSet<String>,
    /// Name of the function currently being lowered (diagnostic only).
    current_fn_name: String,
    // Immutable references:
    decls: &'a DeclInfo,
    infer: &'a InferResult,
    symbols: &'a SymbolTable,
    fields: &'a FieldInterner,
    singletons: &'a HashMap<String, SingletonTarget>,
    tag_targets: &'a HashMap<String, SingletonTarget>,
    _phantom: std::marker::PhantomData<&'src ()>,
}

impl<'a, 'src> LowerCtx<'a, 'src> {
    fn new(
        decls: &'a DeclInfo,
        infer: &'a InferResult,
        symbols: &'a SymbolTable,
        fields: &'a FieldInterner,
        singletons: &'a HashMap<String, SingletonTarget>,
        tag_targets: &'a HashMap<String, SingletonTarget>,
    ) -> Self {
        Self {
            builder: Builder::new(),
            vars: HashMap::new(),
            eq_func_cache: HashSet::new(),
            current_fn_name: String::new(),
            decls,
            infer,
            symbols,
            fields,
            singletons,
            tag_targets,
            _phantom: std::marker::PhantomData,
        }
    }


    /// If the closure expression is a known tag constructor, return
    /// the direct call target.
    fn resolve_closure_target(&self, closure_expr: &Expr<'_>) -> Option<&'a SingletonTarget> {
        if let ExprKind::Call { target, .. } = &closure_expr.kind {
            let name = self.symbols.display(*target);
            self.tag_targets.get(name)
        } else {
            None
        }
    }
}

impl<'a, 'src> LowerCtx<'a, 'src> {
    // ---- Type helpers ----

    fn expr_scalar_type(&self, expr: &Expr<'src>) -> ScalarType {
        self.scalar_type(&expr.ty)
    }

    /// Resolve a type to its SSA scalar type, aware of fieldless tag
    /// unions and transparent aliases. Returns `Ptr` for composite
    /// types — use `repr_type` when the value is known to be freshly
    /// produced (record/tuple/constructor literal) and could stay
    /// packed as `Agg(n)`.
    fn scalar_type(&self, ty: &Type) -> ScalarType {
        let unwrapped = self.resolve_transparent(ty);
        resolve_scalar_type(&unwrapped, &self.decls.fieldless_tags)
    }

    /// Phase A: aggregates are always heap-allocated, so `repr_type`
    /// is identical to `scalar_type`. Kept as a separate function so
    /// future SROA-style passes can re-introduce a register
    /// representation without rewriting every call site.
    fn repr_type(&self, ty: &Type) -> ScalarType {
        self.scalar_type(ty)
    }

    fn expr_repr_type(&self, expr: &Expr<'src>) -> ScalarType {
        self.repr_type(&expr.ty)
    }

    /// Expand a source-level type into its SSA-level slot types.
    /// Tuples and records fan out shallowly; lists and strings
    /// decompose into the `(len, cap, data)` trio. Tag unions and
    /// scalars stay single-slot. Inner aggregate fields stay
    /// heap-resident — only the outermost layer decomposes.
    pub(super) fn expand_slots(&self, ty: &Type) -> Vec<ScalarType> {
        let unwrapped = self.resolve_transparent(ty);
        match &unwrapped {
            Type::Tuple(tys) => tys.iter().map(|t| self.scalar_type(t)).collect(),
            Type::Record { fields, .. } => {
                let mut sorted: Vec<(&str, &Type)> =
                    fields.iter().map(|(n, t)| (n.as_str(), t)).collect();
                sorted.sort_by_key(|(n, _)| *n);
                sorted.into_iter().map(|(_, t)| self.scalar_type(t)).collect()
            }
            // List(T) — and Str (transparently List(U8)) once unwrapped
            // — decompose to (len, cap, data) at the SSA layer. The
            // data buffer stays heap; the header fanout removes a
            // load on every length/data access.
            Type::App(name, _) if name == "List" => {
                vec![ScalarType::U64, ScalarType::U64, ScalarType::RcPtr]
            }
            // Non-fieldless tag unions decompose to (tag, payload):
            // the discriminant lives in a register; the payload heap
            // object holds variant-specific fields with no tag slot
            // inside. Void variants use a null RcPtr payload.
            // Fieldless tag unions stay single-slot (just the
            // discriminant value) — handled by the fallthrough since
            // `scalar_type` returns the right discriminant type for
            // those.
            Type::TagUnion { tags, .. }
                if tags.iter().any(|(_, fields)| !fields.is_empty()) =>
            {
                vec![ScalarType::U64, ScalarType::RcPtr]
            }
            _ => vec![self.scalar_type(&unwrapped)],
        }
    }

    /// Byte offsets of each slot in the materialized heap layout of
    /// an expandable type. Tuples and records use 8-byte stride;
    /// `List` headers use the existing `(len@0, cap@8, data@16)`
    /// layout — same stride, so no special case is needed yet.
    pub(super) fn slot_offsets(&self, ty: &Type) -> Vec<usize> {
        let unwrapped = self.resolve_transparent(ty);
        match &unwrapped {
            Type::Tuple(tys) => (0..tys.len()).map(|i| i * 8).collect(),
            Type::Record { fields, .. } => (0..fields.len()).map(|i| i * 8).collect(),
            Type::App(name, _) if name == "List" => vec![0, 8, 16],
            // Non-fieldless tag union: materializes to tag@0, payload@8.
            Type::TagUnion { tags, .. }
                if tags.iter().any(|(_, fields)| !fields.is_empty()) =>
            {
                vec![0, 8]
            }
            _ => vec![0],
        }
    }

    /// Convert a `LoweredValue` to slot Values matching
    /// `expected_slots`. Materializes a Multi when a single slot is
    /// expected; unmaterializes a heap-resident Single via Loads when
    /// a multi shape is expected.
    pub(super) fn to_slots(&mut self, lv: LoweredValue, src_ty: &Type, expected_slots: &[ScalarType]) -> Vec<Value> {
        match lv {
            LoweredValue::Multi(vs) if vs.len() == expected_slots.len() => vs,
            LoweredValue::Multi(vs) if expected_slots.len() == 1 => {
                let ptr = self.materialize_lv(LoweredValue::Multi(vs), src_ty);
                vec![ptr]
            }
            LoweredValue::Multi(vs) => panic!(
                "to_slots: Multi shape {} doesn't match expected {} (src_ty={src_ty:?})",
                vs.len(),
                expected_slots.len(),
            ),
            LoweredValue::Single(v) if expected_slots.len() == 1 => vec![v],
            LoweredValue::Single(v) => {
                let offsets = self.slot_offsets(src_ty);
                if offsets.len() != expected_slots.len() {
                    // Defensive: the src_ty doesn't carry enough shape
                    // info to splat (e.g. a TypeVar that survived
                    // through specialization). Pass the single ptr
                    // and let downstream Loads pick it up.
                    return vec![v];
                }
                offsets.into_iter()
                    .zip(expected_slots.iter())
                    .map(|(off, &ty)| self.builder.load(v, off, ty))
                    .collect()
            }
        }
    }

    /// Emit a constant for a fieldless tag index using the appropriate discriminant type.
    fn const_tag(&mut self, tag_index: u64, disc_ty: ScalarType) -> Value {
        match disc_ty {
            ScalarType::U8 => self.builder.const_u8(tag_index as u8),
            ScalarType::U16 => self.builder.const_u16(tag_index as u16),
            _ => self.builder.const_u64(tag_index),
        }
    }

    fn func_ret_type(&self, name: &str) -> ScalarType {
        let base = self.decls
            .func_return_types
            .get(name)
            .copied()
            .unwrap_or(ScalarType::RcPtr);
        if !base.is_heap_ptr() {
            return base;
        }
        if let Some(scheme) = self.infer.func_schemes.get(name) {
            let ret = match &scheme.ty {
                Type::Arrow(_, ret) => ret.as_ref(),
                other => other,
            };
            return self.repr_type(ret);
        }
        base
    }

    /// Callee's expanded return slot types. Falls back to a single
    /// `RcPtr` slot when no scheme is available.
    pub(super) fn callee_return_slots(&self, func: &str) -> Vec<ScalarType> {
        self.infer
            .func_schemes
            .get(func)
            .map(|scheme| match &scheme.ty {
                Type::Arrow(_, ret) => self.expand_slots(ret),
                other => self.expand_slots(other),
            })
            .unwrap_or_else(|| vec![ScalarType::RcPtr])
    }

    /// Callee's per-source-param expanded slot types. Falls back to
    /// one `RcPtr` slot per source-level arg when no scheme is
    /// available.
    pub(super) fn callee_param_slots(&self, func: &str, num_args: usize) -> Vec<Vec<ScalarType>> {
        self.infer
            .func_schemes
            .get(func)
            .map(|scheme| match &scheme.ty {
                Type::Arrow(params, _) => {
                    params.iter().map(|t| self.expand_slots(t)).collect()
                }
                _ => vec![vec![ScalarType::RcPtr]; num_args],
            })
            .unwrap_or_else(|| vec![vec![ScalarType::RcPtr]; num_args])
    }

    /// Callee's source-level param Types in declaration order. Used
    /// to drive `to_slots` for unmaterializing closure captures and
    /// other heap-materialized args. Empty vec when no scheme.
    pub(super) fn callee_param_types(&self, func: &str) -> Vec<Type> {
        self.infer
            .func_schemes
            .get(func)
            .map(|scheme| match &scheme.ty {
                Type::Arrow(params, _) => params.clone(),
                _ => Vec::new(),
            })
            .unwrap_or_default()
    }

    /// Emit a dummy value of the given scalar type for statically
    /// unreachable merge paths. The IR needs a well-typed arg at the
    /// terminator even when the path can't execute.
    fn dummy_of(&mut self, ty: ScalarType) -> Value {
        match ty {
            ScalarType::I8 => self.builder.const_i8(0),
            ScalarType::U8 => self.builder.const_u8(0),
            ScalarType::I16 => self.builder.const_i16(0),
            ScalarType::U16 => self.builder.const_u16(0),
            ScalarType::I32 => self.builder.const_i32(0),
            ScalarType::U32 => self.builder.const_u32(0),
            ScalarType::I64 => self.builder.const_i64(0),
            ScalarType::U64 => self.builder.const_u64(0),
            ScalarType::F64 => self.builder.const_f64(0.0),
            ScalarType::Ptr | ScalarType::RcPtr => self.builder.const_ptr_null(),
            ScalarType::Agg(_) => panic!(
                "dummy_of(Agg): lower never emits Agg-typed dummies — \
                 Agg values appear only after opt::sroa, which runs \
                 after lower"
            ),
        }
    }

    // ---- Field slot computation ----

    /// Get the alphabetically-sorted field index.
    fn field_index(&self, ty: &Type, field: &str) -> usize {
        let resolved = self.resolve_transparent(ty);
        match &resolved {
            Type::Record { fields, .. } => {
                let mut names: Vec<&str> = fields.iter().map(|(n, _)| n.as_str()).collect();
                names.sort_unstable();
                names.iter().position(|n| *n == field)
                    .unwrap_or_else(|| panic!("field '{field}' not found in record type"))
            }
            Type::Tuple(_) => field.parse().unwrap_or_else(|_| {
                panic!("field '{field}' not found in tuple type")
            }),
            _ => panic!("field_index on non-record type: {resolved:?}"),
        }
    }

    /// Resolve a method on a concrete type at lowering time. Used when
    /// inference left the resolution as None (polymorphic body).
    fn resolve_method_at_lower_time(&self, method: &str, recv_ty: &Type) -> String {
        // Check the original type first — if it's a named type (Con/App),
        // use that name for method resolution even if it's transparent.
        // This prevents Set.insert from becoming __record_insert when
        // Set is a transparent alias for a record.
        match recv_ty {
            Type::Con(name) | Type::App(name, _) => {
                if crate::numeric::NumericType::from_name(name).is_some()
                    && crate::numeric::NumericType::from_name(name)
                        .unwrap()
                        .has_builtin_method(method)
                {
                    return format!("__builtin.{method}");
                }
                return format!("{name}.{method}");
            }
            _ => {}
        }
        let resolved = self.resolve_transparent(recv_ty);
        match &resolved {
            Type::Record { .. } => {
                // The receiver is a bare record — check if a named type
                // has this method registered (e.g., Set.insert when Set
                // is a transparent alias for this record shape).
                // Search registered functions for TypeName.method__suffix
                // where TypeName is a transparent alias for this record.
                let needle = format!(".{method}");
                for func_name in &self.decls.funcs {
                    if let Some(pos) = func_name.find(&needle) {
                        // Check that what follows is either end-of-string
                        // or a monomorphization suffix like "__..."
                        let after = &func_name[pos + needle.len()..];
                        if after.is_empty() || after.starts_with("__") {
                            return func_name.clone();
                        }
                    }
                }
                format!("__record_{method}")
            }
            Type::Tuple(_) => format!("__tuple_{method}"),
            Type::TagUnion { .. } => format!("__tag_{method}"),
            Type::Con(name) | Type::App(name, _) => {
                if crate::numeric::NumericType::from_name(name).is_some()
                    && crate::numeric::NumericType::from_name(name)
                        .unwrap()
                        .has_builtin_method(method)
                {
                    format!("__builtin.{method}")
                } else {
                    format!("{name}.{method}")
                }
            }
            _ => panic!(
                "cannot resolve method '{method}' on type {recv_ty:?} at lowering time"
            ),
        }
    }

    /// Resolve a type through transparent type aliases.
    fn resolve_transparent(&self, ty: &Type) -> Type {
        match ty {
            Type::App(name, args) => {
                if let Some((param_vars, underlying)) = self.infer.transparent.get(name) {
                    let mut result = underlying.clone();
                    for (var, arg) in param_vars.iter().zip(args) {
                        result = substitute_type_var(&result, *var, arg);
                    }
                    self.resolve_transparent(&result)
                } else {
                    ty.clone()
                }
            }
            Type::Con(name) => {
                if let Some((_, underlying)) = self.infer.transparent.get(name) {
                    self.resolve_transparent(underlying)
                } else {
                    ty.clone()
                }
            }
            _ => ty.clone(),
        }
    }

    // ---- Function lowering ----

    fn lower_function(&mut self, name: &str, param_syms: &[SymbolId], body: &Expr<'src>) {
        let saved_name = std::mem::replace(&mut self.current_fn_name, name.to_string());
        let saved_vars = self.vars.clone();
        let saved_func = std::mem::replace(&mut self.builder.func, crate::ssa::builder::FuncBuilder::new());
        let saved_current = self.builder.current_block.take();

        // Per-source-param expanded slot types. Tuple/record params
        // fan out to N slots; everything else stays single. Schemes
        // are authoritative; synthesized callees default to one
        // RcPtr per source-level arg.
        let per_param_slots: Vec<Vec<ScalarType>> = self
            .infer
            .func_schemes
            .get(name)
            .map(|scheme| match &scheme.ty {
                Type::Arrow(params, _) => params.iter().map(|t| self.expand_slots(t)).collect(),
                _ => vec![vec![ScalarType::RcPtr]; param_syms.len()],
            })
            .unwrap_or_else(|| vec![vec![ScalarType::RcPtr]; param_syms.len()]);

        for (p, slots) in param_syms.iter().zip(&per_param_slots) {
            let vs: Vec<Value> = slots.iter()
                .map(|&ty| self.builder.add_func_param(ty))
                .collect();
            self.vars.insert(*p, LoweredValue::from_slots(vs));
        }

        let has_scheme = self.infer.func_schemes.contains_key(name);
        let scheme_ret_slots: Vec<ScalarType> = if has_scheme {
            self.expand_slots(&body.ty)
        } else {
            vec![self.scalar_type(&body.ty)]
        };
        self.builder.set_return_types(scheme_ret_slots.clone());

        let entry = self.builder.create_block();
        self.builder.switch_to(entry);
        let result_lv = self.lower_expr_lv(body);
        // Refine for scheme-less synth functions: their declared
        // return slot types come from the body's lowered shape.
        let return_slots: Vec<ScalarType> = if has_scheme {
            scheme_ret_slots
        } else {
            match &result_lv {
                LoweredValue::Single(v) => vec![v.ty],
                LoweredValue::Multi(vs) => vs.iter().map(|v| v.ty).collect(),
            }
        };
        self.builder.set_return_types(return_slots.clone());
        let result_vals = self.to_slots(result_lv, &body.ty, &return_slots);
        if result_vals.len() == 1 {
            self.builder.ret(result_vals.into_iter().next().unwrap());
        } else {
            self.builder.ret_multi(result_vals);
        }
        self.builder.finish_function_multi(name, return_slots);

        self.builder.func = saved_func;
        self.builder.current_block = saved_current;
        self.vars = saved_vars;
        self.current_fn_name = saved_name;
    }

    // ---- Expression lowering ----

    /// Lower an expression and return its lowered form. Tuple and
    /// record literals (and a few other constructs introduced in
    /// later steps of phase B) return `Multi`; everything else
    /// returns `Single`.
    fn lower_expr_lv(&mut self, expr: &Expr<'src>) -> LoweredValue {
        match &expr.kind {
            // Tuple literal: decompose to N parallel Values. Each
            // element lowers as a single Value — nested aggregates
            // heap-materialize via the default `lower_expr` path,
            // so an inner tuple becomes a single ptr in the outer's
            // slot. Step 6 may revisit nested flattening.
            ExprKind::Tuple(elems) => {
                let vals: Vec<Value> = elems.iter().map(|e| self.lower_expr(e)).collect();
                LoweredValue::Multi(vals)
            }

            // Record literal: same shape as Tuple, but slots are in
            // alphabetical field-name order (matches the heap layout
            // used by the materialized fallback and by field_index).
            ExprKind::Record { fields } => {
                let mut sorted: Vec<(&str, &Expr<'src>)> = fields
                    .iter()
                    .map(|(field_sym, e)| (self.fields.get(*field_sym), e))
                    .collect();
                sorted.sort_by_key(|(name, _)| *name);
                let vals: Vec<Value> = sorted
                    .into_iter()
                    .map(|(_, e)| self.lower_expr(e))
                    .collect();
                LoweredValue::Multi(vals)
            }

            // RecordUpdate: if the base is a Multi (decomposed),
            // the update is pure value substitution — replace each
            // updated slot's Value, no CowStore. Base on a heap
            // (Single) ptr stays with the existing CowStore chain.
            ExprKind::RecordUpdate { base, updates } => {
                let base_lv = self.lower_expr_lv(base);
                let all_fields: Vec<String> = match &base.ty {
                    Type::Record { fields, .. } => {
                        let mut names: Vec<String> =
                            fields.iter().map(|(n, _)| n.clone()).collect();
                        names.sort_unstable();
                        names
                    }
                    _ => panic!("RecordUpdate base is not a record type"),
                };
                if let LoweredValue::Multi(mut slots) = base_lv {
                    for (sym, e) in updates {
                        let name = self.fields.get(*sym).to_owned();
                        let slot = all_fields
                            .iter()
                            .position(|n| n == &name)
                            .expect("record update on unknown field");
                        let v = self.lower_expr(e);
                        slots[slot] = v;
                    }
                    return LoweredValue::Multi(slots);
                }
                // Heap base. Reproduce the legacy CowStore chain
                // using the already-lowered base ptr.
                let base_val = self.materialize(base_lv);
                let new_vals: Vec<(usize, Value)> = updates
                    .iter()
                    .map(|(sym, e)| {
                        let name = self.fields.get(*sym).to_owned();
                        let slot = all_fields
                            .iter()
                            .position(|n| n == &name)
                            .expect("record update on unknown field");
                        (slot, self.lower_expr(e))
                    })
                    .collect();
                let mut p = base_val;
                for (slot, val) in new_vals {
                    p = self.builder.cow_store(p, slot * 8, val);
                }
                LoweredValue::single(p)
            }

            // Field access on a Multi receiver is name resolution:
            // pick the slot Value, no Load. Falls through to the
            // single-result path when the receiver is heap-resident.
            ExprKind::FieldAccess { record, field } => {
                let rec_lv = self.lower_expr_lv(record);
                if let LoweredValue::Multi(vs) = &rec_lv {
                    let field_name = self.fields.get(*field);
                    let slot = self.field_index(&record.ty, field_name);
                    return LoweredValue::single(vs[slot]);
                }
                // Heap-resident receiver: materialize (no-op for
                // Single) and emit the Load.
                let ptr = self.materialize(rec_lv);
                let field_name = self.fields.get(*field);
                let slot = self.field_index(&record.ty, field_name);
                let ty = self.expr_scalar_type(expr);
                LoweredValue::single(self.builder.load(ptr, slot * 8, ty))
            }

            // Var lookup: return whatever shape the binding has.
            // Zero-arg top-level functions are called here; route them
            // through the lv-call path so multi-slot returns flow.
            ExprKind::Name(sym) => {
                if let Some(lv) = self.vars.get(sym).cloned() {
                    return lv;
                }
                let name = self.symbols.display(*sym).to_owned();
                if self.decls.funcs.contains(&name) {
                    return self.lower_call_lv(&name, &[], &expr.ty);
                }
                LoweredValue::single(self.lower_expr_inner(expr))
            }

            // Call paths route through lv-variants so list builtins
            // and multi-return user calls can flow as `Multi` into
            // immediate destructure / field / builtin chains without
            // a heap roundtrip.
            ExprKind::Call { target, args, .. } => {
                let name = self.symbols.display(*target).to_owned();
                self.lower_call_lv(&name, args, &expr.ty)
            }
            ExprKind::QualifiedCall { segments, args, resolved } => {
                let mangled = resolved.clone().unwrap_or_else(|| segments.join("."));
                self.lower_qualified_call_lv(&mangled, segments, args, expr)
            }
            ExprKind::MethodCall { receiver, method, args, .. } => {
                self.lower_method_call_lv(receiver, method, args, expr)
            }

            _ => LoweredValue::single(self.lower_expr_inner(expr)),
        }
    }

    /// Lower an expression and return a single SSA Value. If the
    /// expression decomposes to `Multi`, materialize it to a heap
    /// pointer at the construction site. Most call sites use this
    /// wrapper today.
    fn lower_expr(&mut self, expr: &Expr<'src>) -> Value {
        let lv = self.lower_expr_lv(expr);
        self.materialize(lv)
    }

    /// Heap-materialize a `Multi` into a single RcPtr. Emits
    /// `Alloc + Store_i` for each slot at offset `i*8`. `Single`
    /// passes through. Used when the source type's slot layout is
    /// uniform 8-byte stride (the default for tuples/records).
    fn materialize(&mut self, lv: LoweredValue) -> Value {
        match lv {
            LoweredValue::Single(v) => v,
            LoweredValue::Multi(vs) => {
                let ptr = self.builder.alloc(vs.len() * 8);
                for (i, v) in vs.into_iter().enumerate() {
                    self.builder.store(ptr, i * 8, v);
                }
                ptr
            }
        }
    }

    /// Type-aware materialize: uses `slot_offsets` for the source
    /// type. Equivalent to `materialize` for tuples/records (same
    /// 8-byte stride), but explicit so future Phase C lists/strs can
    /// use 0/8/16 trio layout.
    pub(super) fn materialize_lv(&mut self, lv: LoweredValue, src_ty: &Type) -> Value {
        match lv {
            LoweredValue::Single(v) => v,
            LoweredValue::Multi(vs) => {
                let offsets = self.slot_offsets(src_ty);
                if offsets.len() != vs.len() {
                    // Defensive fallback: use uniform 8-byte stride.
                    return self.materialize(LoweredValue::Multi(vs));
                }
                let total = offsets.iter().copied().max().unwrap_or(0) + 8;
                let ptr = self.builder.alloc(total);
                for (v, off) in vs.into_iter().zip(offsets) {
                    self.builder.store(ptr, off, v);
                }
                ptr
            }
        }
    }

    fn lower_expr_inner(&mut self, expr: &Expr<'src>) -> Value {
        match &expr.kind {
            ExprKind::IntLit(n) => {
                numeric::lower_int_const(&mut self.builder, *n, &expr.ty)
            }

            ExprKind::FloatLit(n) => self.builder.const_f64(*n),

            ExprKind::StrLit(bytes) => {
                let len = bytes.len();
                let data = self.builder.alloc(len * 8);
                for (i, &b) in bytes.iter().enumerate() {
                    let val = self.builder.const_u8(b);
                    self.builder.store(data, i * 8, val);
                }
                let header = self.builder.alloc(24);
                let len_val = self.builder.const_u64(len as u64);
                self.builder.store(header, 0, len_val);
                self.builder.store(header, 8, len_val);
                self.builder.store(header, 16, data);
                header
            }

            ExprKind::Name(sym) => {
                if let Some(lv) = self.vars.get(sym).cloned() {
                    return self.materialize(lv);
                }
                let name = self.symbols.display(*sym);
                if self.decls.constructors.contains_key(name) {
                    return self.lower_constructor_call(name, &[], Some(&expr.ty));
                }
                // Structural constructor: bare uppercase reference
                // not registered in decl_info. Layout comes from the
                // expression's inferred TagUnion type.
                if name.starts_with(|c: char| c.is_ascii_uppercase()) {
                    return self.lower_constructor_call(name, &[], Some(&expr.ty));
                }
                // Builtins like `crash` can appear as bare Name
                // references when defunc captures them as free
                // variables in a closure. They're not real values —
                // they'll be called at the Call site. Return a dummy.
                if name == "crash" {
                    return self.builder.const_i64(0);
                }
                // Top-level value binding: call as zero-arg function.
                if self.decls.funcs.contains(name) {
                    let ret_ty = self.func_ret_type(name);
                    return self.builder.call(name, vec![], ret_ty);
                }
                panic!("undefined name: {name}");
            }

            ExprKind::BinOp {
                op: BinOp::And,
                lhs,
                rhs,
            } => self.lower_and_expr(lhs, rhs),

            ExprKind::BinOp {
                op: BinOp::Or,
                lhs,
                rhs,
            } => self.lower_or_expr(lhs, rhs),

            ExprKind::Is {
                expr: inner,
                pattern,
            } => self.lower_is_expr(inner, pattern),

            ExprKind::BinOp { op, lhs, rhs } => {
                let l = self.lower_expr(lhs);
                let r = self.lower_expr(rhs);
                let ty = self.expr_scalar_type(expr);
                match op {
                    BinOp::Add => self.builder.binop(BinaryOp::Add, l, r, ty),
                    BinOp::Sub => self.builder.binop(BinaryOp::Sub, l, r, ty),
                    BinOp::Mul => self.builder.binop(BinaryOp::Mul, l, r, ty),
                    BinOp::Div => self.builder.binop(BinaryOp::Div, l, r, ty),
                    BinOp::Rem => self.builder.binop(BinaryOp::Rem, l, r, ty),
                    BinOp::BitOr => self.builder.binop(BinaryOp::Or, l, r, ty),
                    BinOp::BitXor => self.builder.binop(BinaryOp::Xor, l, r, ty),
                    BinOp::Eq | BinOp::Neq => {
                        let negate = matches!(op, BinOp::Neq);
                        let resolved_ty = self.resolve_transparent(&lhs.ty);
                        if self.is_scalar_eq_type(&resolved_ty) {
                            self.lower_eq(l, r, negate)
                        } else {
                            let eq_name = self.ensure_eq_func(&resolved_ty);
                            let result = self.builder.call(&eq_name, vec![l, r], ScalarType::U8);
                            self.lower_bool_from_cmp_neg(result, negate)
                        }
                    }
                    BinOp::Lt => self.lower_cmp(l, r, BinaryOp::Lt),
                    BinOp::Gt => self.lower_cmp(l, r, BinaryOp::Gt),
                    BinOp::Le => self.lower_cmp(l, r, BinaryOp::Le),
                    BinOp::Ge => self.lower_cmp(l, r, BinaryOp::Ge),
                    BinOp::And | BinOp::Or => unreachable!(),
                }
            }

            ExprKind::Call { target, args, .. } => {
                self.lower_call_by_sym(*target, args, &expr.ty)
            }

            ExprKind::Block(stmts, result) => self.lower_block(stmts, result),

            ExprKind::If {
                expr: scrutinee_expr,
                arms,
                else_body,
            } => {
                let result_ty = self.expr_repr_type(expr);
                if Self::is_bool_if_with_is(scrutinee_expr, arms) {
                    self.lower_bool_if_with_is(scrutinee_expr, arms, result_ty)
                } else if Self::is_literal_match(arms) {
                    self.lower_literal_match(
                        scrutinee_expr,
                        arms,
                        else_body.as_deref(),
                        result_ty,
                    )
                } else {
                    self.lower_match(scrutinee_expr, arms, else_body.as_deref(), result_ty)
                }
            }

            ExprKind::Fold { .. } => {
                panic!(
                    "Fold should have been eliminated by fold_lift before SSA lowering (at {:?})",
                    expr.span
                )
            }

            ExprKind::QualifiedCall { segments, args, .. } => {
                self.lower_qualified_call(segments, args, expr)
            }

            ExprKind::Record { fields } => {
                let mut sorted: Vec<(usize, &str, &Expr)> = fields
                    .iter()
                    .enumerate()
                    .map(|(i, (field_sym, expr))| (i, self.fields.get(*field_sym), expr))
                    .collect();
                sorted.sort_by_key(|(_, name, _)| *name);
                let field_types: Vec<ScalarType> = sorted
                    .iter()
                    .map(|(_, _, e)| self.expr_scalar_type(e))
                    .collect();
                let vals: Vec<Value> = sorted
                    .iter()
                    .map(|(_, _, e)| self.lower_expr(e))
                    .collect();
                let _ = field_types; // retained for type-aware extensions
                let ptr = self.builder.alloc(fields.len() * 8);
                for (i, val) in vals.into_iter().enumerate() {
                    self.builder.store(ptr, i * 8, val);
                }
                ptr
            }

            ExprKind::FieldAccess { record, field } => {
                let val = self.lower_expr(record);
                let field_name = self.fields.get(*field);
                let slot = self.field_index(&record.ty, field_name);
                let ty = self.expr_scalar_type(expr);
                self.builder.load(val, slot * 8, ty)
            }

            ExprKind::MethodCall {
                receiver,
                method,
                args,
                ..
            } => self.lower_method_call(receiver, method, args, expr),

            ExprKind::Tuple(elems) => {
                let vals: Vec<Value> = elems.iter()
                    .map(|e| self.lower_expr(e))
                    .collect();
                let ptr = self.builder.alloc(elems.len() * 8);
                for (i, val) in vals.into_iter().enumerate() {
                    self.builder.store(ptr, i * 8, val);
                }
                ptr
            }

            ExprKind::Lambda { .. } => {
                panic!("lambdas are only supported as direct arguments to function calls");
            }

            ExprKind::RecordUpdate { base, updates } => {
                // Emit a chain of CowStores. Each CowStore: if its
                // input ptr is uniquely owned at runtime, mutates
                // in place; otherwise clones-then-writes. FBIP is
                // intrinsic to the runtime semantic — lower doesn't
                // think about it. The first CowStore may clone (if
                // base is shared); subsequent ones see a unique
                // intermediate result.
                let base_val = self.lower_expr(base);
                let all_fields: Vec<String> = match &base.ty {
                    Type::Record { fields, .. } => {
                        let mut names: Vec<String> =
                            fields.iter().map(|(n, _)| n.clone()).collect();
                        names.sort_unstable();
                        names
                    }
                    _ => panic!("RecordUpdate base is not a record type"),
                };
                let update_map: HashMap<String, &Expr> = updates
                    .iter()
                    .map(|(sym, e)| (self.fields.get(*sym).to_owned(), e))
                    .collect();
                // Evaluate update expressions first so they can
                // reference base. (rc_emit will rc_inc base if it's
                // used later than the CowStore consumes it.)
                let new_vals: Vec<(usize, Value)> = all_fields
                    .iter()
                    .enumerate()
                    .filter_map(|(slot, field_name)| {
                        update_map.get(field_name).map(|expr| (slot, self.lower_expr(expr)))
                    })
                    .collect();
                let mut p = base_val;
                for (slot, val) in new_vals {
                    p = self.builder.cow_store(p, slot * 8, val);
                }
                p
            }

            ExprKind::ListLit(elems) => {
                let len = elems.len();
                let data = self.builder.alloc(len * 8);
                for (i, elem) in elems.iter().enumerate() {
                    let val = self.lower_expr(elem);
                    self.builder.store(data, i * 8, val);
                }
                let header = self.builder.alloc(24);
                let len_val = self.builder.const_u64(len as u64);
                self.builder.store(header, 0, len_val);
                self.builder.store(header, 8, len_val);
                self.builder.store(header, 16, data);
                header
            }

            ExprKind::Closure { .. } => {
                panic!(
                    "Closure should have been eliminated before SSA lowering (at {:?})",
                    expr.span
                )
            }
        }
    }

    // ---- Block lowering ----

    fn lower_block(&mut self, stmts: &[Stmt<'src>], result: &Expr<'src>) -> Value {
        for (i, stmt) in stmts.iter().enumerate() {
            match stmt {
                Stmt::Let { name, val } => {
                    // Drop unused let bindings. Ori is pure (System T),
                    // so an unused binding's RHS has no observable
                    // effect and can be elided. Look forward through
                    // remaining stmts and the result expression.
                    let used = stmts[i + 1..]
                        .iter()
                        .any(|s| stmt_uses(s, *name))
                        || expr_uses(result, *name);
                    if !used {
                        continue;
                    }
                    let lv = self.lower_expr_lv(val);
                    self.vars.insert(*name, lv);
                }
                Stmt::Destructure { pattern, val } => {
                    let lv = self.lower_expr_lv(val);
                    self.lower_destructure_lv(pattern, lv, &val.ty);
                }
                Stmt::Guard {
                    condition,
                    return_val,
                } => {
                    if Self::expr_contains_is(condition) {
                        // Use and-chain lowering for Is binding flow
                        let cont_block = self.builder.create_block();
                        let saved_vars = self.vars.clone();
                        self.lower_and_chain(condition, cont_block, &[]);
                        // We're in the success path — return
                        let ret_v = self.lower_expr(return_val);
                        self.builder.ret(ret_v);
                        self.vars = saved_vars;
                        self.builder.switch_to(cont_block);
                    } else {
                        // Lower: if condition is true, return return_val from function
                        let cond_val = self.lower_expr(condition);
                        let disc_ty = self.decls.fieldless_tags.get("Bool").copied().unwrap_or(ScalarType::U8);
                        let true_tag = self.decls.constructors["True"].tag_index;
                        let true_val = self.const_tag(true_tag, disc_ty);
                        let is_true =
                            self.builder
                                .binop(BinaryOp::Eq, cond_val, true_val, ScalarType::U8);
                        let ret_block = self.builder.create_block();
                        let cont_block = self.builder.create_block();
                        self.builder
                            .branch(is_true, ret_block, vec![], cont_block, vec![]);
                        // Return block: evaluate return_val and ret
                        self.builder.switch_to(ret_block);
                        let ret_v = self.lower_expr(return_val);
                        self.builder.ret(ret_v);
                        // Continue block: proceed with next statements
                        self.builder.switch_to(cont_block);
                    }
                }
                Stmt::TypeHint { .. } => {}
            }
        }
        self.lower_expr(result)
    }

    // ---- Call lowering ----
    //
    // After mono + defunc + prune, every call site resolves to a
    // concrete global callable. There are three AST shapes that
    // reach the lowerer:
    //
    // - `Call { target: SymbolId, args }` — direct call by SymbolId.
    //   Lowered via `lower_call` (which also handles list-walk
    //   intrinsics and the other dispatch-table branches).
    // - `QualifiedCall { segments, resolved, args }` — either a
    //   static qualified call (`resolved = None`) or a method call
    //   on a local receiver (`resolved = Some(name)`). The static
    //   form routes through `lower_call`.
    // - `MethodCall { receiver, resolved, args }` — always a
    //   method call with explicit receiver as first arg.
}

// ---- SSA emission (Pass 4) ----

fn lower_to_ssa<'src>(
    module: &ast::Module<'src>,
    infer_result: &InferResult,
    decls: &DeclInfo,
    symbols: &SymbolTable,
    fields: &FieldInterner,
    singletons: &HashMap<String, SingletonTarget>,
    tag_targets: &HashMap<String, SingletonTarget>,
) -> Result<(Module, Vec<Value>), CompileError> {
    let mut ctx = LowerCtx::new(decls, infer_result, symbols, fields, singletons, tag_targets);

    let mut main_params: Option<Vec<SymbolId>> = None;
    let mut main_body: Option<Expr<'src>> = None;

    for decl in &module.decls {
        let Decl::FuncDef {
            name, params, body, ..
        } = decl
        else {
            continue;
        };
        let name_str = symbols.display(*name);

        if name_str == "main" {
            main_params = Some(params.clone());
            main_body = Some(body.clone());
            continue;
        }

        ctx.lower_function(name_str, params, body);

        for p in params {
            ctx.vars.remove(p);
        }
    }

    // Lower associated function bodies
    for decl in &module.decls {
        let Decl::TypeAnno {
            name: type_name,
            methods,
            ..
        } = decl
        else {
            continue;
        };
        let type_name_str = symbols.display(*type_name);
        for method_decl in methods {
            let Decl::FuncDef {
                name: method_name,
                params,
                body,
                ..
            } = method_decl
            else {
                continue;
            };
            let method_name_str = symbols.display(*method_name);
            let mangled = method_key(type_name_str, method_name_str);
            ctx.lower_function(&mangled, params, body);

            for p in params {
                ctx.vars.remove(p);
            }
        }
    }

    // Lower main
    let params = main_params.ok_or_else(|| CompileError::new("no 'main' function defined"))?;
    let body = main_body.unwrap();

    // Declared param types from the scheme, falling back to Ptr for
    // synthesized mains without schemes. Using the scheme keeps the
    // declared param types honest for scalar `main : I64 -> I64`
    // tests; runtime callers that pass `Ptr` (e.g. the CLI harness
    // for `List(List(U8)) -> ...` mains) already match the declared
    // types for their common case.
    let main_param_tys: Vec<ScalarType> = ctx
        .infer
        .func_schemes
        .get("main")
        .and_then(|s| match &s.ty {
            Type::Arrow(ps, _) => Some(ps.iter().map(|t| ctx.scalar_type(t)).collect()),
            _ => None,
        })
        .unwrap_or_else(|| vec![ScalarType::RcPtr; params.len()]);
    let main_ssa_params: Vec<Value> = params
        .iter()
        .zip(&main_param_tys)
        .map(|(p, &ty)| {
            let v = ctx.builder.add_func_param(ty);
            ctx.vars.insert(*p, LoweredValue::single(v));
            v
        })
        .collect();
    let main_ret_ty = ctx.func_ret_type("main");
    ctx.builder.set_return_type(main_ret_ty);
    let entry = ctx.builder.create_block();
    ctx.builder.switch_to(entry);
    let result = ctx.lower_expr(&body);
    ctx.builder.ret(result);
    ctx.builder.finish_function("__main", main_ret_ty);

    let ssa_module = ctx.builder.build("__main");
    Ok((ssa_module, main_ssa_params))
}

// ---- Free helpers ----

/// Classify a mangled callable name as a `List.walk*` variant.
/// Returns `None` for every non-walk name. Lives at module level
/// (not as a method on `LowerCtx`) because it's pure string analysis.
/// Compute layout info for a structural constructor from a closed

/// Replace all occurrences of `var` in `ty` with `replacement`.
pub(super) fn substitute_type_var(ty: &Type, var: TypeVar, replacement: &Type) -> Type {
    match ty {
        Type::Var(v) if *v == var => replacement.clone(),
        Type::Var(_) | Type::Con(_) => ty.clone(),
        Type::App(name, args) => Type::App(
            name.clone(),
            args.iter()
                .map(|a| substitute_type_var(a, var, replacement))
                .collect(),
        ),
        Type::Arrow(params, ret) => Type::Arrow(
            params
                .iter()
                .map(|p| substitute_type_var(p, var, replacement))
                .collect(),
            Box::new(substitute_type_var(ret, var, replacement)),
        ),
        Type::Record { fields, rest } => Type::Record {
            fields: fields
                .iter()
                .map(|(n, t)| (n.clone(), substitute_type_var(t, var, replacement)))
                .collect(),
            rest: rest
                .as_ref()
                .map(|r| Box::new(substitute_type_var(r, var, replacement))),
        },
        Type::Tuple(elems) => Type::Tuple(
            elems
                .iter()
                .map(|e| substitute_type_var(e, var, replacement))
                .collect(),
        ),
        Type::TagUnion { tags, rest } => Type::TagUnion {
            tags: tags
                .iter()
                .map(|(n, payloads)| {
                    (
                        n.clone(),
                        payloads
                            .iter()
                            .map(|p| substitute_type_var(p, var, replacement))
                            .collect(),
                    )
                })
                .collect(),
            rest: rest
                .as_ref()
                .map(|r| Box::new(substitute_type_var(r, var, replacement))),
        },
    }
}
