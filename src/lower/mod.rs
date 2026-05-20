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
//! - `self.vars: HashMap<SymbolId, Value>` — the live local map for
//!   the current block. Updated as let-bindings introduce names.
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

pub mod list_ops;
pub mod eq;
pub mod hash;
pub mod numeric;
pub mod rc_emit;
pub mod ssa_form;
pub mod pattern;
pub mod walk;

pub(crate) use walk::{classify_walk, walk_apply_name};

use std::collections::{HashMap, HashSet};

use crate::ast::{self, BinOp, Decl, Expr, ExprKind, Stmt};
use crate::passes::decl_info::{self, DeclInfo, method_key, resolve_scalar_type};
use crate::passes::mono::Monomorphized;
use crate::error::CompileError;
use crate::ssa::Module;
use crate::ssa::builder::Builder;
use crate::ssa::instruction::{BinaryOp, BlockId, ScalarType, Value};
use crate::symbol::{FieldInterner, SymbolId, SymbolTable};
use crate::types::engine::{Type, TypeVar};
use crate::types::infer::InferResult;

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
    Ok((module, input_vals))
}

// ---- SSA lowering context ----

use crate::passes::lambda_specialize::SingletonTarget;

struct LowerCtx<'a, 'src> {
    builder: Builder,
    /// Locals in scope: binding `SymbolId` → SSA value. Function
    /// parameters, let-bound names, lambda params, and pattern
    /// bindings all enter/exit this map as their scopes open and close.
    vars: HashMap<SymbolId, Value>,
    /// Generated equality functions, keyed by canonical name.
    /// Each entry is a real SSA function that compares two values
    /// of a concrete type field-by-field. Generated on first use
    /// by `ensure_eq_func`.
    eq_func_cache: HashSet<String>,
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

    /// Element scalar type of a `List(T)`, or `None` if `ty` isn't a
    /// list. Strings — `List(U8)` — give `U8`.
    fn list_elem_scalar_type(&self, ty: &Type) -> Option<ScalarType> {
        let unwrapped = self.resolve_transparent(ty);
        match &unwrapped {
            Type::App(name, args) if name == "List" => args.first().map(|t| self.scalar_type(t)),
            _ => None,
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
            .unwrap_or(ScalarType::Ptr);
        if base != ScalarType::Ptr {
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
            ScalarType::Ptr => self.builder.const_ptr_null(),
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
        let saved_vars = self.vars.clone();
        let saved_func = std::mem::replace(&mut self.builder.func, crate::ssa::builder::FuncBuilder::new());
        let saved_current = self.builder.current_block.take();

        // Parameter scalar types come from the function's inferred
        // scheme when available. Synthesized `__apply_K` functions
        // don't have schemes — they default to all-`Ptr`, which is
        // correct since closures carry type-erased captures and
        // arguments.
        let param_types: Vec<ScalarType> = self
            .infer
            .func_schemes
            .get(name)
            .map(|scheme| match &scheme.ty {
                Type::Arrow(params, _) => {
                    params.iter().map(|t| self.scalar_type(t)).collect()
                }
                _ => vec![ScalarType::Ptr; param_syms.len()],
            })
            .unwrap_or_else(|| vec![ScalarType::Ptr; param_syms.len()]);

        for (p, ty) in param_syms.iter().zip(&param_types) {
            let v = self.builder.add_func_param(*ty);
            self.vars.insert(*p, v);
        }

        // Set the return type BEFORE lowering the body so `ret` can
        // coerce its operand when it fires from inside nested
        // expressions. Use repr_type so packable composites stay as
        // Agg through returns — Pack is first-class at runtime.
        let scheme_ret_ty = self.repr_type(&body.ty);
        let has_scheme = self.infer.func_schemes.contains_key(name);
        self.builder.set_return_type(scheme_ret_ty);

        let entry = self.builder.create_block();
        self.builder.switch_to(entry);
        let result = self.lower_expr(body);
        let return_type = if has_scheme {
            scheme_ret_ty
        } else {
            result.ty
        };
        // Refine the declared return type for scheme-less synth
        // functions before emitting the final `ret`, so `ret`'s
        // coercion check uses the same type the function claims.
        self.builder.set_return_type(return_type);
        self.builder.ret(result);
        self.builder.finish_function(name, return_type);

        self.builder.func = saved_func;
        self.builder.current_block = saved_current;
        self.vars = saved_vars;
    }

    // ---- Expression lowering ----

    fn lower_expr(&mut self, expr: &Expr<'src>) -> Value {
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
                if let Some(&val) = self.vars.get(sym) {
                    return val;
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
                let base_val = self.lower_expr(base);
                // Get all field names from the base record type, sorted.
                let all_fields: Vec<String> = match &base.ty {
                    Type::Record { fields, .. } => {
                        let mut names: Vec<String> =
                            fields.iter().map(|(n, _)| n.clone()).collect();
                        names.sort_unstable();
                        names
                    }
                    _ => panic!("RecordUpdate base is not a record type"),
                };
                // Build a map of update field name → expression.
                let update_map: HashMap<String, &Expr> = updates
                    .iter()
                    .map(|(sym, e)| (self.fields.get(*sym).to_owned(), e))
                    .collect();
                // Get sorted field types from the base record type.
                let field_types: Vec<ScalarType> = match &base.ty {
                    Type::Record { fields, .. } => {
                        let mut sorted: Vec<(&str, &Type)> =
                            fields.iter().map(|(n, t)| (n.as_str(), t)).collect();
                        sorted.sort_unstable_by_key(|(n, _)| *n);
                        sorted.iter().map(|(_, t)| self.scalar_type(t)).collect()
                    }
                    _ => vec![],
                };
                let num_fields = all_fields.len();
                // Collect all field values.
                let vals: Vec<Value> = all_fields
                    .iter()
                    .enumerate()
                    .map(|(slot, field_name)| {
                        if let Some(upd_expr) = update_map.get(field_name) {
                            self.lower_expr(upd_expr)
                        } else {
                            let ty = field_types.get(slot).copied().unwrap_or(ScalarType::Ptr);
                            self.builder.load(base_val, slot * 8, ty)
                        }
                    })
                    .collect();
                {
                    let ptr = self.builder.alloc(num_fields * 8);
                    for (slot, val) in vals.into_iter().enumerate() {
                        self.builder.store(ptr, slot * 8, val);
                    }
                    ptr
                }
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
        for stmt in stmts {
            match stmt {
                Stmt::Let { name, val } => {
                    let v = self.lower_expr(val);
                    self.vars.insert(*name, v);
                }
                Stmt::Destructure { pattern, val } => {
                    let v = self.lower_expr(val);
                    self.lower_destructure(pattern, v, &val.ty);
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

    fn lower_call_by_sym(
        &mut self,
        target: SymbolId,
        args: &[Expr<'src>],
        result_ty: &Type,
    ) -> Value {
        let name = self.symbols.display(target).to_owned();
        self.lower_call(&name, args, result_ty)
    }

    fn lower_qualified_call(
        &mut self,
        segments: &[&'src str],
        args: &[Expr<'src>],
        outer: &Expr<'src>,
    ) -> Value {
        let ExprKind::QualifiedCall { resolved, .. } = &outer.kind else {
            unreachable!("lower_qualified_call called on non-QualifiedCall");
        };
        // `__builtin.<op>` dispatch: the call came out of either the
        // numeric method-call resolution (`x.add(y)` where x : I64)
        // or the eta-expansion of a numeric method reference (`I64.add`
        // used as a first-class function). Both shapes share this
        // path — the difference is only in whether `segments[0]` is
        // a local binding or the type name.
        if let Some(resolved_name) = resolved
            && let Some(op_name) = resolved_name.strip_prefix("__builtin.")
        {
            // Numeric builtin intrinsic. `segments[0]` is either a
            // local binding (receiver for `x.add(y)`) or a type name
            // (`I64` for eta-expanded `I64.add(a, b)`).
            let local_val = self
                .vars
                .iter()
                .find(|(sym, _)| self.symbols.display(**sym) == segments[0])
                .map(|(_, v)| *v);
            if op_name == "to_bits" {
                let arg = local_val.unwrap_or_else(|| self.lower_expr(&args[0]));
                let dest_ty = numeric::bits_dest_ty(segments[0]);
                return self.builder.bitcast(arg, dest_ty);
            }
            if op_name == "from_bits" {
                let arg = local_val.unwrap_or_else(|| self.lower_expr(&args[0]));
                return self.builder.bitcast(arg, ScalarType::F64);
            }
            if op_name == "from_u8" {
                let arg = local_val.unwrap_or_else(|| self.lower_expr(&args[0]));
                let dest_ty = match segments[0] {
                    "U32" => ScalarType::U32,
                    _ => ScalarType::U64,
                };
                return self.builder.cast(arg, dest_ty);
            }
            if op_name == "to_u8" {
                let arg = local_val.unwrap_or_else(|| self.lower_expr(&args[0]));
                return self.builder.cast(arg, ScalarType::U8);
            }
            if op_name == "to_u64" {
                let arg = local_val.unwrap_or_else(|| self.lower_expr(&args[0]));
                return self.builder.cast(arg, ScalarType::U64);
            }
            if op_name == "to_i64" {
                let arg = local_val.unwrap_or_else(|| self.lower_expr(&args[0]));
                return self.builder.cast(arg, ScalarType::I64);
            }
            // Binary arithmetic op
            let (lhs, rhs) = if let Some(local_val) = local_val {
                (local_val, self.lower_expr(&args[0]))
            } else {
                (self.lower_expr(&args[0]), self.lower_expr(&args[1]))
            };
            let ty = self.expr_scalar_type(&args[0]);
            return self.lower_builtin_op(op_name, lhs, rhs, ty);
        }
        if let Some(resolved_name) = resolved {
            // Non-builtin method dispatch on a local receiver (the
            // qualified-call form of `receiver.method(args)`).
            let receiver_name = segments[0];
            let receiver_val = self
                .vars
                .iter()
                .find(|(sym, _)| self.symbols.display(**sym) == receiver_name)
                .map(|(_, v)| *v)
                .unwrap_or_else(|| {
                    // Receiver is a declared nullary constructor
                    // being used as a method target (e.g. `True.not()`).
                    // Structural constructors don't flow through this
                    // path — they go through `ExprKind::Call` instead.
                    self.lower_constructor_call(receiver_name, &[], None)
                });
            let mut arg_vals = vec![receiver_val];
            for a in args {
                arg_vals.push(self.lower_expr(a));
            }
            let ret_ty = self.func_ret_type(resolved_name);
            return self.builder.call(resolved_name, arg_vals, ret_ty);
        }
        // Plain static qualified call: prefer the mono'd `resolved`
        // name so apply-function dispatch and walk classification see
        // the per-monomorphization callable name (e.g.
        // `List.walk__I64_I64`). Falling back to segments keeps pre-
        // mono shapes working.
        let mangled = resolved.clone().unwrap_or_else(|| segments.join("."));
        self.lower_call(&mangled, args, &outer.ty)
    }

    fn lower_method_call(
        &mut self,
        receiver: &Expr<'src>,
        method: &'src str,
        args: &[Expr<'src>],
        outer: &Expr<'src>,
    ) -> Value {
        let ExprKind::MethodCall { resolved, .. } = &outer.kind else {
            unreachable!("lower_method_call called on non-MethodCall");
        };
        let mangled = if let Some(r) = resolved.clone() {
            r
        } else {
            // No resolution from inference — resolve based on the
            // concrete receiver type (happens for polymorphic methods
            // after monomorphization).
            self.resolve_method_at_lower_time(method, &receiver.ty)
        };
        // Deforestation: check for List.range(a,b).walk(...) BEFORE
        // lowering the receiver to avoid materializing the range list.
        if let Some(walk) = classify_walk(&mangled) {
            if let Some((start, end)) = self.as_range_call(receiver) {
                assert!(args.len() == 2, "List.walk* method form takes 2 args");
                let init_val = self.lower_expr(&args[0]);
                let acc_ty = self.expr_scalar_type(&args[0]);
                let direct = self.resolve_closure_target(&args[1]);
                let closure_val = self.lower_expr(&args[1]);
                let apply_name = walk_apply_name(&mangled, &args[1].ty);
                return self.lower_range_walk(
                    start, end, init_val, closure_val, &apply_name,
                    walk.until, acc_ty, direct,
                );
            }
        }
        let recv_val = self.lower_expr(receiver);
        if mangled == "__record_equals" || mangled == "__tuple_equals" {
            let rhs = self.lower_expr(&args[0]);
            let resolved = self.resolve_transparent(&receiver.ty);
            let eq_name = self.ensure_eq_func(&resolved);
            let result = self.builder.call(&eq_name, vec![recv_val, rhs], ScalarType::U8);
            return self.lower_bool_from_cmp(result);
        }
        if mangled == "__record_to_str" {
            return self.lower_record_to_str(recv_val, &receiver.ty);
        }
        if mangled == "__record_hash" {
            return self.lower_record_hash(recv_val, &receiver.ty);
        }
        if mangled == "__tuple_hash" {
            return self.lower_tuple_hash(recv_val, &receiver.ty);
        }
        if mangled == "__tag_hash" {
            return self.lower_tag_hash(recv_val, &receiver.ty);
        }
        if let Some(op_name) = mangled.strip_prefix("__builtin.") {
            if op_name == "to_bits" {
                let dest_ty = numeric::bits_dest_ty_for_ty(&receiver.ty);
                return self.builder.bitcast(recv_val, dest_ty);
            }
            if op_name == "from_bits" {
                return self.builder.bitcast(recv_val, ScalarType::F64);
            }
            if op_name == "from_u8" {
                let dest_ty = self.expr_scalar_type(outer);
                return self.builder.cast(recv_val, dest_ty);
            }
            if op_name == "to_u8" {
                return self.builder.cast(recv_val, ScalarType::U8);
            }
            if op_name == "to_u64" {
                return self.builder.cast(recv_val, ScalarType::U64);
            }
            if op_name == "to_i64" {
                return self.builder.cast(recv_val, ScalarType::I64);
            }
            let rhs = self.lower_expr(&args[0]);
            let ty = self.expr_scalar_type(receiver);
            return self.lower_builtin_op(op_name, recv_val, rhs, ty);
        }
        // List walks: the walk loop needs untyped Values, so build
        // them positionally.
        if let Some(walk) = classify_walk(&mangled) {
            assert!(args.len() == 2, "List.walk* method form takes 2 args");
            let init_val = self.lower_expr(&args[0]);
            let acc_ty = self.expr_scalar_type(&args[0]);
            let direct = self.resolve_closure_target(&args[1]);
            let closure_val = self.lower_expr(&args[1]);
            let apply_name = walk_apply_name(&mangled, &args[1].ty);
            return self.lower_list_walk(
                recv_val,
                init_val,
                closure_val,
                &apply_name,
                walk.until,
                acc_ty,
                direct,
            );
        }
        let mut arg_vals = Vec::with_capacity(args.len() + 1);
        arg_vals.push(recv_val);
        for a in args {
            arg_vals.push(self.lower_expr(a));
        }
        if Self::is_list_builtin(&mangled) {
            // Receiver is `List(T)`; element type drives in-copy RC.
            let elem_ty = self.list_elem_scalar_type(&receiver.ty)
                .unwrap_or(ScalarType::I64);
            return list_ops::emit_list_builtin_call(&mut self.builder, &mangled, arg_vals, elem_ty);
        }
        let ret_ty = self.func_ret_type(&mangled);
        self.builder.call(&mangled, arg_vals, ret_ty)
    }

    /// Central dispatch for direct and static qualified calls: list
    /// walks (which need the walk loop emitted inline), list
    /// builtins, num-to-str, constructors, and plain function calls.
    ///
    /// `result_ty` is the type of the enclosing expression, used to
    /// compute layout for structural constructor calls.
    fn lower_call(
        &mut self,
        func: &str,
        args: &[Expr<'src>],
        result_ty: &Type,
    ) -> Value {
        if let Some(walk) = classify_walk(func) {
            assert!(args.len() >= 3, "List.walk* takes 3 arguments");
            let init_val = self.lower_expr(&args[1]);
            let acc_ty = self.expr_scalar_type(&args[1]);
            let direct = self.resolve_closure_target(&args[2]);
            let closure_val = self.lower_expr(&args[2]);
            let apply_name = walk_apply_name(func, &args[2].ty);
            // Deforestation: List.walk(List.range(a, b), init, f) → counter loop.
            if let Some((start, end)) = self.as_range_call(&args[0]) {
                return self.lower_range_walk(
                    start, end, init_val, closure_val, &apply_name,
                    walk.until, acc_ty, direct,
                );
            }
            let list_val = self.lower_expr(&args[0]);
            return self.lower_list_walk(
                list_val,
                init_val,
                closure_val,
                &apply_name,
                walk.until,
                acc_ty,
                direct,
            );
        }
        if func == "crash" {
            // Crash diverges, so its return is never observed at
            // runtime. Typing it as the caller's expected result type
            // keeps merge/return type agreement honest in the IR.
            let msg_val = self.lower_expr(&args[0]);
            let ret_ty = self.scalar_type(result_ty);
            return self.builder.call("__crash", vec![msg_val], ret_ty);
        }
        if Self::is_list_builtin(func) {
            let arg_vals: Vec<Value> = args.iter().map(|a| self.lower_expr(a)).collect();
            // Static-form list builtins (`List.range`, `List.repeat`,
            // etc.) return a list — their result type carries the
            // element. Method-form ones (`xs.set(i, v)`) have a list
            // as their first arg. Try result type first, fall back.
            let elem_ty = self.list_elem_scalar_type(result_ty)
                .or_else(|| self.list_elem_scalar_type(&args[0].ty))
                .unwrap_or(ScalarType::I64);
            return list_ops::emit_list_builtin_call(&mut self.builder, func, arg_vals, elem_ty);
        }
        if self.decls.constructors.contains_key(func) {
            let arg_vals: Vec<Value> = args.iter().map(|a| self.lower_expr(a)).collect();
            return self.lower_constructor_call(func, &arg_vals, Some(result_ty));
        }
        if self.decls.funcs.contains(func) {
            let ret_ty = self.func_ret_type(func);
            let arg_vals: Vec<Value> = args.iter().map(|a| self.lower_expr(a)).collect();
            return self.builder.call(func, arg_vals, ret_ty);
        }
        // Structural constructor (not in decl_info). Layout is
        // derived from `result_ty` which inference closed to a
        // concrete `Type::TagUnion`.
        if func.starts_with(|c: char| c.is_ascii_uppercase()) {
            let arg_vals: Vec<Value> = args.iter().map(|a| self.lower_expr(a)).collect();
            return self.lower_constructor_call(func, &arg_vals, Some(result_ty));
        }
        panic!("undefined function or constructor: {func}")
    }

    fn is_list_builtin(name: &str) -> bool {
        matches!(
            name,
            "List.len"
                | "List.get"
                | "List.set"
                | "List.append"
                | "List.reverse"
                | "List.sublist"
                | "List.repeat"
                | "List.range"
        )
    }

    // ---- Builtin arithmetic dispatch ----

    fn lower_builtin_op(&mut self, name: &str, lhs: Value, rhs: Value, ty: ScalarType) -> Value {
        match name {
            "add" => self.builder.binop(BinaryOp::Add, lhs, rhs, ty),
            "sub" => self.builder.binop(BinaryOp::Sub, lhs, rhs, ty),
            "mul" => self.builder.binop(BinaryOp::Mul, lhs, rhs, ty),
            "div" => self.builder.binop(BinaryOp::Div, lhs, rhs, ty),
            "mod" => self.builder.binop(BinaryOp::Rem, lhs, rhs, ty),
            "bit_and" => self.builder.binop(BinaryOp::And, lhs, rhs, ty),
            "bit_or" => self.builder.binop(BinaryOp::Or, lhs, rhs, ty),
            "bit_xor" => self.builder.binop(BinaryOp::Xor, lhs, rhs, ty),
            "shl" => self.builder.binop(BinaryOp::Shl, lhs, rhs, ty),
            "shr" => self.builder.binop(BinaryOp::Shr, lhs, rhs, ty),
            "equals" => self.lower_eq(lhs, rhs, false),
            "compare" => self.lower_compare(lhs, rhs, ty),
            _ => panic!("unknown builtin: {name}"),
        }
    }

    /// Emit a compare operation returning an Order tag union (Lt/Eq/Gt).
    fn lower_compare(&mut self, lhs: Value, rhs: Value, _ty: ScalarType) -> Value {
        let lt_meta = &self.decls.constructors["Lt"];
        let eq_meta = &self.decls.constructors["Eq"];
        let gt_meta = &self.decls.constructors["Gt"];
        let alloc_size = 8; // Order tags have no payload, one U64 tag discriminant

        let lt_tag_idx = lt_meta.tag_index;
        let eq_tag_idx = eq_meta.tag_index;
        let gt_tag_idx = gt_meta.tag_index;

        let is_lt = self.builder.binop(BinaryOp::Lt, lhs, rhs, ScalarType::U8);
        let is_eq = self.builder.binop(BinaryOp::Eq, lhs, rhs, ScalarType::U8);

        let lt_block = self.builder.create_block();
        let not_lt_block = self.builder.create_block();
        let is_eq_param = self.builder.add_block_param(not_lt_block, ScalarType::U8);
        let eq_block = self.builder.create_block();
        let gt_block = self.builder.create_block();
        let merge = self.builder.create_block();
        let merge_param = self.builder.add_block_param(merge, ScalarType::Ptr);

        self.builder.branch(is_lt, lt_block, vec![], not_lt_block, vec![is_eq]);

        self.builder.switch_to(lt_block);
        let lt_ptr = self.builder.alloc(alloc_size);
        let lt_tag = self.builder.const_u64(lt_tag_idx);
        self.builder.store(lt_ptr, 0, lt_tag);
        self.builder.jump(merge, vec![lt_ptr]);

        self.builder.switch_to(not_lt_block);
        self.builder.branch(is_eq_param, eq_block, vec![], gt_block, vec![]);

        self.builder.switch_to(eq_block);
        let eq_ptr = self.builder.alloc(alloc_size);
        let eq_tag = self.builder.const_u64(eq_tag_idx);
        self.builder.store(eq_ptr, 0, eq_tag);
        self.builder.jump(merge, vec![eq_ptr]);

        self.builder.switch_to(gt_block);
        let gt_ptr = self.builder.alloc(alloc_size);
        let gt_tag = self.builder.const_u64(gt_tag_idx);
        self.builder.store(gt_ptr, 0, gt_tag);
        self.builder.jump(merge, vec![gt_ptr]);

        self.builder.switch_to(merge);
        merge_param
    }

    // ---- Constructor layout ----

    /// Return the layout info for a constructor: `(tag_index,
    /// max_fields, field_scalar_types)`. Declared constructors
    /// (from `TypeAnno` declarations) use their stored
    /// `ConstructorMeta`. Structural constructors (created by
    /// `ast::from_raw`'s pre-pass for uppercase names not in any
    /// declaration) compute layout from the provided `ctx_ty`, which
    /// must be a closed `Type::TagUnion`. Tag index is the
    /// constructor's position in the sorted tag list.
    /// Given a constructor name and a concrete scrutinee type, derive
    /// the specialized payload types by matching the constructor
    /// scheme's return type against `ctx_ty` and substituting type
    /// variables. Returns `None` when the scrutinee's shape doesn't
    /// match the scheme (should not happen for type-correct programs,
    /// but we fall back to the declared meta in that case).
    fn specialize_con_fields(&self, con_name: &str, ctx_ty: &Type) -> Option<Vec<ScalarType>> {
        let scheme = self.decls.constructor_schemes.get(con_name)?;
        let Type::Arrow(params, ret) = &scheme.ty else {
            return None;
        };
        let resolved_ctx = self.resolve_transparent(ctx_ty);
        let (scheme_args, ctx_args) = match (ret.as_ref(), &resolved_ctx) {
            (Type::App(sn, sa), Type::App(cn, ca)) if sn == cn && sa.len() == ca.len() => {
                (sa, ca)
            }
            (Type::Con(sn), Type::Con(cn)) if sn == cn => {
                return Some(
                    params.iter().map(|p| self.scalar_type(p)).collect(),
                );
            }
            // Scheme's return is a bare TagUnion (unusual) or shapes
            // don't line up — punt to the caller's fallback.
            _ => return None,
        };
        let mut specialized_params: Vec<Type> = params.to_vec();
        for (sa, ca) in scheme_args.iter().zip(ctx_args) {
            if let Type::Var(v) = sa {
                specialized_params = specialized_params
                    .iter()
                    .map(|p| substitute_type_var(p, *v, ca))
                    .collect();
            }
        }
        Some(specialized_params.iter().map(|p| self.scalar_type(p)).collect())
    }

    fn con_layout(
        &self,
        name: &str,
        ctx_ty: Option<&Type>,
    ) -> (u64, usize, Vec<ScalarType>) {
        // Field types stored in `decl_info.constructors` come from the
        // polymorphic declared scheme, so a generic parameter like `ok`
        // in `Ok : ok -> Result(ok, err)` resolves to `Ptr`. The
        // monomorphized call site knows the concrete payload types via
        // `ctx_ty`; use them to override, while keeping the declared
        // meta's tag_index (declaration order) and max_fields.
        let specialized = ctx_ty.and_then(|ty| self.specialize_con_fields(name, ty));
        if let Some(meta) = self.decls.constructors.get(name) {
            let fields = specialized.unwrap_or_else(|| meta.field_types.clone());
            return (meta.tag_index, meta.max_fields, fields);
        }
        let ty = ctx_ty.unwrap_or_else(|| {
            panic!("structural constructor '{name}' without context type")
        });
        structural_con_layout(ty, name, &self.decls.fieldless_tags)
    }

    // ---- Constructor call emission ----

    /// Emit a constructor call. `ctx_ty` is the type of the
    /// enclosing expression — used to compute layout for
    /// structural constructors (which don't have entries in
    /// `decl_info.constructors`). For declared constructors the
    /// `ctx_ty` is ignored and `ConstructorMeta` is used directly.
    fn lower_constructor_call(
        &mut self,
        name: &str,
        args: &[Value],
        ctx_ty: Option<&Type>,
    ) -> Value {
        let (tag_index, max_fields, field_types) = self.con_layout(name, ctx_ty);
        // Fieldless tag union: represent as a bare discriminant integer.
        if max_fields == 0 {
            let disc_ty = ctx_ty
                .map(|t| self.scalar_type(t))
                .unwrap_or(ScalarType::U8);
            return self.const_tag(tag_index, disc_ty);
        }
        // Every tag-union constructor is heap-allocated (Phase A:
        // `Agg(n)` is gone). The shape: tag at slot 0, payload from
        // slot 1.
        {
            let alloc_size = (1 + max_fields) * 8;
            let ptr = self.builder.alloc(alloc_size);
            let tag_val = self.builder.const_u64(tag_index);
            self.builder.store(ptr, 0, tag_val);
            for (i, &arg) in args.iter().enumerate() {
                self.builder.store(ptr, (i + 1) * 8, arg);
            }
            ptr
        }
    }

    // ---- Bool tagged-union emission from a raw comparison ----

    /// Materialize a `Bool` tagged-union value (`True` or `False`
    /// ptr) from a raw SSA boolean comparison. Used by `==`/`!=`
    /// lowering and by `x is Con(..)` expressions. Pass `negate =
    /// true` to flip which branch emits `True`.

    /// FNV-1a hash of a single scalar value. Widens or bit-reinterprets
    /// to U64 (F64 via BitCast; integer/Ptr via Cast — same-width Cast
    /// is bit-equivalent), then `(FNV_OFFSET XOR bits) * FNV_PRIME`.

    fn lower_cmp(&mut self, lhs: Value, rhs: Value, op: BinaryOp) -> Value {
        let cmp = self.builder.binop(op, lhs, rhs, ScalarType::U8);
        self.lower_bool_from_cmp(cmp)
    }

    fn lower_bool_from_cmp(&mut self, cmp: Value) -> Value {
        self.lower_bool_from_cmp_neg(cmp, false)
    }

    fn lower_bool_from_cmp_neg(&mut self, cmp: Value, negate: bool) -> Value {
        // Comparisons produce U8(0/1). Bool := [False, True] has
        // False=0, True=1. They're bit-identical — no conversion.
        debug_assert_eq!(self.decls.constructors["False"].tag_index, 0);
        debug_assert_eq!(self.decls.constructors["True"].tag_index, 1);
        if negate {
            let one = self.builder.const_u8(1);
            self.builder.binop(BinaryOp::Xor, cmp, one, ScalarType::U8)
        } else {
            cmp
        }
    }

    /// Lower a standalone `x is Pattern` expression (produces Bool, no binding flow).
    fn lower_is_expr(&mut self, inner: &Expr<'src>, pattern: &ast::Pattern<'src>) -> Value {
        let inner_ty = inner.ty.clone();
        let scr = self.lower_expr(inner);
        match pattern {
            ast::Pattern::Constructor { name, .. } => {
                let (tag_index, max_fields, _) = self.con_layout(name, Some(&inner_ty));
                let fieldless = max_fields == 0;
                let tag = if fieldless {
                    scr
                } else {
                    self.builder.load(scr, 0, ScalarType::U64)
                };
                let disc_ty = if fieldless {
                    self.scalar_type(&inner_ty)
                } else {
                    ScalarType::U64
                };
                let expected_tag = self.const_tag(tag_index, disc_ty);
                let matches = self
                    .builder
                    .binop(BinaryOp::Eq, tag, expected_tag, ScalarType::U8);
                self.lower_bool_from_cmp(matches)
            }
            ast::Pattern::IntLit(n) => {
                let scr_ty = self.expr_scalar_type(inner);
                let lit_val = self.builder.const_i64(*n);
                let eq = self
                    .builder
                    .binop(BinaryOp::Eq, scr, lit_val, scr_ty);
                self.lower_bool_from_cmp(eq)
            }
            ast::Pattern::Wildcard | ast::Pattern::Binding(_) => {
                // Always matches — emit a declared Bool::True.
                self.lower_constructor_call("True", &[], None)
            }
            _ => panic!("unsupported pattern in `is` expression"),
        }
    }

    /// Lower `lhs and rhs` with fused Is-chain support (bindings flow from lhs into rhs).
    fn lower_and_expr(&mut self, lhs: &Expr<'src>, rhs: &Expr<'src>) -> Value {
        let disc_ty = self.decls.fieldless_tags.get("Bool").copied().unwrap_or(ScalarType::U8);
        let merge = self.builder.create_block();
        let merge_param = self.builder.add_block_param(merge, disc_ty);
        let false_block = self.builder.create_block();

        let saved_vars = self.vars.clone();

        // Lower LHS chain — may emit branches to false_block, accumulating bindings
        self.lower_and_chain(lhs, false_block, &[]);

        // We're in the success path — all Is bindings from lhs are in scope
        let rhs_val = self.lower_expr(rhs);
        self.builder.jump(merge, vec![rhs_val]);

        // False block: produce False tag and jump to merge
        self.builder.switch_to(false_block);
        let false_tag_idx = self.decls.constructors["False"].tag_index;
        let false_val = self.const_tag(false_tag_idx, disc_ty);
        self.builder.jump(merge, vec![false_val]);

        self.vars = saved_vars;
        self.builder.switch_to(merge);
        merge_param
    }

    /// Recursively process an And chain, branching to `false_block` on failure
    /// and accumulating Is bindings in `self.vars` on success.
    fn lower_and_chain(&mut self, expr: &Expr<'src>, false_block: BlockId, false_args: &[Value]) {
        match &expr.kind {
            ExprKind::Is {
                expr: inner,
                pattern,
            } => {
                let inner_ty = inner.ty.clone();
                let scr = self.lower_expr(inner);
                match pattern {
                    ast::Pattern::Constructor { name, fields } => {
                        let (tag_index, max_fields, field_types) =
                            self.con_layout(name, Some(&inner_ty));
                        let fieldless = max_fields == 0;
                        let tag = if fieldless {
                            scr // already the discriminant
                        } else {
                            self.builder.load(scr, 0, ScalarType::U64)
                        };
                        let disc_ty = if fieldless {
                            self.scalar_type(&inner_ty)
                        } else {
                            ScalarType::U64
                        };
                        let expected_tag = self.const_tag(tag_index, disc_ty);
                        let matches =
                            self.builder
                                .binop(BinaryOp::Eq, tag, expected_tag, ScalarType::U8);
                        let match_block = self.builder.create_block();
                        let scr_is_func_param = self.builder.func.params.contains(&scr);
                        let scr_in_match = if scr_is_func_param {
                            self.builder
                                .branch(matches, match_block, vec![], false_block, false_args.to_vec());
                            scr
                        } else {
                            let scr_ty = scr.ty;
                            let scr_param = self.builder.add_block_param(match_block, scr_ty);
                            self.builder
                                .branch(matches, match_block, vec![scr], false_block, false_args.to_vec());
                            scr_param
                        };
                        self.builder.switch_to(match_block);
                        // Bind pattern fields (empty for fieldless tags)
                        for (fi, field_pat) in fields.iter().enumerate() {
                            let field_ty =
                                field_types.get(fi).copied().unwrap_or(ScalarType::Ptr);
                            let field_val =
                                self.builder.load(scr_in_match, (fi + 1) * 8, field_ty);
                            self.bind_pattern_field(field_pat, field_val);
                        }
                    }
                    ast::Pattern::Binding(sym) => {
                        // Always matches, bind value
                        self.vars.insert(*sym, scr);
                    }
                    ast::Pattern::Wildcard => {
                        // Always matches, no binding
                    }
                    _ => panic!("unsupported pattern in `is` chain"),
                }
            }
            ExprKind::BinOp {
                op: BinOp::And,
                lhs,
                rhs,
            } => {
                // Process LHS first (may branch, accumulating bindings)
                self.lower_and_chain(lhs, false_block, false_args);
                // Then process RHS (we're in the LHS success path)
                self.lower_and_chain(rhs, false_block, false_args);
            }
            _ => {
                // Regular boolean expression — evaluate, compare unboxed tag, branch
                let val = self.lower_expr(expr);
                let disc_ty = self.decls.fieldless_tags.get("Bool").copied().unwrap_or(ScalarType::U8);
                let true_tag = self.decls.constructors["True"].tag_index;
                let true_val = self.const_tag(true_tag, disc_ty);
                let is_true = self
                    .builder
                    .binop(BinaryOp::Eq, val, true_val, ScalarType::U8);
                let continue_block = self.builder.create_block();
                self.builder
                    .branch(is_true, continue_block, vec![], false_block, false_args.to_vec());
                self.builder.switch_to(continue_block);
            }
        }
    }

    /// Lower `lhs or rhs` with short-circuit evaluation.
    fn lower_or_expr(&mut self, lhs: &Expr<'src>, rhs: &Expr<'src>) -> Value {
        let disc_ty = self.decls.fieldless_tags.get("Bool").copied().unwrap_or(ScalarType::U8);
        let merge = self.builder.create_block();
        let merge_param = self.builder.add_block_param(merge, disc_ty);

        let lhs_val = self.lower_expr(lhs);
        let true_tag = self.decls.constructors["True"].tag_index;
        let true_val = self.const_tag(true_tag, disc_ty);
        let is_true = self
            .builder
            .binop(BinaryOp::Eq, lhs_val, true_val, ScalarType::U8);
        let rhs_block = self.builder.create_block();
        // If LHS is True, short-circuit to merge with LHS value
        self.builder
            .branch(is_true, merge, vec![lhs_val], rhs_block, vec![]);

        self.builder.switch_to(rhs_block);
        let rhs_val = self.lower_expr(rhs);
        self.builder.jump(merge, vec![rhs_val]);

        self.builder.switch_to(merge);
        merge_param
    }


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
        .unwrap_or_else(|| vec![ScalarType::Ptr; params.len()]);
    let main_ssa_params: Vec<Value> = params
        .iter()
        .zip(&main_param_tys)
        .map(|(p, &ty)| {
            let v = ctx.builder.add_func_param(ty);
            ctx.vars.insert(*p, v);
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
/// `Type::TagUnion` context. Returns `(tag_index, max_fields,
/// field_scalar_types)`. Tag index is the constructor's position in
/// the tag list sorted by name (dense, 0..N). Max fields is the
/// maximum payload arity across all tags in the union. Payload scalar
/// types are computed from the constructor's payload types in the
/// sorted union.
///
/// Panics if `ty` isn't a closed `Type::TagUnion` or if `con_name`
/// isn't present among its tags — both are bugs in earlier passes
/// that should have been caught by inference/mono.
fn structural_con_layout(
    ty: &Type,
    con_name: &str,
    fieldless: &HashMap<String, ScalarType>,
) -> (u64, usize, Vec<ScalarType>) {
    let Type::TagUnion { tags, rest } = ty else {
        panic!(
            "structural constructor '{con_name}' expected TagUnion context, got {ty:?}"
        );
    };
    assert!(
        rest.is_none(),
        "structural constructor '{con_name}' context has open row — mono should have closed it"
    );
    let mut sorted: Vec<(String, Vec<Type>)> = tags.clone();
    sorted.sort_by(|a, b| a.0.cmp(&b.0));
    let max_fields = sorted.iter().map(|(_, p)| p.len()).max().unwrap_or(0);
    let idx = sorted
        .iter()
        .position(|(n, _)| n == con_name)
        .unwrap_or_else(|| {
            panic!("structural constructor '{con_name}' not in union {tags:?}")
        });
    #[allow(clippy::cast_possible_truncation, reason = "tag count fits in u64")]
    let tag_index = idx as u64;
    let field_types: Vec<ScalarType> = sorted[idx]
        .1
        .iter()
        .map(|t| resolve_scalar_type(t, fieldless))
        .collect();
    (tag_index, max_fields, field_types)
}

/// Replace all occurrences of `var` in `ty` with `replacement`.
fn substitute_type_var(ty: &Type, var: TypeVar, replacement: &Type) -> Type {
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
