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
pub fn lower(
    mono: &Monomorphized<'_>,
    fields: &FieldInterner,
) -> Result<(Module, Vec<Value>), CompileError> {
    let decls = decl_info::build(mono);
    lower_to_ssa(&mono.module, &mono.infer, &decls, &mono.symbols, fields, &mono.singletons, &mono.tag_targets)
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

    /// Check if a value is a value-type aggregate (Pack result).
    fn is_agg(&self, val: Value) -> bool {
        matches!(self.builder.value_types.get(&val), Some(ScalarType::Agg(_)))
    }

    /// Box a value-type aggregate into a heap-allocated Ptr.
    /// Returns the value unchanged if it's already Ptr.
    fn box_if_agg(&mut self, val: Value) -> Value {
        let Some(ScalarType::Agg(n)) = self.builder.value_types.get(&val).copied() else {
            return val;
        };
        let ptr = self.builder.alloc(n);
        for i in 0..n {
            let field = self.builder.extract(val, i, ScalarType::U64); // type doesn't matter for runtime
            self.builder.store(ptr, i, field);
        }
        ptr
    }

    /// Load a field from a value — Extract if Agg, Load if Ptr.
    fn load_field(&mut self, val: Value, slot: usize, ty: ScalarType) -> Value {
        if self.is_agg(val) {
            self.builder.extract(val, slot, ty)
        } else {
            self.builder.load(val, slot, ty)
        }
    }

    /// Check if a list of scalar types can be packed (all non-Ptr, ≤8 fields).
    fn can_pack(field_types: &[ScalarType]) -> bool {
        field_types.len() <= 8
            && !field_types.is_empty()
            && field_types.iter().all(|t| !matches!(t, ScalarType::Ptr | ScalarType::Agg(_)))
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

struct WalkKind {
    until: bool,
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

    /// Like `scalar_type` but returns `Agg(n)` for packable composite
    /// types. Used at merge-point block params so that freshly packed
    /// values flow through without heap boxing.
    fn repr_type(&self, ty: &Type) -> ScalarType {
        let base = self.scalar_type(ty);
        if base == ScalarType::Ptr {
            if let Some(n) = self.packable_field_count(ty) {
                return ScalarType::Agg(n);
            }
        }
        base
    }

    fn expr_repr_type(&self, expr: &Expr<'src>) -> ScalarType {
        self.repr_type(&expr.ty)
    }

    /// If `ty` is a composite that `can_pack` would accept, return
    /// its field count. Records and tuples return their field count
    /// directly; tag unions return 1 + max_fields (tag slot + payload).
    fn packable_field_count(&self, ty: &Type) -> Option<usize> {
        let resolved = self.resolve_transparent(ty);
        match &resolved {
            Type::Record { fields, .. } => {
                let mut sorted: Vec<(&str, &Type)> =
                    fields.iter().map(|(n, t)| (n.as_str(), t)).collect();
                sorted.sort_unstable_by_key(|(n, _)| *n);
                let field_types: Vec<ScalarType> =
                    sorted.iter().map(|(_, t)| self.scalar_type(t)).collect();
                if Self::can_pack(&field_types) {
                    Some(field_types.len())
                } else {
                    None
                }
            }
            Type::Tuple(elems) => {
                let field_types: Vec<ScalarType> =
                    elems.iter().map(|t| self.scalar_type(t)).collect();
                if Self::can_pack(&field_types) {
                    Some(field_types.len())
                } else {
                    None
                }
            }
            Type::TagUnion { tags, .. } => {
                if tags.iter().all(|(_, fs)| fs.is_empty()) {
                    return None;
                }
                let max_fields = tags.iter().map(|(_, fs)| fs.len()).max().unwrap_or(0);
                let all_non_ptr = tags.iter().all(|(_, fs)| {
                    fs.iter()
                        .all(|t| !matches!(self.scalar_type(t), ScalarType::Ptr | ScalarType::Agg(_)))
                });
                if all_non_ptr && 1 + max_fields <= 8 {
                    Some(1 + max_fields)
                } else {
                    None
                }
            }
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
            ScalarType::Agg(n) => {
                let fields: Vec<Value> = (0..n).map(|_| self.builder.const_u64(0)).collect();
                self.builder.pack(fields)
            }
        }
    }

    // ---- Field slot computation ----

    fn field_slot(&self, ty: &Type, field: &str) -> usize {
        // Unwrap transparent types to their underlying representation.
        let resolved = self.resolve_transparent(ty);
        match &resolved {
            Type::Record { fields, .. } => {
                let mut names: Vec<&str> = fields.iter().map(|(n, _)| n.as_str()).collect();
                names.sort_unstable();
                names
                    .iter()
                    .position(|n| *n == field)
                    .unwrap_or_else(|| panic!("field '{field}' not found in record type"))
            }
            Type::Tuple(elems) => {
                let mut names: Vec<String> = (0..elems.len()).map(|i| i.to_string()).collect();
                names.sort_unstable();
                names
                    .iter()
                    .position(|n| n == field)
                    .unwrap_or_else(|| panic!("field '{field}' not found in tuple type"))
            }
            _ => panic!("field access on non-record type: {resolved:?} (original: {ty:?})"),
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
            self.builder
                .value_types
                .get(&result)
                .copied()
                .unwrap_or(ScalarType::Ptr)
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
                lower_int_const(&mut self.builder, *n, &expr.ty)
            }

            ExprKind::FloatLit(n) => self.builder.const_f64(*n),

            ExprKind::StrLit(bytes) => {
                let len = bytes.len();
                let data = self.builder.alloc(len);
                for (i, &b) in bytes.iter().enumerate() {
                    let val = self.builder.const_u8(b);
                    self.builder.store(data, i, val);
                }
                let header = self.builder.alloc(3);
                let len_val = self.builder.const_u64(len as u64);
                self.builder.store(header, 0, len_val);
                self.builder.store(header, 1, len_val);
                self.builder.store(header, 2, data);
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
                if Self::can_pack(&field_types) {
                    self.builder.pack(vals)
                } else {
                    let ptr = self.builder.alloc(fields.len());
                    for (slot, val) in vals.into_iter().enumerate() {
                        self.builder.store(ptr, slot, val);
                    }
                    ptr
                }
            }

            ExprKind::FieldAccess { record, field } => {
                let val = self.lower_expr(record);
                let field_name = self.fields.get(*field);
                let slot = self.field_slot(&record.ty, field_name);
                let ty = self.expr_scalar_type(expr);
                if self.is_agg(val) {
                    self.builder.extract(val, slot, ty)
                } else {
                    self.builder.load(val, slot, ty)
                }
            }

            ExprKind::MethodCall {
                receiver,
                method,
                args,
                ..
            } => self.lower_method_call(receiver, method, args, expr),

            ExprKind::Tuple(elems) => {
                let field_types: Vec<ScalarType> = elems.iter()
                    .map(|e| self.expr_scalar_type(e))
                    .collect();
                let vals: Vec<Value> = elems.iter()
                    .map(|e| self.lower_expr(e))
                    .collect();
                if Self::can_pack(&field_types) {
                    self.builder.pack(vals)
                } else {
                    let ptr = self.builder.alloc(elems.len());
                    for (i, val) in vals.into_iter().enumerate() {
                        self.builder.store(ptr, i, val);
                    }
                    ptr
                }
            }

            ExprKind::Lambda { .. } => {
                panic!("lambdas are only supported as direct arguments to function calls");
            }

            ExprKind::RecordUpdate { base, updates } => {
                let base_val = self.lower_expr(base);
                let is_base_agg = self.is_agg(base_val);
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
                let num_fields = all_fields.len();
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
                // Collect all field values.
                let vals: Vec<Value> = all_fields
                    .iter()
                    .enumerate()
                    .map(|(slot, field_name)| {
                        if let Some(upd_expr) = update_map.get(field_name) {
                            self.lower_expr(upd_expr)
                        } else {
                            let ty = field_types.get(slot).copied().unwrap_or(ScalarType::Ptr);
                            if is_base_agg {
                                self.builder.extract(base_val, slot, ty)
                            } else {
                                self.builder.load(base_val, slot, ty)
                            }
                        }
                    })
                    .collect();
                if is_base_agg && Self::can_pack(&field_types) {
                    self.builder.pack(vals)
                } else {
                    let ptr = self.builder.alloc(num_fields);
                    for (slot, val) in vals.into_iter().enumerate() {
                        self.builder.store(ptr, slot, val);
                    }
                    ptr
                }
            }

            ExprKind::ListLit(elems) => {
                let len = elems.len();
                let data = self.builder.alloc(len);
                for (i, elem) in elems.iter().enumerate() {
                    let val = self.lower_expr(elem);
                    self.builder.store(data, i, val);
                }
                let header = self.builder.alloc(3);
                let len_val = self.builder.const_u64(len as u64);
                self.builder.store(header, 0, len_val);
                self.builder.store(header, 1, len_val);
                self.builder.store(header, 2, data);
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
            if op_name == "to_str" {
                // Unary: `x.to_str()` or eta-expanded `I64.to_str(x)`
                let arg = local_val.unwrap_or_else(|| self.lower_expr(&args[0]));
                return self
                    .builder
                    .call("__num_to_str", vec![arg], ScalarType::Ptr);
            }
            if op_name == "from_u8" {
                let arg = local_val.unwrap_or_else(|| self.lower_expr(&args[0]));
                let (rt_fn, ret_ty) = match segments[0] {
                    "U32" => ("__u32_from_u8", ScalarType::U32),
                    _ => ("__u64_from_u8", ScalarType::U64),
                };
                return self.builder.call(rt_fn, vec![arg], ret_ty);
            }
            if op_name == "to_u8" {
                let arg = local_val.unwrap_or_else(|| self.lower_expr(&args[0]));
                return self.builder.call("__to_u8", vec![arg], ScalarType::U8);
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
            if op_name == "to_str" {
                return self
                    .builder
                    .call("__num_to_str", vec![recv_val], ScalarType::Ptr);
            }
            if op_name == "hash" {
                return self
                    .builder
                    .call("__num_hash", vec![recv_val], ScalarType::U64);
            }
            if op_name == "from_u8" {
                let ret_ty = self.expr_scalar_type(outer);
                let rt_fn = if ret_ty == ScalarType::U32 { "__u32_from_u8" } else { "__u64_from_u8" };
                return self.builder.call(rt_fn, vec![recv_val], ret_ty);
            }
            if op_name == "to_u8" {
                return self.builder.call("__to_u8", vec![recv_val], ScalarType::U8);
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
            return emit_list_builtin_call(&mut self.builder, &mangled, arg_vals);
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
            return emit_list_builtin_call(&mut self.builder, func, arg_vals);
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
        let alloc_size = 1; // Order tags have no payload

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
        // Check if all fields (tag + payload) are non-Ptr → Pack.
        let all_non_ptr = field_types.iter().all(|t| !matches!(t, ScalarType::Ptr | ScalarType::Agg(_)));
        if all_non_ptr && 1 + max_fields <= 8 {
            let tag_val = self.builder.const_u64(tag_index);
            let mut pack_fields = Vec::with_capacity(1 + args.len());
            pack_fields.push(tag_val);
            pack_fields.extend_from_slice(args);
            // Pad to max_fields + 1 (tag) if this variant has fewer fields.
            while pack_fields.len() < 1 + max_fields {
                let pad = self.builder.const_u64(0);
                pack_fields.push(pad);
            }
            self.builder.pack(pack_fields)
        } else {
            let alloc_size = 1 + max_fields;
            let ptr = self.builder.alloc(alloc_size);
            let tag_val = self.builder.const_u64(tag_index);
            self.builder.store(ptr, 0, tag_val);
            for (i, &arg) in args.iter().enumerate() {
                self.builder.store(ptr, i + 1, arg);
            }
            ptr
        }
    }

    // ---- Bool tagged-union emission from a raw comparison ----

    /// Materialize a `Bool` tagged-union value (`True` or `False`
    /// ptr) from a raw SSA boolean comparison. Used by `==`/`!=`
    /// lowering and by `x is Con(..)` expressions. Pass `negate =
    /// true` to flip which branch emits `True`.
    fn lower_eq(&mut self, lhs: Value, rhs: Value, negate: bool) -> Value {
        let cmp = self.builder.binop(BinaryOp::Eq, lhs, rhs, ScalarType::U8);
        self.lower_bool_from_cmp_neg(cmp, negate)
    }

    /// True for types where `==` is a single scalar comparison.
    fn is_scalar_eq_type(&self, ty: &Type) -> bool {
        match ty {
            Type::Con(name) => {
                crate::numeric::NumericType::from_name(name).is_some()
                    || self.decls.fieldless_tags.contains_key(name.as_str())
            }
            Type::TagUnion { tags, .. } => tags.iter().all(|(_, fs)| fs.is_empty()),
            _ => false,
        }
    }

    // ---- Generated equality functions ----
    //
    // Instead of inlining equality SSA at every `==` site, generate
    // one named function per concrete type. The BinOp::Eq dispatch
    // just calls it. Cached in `eq_func_cache` so each type gets
    // one function.

    /// True if `ensure_eq_func` would generate a meaningful equality
    /// function (not just scalar eq).
    fn has_eq_func(&self, ty: &Type) -> bool {
        matches!(ty, Type::Record { .. } | Type::Tuple(_) | Type::TagUnion { .. })
            || matches!(ty, Type::App(n, _) if n == "List")
            || self.packable_field_count(ty).is_some()
    }

    /// For a nominal type like Result or Step, find the slot count
    /// (1 + max_fields) by looking up its constructors.
    fn nominal_slot_count(&self, type_name: &str) -> Option<usize> {
        for (con_name, scheme) in &self.infer.constructor_schemes {
            let ret_ty = match &scheme.ty {
                Type::Arrow(_, ret) => ret.as_ref(),
                other => other,
            };
            if let Type::App(ret_name, _) = ret_ty {
                if ret_name == type_name {
                    if let Some(meta) = self.decls.constructors.get(con_name) {
                        if meta.max_fields > 0 && 1 + meta.max_fields <= 8 {
                            return Some(1 + meta.max_fields);
                        }
                    }
                }
            }
        }
        None
    }

    fn mangle_type(ty: &Type) -> String {
        match ty {
            Type::Con(n) => n.clone(),
            Type::App(n, args) => {
                let inner: Vec<String> = args.iter().map(Self::mangle_type).collect();
                format!("{n}({})", inner.join(","))
            }
            Type::Tuple(elems) => {
                let inner: Vec<String> = elems.iter().map(Self::mangle_type).collect();
                format!("({})", inner.join(","))
            }
            Type::Record { fields, .. } => {
                let mut sorted: Vec<(&str, &Type)> =
                    fields.iter().map(|(n, t)| (n.as_str(), t)).collect();
                sorted.sort_by_key(|(n, _)| *n);
                let inner: Vec<String> = sorted
                    .iter()
                    .map(|(n, t)| format!("{n}:{}", Self::mangle_type(t)))
                    .collect();
                format!("{{{}}}", inner.join(","))
            }
            Type::TagUnion { tags, .. } => {
                let inner: Vec<String> = tags
                    .iter()
                    .map(|(n, fs)| {
                        if fs.is_empty() {
                            n.clone()
                        } else {
                            let fstrs: Vec<String> = fs.iter().map(Self::mangle_type).collect();
                            format!("{n}({})", fstrs.join(","))
                        }
                    })
                    .collect();
                format!("[{}]", inner.join(","))
            }
            _ => format!("{ty:?}"),
        }
    }

    fn ensure_eq_func(&mut self, ty: &Type) -> String {
        let name = format!("__eq__{}", Self::mangle_type(ty));
        if self.eq_func_cache.contains(&name) {
            return name;
        }
        // Mark as generated BEFORE emitting body (handles recursive types).
        self.eq_func_cache.insert(name.clone());

        let saved_vars = std::mem::take(&mut self.vars);
        let saved_func = std::mem::replace(
            &mut self.builder.func,
            crate::ssa::builder::FuncBuilder::new(),
        );
        let saved_current = self.builder.current_block.take();
        let saved_types = std::mem::take(&mut self.builder.value_types);

        let param_ty = self.scalar_type(ty);
        let lhs = self.builder.add_func_param(param_ty);
        let rhs = self.builder.add_func_param(param_ty);
        self.builder.set_return_type(ScalarType::U8);

        let entry = self.builder.create_block();
        self.builder.switch_to(entry);
        let result = self.emit_eq_body(lhs, rhs, ty);
        self.builder.ret(result);
        self.builder.finish_function(&name, ScalarType::U8);

        self.builder.func = saved_func;
        self.builder.current_block = saved_current;
        self.builder.value_types = saved_types;
        self.vars = saved_vars;

        name
    }

    fn emit_eq_body(&mut self, lhs: Value, rhs: Value, ty: &Type) -> Value {
        let resolved = self.resolve_transparent(ty);
        let ty = &resolved;
        match ty {
            Type::Record { fields, .. } => {
                let mut sorted: Vec<(&str, &Type)> =
                    fields.iter().map(|(n, t)| (n.as_str(), t)).collect();
                sorted.sort_by_key(|(n, _)| *n);
                let field_types: Vec<&Type> = sorted.iter().map(|(_, t)| *t).collect();
                self.emit_fields_eq(lhs, rhs, &field_types)
            }
            Type::Tuple(elems) => {
                let field_types: Vec<&Type> = elems.iter().collect();
                self.emit_fields_eq(lhs, rhs, &field_types)
            }
            Type::TagUnion { tags, .. } => {
                let max_fields = tags.iter().map(|(_, fs)| fs.len()).max().unwrap_or(0);
                // Tag + payload slots — compare all as U64.
                let n = 1 + max_fields;
                self.emit_slots_eq(lhs, rhs, n)
            }
            Type::App(name, args) if name == "List" => {
                let elem_ty = args.first();
                self.emit_list_eq(lhs, rhs, elem_ty)
            }
            Type::App(name, _) | Type::Con(name) => {
                // Nominal types (Result, Step, etc.): find the
                // constructor slot count and compare structurally.
                if let Some(n) = self.nominal_slot_count(name) {
                    self.emit_slots_eq(lhs, rhs, n)
                } else {
                    self.builder.binop(BinaryOp::Eq, lhs, rhs, ScalarType::U8)
                }
            }
            _ => self.builder.binop(BinaryOp::Eq, lhs, rhs, ScalarType::U8),
        }
    }

    /// Compare a fixed number of typed fields, recursing into sub-types.
    fn emit_fields_eq(&mut self, lhs: Value, rhs: Value, field_types: &[&Type]) -> Value {
        if field_types.is_empty() {
            return self.builder.const_u8(1);
        }
        let false_block = self.builder.create_block();
        let true_block = self.builder.create_block();
        let merge = self.builder.create_block();
        let merge_param = self.builder.add_block_param(merge, ScalarType::U8);

        for (slot, field_ty) in field_types.iter().enumerate() {
            let sty = self.scalar_type(field_ty);
            let l = self.load_field(lhs, slot, sty);
            let r = self.load_field(rhs, slot, sty);
            let field_eq = if self.is_scalar_eq_type(field_ty) {
                self.builder.binop(BinaryOp::Eq, l, r, ScalarType::U8)
            } else {
                let sub_eq = self.ensure_eq_func(field_ty);
                self.builder.call(&sub_eq, vec![l, r], ScalarType::U8)
            };
            let next = if slot + 1 < field_types.len() {
                self.builder.create_block()
            } else {
                true_block
            };
            self.builder.branch(field_eq, next, vec![], false_block, vec![]);
            if slot + 1 < field_types.len() {
                self.builder.switch_to(next);
            }
        }

        self.builder.switch_to(true_block);
        let t = self.builder.const_u8(1);
        self.builder.jump(merge, vec![t]);
        self.builder.switch_to(false_block);
        let f = self.builder.const_u8(0);
        self.builder.jump(merge, vec![f]);
        self.builder.switch_to(merge);
        merge_param
    }

    /// Compare n slots as raw U64 values (for packed tag unions / Agg).
    fn emit_slots_eq(&mut self, lhs: Value, rhs: Value, n: usize) -> Value {
        if n == 0 {
            return self.builder.const_u8(1);
        }
        let false_block = self.builder.create_block();
        let true_block = self.builder.create_block();
        let merge = self.builder.create_block();
        let merge_param = self.builder.add_block_param(merge, ScalarType::U8);

        for slot in 0..n {
            let l = self.load_field(lhs, slot, ScalarType::U64);
            let r = self.load_field(rhs, slot, ScalarType::U64);
            let eq = self.builder.binop(BinaryOp::Eq, l, r, ScalarType::U8);
            let next = if slot + 1 < n { self.builder.create_block() } else { true_block };
            self.builder.branch(eq, next, vec![], false_block, vec![]);
            if slot + 1 < n { self.builder.switch_to(next); }
        }

        self.builder.switch_to(true_block);
        let t = self.builder.const_u8(1);
        self.builder.jump(merge, vec![t]);
        self.builder.switch_to(false_block);
        let f = self.builder.const_u8(0);
        self.builder.jump(merge, vec![f]);
        self.builder.switch_to(merge);
        merge_param
    }

    /// List equality: compare lengths, then element-by-element.
    fn emit_list_eq(&mut self, lhs: Value, rhs: Value, elem_ty: Option<&Type>) -> Value {
        let len_a = self.builder.call("__list_len", vec![lhs], ScalarType::U64);
        let len_b = self.builder.call("__list_len", vec![rhs], ScalarType::U64);
        let len_eq = self.builder.binop(BinaryOp::Eq, len_a, len_b, ScalarType::U8);

        let check_elems = self.builder.create_block();
        let check_len_param = self.builder.add_block_param(check_elems, ScalarType::U64);
        let false_block = self.builder.create_block();
        let merge = self.builder.create_block();
        let merge_param = self.builder.add_block_param(merge, ScalarType::U8);
        self.builder.branch(len_eq, check_elems, vec![len_a], false_block, vec![]);

        self.builder.switch_to(check_elems);
        let header = self.builder.create_block();
        let i_param = self.builder.add_block_param(header, ScalarType::U64);
        let header_len_param = self.builder.add_block_param(header, ScalarType::U64);
        let body = self.builder.create_block();
        let body_i_param = self.builder.add_block_param(body, ScalarType::U64);
        let body_len_param = self.builder.add_block_param(body, ScalarType::U64);
        let zero = self.builder.const_u64(0);
        self.builder.jump(header, vec![zero, check_len_param]);

        self.builder.switch_to(header);
        let done = self.builder.binop(BinaryOp::Eq, i_param, header_len_param, ScalarType::U8);
        let true_val = self.builder.const_u8(1);
        self.builder.branch(done, merge, vec![true_val], body, vec![i_param, header_len_param]);

        self.builder.switch_to(body);
        let elem_a = self.builder.call("__list_get", vec![lhs, body_i_param], ScalarType::Ptr);
        let elem_b = self.builder.call("__list_get", vec![rhs, body_i_param], ScalarType::Ptr);
        let elem_eq = if let Some(et) = elem_ty {
            if self.is_scalar_eq_type(et) {
                self.builder.binop(BinaryOp::Eq, elem_a, elem_b, ScalarType::U8)
            } else {
                let sub_eq = self.ensure_eq_func(et);
                self.builder.call(&sub_eq, vec![elem_a, elem_b], ScalarType::U8)
            }
        } else {
            self.builder.binop(BinaryOp::Eq, elem_a, elem_b, ScalarType::U8)
        };
        let one = self.builder.const_u64(1);
        let next_i = self.builder.binop(BinaryOp::Add, body_i_param, one, ScalarType::U64);
        self.builder.branch(elem_eq, header, vec![next_i, body_len_param], false_block, vec![]);

        self.builder.switch_to(false_block);
        let false_val = self.builder.const_u8(0);
        self.builder.jump(merge, vec![false_val]);

        self.builder.switch_to(merge);
        merge_param
    }

    /// Record hash: FNV-1a over each field in sorted order.
    fn lower_record_hash(&mut self, recv: Value, ty: &Type) -> Value {
        let Type::Record { fields, .. } = ty else {
            panic!("lower_record_hash called on non-record type");
        };
        let mut sorted: Vec<(&str, &Type)> = fields.iter().map(|(n, t)| (n.as_str(), t)).collect();
        sorted.sort_by_key(|(n, _)| *n);

        // FNV-1a offset basis
        #[expect(clippy::unreadable_literal)]
        let mut hash = self.builder.const_u64(14695981039346656037);

        for (slot, (_name, field_ty)) in sorted.iter().enumerate() {
            let field_val = self.load_field(recv, slot, self.scalar_type(field_ty));
            let field_hash = if let Type::Record { .. } = field_ty {
                self.lower_record_hash(field_val, field_ty)
            } else {
                self.builder
                    .call("__num_hash", vec![field_val], ScalarType::U64)
            };
            // hash = (hash XOR field_hash) * FNV prime
            hash = self
                .builder
                .binop(BinaryOp::Xor, hash, field_hash, ScalarType::U64);
            #[expect(clippy::unreadable_literal)]
            let prime = self.builder.const_u64(1099511628211);
            hash = self
                .builder
                .binop(BinaryOp::Mul, hash, prime, ScalarType::U64);
        }
        hash
    }

    /// Tuple hash: FNV-1a over each element in order.
    fn lower_tuple_hash(&mut self, recv: Value, ty: &Type) -> Value {
        let Type::Tuple(elem_types) = ty else {
            panic!("lower_tuple_hash called on non-tuple type");
        };

        #[expect(clippy::unreadable_literal)]
        let mut hash = self.builder.const_u64(14695981039346656037);

        for (slot, elem_ty) in elem_types.iter().enumerate() {
            let elem_val = self.load_field(recv, slot, self.scalar_type(elem_ty));
            let elem_hash = if let Type::Record { .. } = elem_ty {
                self.lower_record_hash(elem_val, elem_ty)
            } else if let Type::Tuple(_) = elem_ty {
                self.lower_tuple_hash(elem_val, elem_ty)
            } else {
                self.builder
                    .call("__num_hash", vec![elem_val], ScalarType::U64)
            };
            hash = self
                .builder
                .binop(BinaryOp::Xor, hash, elem_hash, ScalarType::U64);
            #[expect(clippy::unreadable_literal)]
            let prime = self.builder.const_u64(1099511628211);
            hash = self
                .builder
                .binop(BinaryOp::Mul, hash, prime, ScalarType::U64);
        }
        hash
    }

    /// Tag union hash: hash the tag index, then the payload fields.
    fn lower_tag_hash(&mut self, recv: Value, _ty: &Type) -> Value {
        // Hash the tag index (slot 0) plus the payload (slot 1).
        // This is a simplified version — we treat the payload as
        // an opaque Ptr and hash its address. For full structural
        // hashing of payloads, we'd need to know the payload type
        // per-tag at this point.
        #[expect(clippy::unreadable_literal)]
        let mut hash = self.builder.const_u64(14695981039346656037);

        // Hash the tag index.
        let tag = self.builder.load(recv, 0, ScalarType::U64);
        let tag_hash = self
            .builder
            .call("__num_hash", vec![tag], ScalarType::U64);
        hash = self
            .builder
            .binop(BinaryOp::Xor, hash, tag_hash, ScalarType::U64);
        #[expect(clippy::unreadable_literal)]
        let prime = self.builder.const_u64(1099511628211);
        hash = self
            .builder
            .binop(BinaryOp::Mul, hash, prime, ScalarType::U64);

        // Hash the payload (slot 1) — treat as raw value.
        let payload = self.builder.load(recv, 1, ScalarType::Ptr);
        let payload_hash = self
            .builder
            .call("__num_hash", vec![payload], ScalarType::U64);
        hash = self
            .builder
            .binop(BinaryOp::Xor, hash, payload_hash, ScalarType::U64);
        #[expect(clippy::unreadable_literal)]
        let prime2 = self.builder.const_u64(1099511628211);
        self.builder
            .binop(BinaryOp::Mul, hash, prime2, ScalarType::U64)
    }

    /// Record to_str: produces `"{ field1: val1, field2: val2 }"`.
    fn lower_record_to_str(&mut self, recv: Value, ty: &Type) -> Value {
        let Type::Record { fields, .. } = ty else {
            panic!("lower_record_to_str called on non-record type");
        };
        let mut sorted: Vec<(String, Type)> = fields
            .iter()
            .map(|(n, t)| (n.clone(), t.clone()))
            .collect();
        sorted.sort_by(|(a, _), (b, _)| a.cmp(b));

        // Start with "{ "
        let mut acc = self.lower_str_literal(b"{ ");
        for (i, (name, field_ty)) in sorted.iter().enumerate() {
            if i > 0 {
                let sep = self.lower_str_literal(b", ");
                acc = self.lower_str_concat(acc, sep);
            }
            // "fieldname: "
            let label = format!("{name}: ");
            let label_val = self.lower_str_literal(label.as_bytes());
            acc = self.lower_str_concat(acc, label_val);
            // value.to_str()
            let field_val = self.load_field(recv, i, self.scalar_type(&field_ty));
            let val_str = if let Type::Record { .. } = &field_ty {
                self.lower_record_to_str(field_val, &field_ty)
            } else {
                self.builder.call("__num_to_str", vec![field_val], ScalarType::Ptr)
            };
            acc = self.lower_str_concat(acc, val_str);
        }
        // " }"
        let close = self.lower_str_literal(b" }");
        self.lower_str_concat(acc, close)
    }

    /// Helper: emit a string literal as a List(U8) header.
    fn lower_str_literal(&mut self, bytes: &[u8]) -> Value {
        let len = bytes.len();
        let data = self.builder.alloc(len);
        for (i, &b) in bytes.iter().enumerate() {
            let val = self.builder.const_u8(b);
            self.builder.store(data, i, val);
        }
        let header = self.builder.alloc(3);
        let len_val = self.builder.const_u64(len as u64);
        self.builder.store(header, 0, len_val);
        self.builder.store(header, 1, len_val);
        self.builder.store(header, 2, data);
        header
    }

    /// Helper: emit string concatenation via builtin.
    fn lower_str_concat(&mut self, a: Value, b: Value) -> Value {
        self.builder.call("__str_concat", vec![a, b], ScalarType::Ptr)
    }

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
                let scr_is_agg = self.is_agg(scr);
                let tag = if fieldless {
                    scr
                } else if scr_is_agg {
                    self.builder.extract(scr, 0, ScalarType::U64)
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
                        let scr_is_agg = self.is_agg(scr);
                        let tag = if fieldless {
                            scr // already the discriminant
                        } else if scr_is_agg {
                            self.builder.extract(scr, 0, ScalarType::U64)
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
                            let scr_ty = self.builder.value_types.get(&scr).copied().unwrap_or(ScalarType::Ptr);
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
                            let field_val = if scr_is_agg {
                                self.builder.extract(scr_in_match, fi + 1, field_ty)
                            } else {
                                self.builder.load(scr_in_match, fi + 1, field_ty)
                            };
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

    // ---- Boolean if-then-else with Is binding flow ----

    /// Check if this is a boolean if-then-else (True/False arms) where the
    /// scrutinee contains Is expressions that need binding flow.
    fn is_bool_if_with_is(scrutinee: &Expr<'src>, arms: &[ast::MatchArm<'src>]) -> bool {
        if arms.len() != 2 {
            return false;
        }
        let is_true_false = matches!(
            (&arms[0].pattern, &arms[1].pattern),
            (
                ast::Pattern::Constructor { name: "True", .. },
                ast::Pattern::Constructor { name: "False", .. }
            )
        );
        if !is_true_false {
            return false;
        }
        Self::expr_contains_is(scrutinee)
    }

    /// Check if an expression tree contains any Is expression.
    fn expr_contains_is(expr: &Expr<'src>) -> bool {
        match &expr.kind {
            ExprKind::Is { .. } => true,
            ExprKind::BinOp { lhs, rhs, .. } => {
                Self::expr_contains_is(lhs) || Self::expr_contains_is(rhs)
            }
            _ => false,
        }
    }

    /// Lower a boolean if-then-else where the scrutinee contains Is expressions,
    /// flowing bindings from the scrutinee into the True arm body.
    fn lower_bool_if_with_is(
        &mut self,
        scrutinee: &Expr<'src>,
        arms: &[ast::MatchArm<'src>],
        result_ty: ScalarType,
    ) -> Value {
        let merge = self.builder.create_block();
        let merge_param = self.builder.add_block_param(merge, result_ty);
        let false_block = self.builder.create_block();

        let saved_vars = self.vars.clone();

        // Use and-chain lowering for the scrutinee — bindings flow into self.vars
        self.lower_and_chain(scrutinee, false_block, &[]);

        // True arm: bindings from Is are in scope
        let true_result = self.lower_expr(&arms[0].body);
        if arms[0].is_return {
            self.builder.ret(true_result);
        } else {
            self.builder.jump(merge, vec![true_result]);
        }

        // False arm
        self.builder.switch_to(false_block);
        self.vars = saved_vars;
        let false_result = self.lower_expr(&arms[1].body);
        if arms[1].is_return {
            self.builder.ret(false_result);
        } else {
            self.builder.jump(merge, vec![false_result]);
        }

        self.builder.switch_to(merge);
        merge_param
    }

    // ---- Match/fold shared helpers ----

    /// Group match arms by the tag index of their top-level
    /// constructor pattern. `scrutinee_ty` provides the context
    /// needed to compute tag indices for structural constructors
    /// (which aren't in `decl_info.constructors`).
    fn group_arms_by_tag(
        &self,
        arms: &[ast::MatchArm<'src>],
        scrutinee_ty: &Type,
    ) -> Vec<(u64, Vec<usize>)> {
        let mut groups: Vec<(u64, Vec<usize>)> = Vec::new();
        for (i, arm) in arms.iter().enumerate() {
            let ast::Pattern::Constructor { name: con_name, .. } = &arm.pattern else {
                panic!("arms must use constructor patterns");
            };
            let (tag_idx, _, _) = self.con_layout(con_name, Some(scrutinee_ty));
            if let Some(group) = groups.iter_mut().find(|(t, _)| *t == tag_idx) {
                group.1.push(i);
            } else {
                groups.push((tag_idx, vec![i]));
            }
        }
        groups
    }

    fn lower_guards(
        &mut self,
        guards: &[Expr<'src>],
        arm_idx: usize,
        tag_idx: u64,
        tag_groups: &[(u64, Vec<usize>)],
        arm_blocks: &[BlockId],
        default_fail: BlockId,
        fail_args: &[Value],
    ) {
        let group = &tag_groups.iter().find(|(t, _)| *t == tag_idx).unwrap().1;
        let pos_in_group = group.iter().position(|&idx| idx == arm_idx).unwrap();
        let (fail_target, target_args) = if pos_in_group + 1 < group.len() {
            (arm_blocks[group[pos_in_group + 1]], fail_args.to_vec())
        } else {
            (default_fail, vec![])
        };

        // Route every guard through `lower_and_chain` so that any `is`
        // expressions embedded in the guard (e.g. from
        // `flatten_patterns` hoisting nested constructor fields) bind
        // their fields into `self.vars` before the arm body lowers.
        // Plain boolean guards fall through to the chain's generic
        // branch-on-True path. Fall-through to the next arm in the
        // same tag group is wired via `fail_target`.
        for guard_expr in guards {
            self.lower_and_chain(guard_expr, fail_target, &target_args);
        }
    }

    // ---- Literal match lowering ----

    /// True if every arm's pattern is `IntLit` or `StrLit`.
    fn is_literal_match(arms: &[ast::MatchArm<'_>]) -> bool {
        arms.iter().all(|arm| {
            matches!(
                arm.pattern,
                ast::Pattern::IntLit(_) | ast::Pattern::StrLit(_)
            )
        })
    }

    /// Lower a match on literal patterns as a chain of equality checks.
    /// Each arm becomes `if scrutinee == literal then body else next_arm`.
    fn lower_literal_match(
        &mut self,
        scrutinee_expr: &Expr<'src>,
        arms: &[ast::MatchArm<'src>],
        else_body: Option<&Expr<'src>>,
        result_ty: ScalarType,
    ) -> Value {
        let scr_val = self.lower_expr(scrutinee_expr);
        let scr_ty = self.expr_scalar_type(scrutinee_expr);
        let scr_is_func_param = self.builder.func.params.contains(&scr_val);
        let merge = self.builder.create_block();
        let merge_param = self.builder.add_block_param(merge, result_ty);

        let mut current_scr = scr_val;
        for arm in arms {
            let next_block = self.builder.create_block();
            let next_scr_param = if scr_is_func_param {
                scr_val // function params don't need threading
            } else {
                self.builder.add_block_param(next_block, scr_ty)
            };
            let body_block = self.builder.create_block();
            let lit_val = match &arm.pattern {
                ast::Pattern::IntLit(n) => match scr_ty {
                    ScalarType::I8 => self.builder.const_i8(*n as i8),
                    ScalarType::U8 => self.builder.const_u8(*n as u8),
                    ScalarType::I16 => self.builder.const_i16(*n as i16),
                    ScalarType::U16 => self.builder.const_u16(*n as u16),
                    ScalarType::I32 => self.builder.const_i32(*n as i32),
                    ScalarType::U32 => self.builder.const_u32(*n as u32),
                    ScalarType::U64 => self.builder.const_u64(*n as u64),
                    _ => self.builder.const_i64(*n),
                },
                ast::Pattern::StrLit(_) => {
                    panic!("string literal pattern matching not yet supported in lowering")
                }
                _ => unreachable!(),
            };
            let eq = self
                .builder
                .binop(BinaryOp::Eq, current_scr, lit_val, ScalarType::U8);
            let next_args = if scr_is_func_param { vec![] } else { vec![current_scr] };
            self.builder.branch(eq, body_block, vec![], next_block, next_args);

            self.builder.switch_to(body_block);
            let body_val = self.lower_expr(&arm.body);
            self.builder.jump(merge, vec![body_val]);

            self.builder.switch_to(next_block);
            current_scr = next_scr_param;
        }

        // Else / unreachable fallthrough
        if let Some(eb) = else_body {
            let else_val = self.lower_expr(eb);
            self.builder.jump(merge, vec![else_val]);
        } else {
            // No else — unreachable. Jump with a dummy value of the
            // right type so the merge param types stay honest.
            let dummy = self.dummy_of(result_ty);
            self.builder.jump(merge, vec![dummy]);
        }

        self.builder.switch_to(merge);
        merge_param
    }

    // ---- Match lowering ----

    fn lower_match(
        &mut self,
        scrutinee_expr: &Expr<'src>,
        arms: &[ast::MatchArm<'src>],
        else_body: Option<&Expr<'src>>,
        result_ty: ScalarType,
    ) -> Value {
        let scrutinee_ty = scrutinee_expr.ty.clone();
        let scr_val = self.lower_expr(scrutinee_expr);
        // Determine fieldless from the first constructor's layout — more
        // reliable than `is_fieldless_type` since synthesized expressions
        // (apply functions) may have placeholder types.
        let first_con_name = match &arms[0].pattern {
            ast::Pattern::Constructor { name, .. } => *name,
            _ => panic!("match arms must use constructor patterns"),
        };
        let (_, first_max, _) = self.con_layout(first_con_name, Some(&scrutinee_ty));
        let fieldless = first_max == 0;
        let scr_is_agg = self.is_agg(scr_val);
        let tag = if fieldless {
            scr_val // already the discriminant
        } else if scr_is_agg {
            self.builder.extract(scr_val, 0, ScalarType::U64)
        } else {
            self.builder.load(scr_val, 0, ScalarType::U64)
        };
        let tag_block = self.builder.current_block.unwrap();

        // Thread scr_val through block params only when it's NOT a
        // function param (function params are always accessible).
        let scr_is_func_param = self.builder.func.params.contains(&scr_val);
        let scr_val_ty = self.builder.value_types.get(&scr_val).copied().unwrap_or(ScalarType::Ptr);
        let merge = self.builder.create_block();
        let merge_param = self.builder.add_block_param(merge, result_ty);
        let else_block = else_body.map(|_| self.builder.create_block());
        let arm_blocks: Vec<_> = arms.iter().map(|_| self.builder.create_block()).collect();
        let arm_scr_params: Vec<_> = if scr_is_func_param {
            vec![]
        } else {
            arm_blocks.iter().map(|&b| self.builder.add_block_param(b, scr_val_ty)).collect()
        };
        let tag_groups = self.group_arms_by_tag(arms, &scrutinee_ty);

        let switch_args = if scr_is_func_param { vec![] } else { vec![scr_val] };
        let switch_arms: Vec<_> = tag_groups
            .iter()
            .map(|(tag_idx, arm_indices)| (*tag_idx, arm_blocks[arm_indices[0]], switch_args.clone()))
            .collect();
        self.builder.switch_to(tag_block);
        self.builder
            .switch_int(tag, switch_arms, else_block.map(|b| (b, vec![])));

        // Dead-fallthrough sink: when there's no `else` body but some
        // arm has guards, the last guard-chain needs a well-typed
        // target to fall through to. That target is statically
        // unreachable (the match is exhaustive), but the IR still
        // needs a valid block with the right arg count to merge.
        // Created lazily since matches without guards don't need it.
        let mut unreachable_sink: Option<BlockId> = None;

        for (i, arm) in arms.iter().enumerate() {
            let ast::Pattern::Constructor {
                name: con_name,
                fields,
            } = &arm.pattern
            else {
                panic!("match arms must use constructor patterns");
            };
            self.builder.switch_to(arm_blocks[i]);
            let arm_scr = if scr_is_func_param {
                scr_val
            } else {
                arm_scr_params[i]
            };

            let (arm_tag_idx, _, field_types) =
                self.con_layout(con_name, Some(&scrutinee_ty));
            let saved_vars = self.vars.clone();

            if !fieldless {
                for (fi, field_pat) in fields.iter().enumerate() {
                    let field_ty = field_types.get(fi).copied().unwrap_or(ScalarType::Ptr);
                    let field_val = if scr_is_agg {
                        self.builder.extract(arm_scr, fi + 1, field_ty)
                    } else {
                        self.builder.load(arm_scr, fi + 1, field_ty)
                    };
                    self.bind_pattern_field(field_pat, field_val);
                }
            }

            if !arm.guards.is_empty() {
                let default_fail = if let Some(eb) = else_block {
                    eb
                } else {
                    *unreachable_sink.get_or_insert_with(|| {
                        let saved = self.builder.current_block;
                        let sink = self.builder.create_block();
                        self.builder.switch_to(sink);
                        let dummy = self.dummy_of(result_ty);
                        self.builder.jump(merge, vec![dummy]);
                        self.builder.current_block = saved;
                        sink
                    })
                };
                let guard_fail_args = if scr_is_func_param { vec![] } else { vec![arm_scr] };
                self.lower_guards(
                    &arm.guards,
                    i,
                    arm_tag_idx,
                    &tag_groups,
                    &arm_blocks,
                    default_fail,
                    &guard_fail_args,
                );
            }

            let result = self.lower_expr(&arm.body);
            if arm.is_return {
                self.builder.ret(result);
            } else {
                self.builder.jump(merge, vec![result]);
            }

            self.vars = saved_vars;
        }

        if let (Some(else_block_id), Some(else_expr)) = (else_block, else_body) {
            self.builder.switch_to(else_block_id);
            let else_val = self.lower_expr(else_expr);
            self.builder.jump(merge, vec![else_val]);
        }

        self.builder.switch_to(merge);
        merge_param
    }

    fn bind_pattern_field(&mut self, pat: &ast::Pattern<'src>, val: Value) {
        match pat {
            ast::Pattern::Binding(sym) => {
                self.vars.insert(*sym, val);
            }
            ast::Pattern::Wildcard | ast::Pattern::IntLit(_) | ast::Pattern::StrLit(_) => {}
            _ => panic!("unsupported nested pattern in match arm field"),
        }
    }

    /// Detect `List.range(a, b)` as the receiver/list expression.
    /// Returns lowered (start, end) Values if matched.
    /// Detect `List.range(a, b)` as the list expression in a walk.
    fn as_range_call(&mut self, expr: &Expr<'src>) -> Option<(Value, Value)> {
        let is_range = |r: &str| r == "List.range" || r.ends_with(".range");
        match &expr.kind {
            ExprKind::QualifiedCall { resolved, segments, args, .. } => {
                let full = resolved.clone()
                    .unwrap_or_else(|| segments.join("."));
                if is_range(&full) && args.len() == 2 {
                    let start = self.lower_expr(&args[0]);
                    let end = self.lower_expr(&args[1]);
                    Some((start, end))
                } else {
                    None
                }
            }
            ExprKind::Call { target, args } if args.len() == 2 => {
                let name = self.symbols.display(*target);
                if is_range(name) {
                    let start = self.lower_expr(&args[0]);
                    let end = self.lower_expr(&args[1]);
                    Some((start, end))
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    /// Emit a range-walk loop: counter from start to end, no list allocation.
    fn lower_range_walk(
        &mut self,
        start: Value,
        end: Value,
        init_val: Value,
        step_val: Value,
        apply_name: &str,
        until: bool,
        acc_ty: ScalarType,
        direct: Option<&SingletonTarget>,
    ) -> Value {
        let step_ty = self.builder.value_types.get(&step_val).copied().unwrap_or(ScalarType::Ptr);

        let header = self.builder.create_block();
        let i_param = self.builder.add_block_param(header, ScalarType::U64);
        let acc_param = self.builder.add_block_param(header, acc_ty);
        let end_param = self.builder.add_block_param(header, ScalarType::U64);
        let step_param = self.builder.add_block_param(header, step_ty);
        let body_block = self.builder.create_block();
        let body_i = self.builder.add_block_param(body_block, ScalarType::U64);
        let body_acc = self.builder.add_block_param(body_block, acc_ty);
        let body_end = self.builder.add_block_param(body_block, ScalarType::U64);
        let body_step = self.builder.add_block_param(body_block, step_ty);
        let done = self.builder.create_block();
        let done_param = self.builder.add_block_param(done, acc_ty);

        self.builder.jump(header, vec![start, init_val, end, step_val]);

        self.builder.switch_to(header);
        let cmp = self.builder.binop(BinaryOp::Eq, i_param, end_param, ScalarType::U8);
        self.builder.branch(cmp, done, vec![acc_param], body_block, vec![i_param, acc_param, end_param, step_param]);

        self.builder.switch_to(body_block);
        // The element IS the counter — no list load needed.
        let elem = body_i;
        let resolved = direct.or_else(|| self.singletons.get(apply_name));
        let result = if let Some(st) = resolved {
            let mut call_args = Vec::with_capacity(st.num_captures + 2);
            for i in 0..st.num_captures {
                call_args.push(self.builder.load(body_step, i + 1, ScalarType::Ptr));
            }
            call_args.push(body_acc);
            call_args.push(elem);
            let ret_ty = self.func_ret_type(&st.target_func);
            self.builder.call(&st.target_func, call_args, ret_ty)
        } else {
            let ret_ty = self.func_ret_type(apply_name);
            self.builder.call(apply_name, vec![body_step, body_acc, elem], ret_ty)
        };

        let one = self.builder.const_u64(1);
        let next_i = self.builder.binop(BinaryOp::Add, body_i, one, ScalarType::U64);

        if until {
            let tag = self.builder.load(result, 0, ScalarType::U64);
            // The Step wrapper is a heap object; its payload slot holds
            // the accumulator in its STORAGE representation (Ptr even when
            // acc_ty is Agg). coerce_args at the branch/jump handles the
            // Ptr→Agg conversion if the target block param is Agg.
            let payload_load_ty = match acc_ty {
                ScalarType::Agg(_) => ScalarType::Ptr,
                other => other,
            };
            let payload = self.builder.load(result, 1, payload_load_ty);
            let break_tag = self.decls.constructors["Break"].tag_index;
            let break_val = self.builder.const_u64(break_tag);
            let is_break = self.builder.binop(BinaryOp::Eq, tag, break_val, ScalarType::U8);
            self.builder.branch(is_break, done, vec![payload], header, vec![next_i, payload, body_end, body_step]);
        } else {
            self.builder.jump(header, vec![next_i, result, body_end, body_step]);
        }

        self.builder.switch_to(done);
        done_param
    }

    fn lower_list_walk(
        &mut self,
        list_val: Value,
        init_val: Value,
        step_val: Value,
        apply_name: &str,
        until: bool,
        acc_ty: ScalarType,
        direct: Option<&SingletonTarget>,
    ) -> Value {
        let len_val = self.builder.load(list_val, 0, ScalarType::U64);
        let data_ptr = self.builder.load(list_val, 2, ScalarType::Ptr);
        let step_ty = self.builder.value_types.get(&step_val).copied().unwrap_or(ScalarType::Ptr);

        let header = self.builder.create_block();
        let i_param = self.builder.add_block_param(header, ScalarType::U64);
        let acc_param = self.builder.add_block_param(header, acc_ty);
        let len_param = self.builder.add_block_param(header, ScalarType::U64);
        let data_param = self.builder.add_block_param(header, ScalarType::Ptr);
        let step_param = self.builder.add_block_param(header, step_ty);
        let body_block = self.builder.create_block();
        let body_i = self.builder.add_block_param(body_block, ScalarType::U64);
        let body_acc = self.builder.add_block_param(body_block, acc_ty);
        let body_len = self.builder.add_block_param(body_block, ScalarType::U64);
        let body_data = self.builder.add_block_param(body_block, ScalarType::Ptr);
        let body_step = self.builder.add_block_param(body_block, step_ty);
        let done = self.builder.create_block();
        let done_param = self.builder.add_block_param(done, acc_ty);

        let zero = self.builder.const_u64(0);
        self.builder.jump(header, vec![zero, init_val, len_val, data_ptr, step_val]);

        self.builder.switch_to(header);
        let cmp = self
            .builder
            .binop(BinaryOp::Eq, i_param, len_param, ScalarType::U8);
        self.builder
            .branch(cmp, done, vec![acc_param], body_block, vec![i_param, acc_param, len_param, data_param, step_param]);

        self.builder.switch_to(body_block);
        let elem = self.builder.load_dyn(body_data, body_i, ScalarType::Ptr);
        // Resolve direct call target: per-call-site tag > singleton > apply dispatch.
        let resolved = direct.or_else(|| self.singletons.get(apply_name));
        let result = if let Some(st) = resolved {
            let mut call_args = Vec::with_capacity(st.num_captures + 2);
            for i in 0..st.num_captures {
                call_args.push(self.builder.load(body_step, i + 1, ScalarType::Ptr));
            }
            call_args.push(body_acc);
            call_args.push(elem);
            let ret_ty = self.func_ret_type(&st.target_func);
            self.builder.call(&st.target_func, call_args, ret_ty)
        } else {
            let ret_ty = self.func_ret_type(apply_name);
            self.builder.call(apply_name, vec![body_step, body_acc, elem], ret_ty)
        };

        let one = self.builder.const_u64(1);
        let next_i = self
            .builder
            .binop(BinaryOp::Add, body_i, one, ScalarType::U64);

        if until {
            let tag = self.builder.load(result, 0, ScalarType::U64);
            let payload_load_ty = match acc_ty {
                ScalarType::Agg(_) => ScalarType::Ptr,
                other => other,
            };
            let payload = self.builder.load(result, 1, payload_load_ty);
            let break_tag = self.decls.constructors["Break"].tag_index;
            let break_val = self.builder.const_u64(break_tag);
            let is_break = self
                .builder
                .binop(BinaryOp::Eq, tag, break_val, ScalarType::U8);
            self.builder
                .branch(is_break, done, vec![payload], header, vec![next_i, payload, body_len, body_data, body_step]);
        } else {
            self.builder.jump(header, vec![next_i, result, body_len, body_data, body_step]);
        }

        self.builder.switch_to(done);
        done_param
    }

    // ---- Destructure lowering ----

    fn lower_destructure(
        &mut self,
        pattern: &ast::Pattern<'src>,
        val: Value,
        val_ty: &Type,
    ) {
        let val_is_agg = self.is_agg(val);
        match pattern {
            ast::Pattern::Tuple(elems) => {
                let elem_types = match val_ty {
                    Type::Tuple(tys) => tys.as_slice(),
                    other => {
                        eprintln!("BUG: tuple destructure got val_ty={other:?}");
                        &[]
                    }
                };
                for (i, elem) in elems.iter().enumerate() {
                    let ty = elem_types
                        .get(i)
                        .map(|t| self.scalar_type(t))
                        .unwrap_or(ScalarType::Ptr);
                    let field_val = if val_is_agg {
                        self.builder.extract(val, i, ty)
                    } else {
                        self.builder.load(val, i, ty)
                    };
                    self.lower_destructure_elem(elem, field_val);
                }
            }
            ast::Pattern::Record { fields, .. } => {
                // Get ALL field names from the record TYPE (not just the
                // pattern fields) to compute correct slot indices. The
                // pattern may use `..` to ignore some fields.
                let all_names: Vec<&str> = match val_ty {
                    Type::Record {
                        fields: type_fields,
                        ..
                    } => {
                        let mut names: Vec<&str> =
                            type_fields.iter().map(|(n, _)| n.as_str()).collect();
                        names.sort_unstable();
                        names
                    }
                    _ => {
                        // Fallback: use pattern field names (old behavior).
                        let mut names: Vec<&str> = fields
                            .iter()
                            .map(|(sym, _)| self.fields.get(*sym))
                            .collect();
                        names.sort_unstable();
                        names
                    }
                };
                let type_fields: Vec<(&str, &Type)> = match val_ty {
                    Type::Record { fields: tf, .. } => {
                        let mut sorted: Vec<(&str, &Type)> =
                            tf.iter().map(|(n, t)| (n.as_str(), t)).collect();
                        sorted.sort_unstable_by_key(|(n, _)| *n);
                        sorted
                    }
                    _ => vec![],
                };
                for (field_sym, elem) in fields {
                    let name = self.fields.get(*field_sym);
                    let slot = all_names.iter().position(|n| *n == name).unwrap();
                    let ty = type_fields
                        .get(slot)
                        .map(|(_, t)| self.scalar_type(t))
                        .unwrap_or(ScalarType::Ptr);
                    let field_val = if val_is_agg {
                        self.builder.extract(val, slot, ty)
                    } else {
                        self.builder.load(val, slot, ty)
                    };
                    self.lower_destructure_elem(elem, field_val);
                }
            }
            _ => panic!("expected tuple or record pattern in destructure"),
        }
    }

    fn lower_destructure_elem(&mut self, elem: &ast::Pattern<'src>, val: Value) {
        match elem {
            ast::Pattern::Binding(sym) => {
                self.vars.insert(*sym, val);
            }
            ast::Pattern::Tuple(_) | ast::Pattern::Record { .. } => {
                // Nested destructure: use a dummy type (falls back to
                // pattern-field-only slot computation, which is correct
                // when the pattern names all fields).
                let dummy_ty = Type::Var(crate::types::engine::TypeVar(0));
                self.lower_destructure(elem, val, &dummy_ty);
            }
            ast::Pattern::Wildcard => {}
            _ => panic!("unsupported pattern in destructure"),
        }
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

fn classify_walk(name: &str) -> Option<WalkKind> {
    // Strip the mono suffix (`__<sig>`) so specialized walks like
    // `List.walk__I64_I64` still classify as `walk`.
    let core = name.split("__").next().unwrap_or(name);
    let base = core
        .strip_prefix("List.")
        .or_else(|| core.rsplit_once(".List.").map(|(_, rest)| rest))?;
    match base {
        "walk" => Some(WalkKind { until: false }),
        "walk_until" => Some(WalkKind { until: true }),
        _ => None,
    }
}

/// Build the apply-function name for a walk call. Mirrors the
/// `walk_call_key` logic in `lambda_solve`: appends the step
/// function's full `Arrow` type to the callee so specialized walks
/// get their own per-type apply dispatchers. `List.walk` is an
/// intrinsic (no body to monomorphize), so without this all walks
/// would share a single apply with type-incoherent arm returns.
fn walk_apply_name(callee: &str, step_ty: &Type) -> String {
    let mut key = callee.to_owned();
    key.push_str("__");
    crate::passes::mono::append_type_mangling(&mut key, step_ty);
    format!("__apply_{key}_2")
}

/// Emit a call to one of the built-in list intrinsics
/// (`List.len` / `List.get` / `List.set` / `List.append` /
/// `List.reverse`). Assumes the caller already verified that `name`
/// is a list builtin via `LowerCtx::is_list_builtin`.
/// Emit an SSA constant for an integer literal, dispatching to the
/// correct width based on the resolved type.
#[expect(
    clippy::cast_sign_loss,
    clippy::cast_precision_loss,
    clippy::cast_possible_truncation
)]
fn lower_int_const(builder: &mut Builder, n: i64, ty: &Type) -> Value {
    use crate::numeric::NumericType;
    if let Type::Con(name) = ty {
        if let Some(num) = NumericType::from_name(name) {
            return match num {
                NumericType::I8 => builder.const_i8(n as i8),
                NumericType::U8 => builder.const_u8(n as u8),
                NumericType::I16 => builder.const_i16(n as i16),
                NumericType::U16 => builder.const_u16(n as u16),
                NumericType::I32 => builder.const_i32(n as i32),
                NumericType::U32 => builder.const_u32(n as u32),
                NumericType::I64 => builder.const_i64(n),
                NumericType::U64 => builder.const_u64(n as u64),
                NumericType::F64 => builder.const_f64(n as f64),
            };
        }
    }
    builder.const_i64(n)
}

fn emit_list_builtin_call(builder: &mut Builder, name: &str, args: Vec<Value>) -> Value {
    let (intrinsic, ret_ty) = if name.ends_with(".len") || name == "List.len" {
        ("__list_len", ScalarType::U64)
    } else if name.ends_with(".get") || name == "List.get" {
        return emit_list_get_checked(builder, args);
    } else if name.ends_with(".append") || name == "List.append" {
        return emit_list_append(builder, args);
    } else if name.ends_with(".set") || name == "List.set" {
        ("__list_set", ScalarType::Ptr)
    } else if name.ends_with(".reverse") || name == "List.reverse" {
        ("__list_reverse", ScalarType::Ptr)
    } else if name.ends_with(".sublist") || name == "List.sublist" {
        ("__list_sublist", ScalarType::Ptr)
    } else if name.ends_with(".repeat") || name == "List.repeat" {
        ("__list_repeat", ScalarType::Ptr)
    } else if name.ends_with(".range") || name == "List.range" {
        ("__list_range", ScalarType::Ptr)
    } else {
        panic!("unknown list builtin: {name}");
    };
    builder.call(intrinsic, args, ret_ty)
}

/// Lower `list.append(val)` as SSA-level `load + alloc_dyn +
/// copy_into + store + alloc 3 + stores`. Exposing the allocations
/// at SSA level lets `insert_reuse` pair them with the caller's
/// `rc_dec list` and mutate in place when the list is unique.
fn emit_list_append(builder: &mut Builder, args: Vec<Value>) -> Value {
    use crate::ssa::instruction::BinaryOp;
    let list = args[0];
    let val = args[1];

    let len = builder.load(list, 0, ScalarType::U64);
    let data = builder.load(list, 2, ScalarType::Ptr);
    let one = builder.const_u64(1);
    let new_len = builder.binop(BinaryOp::Add, len, one, ScalarType::U64);

    let new_data = builder.alloc_dyn(new_len);
    builder.call("__list_copy_into", vec![data, new_data, len], ScalarType::I64);
    builder.store_dyn(new_data, len, val);

    let new_list = builder.alloc(3);
    builder.store(new_list, 0, new_len);
    builder.store(new_list, 1, new_len);
    builder.store(new_list, 2, new_data);
    new_list
}

/// Emit a bounds-checked List.get that returns Result(a, [OutOfBounds]).
/// SSA: load len, compare, branch to Ok(element) or Err(OutOfBounds).
fn emit_list_get_checked(builder: &mut Builder, args: Vec<Value>) -> Value {
    use crate::ssa::instruction::BinaryOp;
    let list = args[0];
    let idx = args[1];

    let len = builder.call("__list_len", vec![list], ScalarType::U64);
    let in_bounds = builder.binop(BinaryOp::Lt, idx, len, ScalarType::U8);

    let ok_block = builder.create_block();
    let err_block = builder.create_block();
    let merge = builder.create_block();
    let merge_param = builder.add_block_param(merge, ScalarType::Ptr);

    builder.branch(in_bounds, ok_block, vec![], err_block, vec![]);

    // Ok path: get element, wrap in Ok(elem) = [tag=0, elem]
    builder.switch_to(ok_block);
    let elem = builder.call("__list_get", vec![list, idx], ScalarType::Ptr);
    let ok_result = builder.alloc(2);
    let ok_tag = builder.const_u64(0);
    builder.store(ok_result, 0, ok_tag);
    builder.store(ok_result, 1, elem);
    builder.jump(merge, vec![ok_result]);

    // Err path: Err(OutOfBounds) = [tag=1, OutOfBounds=tag0]
    builder.switch_to(err_block);
    let err_result = builder.alloc(2);
    let err_tag = builder.const_u64(1);
    builder.store(err_result, 0, err_tag);
    let oob_tag = builder.const_u8(0);
    builder.store(err_result, 1, oob_tag);
    builder.jump(merge, vec![err_result]);

    builder.switch_to(merge);
    merge_param
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
