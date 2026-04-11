use std::collections::HashMap;

use crate::ast::{self, BinOp, Decl, Expr, ExprKind, Stmt};
use crate::decl_info::{self, DeclInfo, method_key, type_to_scalar};
use crate::error::CompileError;
use crate::source::SourceArena;
use crate::ssa::Module;
use crate::ssa::builder::Builder;
use crate::ssa::instruction::{BinaryOp, BlockId, ScalarType, Value};
use crate::symbol::{FieldInterner, SymbolId, SymbolTable};
use crate::types::engine::Type;
use crate::types::infer::InferResult;

/// Lower a parsed AST module directly to SSA IR.
///
/// Returns the SSA module and a list of SSA values representing main's parameters
/// (that the runtime must bind before evaluation).
pub fn lower<'src>(
    arena: &'src SourceArena,
    module: &ast::Module<'src>,
    scope: &crate::resolve::ModuleScope,
    infer_result: &InferResult,
    symbols: &crate::symbol::SymbolTable,
    fields: &FieldInterner,
) -> Result<(Module, Vec<Value>), CompileError> {
    // Post-Step 9, the module was already pruned by
    // `reachable::prune`, so every `Decl::FuncDef` here is reachable
    // from `main` and must be lowered. The reachability side-table
    // that the lowerer used to maintain is gone.
    let decls = decl_info::build(arena, module, scope, infer_result, symbols);
    lower_to_ssa(module, infer_result, &decls, symbols, fields)
}

// ---- SSA lowering context ----

struct LowerCtx<'a, 'src> {
    builder: Builder,
    /// Locals in scope: binding `SymbolId` → SSA value. Function
    /// parameters, let-bound names, lambda params, and pattern
    /// bindings all enter/exit this map as their scopes open and close.
    vars: HashMap<SymbolId, Value>,
    // Immutable references:
    decls: &'a DeclInfo,
    infer: &'a InferResult,
    symbols: &'a SymbolTable,
    fields: &'a FieldInterner,
    _phantom: std::marker::PhantomData<&'src ()>,
}

impl<'a, 'src> LowerCtx<'a, 'src> {
    fn new(
        decls: &'a DeclInfo,
        infer: &'a InferResult,
        symbols: &'a SymbolTable,
        fields: &'a FieldInterner,
    ) -> Self {
        Self {
            builder: Builder::new(),
            vars: HashMap::new(),
            decls,
            infer,
            symbols,
            fields,
            _phantom: std::marker::PhantomData,
        }
    }
}

struct WalkKind {
    backwards: bool,
    until: bool,
}

impl<'a, 'src> LowerCtx<'a, 'src> {
    // ---- Type helpers ----

    fn expr_scalar_type(&self, expr: &Expr<'src>) -> ScalarType {
        type_to_scalar(&expr.ty)
    }

    fn func_ret_type(&self, name: &str) -> ScalarType {
        self.decls
            .func_return_types
            .get(name)
            .copied()
            .unwrap_or(ScalarType::Ptr)
    }

    // ---- Field slot computation ----

    fn field_slot(ty: &Type, field: &str) -> usize {
        match ty {
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
            _ => panic!("field access on non-record type: {ty:?}"),
        }
    }

    // ---- Function lowering ----

    fn lower_function(&mut self, name: &str, param_syms: &[SymbolId], body: &Expr<'src>) {
        let saved_vars = self.vars.clone();
        let saved_blocks = std::mem::take(&mut self.builder.blocks);
        let saved_current = self.builder.current_block.take();

        let ssa_params: Vec<Value> = param_syms
            .iter()
            .map(|p| {
                let v = self.builder.fresh_value();
                self.vars.insert(*p, v);
                v
            })
            .collect();

        let entry = self.builder.create_block();
        self.builder.switch_to(entry);
        let result = self.lower_expr(body);
        self.builder.ret(result);
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
                Type::Arrow(params, _) => params.iter().map(type_to_scalar).collect(),
                _ => vec![ScalarType::Ptr; ssa_params.len()],
            })
            .unwrap_or_else(|| vec![ScalarType::Ptr; ssa_params.len()]);
        let return_type = self.func_ret_type(name);
        self.builder
            .finish_function(name, ssa_params, param_types, return_type);

        self.builder.blocks = saved_blocks;
        self.builder.current_block = saved_current;
        self.vars = saved_vars;
    }

    // ---- Expression lowering ----

    fn lower_expr(&mut self, expr: &Expr<'src>) -> Value {
        match &expr.kind {
            #[expect(
                clippy::cast_sign_loss,
                clippy::cast_precision_loss,
                clippy::cast_possible_truncation
            )]
            ExprKind::IntLit(n) => match &expr.ty {
                Type::Con(name) if name == "U8" => self.builder.const_u8(*n as u8),
                Type::Con(name) if name == "I8" => self.builder.const_i8(*n as i8),
                Type::Con(name) if name == "U64" => self.builder.const_u64(*n as u64),
                Type::Con(name) if name == "F64" => self.builder.const_f64(*n as f64),
                _ => self.builder.const_i64(*n),
            },

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
                    return self.lower_constructor_call(name, &[]);
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
                    BinOp::Eq => self.lower_eq(l, r, false),
                    BinOp::Neq => self.lower_eq(l, r, true),
                    BinOp::And | BinOp::Or => unreachable!(),
                }
            }

            ExprKind::Call { target, args, .. } => self.lower_call_by_sym(*target, args),

            ExprKind::Block(stmts, result) => self.lower_block(stmts, result),

            ExprKind::If {
                expr: scrutinee_expr,
                arms,
                else_body,
            } => {
                let result_ty = self.expr_scalar_type(expr);
                // Detect boolean if-then-else with Is bindings in scrutinee
                if Self::is_bool_if_with_is(scrutinee_expr, arms) {
                    self.lower_bool_if_with_is(scrutinee_expr, arms, result_ty)
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
                let ptr = self.builder.alloc(fields.len());
                let mut sorted: Vec<(usize, &str, &Expr)> = fields
                    .iter()
                    .enumerate()
                    .map(|(i, (field_sym, expr))| (i, self.fields.get(*field_sym), expr))
                    .collect();
                sorted.sort_by_key(|(_, name, _)| *name);
                for (slot, (_, _, field_expr)) in sorted.iter().enumerate() {
                    let val = self.lower_expr(field_expr);
                    self.builder.store(ptr, slot, val);
                }
                ptr
            }

            ExprKind::FieldAccess { record, field } => {
                let ptr = self.lower_expr(record);
                let field_name = self.fields.get(*field);
                let slot = Self::field_slot(&record.ty, field_name);
                let ty = self.expr_scalar_type(expr);
                self.builder.load(ptr, slot, ty)
            }

            ExprKind::MethodCall {
                receiver,
                method,
                args,
                ..
            } => self.lower_method_call(receiver, method, args, expr),

            ExprKind::Tuple(elems) => {
                let ptr = self.builder.alloc(elems.len());
                for (i, e) in elems.iter().enumerate() {
                    let val = self.lower_expr(e);
                    self.builder.store(ptr, i, val);
                }
                ptr
            }

            ExprKind::Lambda { .. } => {
                panic!("lambdas are only supported as direct arguments to function calls");
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
                    self.lower_destructure(pattern, v);
                }
                Stmt::Guard {
                    condition,
                    return_val,
                } => {
                    if Self::expr_contains_is(condition) {
                        // Use and-chain lowering for Is binding flow
                        let cont_block = self.builder.create_block();
                        let saved_vars = self.vars.clone();
                        self.lower_and_chain(condition, cont_block);
                        // We're in the success path — return
                        let ret_v = self.lower_expr(return_val);
                        self.builder.ret(ret_v);
                        self.vars = saved_vars;
                        self.builder.switch_to(cont_block);
                    } else {
                        // Lower: if condition is true, return return_val from function
                        let cond_val = self.lower_expr(condition);
                        let cond_tag = self.builder.load(cond_val, 0, ScalarType::U64);
                        let true_tag = self.decls.constructors["True"].tag_index;
                        let true_val = self.builder.const_u64(true_tag);
                        let is_true =
                            self.builder
                                .binop(BinaryOp::Eq, cond_tag, true_val, ScalarType::Bool);
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

    fn lower_call_by_sym(&mut self, target: SymbolId, args: &[Expr<'src>]) -> Value {
        let name = self.symbols.display(target).to_owned();
        self.lower_call(&name, args)
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
        if let Some(resolved_name) = resolved {
            // Local-receiver method dispatch. In practice this path
            // is only hit for `receiver.method(args)` parsed as
            // `QualifiedCall` when the receiver is a local binding
            // (the usual form is `MethodCall`). `segments[0]` names
            // the receiver; look it up in the current scope by
            // display name.
            let receiver_name = segments[0];
            let receiver_val = self
                .vars
                .iter()
                .find(|(sym, _)| self.symbols.display(**sym) == receiver_name)
                .map(|(_, v)| *v)
                .unwrap_or_else(|| self.lower_constructor_call(receiver_name, &[]));
            if let Some(op_name) = resolved_name.strip_prefix("__builtin.") {
                let rhs = self.lower_expr(&args[0]);
                let ty = self.expr_scalar_type(outer);
                return self.lower_builtin_op(op_name, receiver_val, rhs, ty);
            }
            let mut arg_vals = vec![receiver_val];
            for a in args {
                arg_vals.push(self.lower_expr(a));
            }
            let ret_ty = self.func_ret_type(resolved_name);
            return self.builder.call(resolved_name, arg_vals, ret_ty);
        }
        // Plain static qualified call: treat segments.join(".") as
        // the callable name and route through `lower_call`.
        let mangled = segments.join(".");
        self.lower_call(&mangled, args)
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
        let Some(mangled) = resolved.clone() else {
            panic!("no method resolution for .{method}() at {:?}", outer.span);
        };
        let recv_val = self.lower_expr(receiver);
        if let Some(op_name) = mangled.strip_prefix("__builtin.") {
            let rhs = self.lower_expr(&args[0]);
            let ty = self.expr_scalar_type(outer);
            return self.lower_builtin_op(op_name, recv_val, rhs, ty);
        }
        // List walks: the walk loop needs untyped Values, so build
        // them positionally.
        if let Some(walk) = classify_walk(&mangled) {
            assert!(args.len() == 2, "List.walk* method form takes 2 args");
            let init_val = self.lower_expr(&args[0]);
            let acc_ty = self.expr_scalar_type(&args[0]);
            let closure_val = self.lower_expr(&args[1]);
            let apply_name = format!("__apply_{mangled}_2");
            return self.lower_list_walk(
                recv_val,
                init_val,
                closure_val,
                &apply_name,
                walk.backwards,
                walk.until,
                acc_ty,
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
        if is_num_to_str(&mangled) {
            return self
                .builder
                .call("__num_to_str", vec![arg_vals[0]], ScalarType::Ptr);
        }
        let ret_ty = self.func_ret_type(&mangled);
        self.builder.call(&mangled, arg_vals, ret_ty)
    }

    /// Central dispatch for direct and static qualified calls: list
    /// walks (which need the walk loop emitted inline), list
    /// builtins, num-to-str, constructors, and plain function calls.
    fn lower_call(&mut self, func: &str, args: &[Expr<'src>]) -> Value {
        if let Some(walk) = classify_walk(func) {
            assert!(args.len() >= 3, "List.walk* takes 3 arguments");
            let list_val = self.lower_expr(&args[0]);
            let init_val = self.lower_expr(&args[1]);
            let acc_ty = self.expr_scalar_type(&args[1]);
            let closure_val = self.lower_expr(&args[2]);
            let apply_name = format!("__apply_{func}_2");
            return self.lower_list_walk(
                list_val,
                init_val,
                closure_val,
                &apply_name,
                walk.backwards,
                walk.until,
                acc_ty,
            );
        }
        if Self::is_list_builtin(func) {
            let arg_vals: Vec<Value> = args.iter().map(|a| self.lower_expr(a)).collect();
            return emit_list_builtin_call(&mut self.builder, func, arg_vals);
        }
        if is_num_to_str(func) {
            let arg_val = self.lower_expr(&args[0]);
            return self
                .builder
                .call("__num_to_str", vec![arg_val], ScalarType::Ptr);
        }
        if self.decls.constructors.contains_key(func) {
            let arg_vals: Vec<Value> = args.iter().map(|a| self.lower_expr(a)).collect();
            return self.lower_constructor_call(func, &arg_vals);
        }
        if self.decls.funcs.contains(func) {
            let ret_ty = self.func_ret_type(func);
            let arg_vals: Vec<Value> = args.iter().map(|a| self.lower_expr(a)).collect();
            return self.builder.call(func, arg_vals, ret_ty);
        }
        panic!("undefined function or constructor: {func}")
    }

    fn is_list_builtin(name: &str) -> bool {
        matches!(name, "List.len" | "List.get" | "List.set" | "List.append")
    }

    // ---- Builtin arithmetic dispatch ----

    fn lower_builtin_op(&mut self, name: &str, lhs: Value, rhs: Value, ty: ScalarType) -> Value {
        match name {
            "add" => self.builder.binop(BinaryOp::Add, lhs, rhs, ty),
            "sub" => self.builder.binop(BinaryOp::Sub, lhs, rhs, ty),
            "mul" => self.builder.binop(BinaryOp::Mul, lhs, rhs, ty),
            "div" => self.builder.binop(BinaryOp::Div, lhs, rhs, ty),
            "rem" => self.builder.binop(BinaryOp::Rem, lhs, rhs, ty),
            "eq" => self.lower_eq(lhs, rhs, false),
            "neq" => self.lower_eq(lhs, rhs, true),
            _ => panic!("unknown builtin: {name}"),
        }
    }

    // ---- Constructor call emission ----

    fn lower_constructor_call(&mut self, name: &str, args: &[Value]) -> Value {
        let meta = self.decls.constructors[name].clone();
        let alloc_size = 1 + meta.max_fields;
        let ptr = self.builder.alloc(alloc_size);
        let tag_val = self.builder.const_u64(meta.tag_index);
        self.builder.store(ptr, 0, tag_val);
        for (i, &arg) in args.iter().enumerate() {
            self.builder.store(ptr, i + 1, arg);
        }
        ptr
    }

    // ---- Bool tagged-union emission from a raw comparison ----

    /// Materialize a `Bool` tagged-union value (`True` or `False`
    /// ptr) from a raw SSA boolean comparison. Used by `==`/`!=`
    /// lowering and by `x is Con(..)` expressions. Pass `negate =
    /// true` to flip which branch emits `True`.
    fn lower_eq(&mut self, lhs: Value, rhs: Value, negate: bool) -> Value {
        let cmp = self.builder.binop(BinaryOp::Eq, lhs, rhs, ScalarType::Bool);
        self.lower_bool_from_cmp_neg(cmp, negate)
    }

    fn lower_bool_from_cmp(&mut self, cmp: Value) -> Value {
        self.lower_bool_from_cmp_neg(cmp, false)
    }

    fn lower_bool_from_cmp_neg(&mut self, cmp: Value, negate: bool) -> Value {
        let true_meta = &self.decls.constructors["True"];
        let false_meta = &self.decls.constructors["False"];
        let alloc_size = 1 + true_meta.max_fields;
        let (then_tag_idx, else_tag_idx) = if negate {
            (false_meta.tag_index, true_meta.tag_index)
        } else {
            (true_meta.tag_index, false_meta.tag_index)
        };

        let then_block = self.builder.create_block();
        let else_block = self.builder.create_block();
        let merge = self.builder.create_block();
        let merge_param = self.builder.add_block_param(merge, ScalarType::Ptr);

        self.builder
            .branch(cmp, then_block, vec![], else_block, vec![]);

        self.builder.switch_to(then_block);
        let true_ptr = self.builder.alloc(alloc_size);
        let true_tag = self.builder.const_u64(then_tag_idx);
        self.builder.store(true_ptr, 0, true_tag);
        self.builder.jump(merge, vec![true_ptr]);

        self.builder.switch_to(else_block);
        let false_ptr = self.builder.alloc(alloc_size);
        let false_tag = self.builder.const_u64(else_tag_idx);
        self.builder.store(false_ptr, 0, false_tag);
        self.builder.jump(merge, vec![false_ptr]);

        self.builder.switch_to(merge);
        merge_param
    }

    /// Lower a standalone `x is Pattern` expression (produces Bool, no binding flow).
    fn lower_is_expr(&mut self, inner: &Expr<'src>, pattern: &ast::Pattern<'src>) -> Value {
        let scr = self.lower_expr(inner);
        match pattern {
            ast::Pattern::Constructor { name, .. } => {
                let tag = self.builder.load(scr, 0, ScalarType::U64);
                let meta = &self.decls.constructors[*name];
                let expected_tag = self.builder.const_u64(meta.tag_index);
                let matches = self
                    .builder
                    .binop(BinaryOp::Eq, tag, expected_tag, ScalarType::Bool);
                self.lower_bool_from_cmp(matches)
            }
            ast::Pattern::Wildcard | ast::Pattern::Binding(_) => {
                // Always matches
                self.lower_constructor_call("True", &[])
            }
            _ => panic!("unsupported pattern in `is` expression"),
        }
    }

    /// Lower `lhs and rhs` with fused Is-chain support (bindings flow from lhs into rhs).
    fn lower_and_expr(&mut self, lhs: &Expr<'src>, rhs: &Expr<'src>) -> Value {
        let merge = self.builder.create_block();
        let merge_param = self.builder.add_block_param(merge, ScalarType::Ptr);
        let false_block = self.builder.create_block();

        let saved_vars = self.vars.clone();

        // Lower LHS chain — may emit branches to false_block, accumulating bindings
        self.lower_and_chain(lhs, false_block);

        // We're in the success path — all Is bindings from lhs are in scope
        let rhs_val = self.lower_expr(rhs);
        self.builder.jump(merge, vec![rhs_val]);

        // False block: produce False and jump to merge
        self.builder.switch_to(false_block);
        let false_val = self.lower_constructor_call("False", &[]);
        self.builder.jump(merge, vec![false_val]);

        self.vars = saved_vars;
        self.builder.switch_to(merge);
        merge_param
    }

    /// Recursively process an And chain, branching to `false_block` on failure
    /// and accumulating Is bindings in `self.vars` on success.
    fn lower_and_chain(&mut self, expr: &Expr<'src>, false_block: BlockId) {
        match &expr.kind {
            ExprKind::Is {
                expr: inner,
                pattern,
            } => {
                let scr = self.lower_expr(inner);
                match pattern {
                    ast::Pattern::Constructor { name, fields } => {
                        let tag = self.builder.load(scr, 0, ScalarType::U64);
                        let meta = self.decls.constructors[*name].clone();
                        let expected_tag = self.builder.const_u64(meta.tag_index);
                        let matches =
                            self.builder
                                .binop(BinaryOp::Eq, tag, expected_tag, ScalarType::Bool);
                        let match_block = self.builder.create_block();
                        self.builder
                            .branch(matches, match_block, vec![], false_block, vec![]);
                        self.builder.switch_to(match_block);
                        // Bind pattern fields
                        for (fi, field_pat) in fields.iter().enumerate() {
                            let field_ty =
                                meta.field_types.get(fi).copied().unwrap_or(ScalarType::Ptr);
                            let field_val = self.builder.load(scr, fi + 1, field_ty);
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
                self.lower_and_chain(lhs, false_block);
                // Then process RHS (we're in the LHS success path)
                self.lower_and_chain(rhs, false_block);
            }
            _ => {
                // Regular boolean expression — evaluate, check True tag, branch
                let val = self.lower_expr(expr);
                let tag = self.builder.load(val, 0, ScalarType::U64);
                let true_tag = self.decls.constructors["True"].tag_index;
                let true_val = self.builder.const_u64(true_tag);
                let is_true = self
                    .builder
                    .binop(BinaryOp::Eq, tag, true_val, ScalarType::Bool);
                let continue_block = self.builder.create_block();
                self.builder
                    .branch(is_true, continue_block, vec![], false_block, vec![]);
                self.builder.switch_to(continue_block);
            }
        }
    }

    /// Lower `lhs or rhs` with short-circuit evaluation.
    fn lower_or_expr(&mut self, lhs: &Expr<'src>, rhs: &Expr<'src>) -> Value {
        let merge = self.builder.create_block();
        let merge_param = self.builder.add_block_param(merge, ScalarType::Ptr);

        let lhs_val = self.lower_expr(lhs);
        let tag = self.builder.load(lhs_val, 0, ScalarType::U64);
        let true_tag = self.decls.constructors["True"].tag_index;
        let true_val = self.builder.const_u64(true_tag);
        let is_true = self
            .builder
            .binop(BinaryOp::Eq, tag, true_val, ScalarType::Bool);
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
        self.lower_and_chain(scrutinee, false_block);

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

    fn group_arms_by_tag(&self, arms: &[ast::MatchArm<'src>]) -> Vec<(u64, Vec<usize>)> {
        let mut groups: Vec<(u64, Vec<usize>)> = Vec::new();
        for (i, arm) in arms.iter().enumerate() {
            let ast::Pattern::Constructor { name: con_name, .. } = &arm.pattern else {
                panic!("arms must use constructor patterns");
            };
            let tag_idx = self.decls.constructors[*con_name].tag_index;
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
    ) {
        let group = &tag_groups.iter().find(|(t, _)| *t == tag_idx).unwrap().1;
        let pos_in_group = group.iter().position(|&idx| idx == arm_idx).unwrap();
        let fail_target = if pos_in_group + 1 < group.len() {
            arm_blocks[group[pos_in_group + 1]]
        } else {
            default_fail
        };

        // Route every guard through `lower_and_chain` so that any `is`
        // expressions embedded in the guard (e.g. from
        // `flatten_patterns` hoisting nested constructor fields) bind
        // their fields into `self.vars` before the arm body lowers.
        // Plain boolean guards fall through to the chain's generic
        // branch-on-True path. Fall-through to the next arm in the
        // same tag group is wired via `fail_target`.
        for guard_expr in guards {
            self.lower_and_chain(guard_expr, fail_target);
        }
    }

    // ---- Match lowering ----

    fn lower_match(
        &mut self,
        scrutinee_expr: &Expr<'src>,
        arms: &[ast::MatchArm<'src>],
        else_body: Option<&Expr<'src>>,
        result_ty: ScalarType,
    ) -> Value {
        let scr_val = self.lower_expr(scrutinee_expr);
        let tag = self.builder.load(scr_val, 0, ScalarType::U64);
        let tag_block = self.builder.current_block.unwrap();

        let merge = self.builder.create_block();
        let merge_param = self.builder.add_block_param(merge, result_ty);
        let else_block = else_body.map(|_| self.builder.create_block());
        let arm_blocks: Vec<_> = arms.iter().map(|_| self.builder.create_block()).collect();
        let tag_groups = self.group_arms_by_tag(arms);

        let switch_arms: Vec<_> = tag_groups
            .iter()
            .map(|(tag_idx, arm_indices)| (*tag_idx, arm_blocks[arm_indices[0]], vec![]))
            .collect();
        self.builder.switch_to(tag_block);
        self.builder
            .switch_int(tag, switch_arms, else_block.map(|b| (b, vec![])));

        for (i, arm) in arms.iter().enumerate() {
            let ast::Pattern::Constructor {
                name: con_name,
                fields,
            } = &arm.pattern
            else {
                panic!("match arms must use constructor patterns");
            };
            self.builder.switch_to(arm_blocks[i]);

            let meta = self.decls.constructors[*con_name].clone();
            let saved_vars = self.vars.clone();

            for (fi, field_pat) in fields.iter().enumerate() {
                let field_ty = meta.field_types.get(fi).copied().unwrap_or(ScalarType::Ptr);
                let field_val = self.builder.load(scr_val, fi + 1, field_ty);
                self.bind_pattern_field(field_pat, field_val);
            }

            if !arm.guards.is_empty() {
                let default_fail = else_block.unwrap_or(merge);
                self.lower_guards(
                    &arm.guards,
                    i,
                    meta.tag_index,
                    &tag_groups,
                    &arm_blocks,
                    default_fail,
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
            ast::Pattern::Wildcard => {}
            _ => panic!("unsupported nested pattern in match arm field"),
        }
    }

    // ---- List walk lowering ----
    //
    // Fold lowering used to live here; it now runs as an AST → AST
    // rewrite in `src/fold_lift.rs`. The lowerer panics on `Fold`
    // expressions because fold_lift eliminates them before SSA.

    fn lower_list_walk(
        &mut self,
        list_val: Value,
        init_val: Value,
        step_val: Value,
        apply_name: &str,
        backwards: bool,
        until: bool,
        acc_ty: ScalarType,
    ) -> Value {
        let len_val = self.builder.load(list_val, 0, ScalarType::U64);
        let data_ptr = self.builder.load(list_val, 2, ScalarType::Ptr);

        let header = self.builder.create_block();
        let i_param = self.builder.add_block_param(header, ScalarType::U64);
        let acc_param = self.builder.add_block_param(header, acc_ty);
        let body_block = self.builder.create_block();
        let done = self.builder.create_block();
        let done_param = self.builder.add_block_param(done, acc_ty);

        let zero = self.builder.const_u64(0);
        self.builder.jump(header, vec![zero, init_val]);

        self.builder.switch_to(header);
        let cmp = self
            .builder
            .binop(BinaryOp::Eq, i_param, len_val, ScalarType::Bool);
        self.builder
            .branch(cmp, done, vec![acc_param], body_block, vec![]);

        self.builder.switch_to(body_block);
        let elem = if backwards {
            let one = self.builder.const_u64(1);
            let len_minus_1 = self
                .builder
                .binop(BinaryOp::Sub, len_val, one, ScalarType::U64);
            let rev_idx = self
                .builder
                .binop(BinaryOp::Sub, len_minus_1, i_param, ScalarType::U64);
            self.builder.load_dyn(data_ptr, rev_idx, ScalarType::Ptr)
        } else {
            self.builder.load_dyn(data_ptr, i_param, ScalarType::Ptr)
        };
        let result =
            self.builder
                .call(apply_name, vec![step_val, acc_param, elem], ScalarType::Ptr);

        let one = self.builder.const_u64(1);
        let next_i = self
            .builder
            .binop(BinaryOp::Add, i_param, one, ScalarType::U64);

        if until {
            // result is Step(b): slot 0 = tag, slot 1 = payload
            let tag = self.builder.load(result, 0, ScalarType::U64);
            let payload = self.builder.load(result, 1, acc_ty);
            let break_tag = self.decls.constructors["Break"].tag_index;
            let break_val = self.builder.const_u64(break_tag);
            let is_break = self
                .builder
                .binop(BinaryOp::Eq, tag, break_val, ScalarType::Bool);
            self.builder
                .branch(is_break, done, vec![payload], header, vec![next_i, payload]);
        } else {
            self.builder.jump(header, vec![next_i, result]);
        }

        self.builder.switch_to(done);
        done_param
    }

    // ---- Destructure lowering ----

    fn lower_destructure(&mut self, pattern: &ast::Pattern<'src>, val: Value) {
        match pattern {
            ast::Pattern::Tuple(elems) => {
                for (i, elem) in elems.iter().enumerate() {
                    let field_val = self.builder.load(val, i, ScalarType::Ptr);
                    self.lower_destructure_elem(elem, field_val);
                }
            }
            ast::Pattern::Record { fields } => {
                let mut all_names: Vec<&str> = fields
                    .iter()
                    .map(|(sym, _)| self.fields.get(*sym))
                    .collect();
                all_names.sort_unstable();
                for (field_sym, elem) in fields {
                    let name = self.fields.get(*field_sym);
                    let slot = all_names.iter().position(|n| *n == name).unwrap();
                    let field_val = self.builder.load(val, slot, ScalarType::Ptr);
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
                self.lower_destructure(elem, val);
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
) -> Result<(Module, Vec<Value>), CompileError> {
    let mut ctx = LowerCtx::new(decls, infer_result, symbols, fields);

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

    let main_ssa_params: Vec<Value> = params
        .iter()
        .map(|p| {
            let v = ctx.builder.fresh_value();
            ctx.vars.insert(*p, v);
            v
        })
        .collect();
    let entry = ctx.builder.create_block();
    ctx.builder.switch_to(entry);
    let result = ctx.lower_expr(&body);
    ctx.builder.ret(result);
    let main_param_types = vec![ScalarType::Ptr; main_ssa_params.len()];
    let main_ret_ty = ctx.func_ret_type("main");
    ctx.builder.finish_function(
        "__main",
        main_ssa_params.clone(),
        main_param_types,
        main_ret_ty,
    );

    let ssa_module = ctx.builder.build("__main");
    Ok((ssa_module, main_ssa_params))
}

// ---- Free helpers ----

/// Classify a mangled callable name as a `List.walk*` variant.
/// Returns `None` for every non-walk name. Lives at module level
/// (not as a method on `LowerCtx`) because it's pure string analysis.
fn classify_walk(name: &str) -> Option<WalkKind> {
    let base = name
        .strip_prefix("List.")
        .or_else(|| name.rsplit_once(".List.").map(|(_, rest)| rest))?;
    match base {
        "walk" => Some(WalkKind { backwards: false, until: false }),
        "walk_backwards" => Some(WalkKind { backwards: true, until: false }),
        "walk_until" => Some(WalkKind { backwards: false, until: true }),
        "walk_backwards_until" => Some(WalkKind { backwards: true, until: true }),
        _ => None,
    }
}

/// `I64.to_str` / `F64.to_str` / etc. — dispatched to the
/// `__num_to_str` runtime intrinsic.
fn is_num_to_str(name: &str) -> bool {
    matches!(
        name,
        "I8.to_str" | "U8.to_str" | "I64.to_str" | "U64.to_str" | "F64.to_str"
    )
}

/// Emit a call to one of the built-in list intrinsics
/// (`List.len` / `List.get` / `List.set` / `List.append`). Assumes
/// the caller already verified that `name` is a list builtin via
/// `LowerCtx::is_list_builtin`.
fn emit_list_builtin_call(builder: &mut Builder, name: &str, args: Vec<Value>) -> Value {
    let (intrinsic, ret_ty) = if name.ends_with(".len") || name == "List.len" {
        ("__list_len", ScalarType::U64)
    } else if name.ends_with(".get") || name == "List.get" {
        ("__list_get", ScalarType::Ptr)
    } else if name.ends_with(".set") || name == "List.set" {
        ("__list_set", ScalarType::Ptr)
    } else if name.ends_with(".append") || name == "List.append" {
        ("__list_append", ScalarType::Ptr)
    } else {
        panic!("unknown list builtin: {name}");
    };
    builder.call(intrinsic, args, ret_ty)
}
