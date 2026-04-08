use std::collections::{HashMap, HashSet};

use crate::decl_info::{self, DeclInfo, method_key, type_to_scalar};
use crate::defunc::{self, DefuncTable, LambdaSet};
use crate::error::CompileError;
use crate::source::SourceArena;
use crate::ssa::Module;
use crate::ssa::builder::Builder;
use crate::ssa::instruction::{BinaryOp, ScalarType, Value};
use crate::syntax::ast::{self, BinOp, Decl, Expr, ExprKind, Stmt};
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
) -> Result<(Module, Vec<Value>), CompileError> {
    // Parse stdlib modules
    let bool_stdlib = decl_info::parse_stdlib_module(arena, "Bool");
    let result_stdlib = decl_info::parse_stdlib_module(arena, "Result");
    let list_stdlib = decl_info::parse_stdlib_module(arena, "List");
    let str_stdlib = decl_info::parse_stdlib_module(arena, "Str");
    let stdlib_modules = [bool_stdlib, result_stdlib, list_stdlib, str_stdlib];

    // Pass 1: Registration
    let (mut decls, all_stdlib_methods) =
        decl_info::build(arena, module, scope, infer_result, &stdlib_modules);

    // Pass 2: Reachability
    let reachable = crate::reachable::compute(&decls, module, &all_stdlib_methods, infer_result);

    // Pass 3: Defunctionalization
    let defunc_table = defunc::collect(
        module,
        &all_stdlib_methods,
        &decls,
        &reachable,
        infer_result,
    );

    // Merge closure constructors into DeclInfo
    decls
        .constructors
        .extend(defunc_table.closure_constructors.clone());

    // Pass 4: SSA emission
    lower_to_ssa(
        module,
        infer_result,
        &decls,
        &reachable,
        &defunc_table,
        &all_stdlib_methods,
    )
}

// ---- SSA lowering context ----

struct LowerCtx<'a, 'src> {
    builder: Builder,
    vars: HashMap<String, Value>,
    ho_vars: HashMap<String, usize>,
    lambda_arg_counters: HashMap<(String, usize), usize>,
    fold_counter: usize,
    // Immutable references:
    decls: &'a DeclInfo,
    defunc: &'a DefuncTable<'src>,
    infer: &'a InferResult,
}

impl<'a, 'src> LowerCtx<'a, 'src> {
    fn new(decls: &'a DeclInfo, defunc: &'a DefuncTable<'src>, infer: &'a InferResult) -> Self {
        Self {
            builder: Builder::new(),
            vars: HashMap::new(),
            ho_vars: HashMap::new(),
            lambda_arg_counters: HashMap::new(),
            fold_counter: 0,
            decls,
            defunc,
            infer,
        }
    }

    // ---- Type helpers ----

    fn expr_scalar_type(&self, span: ast::Span) -> ScalarType {
        self.infer
            .expr_types
            .get(&span)
            .map_or(ScalarType::Ptr, |ty| type_to_scalar(ty))
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

    fn lower_function(&mut self, name: &str, param_names: &[&str], body: &Expr<'src>) {
        let saved_vars = self.vars.clone();
        let saved_blocks = std::mem::take(&mut self.builder.blocks);
        let saved_current = self.builder.current_block.take();

        let ssa_params: Vec<Value> = param_names
            .iter()
            .map(|p| {
                let v = self.builder.fresh_value();
                self.vars.insert((*p).to_owned(), v);
                v
            })
            .collect();

        let entry = self.builder.create_block();
        self.builder.switch_to(entry);
        let result = self.lower_expr(body);
        self.builder.ret(result);
        let param_types: Vec<ScalarType> = self
            .decls
            .func_schemes
            .get(name)
            .map(|scheme| match &scheme.ty {
                Type::Arrow(params, _) => params.iter().map(|t| type_to_scalar(t)).collect(),
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

    #[expect(clippy::too_many_lines, reason = "handles all expression forms")]
    fn lower_expr(&mut self, expr: &Expr<'src>) -> Value {
        match &expr.kind {
            #[expect(
                clippy::cast_sign_loss,
                clippy::cast_precision_loss,
                clippy::cast_possible_truncation
            )]
            ExprKind::IntLit(n) => match self.infer.lit_types.get(&expr.span) {
                Some(crate::types::infer::NumType::U8) => self.builder.const_u8(*n as u8),
                Some(crate::types::infer::NumType::I8) => self.builder.const_i8(*n as i8),
                Some(crate::types::infer::NumType::U64) => self.builder.const_u64(*n as u64),
                Some(crate::types::infer::NumType::F64) => self.builder.const_f64(*n as f64),
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

            ExprKind::Name(name) => {
                let name = *name;
                if let Some(&val) = self.vars.get(name) {
                    return val;
                }
                if self.decls.constructors.contains_key(name) {
                    return self.lower_constructor_call(name, &[]);
                }
                panic!("undefined name: {name}");
            }

            ExprKind::BinOp { op, lhs, rhs } => {
                let l = self.lower_expr(lhs);
                let r = self.lower_expr(rhs);
                let ty = self.expr_scalar_type(expr.span);
                match op {
                    BinOp::Add => self.builder.binop(BinaryOp::Add, l, r, ty),
                    BinOp::Sub => self.builder.binop(BinaryOp::Sub, l, r, ty),
                    BinOp::Mul => self.builder.binop(BinaryOp::Mul, l, r, ty),
                    BinOp::Div => self.builder.binop(BinaryOp::Div, l, r, ty),
                    BinOp::Rem => self.builder.binop(BinaryOp::Rem, l, r, ty),
                    BinOp::Eq => self.lower_eq(l, r, false),
                    BinOp::Neq => self.lower_eq(l, r, true),
                }
            }

            ExprKind::Call { func, args } => self.lower_call(func, args, expr.span),

            ExprKind::Block(stmts, result) => {
                for stmt in stmts {
                    match stmt {
                        Stmt::Let { name, val } => {
                            let v = self.lower_expr(val);
                            self.vars.insert((*name).to_owned(), v);
                        }
                        Stmt::Destructure { pattern, val } => {
                            let v = self.lower_expr(val);
                            self.lower_destructure(pattern, v);
                        }
                        Stmt::TypeHint { .. } => {}
                    }
                }
                self.lower_expr(result)
            }

            ExprKind::If {
                expr: scrutinee_expr,
                arms,
                ..
            } => {
                let result_ty = self.expr_scalar_type(expr.span);
                self.lower_match(scrutinee_expr, arms, result_ty)
            }

            ExprKind::Fold {
                expr: scrutinee_expr,
                arms,
            } => {
                let result_ty = self.expr_scalar_type(expr.span);
                self.lower_fold(scrutinee_expr, arms, result_ty)
            }

            ExprKind::QualifiedCall { segments, args } => {
                // Check if inference resolved this to a method call
                if let Some(resolved) = self.infer.method_resolutions.get(&expr.span).cloned() {
                    let receiver_name = segments[0];
                    let receiver_val = if let Some(&val) = self.vars.get(receiver_name) {
                        val
                    } else if self.decls.constructors.contains_key(receiver_name) {
                        self.lower_constructor_call(receiver_name, &[])
                    } else {
                        panic!("undefined receiver: {receiver_name}");
                    };
                    if let Some(builtin_name) = resolved.strip_prefix("__builtin.") {
                        let l = receiver_val;
                        let r = self.lower_expr(&args[0]);
                        let ty = self.expr_scalar_type(expr.span);
                        return match builtin_name {
                            "add" => self.builder.binop(BinaryOp::Add, l, r, ty),
                            "sub" => self.builder.binop(BinaryOp::Sub, l, r, ty),
                            "mul" => self.builder.binop(BinaryOp::Mul, l, r, ty),
                            "div" => self.builder.binop(BinaryOp::Div, l, r, ty),
                            "rem" => self.builder.binop(BinaryOp::Rem, l, r, ty),
                            "eq" => self.lower_eq(l, r, false),
                            "neq" => self.lower_eq(l, r, true),
                            _ => panic!("unknown builtin: {builtin_name}"),
                        };
                    }
                    // Method call: receiver.method(args) -> Type.method(receiver, args)
                    let mut arg_vals = vec![receiver_val];
                    for (i, a) in args.iter().enumerate() {
                        let idx = i + 1;
                        let key = (resolved.clone(), idx);
                        if self.defunc.ho_param_sets.contains_key(&key) {
                            arg_vals.push(self.lower_lambda_arg(a, &resolved, idx));
                        } else {
                            arg_vals.push(self.lower_expr(a));
                        }
                    }
                    return self.emit_function_call(&resolved, arg_vals, expr.span);
                }
                let mangled = segments.join(".");
                self.lower_call(&mangled, args, expr.span)
            }

            ExprKind::Record { fields } => {
                let ptr = self.builder.alloc(fields.len());
                let mut sorted: Vec<(usize, &str, &Expr)> = fields
                    .iter()
                    .enumerate()
                    .map(|(i, (name, expr))| (i, *name, expr))
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
                let slot = self
                    .infer
                    .expr_types
                    .get(&record.span)
                    .map_or(0, |ty| Self::field_slot(ty, field));
                let ty = self.expr_scalar_type(expr.span);
                self.builder.load(ptr, slot, ty)
            }

            ExprKind::MethodCall {
                receiver,
                method,
                args,
            } => {
                let resolved = self.infer.method_resolutions.get(&expr.span).cloned();
                if let Some(mangled) = resolved {
                    // List.walk / walk_backwards: special lowering
                    let is_walk = mangled == "List.walk" || mangled.ends_with(".List.walk");
                    let is_walk_back = mangled == "List.walk_backwards"
                        || mangled.ends_with(".List.walk_backwards");
                    if is_walk || is_walk_back {
                        let list_val = self.lower_expr(receiver);
                        let init_val = self.lower_expr(&args[0]);
                        let acc_ty = self.expr_scalar_type(args[0].span);
                        let key = (mangled.clone(), 2);
                        let closure_val = if self.defunc.ho_param_sets.contains_key(&key) {
                            self.lower_lambda_arg(&args[1], &mangled, 2)
                        } else {
                            self.lower_expr(&args[1])
                        };
                        let ls_idx = self.defunc.ho_param_sets[&key];
                        let apply_name = self.defunc.lambda_sets[ls_idx].apply_name.clone();
                        return self.lower_list_walk(
                            list_val,
                            init_val,
                            closure_val,
                            &apply_name,
                            is_walk_back,
                            acc_ty,
                        );
                    }

                    // Build full args: receiver + method args (with lambda handling)
                    let recv_val = self.lower_expr(receiver);
                    let mut full_args = vec![recv_val];
                    for (i, a) in args.iter().enumerate() {
                        let idx = i + 1;
                        let key = (mangled.clone(), idx);
                        if self.defunc.ho_param_sets.contains_key(&key) {
                            full_args.push(self.lower_lambda_arg(a, &mangled, idx));
                        } else {
                            full_args.push(self.lower_expr(a));
                        }
                    }
                    // Check for builtin arithmetic
                    if let Some(op_name) = mangled.strip_prefix("__builtin.") {
                        let ty = self.expr_scalar_type(expr.span);
                        return match op_name {
                            "add" => {
                                self.builder
                                    .binop(BinaryOp::Add, full_args[0], full_args[1], ty)
                            }
                            "sub" => {
                                self.builder
                                    .binop(BinaryOp::Sub, full_args[0], full_args[1], ty)
                            }
                            "mul" => {
                                self.builder
                                    .binop(BinaryOp::Mul, full_args[0], full_args[1], ty)
                            }
                            "div" => {
                                self.builder
                                    .binop(BinaryOp::Div, full_args[0], full_args[1], ty)
                            }
                            "rem" => {
                                self.builder
                                    .binop(BinaryOp::Rem, full_args[0], full_args[1], ty)
                            }
                            "eq" => self.lower_eq(full_args[0], full_args[1], false),
                            "neq" => self.lower_eq(full_args[0], full_args[1], true),
                            _ => panic!("unknown builtin: {op_name}"),
                        };
                    }
                    return self.emit_function_call(&mangled, full_args, expr.span);
                }
                panic!("no method resolution for .{method}() at {:?}", expr.span);
            }

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

    // ---- Call lowering ----

    fn lower_call(&mut self, func: &str, args: &[Expr<'src>], _span: ast::Span) -> Value {
        // List.walk / List.walk_backwards
        let is_walk = func == "List.walk" || func.ends_with(".List.walk");
        let is_walk_back = func == "List.walk_backwards" || func.ends_with(".List.walk_backwards");
        if is_walk || is_walk_back {
            assert!(args.len() >= 3, "List.walk takes 3 arguments");
            let list_val = self.lower_expr(&args[0]);
            let init_val = self.lower_expr(&args[1]);
            let acc_ty = self.expr_scalar_type(args[1].span);
            let key = (func.to_owned(), 2);
            let closure_val = if self.defunc.ho_param_sets.contains_key(&key) {
                self.lower_lambda_arg(&args[2], func, 2)
            } else {
                self.lower_expr(&args[2])
            };
            let ls_idx = self.defunc.ho_param_sets[&key];
            let apply_name = self.defunc.lambda_sets[ls_idx].apply_name.clone();
            return self.lower_list_walk(
                list_val,
                init_val,
                closure_val,
                &apply_name,
                is_walk_back,
                acc_ty,
            );
        }

        // List builtins
        if self.is_list_builtin(func) {
            let arg_vals: Vec<Value> = args.iter().map(|a| self.lower_expr(a)).collect();
            return self.emit_list_builtin(func, arg_vals);
        }

        // NumToStr
        if self.decls.num_to_str_methods.contains(func) {
            let arg_val = self.lower_expr(&args[0]);
            return self
                .builder
                .call("__num_to_str", vec![arg_val], ScalarType::Ptr);
        }

        // Constructor
        if self.decls.constructors.contains_key(func) {
            let arg_vals: Vec<Value> = args.iter().map(|a| self.lower_expr(a)).collect();
            return self.lower_constructor_call(func, &arg_vals);
        }

        // Regular function
        if self.decls.funcs.contains(func) {
            let ret_ty = self.func_ret_type(func);
            let arg_vals: Vec<Value> = args
                .iter()
                .enumerate()
                .map(|(i, a)| {
                    let key = (func.to_owned(), i);
                    if self.defunc.ho_param_sets.contains_key(&key) {
                        self.lower_lambda_arg(a, func, i)
                    } else {
                        self.lower_expr(a)
                    }
                })
                .collect();
            return self.builder.call(func, arg_vals, ret_ty);
        }

        // Variable used as function (higher-order)
        if let Some(&var_val) = self.vars.get(func) {
            if let Some(&ls_idx) = self.ho_vars.get(func) {
                let apply_name = self.defunc.lambda_sets[ls_idx].apply_name.clone();
                let arg_vals: Vec<Value> = args.iter().map(|a| self.lower_expr(a)).collect();
                let mut full_args = vec![var_val];
                full_args.extend(arg_vals);
                return self.builder.call(&apply_name, full_args, ScalarType::Ptr);
            }
            panic!("variable '{func}' called as function but has no lambda set");
        }

        panic!("undefined function or constructor: {func}");
    }

    fn emit_function_call(&mut self, name: &str, args: Vec<Value>, _span: ast::Span) -> Value {
        // Check for list builtins by name
        if self.is_list_builtin(name) {
            return self.emit_list_builtin(name, args);
        }
        // NumToStr
        if self.decls.num_to_str_methods.contains(name) {
            return self
                .builder
                .call("__num_to_str", vec![args[0]], ScalarType::Ptr);
        }
        let ret_ty = self.func_ret_type(name);
        self.builder.call(name, args, ret_ty)
    }

    fn is_list_builtin(&self, name: &str) -> bool {
        matches!(name, "List.len" | "List.get" | "List.set" | "List.append")
            || self.decls.list_builtins.contains(name)
    }

    fn emit_list_builtin(&mut self, name: &str, args: Vec<Value>) -> Value {
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
        self.builder.call(intrinsic, args, ret_ty)
    }

    // ---- Lambda argument lowering ----

    #[expect(
        clippy::arithmetic_side_effects,
        reason = "index counter for lambda matching"
    )]
    fn lower_lambda_arg(&mut self, arg: &Expr<'src>, callee: &str, arg_idx: usize) -> Value {
        let key = (callee.to_owned(), arg_idx);
        let ls_idx = self.defunc.ho_param_sets[&key];
        let counter = self.lambda_arg_counters.entry(key).or_insert(0);
        let entry_idx = *counter;
        *counter += 1;

        let entry = &self.defunc.lambda_sets[ls_idx].entries[entry_idx];
        let tag_name = entry.tag_name.clone();
        let captures: Vec<&'src str> = entry.captures.clone();

        match &arg.kind {
            ExprKind::Lambda { .. } => {
                let capture_vals: Vec<Value> = captures
                    .iter()
                    .map(|name| {
                        *self
                            .vars
                            .get(*name)
                            .unwrap_or_else(|| panic!("captured variable '{name}' not in scope"))
                    })
                    .collect();
                self.lower_constructor_call(&tag_name, &capture_vals)
            }
            ExprKind::Name(_) => {
                // Function reference -- nullary constructor
                self.lower_constructor_call(&tag_name, &[])
            }
            _ => panic!("expected lambda or function reference in higher-order argument"),
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

    // ---- Eq/Neq emission ----

    fn lower_eq(&mut self, lhs: Value, rhs: Value, negate: bool) -> Value {
        let cmp = self.builder.binop(BinaryOp::Eq, lhs, rhs, ScalarType::Bool);
        let true_meta = &self.decls.constructors["True"];
        let false_meta = &self.decls.constructors["False"];
        let alloc_size = 1 + true_meta.max_fields;

        let then_block = self.builder.create_block();
        let else_block = self.builder.create_block();
        let merge = self.builder.create_block();
        let merge_param = self.builder.add_block_param(merge, ScalarType::Ptr);

        self.builder
            .branch(cmp, then_block, vec![], else_block, vec![]);

        // then: return True (or False if negate)
        self.builder.switch_to(then_block);
        let (then_tag_idx, else_tag_idx) = if negate {
            (false_meta.tag_index, true_meta.tag_index)
        } else {
            (true_meta.tag_index, false_meta.tag_index)
        };
        let then_ptr = self.builder.alloc(alloc_size);
        let then_tag = self.builder.const_u64(then_tag_idx);
        self.builder.store(then_ptr, 0, then_tag);
        self.builder.jump(merge, vec![then_ptr]);

        // else: return False (or True if negate)
        self.builder.switch_to(else_block);
        let else_ptr = self.builder.alloc(alloc_size);
        let else_tag = self.builder.const_u64(else_tag_idx);
        self.builder.store(else_ptr, 0, else_tag);
        self.builder.jump(merge, vec![else_ptr]);

        self.builder.switch_to(merge);
        merge_param
    }

    // ---- Match lowering ----

    fn lower_match(
        &mut self,
        scrutinee_expr: &Expr<'src>,
        arms: &[ast::MatchArm<'src>],
        result_ty: ScalarType,
    ) -> Value {
        let scr_val = self.lower_expr(scrutinee_expr);
        let tag = self.builder.load(scr_val, 0, ScalarType::U64);

        let tag_block = self.builder.current_block.unwrap();

        let merge = self.builder.create_block();
        let merge_param = self.builder.add_block_param(merge, result_ty);

        let mut switch_arms = Vec::new();
        let mut arm_blocks = Vec::new();
        for arm in arms {
            let ast::Pattern::Constructor { name: con_name, .. } = &arm.pattern else {
                panic!("match arms must use constructor patterns");
            };
            let meta = &self.decls.constructors[*con_name];
            let arm_block = self.builder.create_block();
            switch_arms.push((meta.tag_index, arm_block, vec![]));
            arm_blocks.push(arm_block);
        }

        self.builder.switch_to(tag_block);
        self.builder.switch_int(tag, switch_arms, None);

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

            let result = self.lower_expr(&arm.body);
            self.builder.jump(merge, vec![result]);
            self.vars = saved_vars;
        }

        self.builder.switch_to(merge);
        merge_param
    }

    fn bind_pattern_field(&mut self, pat: &ast::Pattern<'src>, val: Value) {
        match pat {
            ast::Pattern::Binding(name) => {
                self.vars.insert((*name).to_owned(), val);
            }
            ast::Pattern::Wildcard => {}
            _ => panic!("unsupported nested pattern in match arm field"),
        }
    }

    // ---- Fold lowering ----

    fn lower_fold(
        &mut self,
        scrutinee_expr: &Expr<'src>,
        arms: &[ast::MatchArm<'src>],
        result_ty: ScalarType,
    ) -> Value {
        let fold_name = format!("__fold_{}", self.fold_counter);
        self.fold_counter += 1;

        // Collect captures from arm bodies (free vars minus pattern bindings)
        let captures: Vec<(&str, Value)> = self.collect_fold_captures(arms);

        // Save builder state
        let saved_vars = self.vars.clone();
        let saved_ho_vars = self.ho_vars.clone();
        let saved_blocks = std::mem::take(&mut self.builder.blocks);
        let saved_current = self.builder.current_block.take();

        // Build fold helper function
        let val_param = self.builder.fresh_value();
        let mut fold_params = vec![val_param];
        let mut fold_param_types = vec![ScalarType::Ptr];
        let mut capture_param_map: HashMap<String, Value> = HashMap::new();
        for (cap_name, _) in &captures {
            let p = self.builder.fresh_value();
            fold_params.push(p);
            fold_param_types.push(ScalarType::Ptr);
            capture_param_map.insert((*cap_name).to_owned(), p);
        }

        let entry = self.builder.create_block();
        self.builder.switch_to(entry);

        // Set up var_map with capture params and propagate ho_vars for captures
        let mut fold_ho_vars = HashMap::new();
        for (cap_name, _) in &captures {
            if let Some(&ls_idx) = saved_ho_vars.get(*cap_name) {
                fold_ho_vars.insert((*cap_name).to_owned(), ls_idx);
            }
        }
        self.vars = capture_param_map;
        self.ho_vars = fold_ho_vars;

        let tag = self.builder.load(val_param, 0, ScalarType::U64);

        let merge = self.builder.create_block();
        let merge_param = self.builder.add_block_param(merge, result_ty);
        let mut switch_arms = Vec::new();

        let tag_block = self.builder.current_block.unwrap();

        for arm in arms {
            let ast::Pattern::Constructor {
                name: con_name,
                fields,
            } = &arm.pattern
            else {
                panic!("fold arms must use constructor patterns");
            };
            let con_name = *con_name;
            let meta = self.decls.constructors[con_name].clone();
            let arm_block = self.builder.create_block();
            switch_arms.push((meta.tag_index, arm_block, vec![]));

            self.builder.switch_to(arm_block);

            // Load fields and bind pattern names
            for (fi, field_pat) in fields.iter().enumerate() {
                let field_ty = meta.field_types.get(fi).copied().unwrap_or(ScalarType::Ptr);
                let field_val = self.builder.load(val_param, fi + 1, field_ty);
                self.bind_pattern_field(field_pat, field_val);
            }

            // For recursive fields, emit recursive call and shadow the binding
            let mut rec_idx = 0;
            for (fi, field_pat) in fields.iter().enumerate() {
                if fi < meta.recursive_flags.len() && meta.recursive_flags[fi] {
                    let field_ty = meta.field_types.get(fi).copied().unwrap_or(ScalarType::Ptr);
                    let field_val = self.builder.load(val_param, fi + 1, field_ty);
                    let mut call_args = vec![field_val];
                    for (cap_name, _) in &captures {
                        call_args.push(self.vars[*cap_name]);
                    }
                    let rec_result = self.builder.call(&fold_name, call_args, result_ty);
                    // Shadow: the user's binding name now refers to the fold result
                    if let ast::Pattern::Binding(name) = field_pat {
                        self.vars.insert((*name).to_owned(), rec_result);
                    }
                    rec_idx += 1;
                }
            }
            let _ = rec_idx; // suppress unused

            let result = self.lower_expr(&arm.body);
            self.builder.jump(merge, vec![result]);
        }

        // Emit switch from tag block
        self.builder.switch_to(tag_block);
        self.builder.switch_int(tag, switch_arms, None);

        // Merge block returns
        self.builder.switch_to(merge);
        self.builder.ret(merge_param);
        self.builder
            .finish_function(&fold_name, fold_params, fold_param_types, result_ty);

        // Restore parent function's builder state
        self.builder.blocks = saved_blocks;
        self.builder.current_block = saved_current;
        self.vars = saved_vars;
        self.ho_vars = saved_ho_vars;

        let scr_val = self.lower_expr(scrutinee_expr);
        let mut call_args = vec![scr_val];
        for (_, capture_val) in &captures {
            call_args.push(*capture_val);
        }
        self.builder.call(&fold_name, call_args, result_ty)
    }

    // ---- Free variable collection for fold arms (over AST Expr) ----

    fn collect_fold_captures(&self, arms: &[ast::MatchArm<'src>]) -> Vec<(&'src str, Value)> {
        let mut captures: Vec<(&'src str, Value)> = Vec::new();
        let mut seen: HashSet<&str> = HashSet::new();

        for arm in arms {
            let mut excluded = HashSet::new();
            defunc::pattern_names(&arm.pattern, &mut excluded);
            self.collect_fold_captures_expr(&arm.body, &excluded, &mut seen, &mut captures);
        }
        captures
    }

    fn collect_fold_captures_expr(
        &self,
        expr: &Expr<'src>,
        excluded: &HashSet<&'src str>,
        seen: &mut HashSet<&'src str>,
        captures: &mut Vec<(&'src str, Value)>,
    ) {
        match &expr.kind {
            ExprKind::Name(name) => {
                let name = *name;
                if excluded.contains(name)
                    || self.decls.constructors.contains_key(name)
                    || self.decls.funcs.contains(name)
                    || seen.contains(name)
                {
                    return;
                }
                if let Some(&val) = self.vars.get(name) {
                    seen.insert(name);
                    captures.push((name, val));
                }
            }
            ExprKind::IntLit(_) | ExprKind::FloatLit(_) | ExprKind::StrLit(_) => {}
            ExprKind::BinOp { lhs, rhs, .. } => {
                self.collect_fold_captures_expr(lhs, excluded, seen, captures);
                self.collect_fold_captures_expr(rhs, excluded, seen, captures);
            }
            ExprKind::Call { func, args } => {
                if !excluded.contains(func)
                    && !self.decls.constructors.contains_key(*func)
                    && !self.decls.funcs.contains(*func)
                    && !seen.contains(func)
                {
                    if let Some(&val) = self.vars.get(*func) {
                        seen.insert(func);
                        captures.push((func, val));
                    }
                }
                for a in args {
                    self.collect_fold_captures_expr(a, excluded, seen, captures);
                }
            }
            ExprKind::QualifiedCall { args, .. } => {
                for a in args {
                    self.collect_fold_captures_expr(a, excluded, seen, captures);
                }
            }
            ExprKind::Block(stmts, result) => {
                let mut inner_excluded = excluded.clone();
                for stmt in stmts {
                    match stmt {
                        Stmt::Let { name, val } => {
                            self.collect_fold_captures_expr(val, &inner_excluded, seen, captures);
                            inner_excluded.insert(name);
                        }
                        Stmt::Destructure { pattern, val } => {
                            self.collect_fold_captures_expr(val, &inner_excluded, seen, captures);
                            defunc::pattern_names(pattern, &mut inner_excluded);
                        }
                        Stmt::TypeHint { .. } => {}
                    }
                }
                self.collect_fold_captures_expr(result, &inner_excluded, seen, captures);
            }
            ExprKind::If {
                expr: scr,
                arms,
                else_body,
            } => {
                self.collect_fold_captures_expr(scr, excluded, seen, captures);
                for arm in arms {
                    let mut arm_excl = excluded.clone();
                    defunc::pattern_names(&arm.pattern, &mut arm_excl);
                    self.collect_fold_captures_expr(&arm.body, &arm_excl, seen, captures);
                }
                if let Some(eb) = else_body {
                    self.collect_fold_captures_expr(eb, excluded, seen, captures);
                }
            }
            ExprKind::Fold { expr: scr, arms } => {
                self.collect_fold_captures_expr(scr, excluded, seen, captures);
                for arm in arms {
                    let mut arm_excl = excluded.clone();
                    defunc::pattern_names(&arm.pattern, &mut arm_excl);
                    self.collect_fold_captures_expr(&arm.body, &arm_excl, seen, captures);
                }
            }
            ExprKind::Record { fields } => {
                for (_, e) in fields {
                    self.collect_fold_captures_expr(e, excluded, seen, captures);
                }
            }
            ExprKind::FieldAccess { record, .. } => {
                self.collect_fold_captures_expr(record, excluded, seen, captures);
            }
            ExprKind::MethodCall { receiver, args, .. } => {
                self.collect_fold_captures_expr(receiver, excluded, seen, captures);
                for a in args {
                    self.collect_fold_captures_expr(a, excluded, seen, captures);
                }
            }
            ExprKind::Lambda { params, body } => {
                let mut inner_excluded = excluded.clone();
                for p in params {
                    inner_excluded.insert(p);
                }
                self.collect_fold_captures_expr(body, &inner_excluded, seen, captures);
            }
            ExprKind::Tuple(elems) | ExprKind::ListLit(elems) => {
                for e in elems {
                    self.collect_fold_captures_expr(e, excluded, seen, captures);
                }
            }
        }
    }

    // ---- List walk lowering ----

    fn lower_list_walk(
        &mut self,
        list_val: Value,
        init_val: Value,
        step_val: Value,
        apply_name: &str,
        backwards: bool,
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
        let new_acc =
            self.builder
                .call(apply_name, vec![step_val, acc_param, elem], ScalarType::Ptr);
        let one = self.builder.const_u64(1);
        let next_i = self
            .builder
            .binop(BinaryOp::Add, i_param, one, ScalarType::U64);
        self.builder.jump(header, vec![next_i, new_acc]);

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
                let mut all_names: Vec<&str> = fields.iter().map(|(n, _)| *n).collect();
                all_names.sort_unstable();
                for (name, elem) in fields {
                    let slot = all_names.iter().position(|n| n == name).unwrap();
                    let field_val = self.builder.load(val, slot, ScalarType::Ptr);
                    self.lower_destructure_elem(elem, field_val);
                }
            }
            _ => panic!("expected tuple or record pattern in destructure"),
        }
    }

    fn lower_destructure_elem(&mut self, elem: &ast::Pattern<'src>, val: Value) {
        match elem {
            ast::Pattern::Binding(name) => {
                self.vars.insert((*name).to_owned(), val);
            }
            ast::Pattern::Tuple(_) | ast::Pattern::Record { .. } => {
                self.lower_destructure(elem, val);
            }
            ast::Pattern::Wildcard => {}
            _ => panic!("unsupported pattern in destructure"),
        }
    }

    // ---- Generate apply functions ----

    fn generate_apply_functions(&mut self) {
        let sets: Vec<LambdaSet<'src>> = self.defunc.lambda_sets.clone();

        for ls in &sets {
            let apply_name = ls.apply_name.clone();

            // Save builder state
            let saved_vars = self.vars.clone();
            let saved_blocks = std::mem::take(&mut self.builder.blocks);
            let saved_current = self.builder.current_block.take();

            // Build apply function: (closure, arg0, arg1, ...) -> result
            let closure_param = self.builder.fresh_value();
            let arg_params: Vec<Value> =
                (0..ls.arity).map(|_| self.builder.fresh_value()).collect();

            let entry = self.builder.create_block();
            self.builder.switch_to(entry);

            // Load tag from closure
            let tag = self.builder.load(closure_param, 0, ScalarType::U64);
            let tag_block = self.builder.current_block.unwrap();

            let merge = self.builder.create_block();
            let merge_param = self.builder.add_block_param(merge, ScalarType::Ptr);

            let mut switch_arms_vec = Vec::new();

            for entry_data in &ls.entries {
                let meta = &self.decls.constructors[&entry_data.tag_name];
                let arm_block = self.builder.create_block();
                switch_arms_vec.push((meta.tag_index, arm_block, vec![]));
            }

            self.builder.switch_to(tag_block);
            self.builder.switch_int(tag, switch_arms_vec.clone(), None);

            for (ei, entry_data) in ls.entries.iter().enumerate() {
                self.builder.switch_to(switch_arms_vec[ei].1);

                if let Some(func_name) = &entry_data.func_ref {
                    // Direct dispatch to named function
                    let ret_ty = self.func_ret_type(func_name);
                    let result = self.builder.call(func_name, arg_params.clone(), ret_ty);
                    self.builder.jump(merge, vec![result]);
                } else {
                    // Load captures from closure
                    for (ci, cap_name) in entry_data.captures.iter().enumerate() {
                        let cap_val = self.builder.load(closure_param, ci + 1, ScalarType::Ptr);
                        self.vars.insert((*cap_name).to_owned(), cap_val);
                    }
                    // Wire up ho_vars for captured higher-order variables
                    for (cap_name, ho_idx) in
                        entry_data.captures.iter().zip(entry_data.capture_ho.iter())
                    {
                        if let Some(ls_idx) = ho_idx {
                            self.ho_vars.insert((*cap_name).to_owned(), *ls_idx);
                        }
                    }
                    // Bind params
                    for (param_name, &arg_val) in entry_data.params.iter().zip(&arg_params) {
                        self.vars.insert((*param_name).to_owned(), arg_val);
                    }

                    let result = self.lower_expr(entry_data.body.as_ref().unwrap());
                    self.builder.jump(merge, vec![result]);

                    // Clean up
                    for cap_name in &entry_data.captures {
                        self.vars.remove(*cap_name);
                        self.ho_vars.remove(*cap_name);
                    }
                    for param_name in &entry_data.params {
                        self.vars.remove(*param_name);
                    }
                }
            }

            self.builder.switch_to(merge);
            self.builder.ret(merge_param);

            let mut all_params = vec![closure_param];
            all_params.extend(&arg_params);
            let all_param_types = vec![ScalarType::Ptr; all_params.len()];
            self.builder
                .finish_function(&apply_name, all_params, all_param_types, ScalarType::Ptr);

            // Restore builder state
            self.builder.blocks = saved_blocks;
            self.builder.current_block = saved_current;
            self.vars = saved_vars;
        }
    }
}

// ---- SSA emission (Pass 4) ----

fn lower_to_ssa<'src>(
    module: &ast::Module<'src>,
    infer_result: &InferResult,
    decls: &DeclInfo,
    reachable: &HashSet<String>,
    defunc_table: &DefuncTable<'src>,
    all_stdlib_methods: &[(&'src str, &Decl<'src>)],
) -> Result<(Module, Vec<Value>), CompileError> {
    let mut ctx = LowerCtx::new(decls, defunc_table, infer_result);

    let mut main_params = None;
    let mut main_body = None;

    for decl in &module.decls {
        let Decl::FuncDef {
            name, params, body, ..
        } = decl
        else {
            continue;
        };
        let name = *name;

        if name == "main" {
            main_params = Some(params.clone());
            main_body = Some(body.clone());
            continue;
        }

        if !reachable.contains(name) {
            continue;
        }

        // Mark higher-order parameters
        for (i, p) in params.iter().enumerate() {
            let key = (name.to_owned(), i);
            if let Some(&ls_idx) = defunc_table.ho_param_sets.get(&key) {
                ctx.ho_vars.insert((*p).to_owned(), ls_idx);
            }
        }

        ctx.lower_function(name, params, body);

        for p in params {
            ctx.vars.remove(*p);
            ctx.ho_vars.remove(*p);
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
        let type_name = *type_name;
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
            let method_name = *method_name;
            let mangled = method_key(type_name, method_name);
            if !reachable.contains(&mangled) {
                continue;
            }

            for (i, p) in params.iter().enumerate() {
                let key = (mangled.clone(), i);
                if let Some(&ls_idx) = defunc_table.ho_param_sets.get(&key) {
                    ctx.ho_vars.insert((*p).to_owned(), ls_idx);
                }
            }

            ctx.lower_function(&mangled, params, body);

            for p in params {
                ctx.vars.remove(*p);
                ctx.ho_vars.remove(*p);
            }
        }
    }

    // Lower stdlib method bodies
    for &(type_name, method) in all_stdlib_methods {
        if let Decl::FuncDef {
            name, params, body, ..
        } = method
        {
            let mangled = method_key(type_name, name);
            if !reachable.contains(&mangled) {
                continue;
            }
            for (i, p) in params.iter().enumerate() {
                let key = (mangled.clone(), i);
                if let Some(&ls_idx) = defunc_table.ho_param_sets.get(&key) {
                    ctx.ho_vars.insert((*p).to_owned(), ls_idx);
                }
            }

            ctx.lower_function(&mangled, params, body);

            for p in params {
                ctx.vars.remove(*p);
                ctx.ho_vars.remove(*p);
            }
        }
    }

    // Generate apply functions from collected lambda sets
    ctx.generate_apply_functions();

    // Lower main
    let params = main_params.ok_or_else(|| CompileError::new("no 'main' function defined"))?;
    let body = main_body.unwrap();

    // Mark main's higher-order params (unlikely but consistent)
    for (i, p) in params.iter().enumerate() {
        let key = ("main".to_owned(), i);
        if let Some(&ls_idx) = defunc_table.ho_param_sets.get(&key) {
            ctx.ho_vars.insert((*p).to_owned(), ls_idx);
        }
    }

    let main_ssa_params: Vec<Value> = params
        .iter()
        .map(|p| {
            let v = ctx.builder.fresh_value();
            ctx.vars.insert((*p).to_owned(), v);
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
