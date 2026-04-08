use std::collections::HashMap;

use crate::core::{Builtin, Core, FuncId, Literal, NumVal, Pattern, Program, VarId};
use crate::ssa::Module;
use crate::ssa::builder::Builder;
use crate::ssa::instruction::{BinaryOp, Value};

/// Lower a Core Program to a low-level SSA Module.
pub fn lower(program: &Program, input_vars: &[VarId]) -> Module {
    let mut ctx = LowerCtx::new(program);

    // Build constructor metadata
    ctx.build_constructor_info();

    // Lower all functions
    for func_def in &program.funcs {
        let name = program.debug_names.func_name(func_def.name).to_owned();
        ctx.lower_function(&name, &func_def.params, &func_def.body);
    }

    // Lower main as "__main"
    let main_params: Vec<Value> = input_vars
        .iter()
        .map(|var| {
            let v = ctx.builder.fresh_value();
            ctx.var_map.insert(*var, v);
            v
        })
        .collect();
    let entry = ctx.builder.create_block();
    ctx.builder.switch_to(entry);
    let result = ctx.lower_expr(&program.main);
    ctx.builder.ret(result);
    ctx.builder.finish_function("__main", main_params);

    ctx.builder.build("__main")
}

struct ConstructorInfo {
    /// Tag index within its parent type (0, 1, 2, ...)
    tag_index: u64,
    /// Number of fields
    num_fields: usize,
    /// Max fields across all constructors in the same type
    max_fields: usize,
}

struct LowerCtx<'a> {
    program: &'a Program,
    builder: Builder,
    /// Maps Core VarId to SSA Value.
    var_map: HashMap<VarId, Value>,
    /// Maps Core FuncId to SSA function name.
    func_names: HashMap<FuncId, String>,
    /// Constructor metadata: FuncId → (tag_index, num_fields, max_fields_in_type).
    con_info: HashMap<FuncId, ConstructorInfo>,
    /// Counter for generating unique fold helper names.
    fold_counter: usize,
}

impl<'a> LowerCtx<'a> {
    fn new(program: &'a Program) -> Self {
        let mut func_names = HashMap::new();
        for func_def in &program.funcs {
            let name = program.debug_names.func_name(func_def.name).to_owned();
            func_names.insert(func_def.name, name);
        }
        // Also map builtins
        for &func_id in program.builtins.keys() {
            let name = program.debug_names.func_name(func_id).to_owned();
            func_names.insert(func_id, name);
        }

        Self {
            program,
            builder: Builder::new(),
            var_map: HashMap::new(),
            func_names,
            con_info: HashMap::new(),
            fold_counter: 0,
        }
    }

    fn build_constructor_info(&mut self) {
        for type_def in &self.program.types {
            let max_fields = type_def
                .constructors
                .iter()
                .map(|c| c.fields.len())
                .max()
                .unwrap_or(0);
            for (i, con) in type_def.constructors.iter().enumerate() {
                self.con_info.insert(
                    con.tag,
                    ConstructorInfo {
                        tag_index: i as u64,
                        num_fields: con.fields.len(),
                        max_fields,
                    },
                );
            }
        }
    }

    fn is_constructor(&self, func: FuncId) -> bool {
        self.con_info.contains_key(&func)
    }

    fn lower_function(&mut self, name: &str, params: &[VarId], body: &Core) {
        let saved_vars = self.var_map.clone();

        let ssa_params: Vec<Value> = params
            .iter()
            .map(|var| {
                let v = self.builder.fresh_value();
                self.var_map.insert(*var, v);
                v
            })
            .collect();

        let entry = self.builder.create_block();
        self.builder.switch_to(entry);
        let result = self.lower_expr(body);
        self.builder.ret(result);
        self.builder.finish_function(name, ssa_params);

        self.var_map = saved_vars;
    }

    fn lower_expr(&mut self, expr: &Core) -> Value {
        match expr {
            Core::Var(var_id) => self.var_map[var_id],

            Core::Lit(Literal::Num(n)) => match n {
                NumVal::I64(v) => self.builder.const_i64(*v),
                NumVal::U64(v) => self.builder.const_u64(*v),
                NumVal::F64(v) => self.builder.const_f64(*v),
                NumVal::U8(v) => self.builder.const_u8(*v),
                NumVal::I8(v) => self.builder.const_i8(*v),
            },

            Core::App { func, args } => {
                if self.is_constructor(*func) {
                    self.lower_constructor(*func, args)
                } else if let Some(builtin) = self.program.builtins.get(func) {
                    self.lower_builtin(*builtin, args)
                } else {
                    self.lower_func_call(*func, args)
                }
            }

            Core::Let { name, val, body } => {
                let v = self.lower_expr(val);
                self.var_map.insert(*name, v);
                self.lower_expr(body)
            }

            Core::Match { expr, arms } => self.lower_match(expr, arms),

            Core::Fold { expr, arms } => self.lower_fold(expr, arms),

            Core::Record { fields } => {
                let num_fields = fields.len();
                let ptr = self.builder.alloc(num_fields);
                // Sort by name for consistent layout
                let mut sorted: Vec<(usize, &str, &Core)> = fields
                    .iter()
                    .enumerate()
                    .map(|(i, (name, expr))| (i, name.as_str(), expr))
                    .collect();
                sorted.sort_by_key(|(_, name, _)| *name);
                for (slot, (_, _, field_expr)) in sorted.iter().enumerate() {
                    let val = self.lower_expr(field_expr);
                    self.builder.store(ptr, slot, val);
                }
                ptr
            }

            Core::FieldAccess { record, field } => {
                let ptr = self.lower_expr(record);
                // We need to know the slot index for this field.
                // Since we sort fields alphabetically, compute the index.
                // For now, use a heuristic: look up the record's known fields.
                // TODO: proper record layout from type info
                self.builder.load(ptr, field_slot_index(field))
            }

            Core::ListLit(elements) => {
                let len = elements.len();
                let data = self.builder.alloc(len);
                for (i, elem) in elements.iter().enumerate() {
                    let val = self.lower_expr(elem);
                    self.builder.store(data, i, val);
                }
                let header = self.builder.alloc(3);
                let len_val = self.builder.const_u64(len as u64);
                self.builder.store(header, 0, len_val);
                self.builder.store(header, 1, len_val); // cap = len
                self.builder.store(header, 2, data);
                header
            }

            Core::ListWalk {
                list,
                init,
                step,
                apply_func,
                backwards,
            } => self.lower_list_walk(list, init, step, *apply_func, *backwards),
        }
    }

    fn lower_constructor(&mut self, func: FuncId, args: &[Core]) -> Value {
        let info = &self.con_info[&func];
        let alloc_size = 1 + info.max_fields; // slot 0 = tag, slots 1..N = fields
        let ptr = self.builder.alloc(alloc_size);
        let tag_val = self.builder.const_u64(info.tag_index);
        self.builder.store(ptr, 0, tag_val);
        for (i, arg) in args.iter().enumerate() {
            let val = self.lower_expr(arg);
            self.builder.store(ptr, i + 1, val);
        }
        ptr
    }

    fn lower_builtin(&mut self, builtin: Builtin, args: &[Core]) -> Value {
        match builtin {
            Builtin::Add => self.lower_binop(BinaryOp::Add, args),
            Builtin::Sub => self.lower_binop(BinaryOp::Sub, args),
            Builtin::Mul => self.lower_binop(BinaryOp::Mul, args),
            Builtin::Div => self.lower_binop(BinaryOp::Div, args),
            Builtin::Rem => self.lower_binop(BinaryOp::Rem, args),
            Builtin::Max => self.lower_binop(BinaryOp::Max, args),
            Builtin::Eq {
                true_con,
                false_con,
            } => {
                let lhs = self.lower_expr(&args[0]);
                let rhs = self.lower_expr(&args[1]);
                let cmp = self.builder.binop(BinaryOp::Eq, lhs, rhs);

                // Create tagged union for Bool
                let true_info = &self.con_info[&true_con];
                let false_info = &self.con_info[&false_con];
                let alloc_size = 1 + true_info.max_fields;

                let then_block = self.builder.create_block();
                let else_block = self.builder.create_block();
                let merge = self.builder.create_block();
                let merge_param = self.builder.add_block_param(merge);

                self.builder
                    .branch(cmp, then_block, vec![], else_block, vec![]);

                self.builder.switch_to(then_block);
                let true_ptr = self.builder.alloc(alloc_size);
                let true_tag = self.builder.const_u64(true_info.tag_index);
                self.builder.store(true_ptr, 0, true_tag);
                self.builder.jump(merge, vec![true_ptr]);

                self.builder.switch_to(else_block);
                let false_ptr = self.builder.alloc(alloc_size);
                let false_tag = self.builder.const_u64(false_info.tag_index);
                self.builder.store(false_ptr, 0, false_tag);
                self.builder.jump(merge, vec![false_ptr]);

                self.builder.switch_to(merge);
                merge_param
            }
            Builtin::ListLen => {
                let list = self.lower_expr(&args[0]);
                self.builder.call("__list_len", vec![list])
            }
            Builtin::ListGet => {
                let list = self.lower_expr(&args[0]);
                let idx = self.lower_expr(&args[1]);
                self.builder.call("__list_get", vec![list, idx])
            }
            Builtin::ListSet => {
                let list = self.lower_expr(&args[0]);
                let idx = self.lower_expr(&args[1]);
                let val = self.lower_expr(&args[2]);
                self.builder.call("__list_set", vec![list, idx, val])
            }
            Builtin::ListAppend => {
                let list = self.lower_expr(&args[0]);
                let val = self.lower_expr(&args[1]);
                self.builder.call("__list_append", vec![list, val])
            }
            Builtin::NumToStr => {
                let num = self.lower_expr(&args[0]);
                self.builder.call("__num_to_str", vec![num])
            }
        }
    }

    fn lower_binop(&mut self, op: BinaryOp, args: &[Core]) -> Value {
        let lhs = self.lower_expr(&args[0]);
        let rhs = self.lower_expr(&args[1]);
        self.builder.binop(op, lhs, rhs)
    }

    fn lower_func_call(&mut self, func: FuncId, args: &[Core]) -> Value {
        let name = self
            .func_names
            .get(&func)
            .unwrap_or_else(|| {
                panic!(
                    "unknown function: {}",
                    self.program.debug_names.func_name(func)
                )
            })
            .clone();
        let arg_vals: Vec<Value> = args.iter().map(|a| self.lower_expr(a)).collect();
        self.builder.call(&name, arg_vals)
    }

    fn lower_match(&mut self, scrutinee: &Core, arms: &[(Pattern, Core)]) -> Value {
        let scr_val = self.lower_expr(scrutinee);
        let tag = self.builder.load(scr_val, 0); // slot 0 = tag

        // Save the block where we computed the tag — switch goes here
        let tag_block = self.builder.current_block.unwrap();

        let merge = self.builder.create_block();
        let merge_param = self.builder.add_block_param(merge);

        // Create arm blocks first
        let mut switch_arms = Vec::new();
        let arm_blocks: Vec<_> = arms
            .iter()
            .map(|(pattern, _)| {
                let Pattern::Constructor { tag: con_tag, .. } = pattern;
                let info = &self.con_info[con_tag];
                let arm_block = self.builder.create_block();
                switch_arms.push((info.tag_index, arm_block, vec![]));
                arm_block
            })
            .collect();

        // Emit switch from tag block
        self.builder.switch_to(tag_block);
        self.builder.switch_int(tag, switch_arms, None);

        // Fill arm bodies
        for (i, (pattern, body)) in arms.iter().enumerate() {
            let Pattern::Constructor { fields, .. } = pattern;
            self.builder.switch_to(arm_blocks[i]);

            let saved_vars = self.var_map.clone();
            for (fi, field_var) in fields.iter().enumerate() {
                let field_val = self.builder.load(scr_val, fi + 1);
                self.var_map.insert(*field_var, field_val);
            }

            let result = self.lower_expr(body);
            self.builder.jump(merge, vec![result]);
            self.var_map = saved_vars;
        }

        self.builder.switch_to(merge);
        merge_param
    }

    fn lower_fold(&mut self, scrutinee: &Core, arms: &[crate::core::FoldArm]) -> Value {
        // Generate a recursive fold helper function
        let fold_name = format!("__fold_{}", self.fold_counter);
        self.fold_counter += 1;

        // Collect captured variables (free vars in arm bodies minus pattern bindings)
        let mut captures: Vec<(VarId, Value)> = Vec::new();
        let mut capture_set: HashMap<VarId, usize> = HashMap::new();
        for arm in arms {
            let Pattern::Constructor { fields, .. } = &arm.pattern;
            self.collect_captures(
                &arm.body,
                fields,
                &arm.rec_binds,
                &mut captures,
                &mut capture_set,
            );
        }

        // Build the fold helper function
        // Params: val_ptr, capture_0, capture_1, ...
        let saved_vars = self.var_map.clone();
        let val_param = self.builder.fresh_value();
        let mut fold_params = vec![val_param];
        let mut capture_param_map: HashMap<VarId, Value> = HashMap::new();
        for (var_id, _) in &captures {
            let p = self.builder.fresh_value();
            fold_params.push(p);
            capture_param_map.insert(*var_id, p);
        }

        let entry = self.builder.create_block();
        self.builder.switch_to(entry);

        // Set up var_map with capture params
        self.var_map = capture_param_map;

        let tag = self.builder.load(val_param, 0);

        let merge = self.builder.create_block();
        let merge_param = self.builder.add_block_param(merge);
        let mut switch_arms = Vec::new();

        // Save the tag block to emit switch from
        let tag_block = self.builder.current_block.unwrap();

        for arm in arms {
            let Pattern::Constructor {
                tag: con_tag,
                fields,
            } = &arm.pattern;
            let info = &self.con_info[con_tag];
            let arm_block = self.builder.create_block();
            switch_arms.push((info.tag_index, arm_block, vec![]));

            self.builder.switch_to(arm_block);

            // Load fields
            for (i, field_var) in fields.iter().enumerate() {
                let field_val = self.builder.load(val_param, i + 1);
                self.var_map.insert(*field_var, field_val);
            }

            // Recursively fold recursive fields
            for (ri, rec_var) in arm.rec_binds.iter().enumerate() {
                // Find which field is the ri-th recursive one
                let con_def = self
                    .program
                    .types
                    .iter()
                    .flat_map(|t| &t.constructors)
                    .find(|c| c.tag == *con_tag)
                    .unwrap();
                let mut rec_count = 0;
                for (fi, field_def) in con_def.fields.iter().enumerate() {
                    if field_def.recursive {
                        if rec_count == ri {
                            let field_val = self.builder.load(val_param, fi + 1);
                            // Recursive call: fold_helper(field_val, captures...)
                            let mut call_args = vec![field_val];
                            for (var_id, _) in &captures {
                                call_args.push(self.var_map[var_id]);
                            }
                            let rec_result = self.builder.call(&fold_name, call_args);
                            self.var_map.insert(*rec_var, rec_result);
                            break;
                        }
                        rec_count += 1;
                    }
                }
            }

            let result = self.lower_expr(&arm.body);
            self.builder.jump(merge, vec![result]);
        }

        // Emit switch from tag block
        self.builder.switch_to(tag_block);
        self.builder.switch_int(tag, switch_arms, None);

        // Merge block returns
        self.builder.switch_to(merge);
        self.builder.ret(merge_param);
        self.builder.finish_function(&fold_name, fold_params);

        // Restore var_map and call the fold helper from the original context
        self.var_map = saved_vars;
        let scr_val = self.lower_expr(scrutinee);
        let mut call_args = vec![scr_val];
        for (_, capture_val) in &captures {
            call_args.push(*capture_val);
        }
        self.builder.call(&fold_name, call_args)
    }

    /// Collect free variables in an expression that are in the outer scope.
    fn collect_captures(
        &self,
        body: &Core,
        pattern_fields: &[VarId],
        rec_binds: &[VarId],
        captures: &mut Vec<(VarId, Value)>,
        seen: &mut HashMap<VarId, usize>,
    ) {
        match body {
            Core::Var(var_id) => {
                if pattern_fields.contains(var_id) || rec_binds.contains(var_id) {
                    return; // Bound by pattern
                }
                if seen.contains_key(var_id) {
                    return;
                }
                if let Some(&val) = self.var_map.get(var_id) {
                    seen.insert(*var_id, captures.len());
                    captures.push((*var_id, val));
                }
            }
            Core::Lit(_) => {}
            Core::App { args, .. } => {
                for a in args {
                    self.collect_captures(a, pattern_fields, rec_binds, captures, seen);
                }
            }
            Core::Let { val, body, .. } => {
                self.collect_captures(val, pattern_fields, rec_binds, captures, seen);
                // name is bound in body, so add to excluded (but we don't track let bindings in this simple version)
                self.collect_captures(body, pattern_fields, rec_binds, captures, seen);
            }
            Core::Match { expr, arms } => {
                self.collect_captures(expr, pattern_fields, rec_binds, captures, seen);
                for (_, arm_body) in arms {
                    self.collect_captures(arm_body, pattern_fields, rec_binds, captures, seen);
                }
            }
            Core::Fold { expr, arms } => {
                self.collect_captures(expr, pattern_fields, rec_binds, captures, seen);
                for arm in arms {
                    self.collect_captures(&arm.body, pattern_fields, rec_binds, captures, seen);
                }
            }
            Core::Record { fields } => {
                for (_, e) in fields {
                    self.collect_captures(e, pattern_fields, rec_binds, captures, seen);
                }
            }
            Core::FieldAccess { record, .. } => {
                self.collect_captures(record, pattern_fields, rec_binds, captures, seen);
            }
            Core::ListLit(elems) => {
                for e in elems {
                    self.collect_captures(e, pattern_fields, rec_binds, captures, seen);
                }
            }
            Core::ListWalk {
                list, init, step, ..
            } => {
                self.collect_captures(list, pattern_fields, rec_binds, captures, seen);
                self.collect_captures(init, pattern_fields, rec_binds, captures, seen);
                self.collect_captures(step, pattern_fields, rec_binds, captures, seen);
            }
        }
    }

    fn lower_list_walk(
        &mut self,
        list: &Core,
        init: &Core,
        step: &Core,
        apply_func: FuncId,
        backwards: bool,
    ) -> Value {
        let list_val = self.lower_expr(list);
        let init_val = self.lower_expr(init);
        let step_val = self.lower_expr(step);

        let apply_name = self
            .func_names
            .get(&apply_func)
            .unwrap_or_else(|| {
                panic!(
                    "unknown apply function: {}",
                    self.program.debug_names.func_name(apply_func)
                )
            })
            .clone();

        // Load list header
        let len_val = self.builder.load(list_val, 0);
        let data_ptr = self.builder.load(list_val, 2);

        // Build loop: i goes from 0 to len, acc accumulates.
        // For backwards, element access is at (len - 1 - i) instead of i.
        let header = self.builder.create_block();
        let i_param = self.builder.add_block_param(header);
        let acc_param = self.builder.add_block_param(header);
        let body_block = self.builder.create_block();
        let done = self.builder.create_block();
        let done_param = self.builder.add_block_param(done);

        let zero = self.builder.const_u64(0);
        self.builder.jump(header, vec![zero, init_val]);

        self.builder.switch_to(header);
        let cmp = self.builder.binop(BinaryOp::Eq, i_param, len_val);
        self.builder
            .branch(cmp, done, vec![acc_param], body_block, vec![]);

        self.builder.switch_to(body_block);
        let elem = if backwards {
            let one = self.builder.const_u64(1);
            let len_minus_1 = self.builder.binop(BinaryOp::Sub, len_val, one);
            let rev_idx = self.builder.binop(BinaryOp::Sub, len_minus_1, i_param);
            self.builder.load_dyn(data_ptr, rev_idx)
        } else {
            self.builder.load_dyn(data_ptr, i_param)
        };
        let new_acc = self
            .builder
            .call(&apply_name, vec![step_val, acc_param, elem]);
        let one = self.builder.const_u64(1);
        let next_i = self.builder.binop(BinaryOp::Add, i_param, one);
        self.builder.jump(header, vec![next_i, new_acc]);

        self.builder.switch_to(done);
        done_param
    }
}

/// Compute the slot index for a record field (alphabetical order).
/// TODO: replace with proper layout from type info.
fn field_slot_index(field: &str) -> usize {
    // For now, we can't compute this without knowing all fields.
    // Return 0 as a placeholder — this only matters for records,
    // which are rare in current programs.
    let _ = field;
    0
}
