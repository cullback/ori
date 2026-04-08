use std::collections::HashMap;

use crate::core::{self, Builtin, Core, FuncId, NumVal, Pattern, Program};
use crate::ssa::instruction::{BinaryOp, BlockId, Value};
use crate::ssa::{Builder, Module};

/// Context for lowering Core IR to SSA.
struct Ctx<'a> {
    program: &'a Program,
    builder: Builder,
    /// Core VarId → SSA Value
    vars: HashMap<core::VarId, Value>,
    /// Core FuncId → SSA function name
    func_names: HashMap<FuncId, String>,
    /// Core FuncId → constructor tag name
    con_names: HashMap<FuncId, String>,
    /// Core FuncId → Builtin
    builtins: HashMap<FuncId, Builtin>,
    /// Counter for generated fold helper functions
    fold_counter: usize,
}

/// Collect free VarIds in a Core expression (not in `bound`).
fn collect_core_free_vars(
    expr: &Core,
    bound: &std::collections::HashSet<core::VarId>,
    free: &mut Vec<core::VarId>,
) {
    match expr {
        Core::Var(id) => {
            if !bound.contains(id) && !free.contains(id) {
                free.push(*id);
            }
        }
        Core::Lit(_) => {}
        Core::App { args, .. } => {
            for a in args {
                collect_core_free_vars(a, bound, free);
            }
        }
        Core::Let { name, val, body } => {
            collect_core_free_vars(val, bound, free);
            let mut inner = bound.clone();
            inner.insert(*name);
            collect_core_free_vars(body, &inner, free);
        }
        Core::Match { expr, arms } => {
            collect_core_free_vars(expr, bound, free);
            for (pat, body) in arms {
                let mut inner = bound.clone();
                let Pattern::Constructor { fields, .. } = pat;
                for f in fields {
                    inner.insert(*f);
                }
                collect_core_free_vars(body, &inner, free);
            }
        }
        Core::Fold { expr, arms } => {
            collect_core_free_vars(expr, bound, free);
            for arm in arms {
                let mut inner = bound.clone();
                let Pattern::Constructor { fields, .. } = &arm.pattern;
                for f in fields {
                    inner.insert(*f);
                }
                for r in &arm.rec_binds {
                    inner.insert(*r);
                }
                collect_core_free_vars(&arm.body, &inner, free);
            }
        }
        Core::Record { fields } => {
            for (_, e) in fields {
                collect_core_free_vars(e, bound, free);
            }
        }
        Core::FieldAccess { record, .. } => collect_core_free_vars(record, bound, free),
        Core::ListLit(elems) => {
            for e in elems {
                collect_core_free_vars(e, bound, free);
            }
        }
        Core::ListWalk {
            list, init, step, ..
        } => {
            collect_core_free_vars(list, bound, free);
            collect_core_free_vars(init, bound, free);
            collect_core_free_vars(step, bound, free);
        }
    }
}

/// Lower a Core Program to an SSA Module.
/// `input_vars` are the free variables in `program.main` (main's parameters).
pub fn lower(program: &Program, input_vars: &[core::VarId]) -> Module {
    let mut ctx = Ctx {
        program,
        builder: Builder::new(),
        vars: HashMap::new(),
        func_names: build_func_names(program),
        con_names: build_con_names(program),
        builtins: program.builtins.clone(),
        fold_counter: 0,
    };

    // Lower each function
    for func_def in &program.funcs {
        let name = ctx
            .func_names
            .get(&func_def.name)
            .cloned()
            .unwrap_or_else(|| format!("func_{:?}", func_def.name));
        let entry = ctx.builder.create_block();
        ctx.builder.switch_to(entry);

        let params: Vec<Value> = func_def
            .params
            .iter()
            .map(|vid| {
                let v = ctx.builder.add_block_param(entry);
                ctx.vars.insert(*vid, v);
                v
            })
            .collect();

        let result = ctx.lower_expr(&func_def.body);
        ctx.builder.ret(result);
        ctx.builder.finish_function(&name, params);
    }

    // Lower main — input_vars become __main's params
    let entry = ctx.builder.create_block();
    ctx.builder.switch_to(entry);
    let params: Vec<Value> = input_vars
        .iter()
        .map(|vid| {
            let v = ctx.builder.add_block_param(entry);
            ctx.vars.insert(*vid, v);
            v
        })
        .collect();
    let result = ctx.lower_expr(&program.main);
    ctx.builder.ret(result);
    ctx.builder.finish_function("__main", params);

    ctx.builder.build("__main")
}

fn build_func_names(program: &Program) -> HashMap<FuncId, String> {
    let mut names = HashMap::new();
    for func_def in &program.funcs {
        let name = program.debug_names.func_name(func_def.name).to_owned();
        names.insert(func_def.name, name);
    }
    names
}

fn build_con_names(program: &Program) -> HashMap<FuncId, String> {
    let mut names = HashMap::new();
    for type_def in &program.types {
        for con in &type_def.constructors {
            let name = program.debug_names.func_name(con.tag).to_owned();
            names.insert(con.tag, name);
        }
    }
    names
}

impl Ctx<'_> {
    fn lower_expr(&mut self, expr: &Core) -> Value {
        match expr {
            Core::Var(id) => self.vars[id],

            Core::Lit(core::Literal::Num(n)) => match n {
                NumVal::I64(n) => self.builder.const_i64(*n),
                NumVal::U64(n) => self.builder.const_u64(*n),
                NumVal::F64(n) => self.builder.const_f64(*n),
                NumVal::U8(n) => self.builder.const_u8(*n),
                NumVal::I8(n) => self.builder.const_i8(*n),
            },

            Core::App { func, args } => {
                let arg_vals: Vec<Value> = args.iter().map(|a| self.lower_expr(a)).collect();

                // Constructor call
                if let Some(name) = self.con_names.get(func) {
                    return self.builder.construct(name, arg_vals);
                }

                // Builtin
                if let Some(builtin) = self.builtins.get(func).copied() {
                    return self.lower_builtin(builtin, &arg_vals);
                }

                // Regular function call
                let name = self
                    .func_names
                    .get(func)
                    .cloned()
                    .unwrap_or_else(|| format!("func_{func:?}"));
                self.builder.call(&name, arg_vals)
            }

            Core::Let { name, val, body } => {
                let v = self.lower_expr(val);
                self.vars.insert(*name, v);
                self.lower_expr(body)
            }

            Core::Match { expr, arms } => {
                let scrutinee = self.lower_expr(expr);
                self.lower_match(scrutinee, arms)
            }

            Core::Fold { expr, arms } => {
                let scrutinee = self.lower_expr(expr);
                self.lower_fold(scrutinee, arms)
            }

            Core::Record { fields } => {
                let field_vals: Vec<(String, Value)> = fields
                    .iter()
                    .map(|(name, e)| (name.clone(), self.lower_expr(e)))
                    .collect();
                self.builder.record_new(field_vals)
            }

            Core::FieldAccess { record, field } => {
                let rec = self.lower_expr(record);
                self.builder.field_get(rec, field)
            }

            Core::ListLit(elems) => {
                let vals: Vec<Value> = elems.iter().map(|e| self.lower_expr(e)).collect();
                self.builder.list_new(vals)
            }

            Core::ListWalk {
                list,
                init,
                step,
                apply_func,
                backwards,
            } => {
                let list_val = self.lower_expr(list);
                let init_val = self.lower_expr(init);
                let step_val = self.lower_expr(step);
                let apply_name = self
                    .func_names
                    .get(apply_func)
                    .cloned()
                    .unwrap_or_else(|| format!("func_{apply_func:?}"));
                self.lower_list_walk(list_val, init_val, step_val, &apply_name, *backwards)
            }
        }
    }

    fn lower_builtin(&mut self, builtin: Builtin, args: &[Value]) -> Value {
        match builtin {
            Builtin::Add => self.builder.binop(BinaryOp::Add, args[0], args[1]),
            Builtin::Sub => self.builder.binop(BinaryOp::Sub, args[0], args[1]),
            Builtin::Mul => self.builder.binop(BinaryOp::Mul, args[0], args[1]),
            Builtin::Div => self.builder.binop(BinaryOp::Div, args[0], args[1]),
            Builtin::Rem => self.builder.binop(BinaryOp::Rem, args[0], args[1]),
            Builtin::Max => self.builder.binop(BinaryOp::Max, args[0], args[1]),
            Builtin::Eq {
                true_con,
                false_con,
            } => {
                let cmp = self.builder.binop(BinaryOp::Eq, args[0], args[1]);
                let true_name = self.con_names[&true_con].clone();
                let false_name = self.con_names[&false_con].clone();

                let then_block = self.builder.create_block();
                let else_block = self.builder.create_block();
                let merge = self.builder.create_block();
                let merge_param = self.builder.add_block_param(merge);

                self.builder
                    .branch(cmp, then_block, vec![], else_block, vec![]);

                self.builder.switch_to(then_block);
                let t = self.builder.construct(&true_name, vec![]);
                self.builder.jump(merge, vec![t]);

                self.builder.switch_to(else_block);
                let f = self.builder.construct(&false_name, vec![]);
                self.builder.jump(merge, vec![f]);

                self.builder.switch_to(merge);
                merge_param
            }
            Builtin::NumToStr => self.builder.num_to_str(args[0]),
            Builtin::ListLen => self.builder.list_len(args[0]),
            Builtin::ListGet => self.builder.list_get(args[0], args[1]),
            Builtin::ListSet => self.builder.list_set(args[0], args[1], args[2]),
            Builtin::ListAppend => self.builder.list_append(args[0], args[1]),
        }
    }

    fn lower_match(&mut self, scrutinee: Value, arms: &[(Pattern, Core)]) -> Value {
        let merge = self.builder.create_block();
        let merge_result = self.builder.add_block_param(merge);

        let arm_blocks: Vec<(String, BlockId)> = arms
            .iter()
            .map(|(pat, _)| {
                let Pattern::Constructor { tag, fields } = pat;
                let tag_name = self.con_names[tag].clone();
                let block = self.builder.create_block();
                // Add block params for each constructor field
                for field_var in fields {
                    let param = self.builder.add_block_param(block);
                    self.vars.insert(*field_var, param);
                }
                (tag_name, block)
            })
            .collect();

        self.builder.switch(scrutinee, arm_blocks.clone());

        // Lower each arm body
        for (i, (_, body)) in arms.iter().enumerate() {
            self.builder.switch_to(arm_blocks[i].1);
            let result = self.lower_expr(body);
            self.builder.jump(merge, vec![result]);
        }

        self.builder.switch_to(merge);
        merge_result
    }

    fn lower_fold(&mut self, scrutinee: Value, arms: &[core::FoldArm]) -> Value {
        let fold_name = format!("__fold_{}", self.fold_counter);
        self.fold_counter += 1;

        // Collect free variables (VarIds referenced in arm bodies but not
        // bound by patterns or rec_binds). These become extra params.
        let mut bound: std::collections::HashSet<core::VarId> = std::collections::HashSet::new();
        let mut free_vars: Vec<core::VarId> = Vec::new();
        for arm in arms {
            let Pattern::Constructor { fields, .. } = &arm.pattern;
            for f in fields {
                bound.insert(*f);
            }
            for r in &arm.rec_binds {
                bound.insert(*r);
            }
        }
        for arm in arms {
            collect_core_free_vars(&arm.body, &bound, &mut free_vars);
        }
        free_vars.dedup();

        // Map captures to their current SSA values
        let capture_vals: Vec<Value> = free_vars
            .iter()
            .filter_map(|vid| self.vars.get(vid).copied())
            .collect();
        let captured_vids: Vec<core::VarId> = free_vars
            .iter()
            .filter(|vid| self.vars.contains_key(vid))
            .copied()
            .collect();

        // Save builder state
        let saved_blocks = std::mem::take(&mut self.builder.blocks);
        let saved_current = self.builder.current_block.take();
        let saved_vars = self.vars.clone();

        // Build the fold helper function: (scrutinee, ...captures)
        let entry = self.builder.create_block();
        self.builder.switch_to(entry);
        let scrutinee_param = self.builder.add_block_param(entry);

        let mut all_params = vec![scrutinee_param];
        for vid in &captured_vids {
            let param = self.builder.add_block_param(entry);
            self.vars.insert(*vid, param);
            all_params.push(param);
        }

        let merge = self.builder.create_block();
        let merge_result = self.builder.add_block_param(merge);

        let arm_blocks: Vec<(String, BlockId)> = arms
            .iter()
            .map(|arm| {
                let Pattern::Constructor { tag, fields } = &arm.pattern;
                let tag_name = self.con_names[tag].clone();
                let block = self.builder.create_block();
                for field_var in fields {
                    let param = self.builder.add_block_param(block);
                    self.vars.insert(*field_var, param);
                }
                (tag_name, block)
            })
            .collect();

        self.builder.switch(scrutinee_param, arm_blocks.clone());

        // Lower each arm
        for (i, arm) in arms.iter().enumerate() {
            self.builder.switch_to(arm_blocks[i].1);

            let Pattern::Constructor { tag, fields } = &arm.pattern;
            let con_def = self
                .program
                .types
                .iter()
                .flat_map(|t| &t.constructors)
                .find(|c| c.tag == *tag)
                .unwrap();

            // Recursive calls pass captures through
            let capture_params: Vec<Value> =
                captured_vids.iter().map(|vid| self.vars[vid]).collect();
            let mut rec_idx = 0;
            for (j, field_def) in con_def.fields.iter().enumerate() {
                if field_def.recursive {
                    let field_val = self.vars[&fields[j]];
                    let mut call_args = vec![field_val];
                    call_args.extend_from_slice(&capture_params);
                    let rec_result = self.builder.call(&fold_name, call_args);
                    self.vars.insert(arm.rec_binds[rec_idx], rec_result);
                    rec_idx += 1;
                }
            }

            let result = self.lower_expr(&arm.body);
            self.builder.jump(merge, vec![result]);
        }

        self.builder.switch_to(merge);
        self.builder.ret(merge_result);
        self.builder.finish_function(&fold_name, all_params);

        // Restore state
        self.builder.blocks = saved_blocks;
        self.builder.current_block = saved_current;
        self.vars = saved_vars;

        // Emit the call with captures
        let mut call_args = vec![scrutinee];
        call_args.extend_from_slice(&capture_vals);
        self.builder.call(&fold_name, call_args)
    }

    fn lower_list_walk(
        &mut self,
        list: Value,
        init: Value,
        step: Value,
        apply_name: &str,
        backwards: bool,
    ) -> Value {
        let len = self.builder.list_len(list);

        let header = self.builder.create_block();
        let body = self.builder.create_block();
        let exit = self.builder.create_block();

        let idx_param = self.builder.add_block_param(header);
        let acc_param = self.builder.add_block_param(header);
        let exit_result = self.builder.add_block_param(exit);

        if backwards {
            // Start from len, count remaining down to 0
            self.builder.jump(header, vec![len, init]);

            self.builder.switch_to(header);
            let zero = self.builder.const_u64(0);
            let done = self.builder.binop(BinaryOp::Eq, idx_param, zero);
            self.builder.branch(
                done,
                exit,
                vec![acc_param],
                body,
                vec![idx_param, acc_param],
            );

            self.builder.switch_to(body);
            let body_idx = self.builder.add_block_param(body);
            let body_acc = self.builder.add_block_param(body);
            let one = self.builder.const_u64(1);
            let actual_idx = self.builder.binop(BinaryOp::Sub, body_idx, one);
            let elem = self.builder.list_get(list, actual_idx);
            let new_acc = self.builder.call(apply_name, vec![step, body_acc, elem]);
            self.builder.jump(header, vec![actual_idx, new_acc]);
        } else {
            let zero = self.builder.const_u64(0);
            self.builder.jump(header, vec![zero, init]);

            self.builder.switch_to(header);
            let done = self.builder.binop(BinaryOp::Eq, idx_param, len);
            self.builder.branch(
                done,
                exit,
                vec![acc_param],
                body,
                vec![idx_param, acc_param],
            );

            self.builder.switch_to(body);
            let body_idx = self.builder.add_block_param(body);
            let body_acc = self.builder.add_block_param(body);
            let elem = self.builder.list_get(list, body_idx);
            let new_acc = self.builder.call(apply_name, vec![step, body_acc, elem]);
            let one = self.builder.const_u64(1);
            let next_idx = self.builder.binop(BinaryOp::Add, body_idx, one);
            self.builder.jump(header, vec![next_idx, new_acc]);
        }

        self.builder.switch_to(exit);
        exit_result
    }
}
