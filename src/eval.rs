use std::collections::HashMap;

use crate::ir::{Builtin, Core, FoldArm, FuncId, Literal, NumVal, Pattern, Program, Value, VarId};

type Env = HashMap<VarId, Value>;

#[expect(
    clippy::arithmetic_side_effects,
    clippy::integer_division_remainder_used,
    clippy::integer_division,
    clippy::modulo_arithmetic,
    clippy::float_arithmetic,
    clippy::float_cmp,
    reason = "builtins implement language-level arithmetic"
)]
#[expect(clippy::too_many_lines, reason = "dispatch over all numeric types")]
fn eval_builtin(func: FuncId, args: &[Value], program: &Program) -> Option<Value> {
    let builtin = program.builtins.get(&func)?;
    let u8_pair = || match args {
        [Value::VNum(NumVal::U8(a)), Value::VNum(NumVal::U8(b))] => Some((*a, *b)),
        _ => None,
    };
    let i8_pair = || match args {
        [Value::VNum(NumVal::I8(a)), Value::VNum(NumVal::I8(b))] => Some((*a, *b)),
        _ => None,
    };
    let u64_pair = || match args {
        [Value::VNum(NumVal::U64(a)), Value::VNum(NumVal::U64(b))] => Some((*a, *b)),
        _ => None,
    };
    let i64_pair = || match args {
        [Value::VNum(NumVal::I64(a)), Value::VNum(NumVal::I64(b))] => Some((*a, *b)),
        _ => None,
    };
    let f64_pair = || match args {
        [Value::VNum(NumVal::F64(a)), Value::VNum(NumVal::F64(b))] => Some((*a, *b)),
        _ => None,
    };
    match *builtin {
        Builtin::Add => u8_pair()
            .map(|(a, b)| Value::VNum(NumVal::U8(a + b)))
            .or_else(|| i8_pair().map(|(a, b)| Value::VNum(NumVal::I8(a + b))))
            .or_else(|| u64_pair().map(|(a, b)| Value::VNum(NumVal::U64(a + b))))
            .or_else(|| i64_pair().map(|(a, b)| Value::VNum(NumVal::I64(a + b))))
            .or_else(|| f64_pair().map(|(a, b)| Value::VNum(NumVal::F64(a + b)))),
        Builtin::Sub => u8_pair()
            .map(|(a, b)| Value::VNum(NumVal::U8(a - b)))
            .or_else(|| i8_pair().map(|(a, b)| Value::VNum(NumVal::I8(a - b))))
            .or_else(|| u64_pair().map(|(a, b)| Value::VNum(NumVal::U64(a - b))))
            .or_else(|| i64_pair().map(|(a, b)| Value::VNum(NumVal::I64(a - b))))
            .or_else(|| f64_pair().map(|(a, b)| Value::VNum(NumVal::F64(a - b)))),
        Builtin::Mul => u8_pair()
            .map(|(a, b)| Value::VNum(NumVal::U8(a * b)))
            .or_else(|| i8_pair().map(|(a, b)| Value::VNum(NumVal::I8(a * b))))
            .or_else(|| u64_pair().map(|(a, b)| Value::VNum(NumVal::U64(a * b))))
            .or_else(|| i64_pair().map(|(a, b)| Value::VNum(NumVal::I64(a * b))))
            .or_else(|| f64_pair().map(|(a, b)| Value::VNum(NumVal::F64(a * b)))),
        Builtin::Div => u8_pair()
            .map(|(a, b)| Value::VNum(NumVal::U8(a / b)))
            .or_else(|| i8_pair().map(|(a, b)| Value::VNum(NumVal::I8(a / b))))
            .or_else(|| u64_pair().map(|(a, b)| Value::VNum(NumVal::U64(a / b))))
            .or_else(|| i64_pair().map(|(a, b)| Value::VNum(NumVal::I64(a / b))))
            .or_else(|| f64_pair().map(|(a, b)| Value::VNum(NumVal::F64(a / b)))),
        Builtin::Rem => u8_pair()
            .map(|(a, b)| Value::VNum(NumVal::U8(a % b)))
            .or_else(|| i8_pair().map(|(a, b)| Value::VNum(NumVal::I8(a % b))))
            .or_else(|| u64_pair().map(|(a, b)| Value::VNum(NumVal::U64(a % b))))
            .or_else(|| i64_pair().map(|(a, b)| Value::VNum(NumVal::I64(a % b)))),
        Builtin::Max => u8_pair()
            .map(|(a, b)| Value::VNum(NumVal::U8(a.max(b))))
            .or_else(|| i8_pair().map(|(a, b)| Value::VNum(NumVal::I8(a.max(b)))))
            .or_else(|| u64_pair().map(|(a, b)| Value::VNum(NumVal::U64(a.max(b)))))
            .or_else(|| i64_pair().map(|(a, b)| Value::VNum(NumVal::I64(a.max(b))))),
        Builtin::Eq {
            true_con,
            false_con,
        } => {
            let equal = u8_pair()
                .map(|(a, b)| a == b)
                .or_else(|| i8_pair().map(|(a, b)| a == b))
                .or_else(|| u64_pair().map(|(a, b)| a == b))
                .or_else(|| i64_pair().map(|(a, b)| a == b))
                .or_else(|| f64_pair().map(|(a, b)| a == b))?;
            let tag = if equal { true_con } else { false_con };
            Some(Value::VConstruct {
                tag,
                fields: vec![],
            })
        }
        Builtin::ListLen => {
            let [Value::VList(elems)] = args else {
                panic!("List.len: expected list")
            };
            #[expect(clippy::cast_possible_wrap)]
            Some(Value::VNum(NumVal::I64(elems.len() as i64)))
        }
        Builtin::ListGet => {
            let [Value::VList(elems), Value::VNum(NumVal::I64(idx))] = args else {
                panic!("List.get: expected list and index")
            };
            #[expect(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
            let i = *idx as usize;
            Some(elems[i].clone())
        }
        Builtin::ListAppend => {
            let [Value::VList(elems), val] = args else {
                panic!("List.append: expected list and value")
            };
            let mut new_list = elems.clone();
            new_list.push(val.clone());
            Some(Value::VList(new_list))
        }
        Builtin::ListReverse => {
            let [Value::VList(elems)] = args else {
                panic!("List.reverse: expected list")
            };
            let mut reversed = elems.clone();
            reversed.reverse();
            Some(Value::VList(reversed))
        }
    }
}

fn is_constructor(program: &Program, func: FuncId) -> bool {
    program
        .types
        .iter()
        .flat_map(|t| &t.constructors)
        .any(|c| c.tag == func)
}

/// Call a function by `FuncId` with evaluated argument values.
fn call_func(env: &Env, program: &Program, func: FuncId, args: &[Value]) -> Value {
    if let Some(result) = eval_builtin(func, args, program) {
        return result;
    }
    let func_def = program
        .funcs
        .iter()
        .find(|f| f.name == func)
        .unwrap_or_else(|| {
            panic!(
                "undefined function: {}",
                program.debug_names.func_name(func)
            );
        });
    let mut local_env = env.clone();
    for (param, val) in func_def.params.iter().zip(args) {
        local_env.insert(*param, val.clone());
    }
    eval(&local_env, program, &func_def.body)
}

pub fn eval(env: &Env, program: &Program, core: &Core) -> Value {
    match core {
        Core::Var(name) => env
            .get(name)
            .unwrap_or_else(|| {
                panic!("unbound variable: {}", program.debug_names.var_name(*name));
            })
            .clone(),

        Core::Lit(Literal::Num(n)) => Value::VNum(n.clone()),

        Core::App { func, args } => {
            let arg_vals: Vec<Value> = args.iter().map(|a| eval(env, program, a)).collect();

            if let Some(result) = eval_builtin(*func, &arg_vals, program) {
                return result;
            }

            if is_constructor(program, *func) {
                return Value::VConstruct {
                    tag: *func,
                    fields: arg_vals,
                };
            }

            call_func(env, program, *func, &arg_vals)
        }

        Core::Let { name, val, body } => {
            let v = eval(env, program, val);
            let mut local_env = env.clone();
            local_env.insert(*name, v);
            eval(&local_env, program, body)
        }

        Core::Match { expr, arms } => {
            let val = eval(env, program, expr);
            for (pattern, body) in arms {
                if let Some(bindings) = match_pattern(&val, pattern) {
                    let mut local_env = env.clone();
                    local_env.extend(bindings);
                    return eval(&local_env, program, body);
                }
            }
            panic!("no matching arm for: {val:?}");
        }

        Core::Fold { expr, arms } => {
            let val = eval(env, program, expr);
            fold_value(env, program, &val, arms)
        }

        Core::Record { fields } => {
            let field_vals: Vec<(String, Value)> = fields
                .iter()
                .map(|(name, expr)| (name.clone(), eval(env, program, expr)))
                .collect();
            Value::VRecord { fields: field_vals }
        }

        Core::FieldAccess { record, field } => {
            let val = eval(env, program, record);
            match val {
                Value::VRecord { fields } => {
                    fields
                        .into_iter()
                        .find(|(name, _)| name == field)
                        .unwrap_or_else(|| panic!("no field '{field}' in record"))
                        .1
                }
                _ => panic!("field access on non-record value"),
            }
        }

        Core::ListLit(elements) => {
            let vals: Vec<Value> = elements.iter().map(|e| eval(env, program, e)).collect();
            Value::VList(vals)
        }

        Core::ListWalk {
            list,
            init,
            step,
            apply_func,
        } => {
            let list_val = eval(env, program, list);
            let mut acc = eval(env, program, init);
            let step_closure = eval(env, program, step);
            let Value::VList(elements) = list_val else {
                panic!("List.walk: expected list");
            };
            for elem in elements {
                acc = call_func(
                    env,
                    program,
                    *apply_func,
                    &[step_closure.clone(), acc, elem],
                );
            }
            acc
        }
    }
}

fn match_pattern(val: &Value, pattern: &Pattern) -> Option<HashMap<VarId, Value>> {
    let Pattern::Constructor { tag, fields } = pattern;
    match val {
        Value::VConstruct {
            tag: vtag,
            fields: vfields,
        } if vtag == tag => Some(
            fields
                .iter()
                .copied()
                .zip(vfields.iter().cloned())
                .collect(),
        ),
        Value::VConstruct { .. } | Value::VNum(_) | Value::VRecord { .. } | Value::VList(_) => None,
    }
}

fn fold_value(env: &Env, program: &Program, val: &Value, arms: &[FoldArm]) -> Value {
    match val {
        Value::VNum(_) | Value::VRecord { .. } | Value::VList(_) => val.clone(),

        Value::VConstruct { tag, fields } => {
            let arm = arms
                .iter()
                .find(|a| {
                    let Pattern::Constructor { tag: t, .. } = &a.pattern;
                    t == tag
                })
                .unwrap_or_else(|| {
                    panic!(
                        "no fold arm for tag: {}",
                        program.debug_names.func_name(*tag)
                    );
                });

            let Pattern::Constructor {
                fields: field_names,
                ..
            } = &arm.pattern;

            let constructor_def = program
                .types
                .iter()
                .flat_map(|t| &t.constructors)
                .find(|c| c.tag == *tag)
                .unwrap_or_else(|| {
                    panic!(
                        "unknown constructor: {}",
                        program.debug_names.func_name(*tag)
                    );
                });

            // Recursively fold each recursive field
            let rec_results: Vec<Value> = constructor_def
                .fields
                .iter()
                .zip(fields.iter())
                .filter(|(def, _)| def.recursive)
                .map(|(_, field_val)| fold_value(env, program, field_val, arms))
                .collect();

            // Bind constructor fields and recursive results into the arm body's env
            let mut local_env = env.clone();
            for (bind_name, field_val) in field_names.iter().zip(fields.iter()) {
                local_env.insert(*bind_name, field_val.clone());
            }
            for (bind_name, rec_val) in arm.rec_binds.iter().zip(rec_results) {
                local_env.insert(*bind_name, rec_val);
            }

            eval(&local_env, program, &arm.body)
        }
    }
}
