use std::collections::HashMap;

use crate::ssa::Module;
use crate::ssa::instruction::{BinaryOp, BlockId, Inst, Terminator, Value};

/// Runtime values for the SSA interpreter.
#[derive(Debug, Clone, PartialEq)]
pub enum RtValue {
    I64(i64),
    U64(u64),
    F64(f64),
    U8(u8),
    I8(i8),
    Bool(bool),
    Construct { tag: String, fields: Vec<RtValue> },
    Record { fields: Vec<(String, RtValue)> },
    List(Vec<RtValue>),
}

type Env = HashMap<Value, RtValue>;

/// Evaluate the entry function of an SSA module.
pub fn eval(module: &Module, args: &[RtValue]) -> RtValue {
    eval_with_name(module, &module.entry, args)
}

/// Evaluate a named function in the SSA module.
pub fn eval_with_name(module: &Module, name: &str, args: &[RtValue]) -> RtValue {
    eval_function(module, name, args)
}

fn eval_function(module: &Module, func_name: &str, args: &[RtValue]) -> RtValue {
    let func = &module.functions[func_name];
    let mut env = Env::new();

    // Bind function params
    for (param, arg) in func.params.iter().zip(args) {
        env.insert(*param, arg.clone());
    }

    let mut current = BlockId(0);
    let mut block_args: Vec<RtValue> = vec![];

    loop {
        let block = &func.blocks[current.0];

        // Bind block parameters
        for (param, arg) in block.params.iter().zip(&block_args) {
            env.insert(*param, arg.clone());
        }

        // Execute instructions
        for inst in &block.insts {
            let val = eval_inst(module, &env, inst);
            env.insert(inst.dest(), val);
        }

        // Execute terminator
        match &block.terminator {
            Terminator::Return(v) => return env[v].clone(),

            Terminator::Jump(target, args) => {
                block_args = args.iter().map(|v| env[v].clone()).collect();
                current = *target;
            }

            Terminator::Branch {
                cond,
                then_block,
                then_args,
                else_block,
                else_args,
            } => {
                let is_true = match &env[cond] {
                    RtValue::Bool(b) => *b,
                    other => panic!("branch on non-boolean: {other:?}"),
                };
                if is_true {
                    block_args = then_args.iter().map(|v| env[v].clone()).collect();
                    current = *then_block;
                } else {
                    block_args = else_args.iter().map(|v| env[v].clone()).collect();
                    current = *else_block;
                }
            }

            Terminator::Switch { scrutinee, arms } => {
                let val = &env[scrutinee];
                let RtValue::Construct { tag, fields } = val else {
                    panic!("switch on non-construct: {val:?}");
                };
                let (_, target) = arms
                    .iter()
                    .find(|(t, _)| t == tag)
                    .unwrap_or_else(|| panic!("no matching arm for tag '{tag}'"));
                block_args = fields.clone();
                current = *target;
            }

            Terminator::None => panic!("reached incomplete block"),
        }
    }
}

fn eval_inst(module: &Module, env: &Env, inst: &Inst) -> RtValue {
    match inst {
        Inst::Const(_, n) => RtValue::I64(*n),
        Inst::ConstU64(_, n) => RtValue::U64(*n),
        Inst::ConstF64(_, n) => RtValue::F64(*n),
        Inst::ConstU8(_, n) => RtValue::U8(*n),
        Inst::ConstI8(_, n) => RtValue::I8(*n),

        Inst::BinOp(_, op, lhs, rhs) => eval_binop(*op, &env[lhs], &env[rhs]),

        Inst::Call(_, func_name, args) => {
            let arg_vals: Vec<RtValue> = args
                .iter()
                .map(|v| {
                    env.get(v)
                        .cloned()
                        .unwrap_or_else(|| panic!("missing value {v} in call to {func_name}"))
                })
                .collect();
            eval_function(module, func_name, &arg_vals)
        }

        Inst::Construct(_, tag, fields) => RtValue::Construct {
            tag: tag.clone(),
            fields: fields.iter().map(|v| env[v].clone()).collect(),
        },

        Inst::RecordNew(_, fields) => RtValue::Record {
            fields: fields
                .iter()
                .map(|(name, v)| (name.clone(), env[v].clone()))
                .collect(),
        },

        Inst::FieldGet(_, record, field) => {
            let RtValue::Record { fields } = &env[record] else {
                panic!("field access on non-record");
            };
            fields
                .iter()
                .find(|(n, _)| n == field)
                .unwrap_or_else(|| panic!("no field '{field}'"))
                .1
                .clone()
        }

        Inst::ListNew(_, elems) => RtValue::List(elems.iter().map(|v| env[v].clone()).collect()),

        Inst::ListGet(_, list, index) => {
            let RtValue::List(elems) = &env[list] else {
                panic!("list_get on non-list");
            };
            let i = as_usize(&env[index]);
            elems[i].clone()
        }

        Inst::ListSet(_, list, index, elem) => {
            let RtValue::List(elems) = &env[list] else {
                panic!("list_set on non-list");
            };
            let i = as_usize(&env[index]);
            let mut new_list = elems.clone();
            new_list[i] = env[elem].clone();
            RtValue::List(new_list)
        }

        Inst::ListAppend(_, list, elem) => {
            let RtValue::List(elems) = &env[list] else {
                panic!("list_append on non-list");
            };
            let mut new_list = elems.clone();
            new_list.push(env[elem].clone());
            RtValue::List(new_list)
        }

        Inst::ListLen(_, list) => {
            let RtValue::List(elems) = &env[list] else {
                panic!("list_len on non-list");
            };
            RtValue::U64(elems.len() as u64)
        }

        Inst::NumToStr(_, num) => {
            let s = match &env[num] {
                RtValue::I64(n) => n.to_string(),
                RtValue::U64(n) => n.to_string(),
                RtValue::F64(n) => n.to_string(),
                RtValue::U8(n) => n.to_string(),
                RtValue::I8(n) => n.to_string(),
                other => panic!("num_to_str on {other:?}"),
            };
            RtValue::List(s.into_bytes().into_iter().map(RtValue::U8).collect())
        }
    }
}

fn eval_binop(op: BinaryOp, lhs: &RtValue, rhs: &RtValue) -> RtValue {
    match (op, lhs, rhs) {
        // I64
        (BinaryOp::Add, RtValue::I64(a), RtValue::I64(b)) => RtValue::I64(a + b),
        (BinaryOp::Sub, RtValue::I64(a), RtValue::I64(b)) => RtValue::I64(a - b),
        (BinaryOp::Mul, RtValue::I64(a), RtValue::I64(b)) => RtValue::I64(a * b),
        (BinaryOp::Div, RtValue::I64(a), RtValue::I64(b)) => RtValue::I64(a / b),
        (BinaryOp::Rem, RtValue::I64(a), RtValue::I64(b)) => RtValue::I64(a % b),
        (BinaryOp::Max, RtValue::I64(a), RtValue::I64(b)) => RtValue::I64(*a.max(b)),
        (BinaryOp::Eq, RtValue::I64(a), RtValue::I64(b)) => RtValue::Bool(a == b),
        (BinaryOp::Neq, RtValue::I64(a), RtValue::I64(b)) => RtValue::Bool(a != b),
        // U64
        (BinaryOp::Add, RtValue::U64(a), RtValue::U64(b)) => RtValue::U64(a + b),
        (BinaryOp::Sub, RtValue::U64(a), RtValue::U64(b)) => RtValue::U64(a - b),
        (BinaryOp::Mul, RtValue::U64(a), RtValue::U64(b)) => RtValue::U64(a * b),
        (BinaryOp::Div, RtValue::U64(a), RtValue::U64(b)) => RtValue::U64(a / b),
        (BinaryOp::Rem, RtValue::U64(a), RtValue::U64(b)) => RtValue::U64(a % b),
        (BinaryOp::Max, RtValue::U64(a), RtValue::U64(b)) => RtValue::U64(*a.max(b)),
        (BinaryOp::Eq, RtValue::U64(a), RtValue::U64(b)) => RtValue::Bool(a == b),
        (BinaryOp::Neq, RtValue::U64(a), RtValue::U64(b)) => RtValue::Bool(a != b),
        // U8
        (BinaryOp::Add, RtValue::U8(a), RtValue::U8(b)) => RtValue::U8(a + b),
        (BinaryOp::Sub, RtValue::U8(a), RtValue::U8(b)) => RtValue::U8(a - b),
        (BinaryOp::Mul, RtValue::U8(a), RtValue::U8(b)) => RtValue::U8(a * b),
        (BinaryOp::Div, RtValue::U8(a), RtValue::U8(b)) => RtValue::U8(a / b),
        (BinaryOp::Rem, RtValue::U8(a), RtValue::U8(b)) => RtValue::U8(a % b),
        (BinaryOp::Eq, RtValue::U8(a), RtValue::U8(b)) => RtValue::Bool(a == b),
        (BinaryOp::Neq, RtValue::U8(a), RtValue::U8(b)) => RtValue::Bool(a != b),
        // I8
        (BinaryOp::Add, RtValue::I8(a), RtValue::I8(b)) => RtValue::I8(a + b),
        (BinaryOp::Sub, RtValue::I8(a), RtValue::I8(b)) => RtValue::I8(a - b),
        (BinaryOp::Mul, RtValue::I8(a), RtValue::I8(b)) => RtValue::I8(a * b),
        (BinaryOp::Div, RtValue::I8(a), RtValue::I8(b)) => RtValue::I8(a / b),
        (BinaryOp::Rem, RtValue::I8(a), RtValue::I8(b)) => RtValue::I8(a % b),
        (BinaryOp::Eq, RtValue::I8(a), RtValue::I8(b)) => RtValue::Bool(a == b),
        (BinaryOp::Neq, RtValue::I8(a), RtValue::I8(b)) => RtValue::Bool(a != b),
        // F64
        (BinaryOp::Add, RtValue::F64(a), RtValue::F64(b)) => RtValue::F64(a + b),
        (BinaryOp::Sub, RtValue::F64(a), RtValue::F64(b)) => RtValue::F64(a - b),
        (BinaryOp::Mul, RtValue::F64(a), RtValue::F64(b)) => RtValue::F64(a * b),
        (BinaryOp::Div, RtValue::F64(a), RtValue::F64(b)) => RtValue::F64(a / b),
        (BinaryOp::Eq, RtValue::F64(a), RtValue::F64(b)) => RtValue::Bool(a == b),
        (BinaryOp::Neq, RtValue::F64(a), RtValue::F64(b)) => RtValue::Bool(a != b),
        _ => panic!("unsupported binop {op:?} on {lhs:?}, {rhs:?}"),
    }
}

fn as_usize(val: &RtValue) -> usize {
    match val {
        RtValue::U64(n) => *n as usize,
        RtValue::I64(n) => *n as usize,
        other => panic!("expected index, got {other:?}"),
    }
}
