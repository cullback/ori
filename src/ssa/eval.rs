use std::collections::HashMap;

use crate::ssa::Module;
use crate::ssa::instruction::{BinaryOp, BlockId, Inst, ScalarType, Terminator, Value};

/// A scalar runtime value that fits in a register.
#[derive(Debug, Clone, Copy)]
pub enum Scalar {
    I64(i64),
    U64(u64),
    F64(f64),
    U8(u8),
    I8(i8),
    Bool(bool),
    Ptr(usize), // index into heap
}

/// Simulated heap for the interpreter.
/// Each allocation is a Vec<u8> at a heap index.
pub struct Heap {
    /// Each entry: (refcount, bytes).
    objects: Vec<(usize, Vec<u8>)>,
}

impl Heap {
    fn new() -> Self {
        // Index 0 is null
        Self {
            objects: vec![(0, vec![])],
        }
    }

    fn alloc(&mut self, size: usize) -> usize {
        let idx = self.objects.len();
        self.objects.push((1, vec![0u8; size]));
        idx
    }

    fn load(&self, idx: usize, offset: usize, ty: ScalarType) -> Scalar {
        let bytes = &self.objects[idx].1;
        match ty {
            ScalarType::I8 => Scalar::I8(bytes[offset] as i8),
            ScalarType::U8 => Scalar::U8(bytes[offset]),
            ScalarType::I64 => {
                let b: [u8; 8] = bytes[offset..offset + 8].try_into().unwrap();
                Scalar::I64(i64::from_le_bytes(b))
            }
            ScalarType::U64 => {
                let b: [u8; 8] = bytes[offset..offset + 8].try_into().unwrap();
                Scalar::U64(u64::from_le_bytes(b))
            }
            ScalarType::F64 => {
                let b: [u8; 8] = bytes[offset..offset + 8].try_into().unwrap();
                Scalar::F64(f64::from_le_bytes(b))
            }
            ScalarType::Bool => Scalar::Bool(bytes[offset] != 0),
            ScalarType::Ptr => {
                let b: [u8; 8] = bytes[offset..offset + 8].try_into().unwrap();
                Scalar::Ptr(usize::from_le_bytes(b))
            }
        }
    }

    fn store(&mut self, idx: usize, offset: usize, val: Scalar) {
        let bytes = &mut self.objects[idx].1;
        match val {
            Scalar::I8(n) => bytes[offset] = n as u8,
            Scalar::U8(n) => bytes[offset] = n,
            Scalar::I64(n) => bytes[offset..offset + 8].copy_from_slice(&n.to_le_bytes()),
            Scalar::U64(n) => bytes[offset..offset + 8].copy_from_slice(&n.to_le_bytes()),
            Scalar::F64(n) => bytes[offset..offset + 8].copy_from_slice(&n.to_le_bytes()),
            Scalar::Bool(b) => bytes[offset] = u8::from(b),
            Scalar::Ptr(p) => bytes[offset..offset + 8].copy_from_slice(&p.to_le_bytes()),
        }
    }

    fn rc_inc(&mut self, idx: usize) {
        if idx != 0 {
            self.objects[idx].0 += 1;
        }
    }

    fn rc_dec(&mut self, idx: usize) {
        if idx != 0 {
            self.objects[idx].0 -= 1;
            if self.objects[idx].0 == 0 {
                self.objects[idx].1.clear();
            }
        }
    }
}

type Env = HashMap<Value, Scalar>;

/// Evaluate the entry function of an SSA module.
pub fn eval(module: &Module, heap: &mut Heap, args: &[Scalar]) -> Scalar {
    eval_function(module, heap, &module.entry, args)
}

/// Create a new heap for interpretation.
pub fn new_heap() -> Heap {
    Heap::new()
}

fn eval_function(module: &Module, heap: &mut Heap, name: &str, args: &[Scalar]) -> Scalar {
    let func = &module.functions[name];
    let mut env = Env::new();

    for (param, arg) in func.params.iter().zip(args) {
        env.insert(*param, *arg);
    }

    let mut current = BlockId(0);
    let mut block_args: Vec<Scalar> = vec![];

    loop {
        let block = &func.blocks[current.0];

        for (param, arg) in block.params.iter().zip(&block_args) {
            env.insert(*param, *arg);
        }

        for inst in &block.insts {
            let val = eval_inst(module, heap, &env, inst);
            if let Some(dest) = inst.dest() {
                if let Some(v) = val {
                    env.insert(dest, v);
                }
            }
        }

        match &block.terminator {
            Terminator::Return(v) => return env[v],

            Terminator::Jump(target, args) => {
                block_args = args.iter().map(|v| env[v]).collect();
                current = *target;
            }

            Terminator::Branch {
                cond,
                then_block,
                then_args,
                else_block,
                else_args,
            } => {
                let Scalar::Bool(b) = env[cond] else {
                    panic!("branch on non-bool: {:?}", env[cond]);
                };
                if b {
                    block_args = then_args.iter().map(|v| env[v]).collect();
                    current = *then_block;
                } else {
                    block_args = else_args.iter().map(|v| env[v]).collect();
                    current = *else_block;
                }
            }

            Terminator::SwitchInt {
                scrutinee,
                arms,
                default,
            } => {
                let tag = scalar_to_u64(env[scrutinee]);
                if let Some((_, block, args)) = arms.iter().find(|(v, _, _)| *v == tag) {
                    block_args = args.iter().map(|v| env[v]).collect();
                    current = *block;
                } else if let Some((block, args)) = default {
                    block_args = args.iter().map(|v| env[v]).collect();
                    current = *block;
                } else {
                    panic!("no matching arm for tag {tag}");
                }
            }

            Terminator::None => panic!("reached incomplete block"),
        }
    }
}

fn eval_inst(module: &Module, heap: &mut Heap, env: &Env, inst: &Inst) -> Option<Scalar> {
    match inst {
        Inst::Const(_, ty, bits) => Some(bits_to_scalar(*ty, *bits)),

        Inst::BinOp(_, op, lhs, rhs) => Some(eval_binop(*op, env[lhs], env[rhs])),

        Inst::Call(_, name, args) => {
            let arg_vals: Vec<Scalar> = args.iter().map(|v| env[v]).collect();
            Some(eval_function(module, heap, name, &arg_vals))
        }

        Inst::Alloc(_, size) => {
            let idx = heap.alloc(*size);
            Some(Scalar::Ptr(idx))
        }

        Inst::Load(_, ty, ptr, offset) => {
            let Scalar::Ptr(idx) = env[ptr] else {
                panic!("load from non-ptr: {:?}", env[ptr]);
            };
            Some(heap.load(idx, *offset, *ty))
        }

        Inst::Store(ptr, offset, val) => {
            let Scalar::Ptr(idx) = env[ptr] else {
                panic!("store to non-ptr: {:?}", env[ptr]);
            };
            heap.store(idx, *offset, env[val]);
            None
        }

        Inst::RcInc(ptr) => {
            let Scalar::Ptr(idx) = env[ptr] else {
                panic!("rc_inc on non-ptr");
            };
            heap.rc_inc(idx);
            None
        }

        Inst::RcDec(ptr) => {
            let Scalar::Ptr(idx) = env[ptr] else {
                panic!("rc_dec on non-ptr");
            };
            heap.rc_dec(idx);
            None
        }
    }
}

fn bits_to_scalar(ty: ScalarType, bits: u64) -> Scalar {
    match ty {
        ScalarType::I8 => Scalar::I8(bits as i8),
        ScalarType::U8 => Scalar::U8(bits as u8),
        ScalarType::I64 => Scalar::I64(bits as i64),
        ScalarType::U64 => Scalar::U64(bits),
        ScalarType::F64 => Scalar::F64(f64::from_bits(bits)),
        ScalarType::Bool => Scalar::Bool(bits != 0),
        ScalarType::Ptr => Scalar::Ptr(bits as usize),
    }
}

fn scalar_to_u64(s: Scalar) -> u64 {
    match s {
        Scalar::I64(n) => n as u64,
        Scalar::U64(n) => n,
        Scalar::U8(n) => u64::from(n),
        Scalar::I8(n) => n as u64,
        Scalar::Bool(b) => u64::from(b),
        Scalar::Ptr(p) => p as u64,
        Scalar::F64(_) => panic!("switch on float"),
    }
}

fn eval_binop(op: BinaryOp, lhs: Scalar, rhs: Scalar) -> Scalar {
    match (op, lhs, rhs) {
        (BinaryOp::Add, Scalar::I64(a), Scalar::I64(b)) => Scalar::I64(a.wrapping_add(b)),
        (BinaryOp::Sub, Scalar::I64(a), Scalar::I64(b)) => Scalar::I64(a.wrapping_sub(b)),
        (BinaryOp::Mul, Scalar::I64(a), Scalar::I64(b)) => Scalar::I64(a.wrapping_mul(b)),
        (BinaryOp::Div, Scalar::I64(a), Scalar::I64(b)) => Scalar::I64(a / b),
        (BinaryOp::Rem, Scalar::I64(a), Scalar::I64(b)) => Scalar::I64(a % b),
        (BinaryOp::Max, Scalar::I64(a), Scalar::I64(b)) => Scalar::I64(a.max(b)),
        (BinaryOp::Eq, Scalar::I64(a), Scalar::I64(b)) => Scalar::Bool(a == b),
        (BinaryOp::Neq, Scalar::I64(a), Scalar::I64(b)) => Scalar::Bool(a != b),

        (BinaryOp::Add, Scalar::U64(a), Scalar::U64(b)) => Scalar::U64(a.wrapping_add(b)),
        (BinaryOp::Sub, Scalar::U64(a), Scalar::U64(b)) => Scalar::U64(a.wrapping_sub(b)),
        (BinaryOp::Mul, Scalar::U64(a), Scalar::U64(b)) => Scalar::U64(a.wrapping_mul(b)),
        (BinaryOp::Div, Scalar::U64(a), Scalar::U64(b)) => Scalar::U64(a / b),
        (BinaryOp::Rem, Scalar::U64(a), Scalar::U64(b)) => Scalar::U64(a % b),
        (BinaryOp::Max, Scalar::U64(a), Scalar::U64(b)) => Scalar::U64(a.max(b)),
        (BinaryOp::Eq, Scalar::U64(a), Scalar::U64(b)) => Scalar::Bool(a == b),
        (BinaryOp::Neq, Scalar::U64(a), Scalar::U64(b)) => Scalar::Bool(a != b),

        (BinaryOp::Add, Scalar::U8(a), Scalar::U8(b)) => Scalar::U8(a.wrapping_add(b)),
        (BinaryOp::Sub, Scalar::U8(a), Scalar::U8(b)) => Scalar::U8(a.wrapping_sub(b)),
        (BinaryOp::Mul, Scalar::U8(a), Scalar::U8(b)) => Scalar::U8(a.wrapping_mul(b)),
        (BinaryOp::Div, Scalar::U8(a), Scalar::U8(b)) => Scalar::U8(a / b),
        (BinaryOp::Rem, Scalar::U8(a), Scalar::U8(b)) => Scalar::U8(a % b),
        (BinaryOp::Eq, Scalar::U8(a), Scalar::U8(b)) => Scalar::Bool(a == b),
        (BinaryOp::Neq, Scalar::U8(a), Scalar::U8(b)) => Scalar::Bool(a != b),

        (BinaryOp::Add, Scalar::I8(a), Scalar::I8(b)) => Scalar::I8(a.wrapping_add(b)),
        (BinaryOp::Sub, Scalar::I8(a), Scalar::I8(b)) => Scalar::I8(a.wrapping_sub(b)),
        (BinaryOp::Mul, Scalar::I8(a), Scalar::I8(b)) => Scalar::I8(a.wrapping_mul(b)),
        (BinaryOp::Div, Scalar::I8(a), Scalar::I8(b)) => Scalar::I8(a / b),
        (BinaryOp::Rem, Scalar::I8(a), Scalar::I8(b)) => Scalar::I8(a % b),
        (BinaryOp::Eq, Scalar::I8(a), Scalar::I8(b)) => Scalar::Bool(a == b),
        (BinaryOp::Neq, Scalar::I8(a), Scalar::I8(b)) => Scalar::Bool(a != b),

        (BinaryOp::Add, Scalar::F64(a), Scalar::F64(b)) => Scalar::F64(a + b),
        (BinaryOp::Sub, Scalar::F64(a), Scalar::F64(b)) => Scalar::F64(a - b),
        (BinaryOp::Mul, Scalar::F64(a), Scalar::F64(b)) => Scalar::F64(a * b),
        (BinaryOp::Div, Scalar::F64(a), Scalar::F64(b)) => Scalar::F64(a / b),
        (BinaryOp::Eq, Scalar::F64(a), Scalar::F64(b)) => Scalar::Bool(a == b),
        (BinaryOp::Neq, Scalar::F64(a), Scalar::F64(b)) => Scalar::Bool(a != b),

        _ => panic!("unsupported binop {op:?} on {lhs:?}, {rhs:?}"),
    }
}
