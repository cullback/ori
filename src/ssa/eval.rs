use std::collections::HashMap;

use crate::ssa::Module;
use crate::ssa::instruction::{BinaryOp, BlockId, Inst, ScalarType, Terminator, Value};

/// A scalar runtime value that fits in a register.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Scalar {
    I8(i8),
    U8(u8),
    I16(i16),
    U16(u16),
    I32(i32),
    U32(u32),
    I64(i64),
    U64(u64),
    F64(f64),
    Bool(bool),
    Ptr(usize), // index into heap
}

/// Simulated heap for the interpreter.
/// Each allocation is a Vec of Scalar slots.
pub struct Heap {
    /// Each entry: (refcount, slots).
    objects: Vec<(usize, Vec<Scalar>)>,
}

impl Heap {
    fn new() -> Self {
        // Index 0 is null
        Self {
            objects: vec![(0, vec![])],
        }
    }

    pub fn alloc(&mut self, num_slots: usize) -> usize {
        let idx = self.objects.len();
        self.objects.push((1, vec![Scalar::I64(0); num_slots]));
        idx
    }

    pub fn load(&self, idx: usize, slot: usize) -> Scalar {
        self.objects[idx].1[slot]
    }

    pub fn store(&mut self, idx: usize, slot: usize, val: Scalar) {
        self.objects[idx].1[slot] = val;
    }

    fn load_dyn(&self, idx: usize, slot_val: usize) -> Scalar {
        self.objects[idx].1[slot_val]
    }

    fn store_dyn(&mut self, idx: usize, slot_val: usize, val: Scalar) {
        // Grow if needed (for list append)
        let slots = &mut self.objects[idx].1;
        if slot_val >= slots.len() {
            slots.resize(slot_val + 1, Scalar::I64(0));
        }
        slots[slot_val] = val;
    }

    fn rc_inc(&mut self, idx: usize) {
        if idx != 0 {
            self.objects[idx].0 += 1;
        }
    }

    fn rc_dec(&mut self, idx: usize) {
        if idx != 0 && self.objects[idx].0 > 0 {
            self.objects[idx].0 -= 1;
            // Don't free yet — recursive child decrement not implemented.
            // For now, just track the count.
        }
    }

    /// Clone a heap object, returning the new index.
    pub fn clone_object(&mut self, idx: usize) -> usize {
        let new_idx = self.objects.len();
        let data = self.objects[idx].1.clone();
        self.objects.push((1, data));
        new_idx
    }

    /// Get the number of slots in an object.
    pub fn object_len(&self, idx: usize) -> usize {
        self.objects[idx].1.len()
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
    // Check for runtime intrinsics
    if let Some(result) = eval_intrinsic(name, heap, args) {
        return result;
    }

    let func = module
        .functions
        .get(name)
        .unwrap_or_else(|| panic!("undefined SSA function: {name}"));
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

        Inst::Load(_, ptr, offset) => {
            let Scalar::Ptr(idx) = env[ptr] else {
                panic!("load from non-ptr: {:?}", env[ptr]);
            };
            Some(heap.load(idx, *offset))
        }

        Inst::Store(ptr, offset, val) => {
            let Scalar::Ptr(idx) = env[ptr] else {
                panic!("store to non-ptr: {:?}", env[ptr]);
            };
            heap.store(idx, *offset, env[val]);
            None
        }

        Inst::LoadDyn(_, ptr, idx_val) => {
            let Scalar::Ptr(heap_idx) = env[ptr] else {
                panic!("load_dyn from non-ptr: {:?}", env[ptr]);
            };
            let slot = scalar_to_usize(env[idx_val]);
            Some(heap.load_dyn(heap_idx, slot))
        }

        Inst::StoreDyn(ptr, idx_val, val) => {
            let Scalar::Ptr(heap_idx) = env[ptr] else {
                panic!("store_dyn to non-ptr: {:?}", env[ptr]);
            };
            let slot = scalar_to_usize(env[idx_val]);
            heap.store_dyn(heap_idx, slot, env[val]);
            None
        }

        Inst::RcInc(ptr) => {
            if let Scalar::Ptr(idx) = env[ptr] {
                heap.rc_inc(idx);
            }
            None
        }

        Inst::RcDec(ptr) => {
            if let Scalar::Ptr(idx) = env[ptr] {
                heap.rc_dec(idx);
            }
            None
        }
    }
}

// ---- Runtime intrinsics ----

fn eval_intrinsic(name: &str, heap: &mut Heap, args: &[Scalar]) -> Option<Scalar> {
    match name {
        "__list_len" => {
            // args: [list_ptr] → U64 length
            let Scalar::Ptr(list_idx) = args[0] else {
                panic!("__list_len: expected Ptr");
            };
            let len = heap.load(list_idx, 0);
            Some(len)
        }
        "__list_get" => {
            // args: [list_ptr, index_u64] → element
            let Scalar::Ptr(list_idx) = args[0] else {
                panic!("__list_get: expected Ptr");
            };
            let idx = scalar_to_usize(args[1]);
            let Scalar::Ptr(data_idx) = heap.load(list_idx, 2) else {
                panic!("__list_get: data slot is not Ptr");
            };
            Some(heap.load_dyn(data_idx, idx))
        }
        "__list_set" => {
            // args: [list_ptr, index_u64, new_val] → new_list_ptr
            let Scalar::Ptr(list_idx) = args[0] else {
                panic!("__list_set: expected Ptr");
            };
            let idx = scalar_to_usize(args[1]);
            let len = heap.load(list_idx, 0);
            let cap = heap.load(list_idx, 1);
            let Scalar::Ptr(old_data) = heap.load(list_idx, 2) else {
                panic!("__list_set: data is not Ptr");
            };
            // Clone data buffer and list header
            let new_data = heap.clone_object(old_data);
            heap.store_dyn(new_data, idx, args[2]);
            let new_list = heap.alloc(3);
            heap.store(new_list, 0, len);
            heap.store(new_list, 1, cap);
            heap.store(new_list, 2, Scalar::Ptr(new_data));
            Some(Scalar::Ptr(new_list))
        }
        "__list_append" => {
            // args: [list_ptr, val] → new_list_ptr
            let Scalar::Ptr(list_idx) = args[0] else {
                panic!("__list_append: expected Ptr");
            };
            let Scalar::U64(len) = heap.load(list_idx, 0) else {
                panic!("__list_append: len is not U64");
            };
            let Scalar::Ptr(old_data) = heap.load(list_idx, 2) else {
                panic!("__list_append: data is not Ptr");
            };
            let new_len = len + 1;
            let new_data = heap.clone_object(old_data);
            heap.store_dyn(new_data, len as usize, args[1]);
            let new_list = heap.alloc(3);
            heap.store(new_list, 0, Scalar::U64(new_len));
            heap.store(new_list, 1, Scalar::U64(new_len));
            heap.store(new_list, 2, Scalar::Ptr(new_data));
            Some(Scalar::Ptr(new_list))
        }
        "__list_reverse" => {
            // args: [list_ptr] → new_list_ptr with elements in reverse order
            let Scalar::Ptr(list_idx) = args[0] else {
                panic!("__list_reverse: expected Ptr");
            };
            let Scalar::U64(len) = heap.load(list_idx, 0) else {
                panic!("__list_reverse: len is not U64");
            };
            let Scalar::Ptr(old_data) = heap.load(list_idx, 2) else {
                panic!("__list_reverse: data is not Ptr");
            };
            #[expect(clippy::cast_possible_truncation)]
            let len_usize = len as usize;
            let new_data = heap.alloc(len_usize);
            for i in 0..len_usize {
                let elem = heap.load_dyn(old_data, i);
                heap.store(new_data, len_usize - 1 - i, elem);
            }
            let new_list = heap.alloc(3);
            heap.store(new_list, 0, Scalar::U64(len));
            heap.store(new_list, 1, Scalar::U64(len));
            heap.store(new_list, 2, Scalar::Ptr(new_data));
            Some(Scalar::Ptr(new_list))
        }
        "__list_sublist" => {
            // args: [list_ptr, start_u64, count_u64] → new_list_ptr
            let Scalar::Ptr(list_idx) = args[0] else {
                panic!("__list_sublist: expected Ptr");
            };
            let start = scalar_to_usize(args[1]);
            let count = scalar_to_usize(args[2]);
            let Scalar::Ptr(old_data) = heap.load(list_idx, 2) else {
                panic!("__list_sublist: data is not Ptr");
            };
            let new_data = heap.alloc(count);
            for i in 0..count {
                let elem = heap.load_dyn(old_data, start + i);
                heap.store(new_data, i, elem);
            }
            let new_list = heap.alloc(3);
            let count_u64 = count as u64;
            heap.store(new_list, 0, Scalar::U64(count_u64));
            heap.store(new_list, 1, Scalar::U64(count_u64));
            heap.store(new_list, 2, Scalar::Ptr(new_data));
            Some(Scalar::Ptr(new_list))
        }
        "__num_to_str" => {
            // args: [number] → str_ptr (List(U8))
            let s = match args[0] {
                Scalar::I64(n) => n.to_string(),
                Scalar::U64(n) => n.to_string(),
                Scalar::F64(n) => n.to_string(),
                Scalar::U8(n) => n.to_string(),
                Scalar::I8(n) => n.to_string(),
                _ => panic!("__num_to_str: expected number"),
            };
            let bytes = s.into_bytes();
            let len = bytes.len();
            let data = heap.alloc(len);
            for (i, b) in bytes.into_iter().enumerate() {
                heap.store(data, i, Scalar::U8(b));
            }
            let list = heap.alloc(3);
            heap.store(list, 0, Scalar::U64(len as u64));
            heap.store(list, 1, Scalar::U64(len as u64));
            heap.store(list, 2, Scalar::Ptr(data));
            Some(Scalar::Ptr(list))
        }
        "__str_concat" => {
            // args: [str_a, str_b] → str_ptr (List(U8))
            let Scalar::Ptr(a_idx) = args[0] else {
                panic!("__str_concat: expected Ptr");
            };
            let Scalar::Ptr(b_idx) = args[1] else {
                panic!("__str_concat: expected Ptr");
            };
            let Scalar::U64(a_len) = heap.load(a_idx, 0) else {
                panic!("__str_concat: expected U64 len");
            };
            let Scalar::U64(b_len) = heap.load(b_idx, 0) else {
                panic!("__str_concat: expected U64 len");
            };
            let Scalar::Ptr(a_data) = heap.load(a_idx, 2) else {
                panic!("__str_concat: expected Ptr data");
            };
            let Scalar::Ptr(b_data) = heap.load(b_idx, 2) else {
                panic!("__str_concat: expected Ptr data");
            };
            let total = a_len + b_len;
            let data = heap.alloc(total as usize);
            for i in 0..a_len as usize {
                heap.store(data, i, heap.load(a_data, i));
            }
            for i in 0..b_len as usize {
                heap.store(data, a_len as usize + i, heap.load(b_data, i));
            }
            let list = heap.alloc(3);
            heap.store(list, 0, Scalar::U64(total));
            heap.store(list, 1, Scalar::U64(total));
            heap.store(list, 2, Scalar::Ptr(data));
            Some(Scalar::Ptr(list))
        }
        "__u64_from_u8" => {
            // args: [u8] → u64 (widening conversion)
            let Scalar::U8(n) = args[0] else {
                panic!("__u64_from_u8: expected U8");
            };
            Some(Scalar::U64(u64::from(n)))
        }
        "__crash" => {
            // args: [str_ptr] — print message to stderr and abort.
            let Scalar::Ptr(list_idx) = args[0] else {
                eprintln!("crash: <non-string argument>");
                std::process::exit(1);
            };
            let Scalar::U64(len) = heap.load(list_idx, 0) else {
                eprintln!("crash: <malformed string>");
                std::process::exit(1);
            };
            let Scalar::Ptr(data_idx) = heap.load(list_idx, 2) else {
                eprintln!("crash: <malformed string>");
                std::process::exit(1);
            };
            #[expect(clippy::cast_possible_truncation)]
            let len = len as usize;
            let mut bytes = Vec::with_capacity(len);
            for i in 0..len {
                let Scalar::U8(b) = heap.load(data_idx, i) else {
                    bytes.push(b'?');
                    continue;
                };
                bytes.push(b);
            }
            let msg = String::from_utf8_lossy(&bytes);
            eprintln!("crash: {msg}");
            std::process::exit(1);
        }
        _ => None,
    }
}

// ---- Helpers ----

fn bits_to_scalar(ty: ScalarType, bits: u64) -> Scalar {
    match ty {
        ScalarType::I8 => Scalar::I8(bits as i8),
        ScalarType::U8 => Scalar::U8(bits as u8),
        ScalarType::I16 => Scalar::I16(bits as i16),
        ScalarType::U16 => Scalar::U16(bits as u16),
        ScalarType::I32 => Scalar::I32(bits as i32),
        ScalarType::U32 => Scalar::U32(bits as u32),
        ScalarType::I64 => Scalar::I64(bits as i64),
        ScalarType::U64 => Scalar::U64(bits),
        ScalarType::F64 => Scalar::F64(f64::from_bits(bits)),
        ScalarType::Bool => Scalar::Bool(bits != 0),
        ScalarType::Ptr => Scalar::Ptr(bits as usize),
    }
}

fn scalar_to_u64(s: Scalar) -> u64 {
    match s {
        Scalar::I8(n) => n as u64,
        Scalar::U8(n) => u64::from(n),
        Scalar::I16(n) => n as u64,
        Scalar::U16(n) => u64::from(n),
        Scalar::I32(n) => n as u64,
        Scalar::U32(n) => u64::from(n),
        Scalar::I64(n) => n as u64,
        Scalar::U64(n) => n,
        Scalar::Bool(b) => u64::from(b),
        Scalar::Ptr(p) => p as u64,
        Scalar::F64(_) => panic!("switch on float"),
    }
}

fn scalar_to_usize(s: Scalar) -> usize {
    match s {
        Scalar::U64(n) => n as usize,
        Scalar::I64(n) => n as usize,
        Scalar::Ptr(p) => p,
        _ => panic!("expected integer index, got {s:?}"),
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
        (BinaryOp::Lt, Scalar::I64(a), Scalar::I64(b)) => Scalar::Bool(a < b),
        (BinaryOp::Le, Scalar::I64(a), Scalar::I64(b)) => Scalar::Bool(a <= b),
        (BinaryOp::Gt, Scalar::I64(a), Scalar::I64(b)) => Scalar::Bool(a > b),
        (BinaryOp::Ge, Scalar::I64(a), Scalar::I64(b)) => Scalar::Bool(a >= b),

        (BinaryOp::Add, Scalar::U64(a), Scalar::U64(b)) => Scalar::U64(a.wrapping_add(b)),
        (BinaryOp::Sub, Scalar::U64(a), Scalar::U64(b)) => Scalar::U64(a.wrapping_sub(b)),
        (BinaryOp::Mul, Scalar::U64(a), Scalar::U64(b)) => Scalar::U64(a.wrapping_mul(b)),
        (BinaryOp::Div, Scalar::U64(a), Scalar::U64(b)) => Scalar::U64(a / b),
        (BinaryOp::Rem, Scalar::U64(a), Scalar::U64(b)) => Scalar::U64(a % b),
        (BinaryOp::Max, Scalar::U64(a), Scalar::U64(b)) => Scalar::U64(a.max(b)),
        (BinaryOp::Eq, Scalar::U64(a), Scalar::U64(b)) => Scalar::Bool(a == b),
        (BinaryOp::Neq, Scalar::U64(a), Scalar::U64(b)) => Scalar::Bool(a != b),
        (BinaryOp::Lt, Scalar::U64(a), Scalar::U64(b)) => Scalar::Bool(a < b),
        (BinaryOp::Le, Scalar::U64(a), Scalar::U64(b)) => Scalar::Bool(a <= b),
        (BinaryOp::Gt, Scalar::U64(a), Scalar::U64(b)) => Scalar::Bool(a > b),
        (BinaryOp::Ge, Scalar::U64(a), Scalar::U64(b)) => Scalar::Bool(a >= b),

        (BinaryOp::Add, Scalar::U8(a), Scalar::U8(b)) => Scalar::U8(a.wrapping_add(b)),
        (BinaryOp::Sub, Scalar::U8(a), Scalar::U8(b)) => Scalar::U8(a.wrapping_sub(b)),
        (BinaryOp::Mul, Scalar::U8(a), Scalar::U8(b)) => Scalar::U8(a.wrapping_mul(b)),
        (BinaryOp::Div, Scalar::U8(a), Scalar::U8(b)) => Scalar::U8(a / b),
        (BinaryOp::Rem, Scalar::U8(a), Scalar::U8(b)) => Scalar::U8(a % b),
        (BinaryOp::Eq, Scalar::U8(a), Scalar::U8(b)) => Scalar::Bool(a == b),
        (BinaryOp::Neq, Scalar::U8(a), Scalar::U8(b)) => Scalar::Bool(a != b),
        (BinaryOp::Lt, Scalar::U8(a), Scalar::U8(b)) => Scalar::Bool(a < b),
        (BinaryOp::Le, Scalar::U8(a), Scalar::U8(b)) => Scalar::Bool(a <= b),
        (BinaryOp::Gt, Scalar::U8(a), Scalar::U8(b)) => Scalar::Bool(a > b),
        (BinaryOp::Ge, Scalar::U8(a), Scalar::U8(b)) => Scalar::Bool(a >= b),

        (BinaryOp::Add, Scalar::I8(a), Scalar::I8(b)) => Scalar::I8(a.wrapping_add(b)),
        (BinaryOp::Sub, Scalar::I8(a), Scalar::I8(b)) => Scalar::I8(a.wrapping_sub(b)),
        (BinaryOp::Mul, Scalar::I8(a), Scalar::I8(b)) => Scalar::I8(a.wrapping_mul(b)),
        (BinaryOp::Div, Scalar::I8(a), Scalar::I8(b)) => Scalar::I8(a / b),
        (BinaryOp::Rem, Scalar::I8(a), Scalar::I8(b)) => Scalar::I8(a % b),
        (BinaryOp::Eq, Scalar::I8(a), Scalar::I8(b)) => Scalar::Bool(a == b),
        (BinaryOp::Neq, Scalar::I8(a), Scalar::I8(b)) => Scalar::Bool(a != b),
        (BinaryOp::Lt, Scalar::I8(a), Scalar::I8(b)) => Scalar::Bool(a < b),
        (BinaryOp::Le, Scalar::I8(a), Scalar::I8(b)) => Scalar::Bool(a <= b),
        (BinaryOp::Gt, Scalar::I8(a), Scalar::I8(b)) => Scalar::Bool(a > b),
        (BinaryOp::Ge, Scalar::I8(a), Scalar::I8(b)) => Scalar::Bool(a >= b),

        (BinaryOp::Add, Scalar::I16(a), Scalar::I16(b)) => Scalar::I16(a.wrapping_add(b)),
        (BinaryOp::Sub, Scalar::I16(a), Scalar::I16(b)) => Scalar::I16(a.wrapping_sub(b)),
        (BinaryOp::Mul, Scalar::I16(a), Scalar::I16(b)) => Scalar::I16(a.wrapping_mul(b)),
        (BinaryOp::Div, Scalar::I16(a), Scalar::I16(b)) => Scalar::I16(a / b),
        (BinaryOp::Rem, Scalar::I16(a), Scalar::I16(b)) => Scalar::I16(a % b),
        (BinaryOp::Eq, Scalar::I16(a), Scalar::I16(b)) => Scalar::Bool(a == b),
        (BinaryOp::Neq, Scalar::I16(a), Scalar::I16(b)) => Scalar::Bool(a != b),
        (BinaryOp::Lt, Scalar::I16(a), Scalar::I16(b)) => Scalar::Bool(a < b),
        (BinaryOp::Le, Scalar::I16(a), Scalar::I16(b)) => Scalar::Bool(a <= b),
        (BinaryOp::Gt, Scalar::I16(a), Scalar::I16(b)) => Scalar::Bool(a > b),
        (BinaryOp::Ge, Scalar::I16(a), Scalar::I16(b)) => Scalar::Bool(a >= b),

        (BinaryOp::Add, Scalar::U16(a), Scalar::U16(b)) => Scalar::U16(a.wrapping_add(b)),
        (BinaryOp::Sub, Scalar::U16(a), Scalar::U16(b)) => Scalar::U16(a.wrapping_sub(b)),
        (BinaryOp::Mul, Scalar::U16(a), Scalar::U16(b)) => Scalar::U16(a.wrapping_mul(b)),
        (BinaryOp::Div, Scalar::U16(a), Scalar::U16(b)) => Scalar::U16(a / b),
        (BinaryOp::Rem, Scalar::U16(a), Scalar::U16(b)) => Scalar::U16(a % b),
        (BinaryOp::Eq, Scalar::U16(a), Scalar::U16(b)) => Scalar::Bool(a == b),
        (BinaryOp::Neq, Scalar::U16(a), Scalar::U16(b)) => Scalar::Bool(a != b),
        (BinaryOp::Lt, Scalar::U16(a), Scalar::U16(b)) => Scalar::Bool(a < b),
        (BinaryOp::Le, Scalar::U16(a), Scalar::U16(b)) => Scalar::Bool(a <= b),
        (BinaryOp::Gt, Scalar::U16(a), Scalar::U16(b)) => Scalar::Bool(a > b),
        (BinaryOp::Ge, Scalar::U16(a), Scalar::U16(b)) => Scalar::Bool(a >= b),

        (BinaryOp::Add, Scalar::I32(a), Scalar::I32(b)) => Scalar::I32(a.wrapping_add(b)),
        (BinaryOp::Sub, Scalar::I32(a), Scalar::I32(b)) => Scalar::I32(a.wrapping_sub(b)),
        (BinaryOp::Mul, Scalar::I32(a), Scalar::I32(b)) => Scalar::I32(a.wrapping_mul(b)),
        (BinaryOp::Div, Scalar::I32(a), Scalar::I32(b)) => Scalar::I32(a / b),
        (BinaryOp::Rem, Scalar::I32(a), Scalar::I32(b)) => Scalar::I32(a % b),
        (BinaryOp::Eq, Scalar::I32(a), Scalar::I32(b)) => Scalar::Bool(a == b),
        (BinaryOp::Neq, Scalar::I32(a), Scalar::I32(b)) => Scalar::Bool(a != b),
        (BinaryOp::Lt, Scalar::I32(a), Scalar::I32(b)) => Scalar::Bool(a < b),
        (BinaryOp::Le, Scalar::I32(a), Scalar::I32(b)) => Scalar::Bool(a <= b),
        (BinaryOp::Gt, Scalar::I32(a), Scalar::I32(b)) => Scalar::Bool(a > b),
        (BinaryOp::Ge, Scalar::I32(a), Scalar::I32(b)) => Scalar::Bool(a >= b),

        (BinaryOp::Add, Scalar::U32(a), Scalar::U32(b)) => Scalar::U32(a.wrapping_add(b)),
        (BinaryOp::Sub, Scalar::U32(a), Scalar::U32(b)) => Scalar::U32(a.wrapping_sub(b)),
        (BinaryOp::Mul, Scalar::U32(a), Scalar::U32(b)) => Scalar::U32(a.wrapping_mul(b)),
        (BinaryOp::Div, Scalar::U32(a), Scalar::U32(b)) => Scalar::U32(a / b),
        (BinaryOp::Rem, Scalar::U32(a), Scalar::U32(b)) => Scalar::U32(a % b),
        (BinaryOp::Eq, Scalar::U32(a), Scalar::U32(b)) => Scalar::Bool(a == b),
        (BinaryOp::Neq, Scalar::U32(a), Scalar::U32(b)) => Scalar::Bool(a != b),
        (BinaryOp::Lt, Scalar::U32(a), Scalar::U32(b)) => Scalar::Bool(a < b),
        (BinaryOp::Le, Scalar::U32(a), Scalar::U32(b)) => Scalar::Bool(a <= b),
        (BinaryOp::Gt, Scalar::U32(a), Scalar::U32(b)) => Scalar::Bool(a > b),
        (BinaryOp::Ge, Scalar::U32(a), Scalar::U32(b)) => Scalar::Bool(a >= b),

        (BinaryOp::Add, Scalar::F64(a), Scalar::F64(b)) => Scalar::F64(a + b),
        (BinaryOp::Sub, Scalar::F64(a), Scalar::F64(b)) => Scalar::F64(a - b),
        (BinaryOp::Mul, Scalar::F64(a), Scalar::F64(b)) => Scalar::F64(a * b),
        (BinaryOp::Div, Scalar::F64(a), Scalar::F64(b)) => Scalar::F64(a / b),
        (BinaryOp::Eq, Scalar::F64(a), Scalar::F64(b)) => Scalar::Bool(a == b),
        (BinaryOp::Neq, Scalar::F64(a), Scalar::F64(b)) => Scalar::Bool(a != b),
        (BinaryOp::Lt, Scalar::F64(a), Scalar::F64(b)) => Scalar::Bool(a < b),
        (BinaryOp::Le, Scalar::F64(a), Scalar::F64(b)) => Scalar::Bool(a <= b),
        (BinaryOp::Gt, Scalar::F64(a), Scalar::F64(b)) => Scalar::Bool(a > b),
        (BinaryOp::Ge, Scalar::F64(a), Scalar::F64(b)) => Scalar::Bool(a >= b),

        _ => panic!("unsupported binop {op:?} on {lhs:?}, {rhs:?}"),
    }
}
