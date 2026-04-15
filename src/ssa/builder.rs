use super::{Block, Function, Module};
use crate::ssa::instruction::{BinaryOp, BlockId, Inst, ScalarType, Terminator, Value};
use std::collections::{BTreeMap, HashMap};

/// Block under construction — no terminator yet.
pub struct PendingBlock {
    pub params: Vec<Value>,
    pub insts: Vec<Inst>,
}

/// Accumulated state for one function being built.
pub struct FuncBuilder {
    pub pending: BTreeMap<BlockId, PendingBlock>,
    pub finished: BTreeMap<BlockId, Block>,
    pub next_block: usize,
}

impl FuncBuilder {
    pub fn new() -> Self {
        Self {
            pending: BTreeMap::new(),
            finished: BTreeMap::new(),
            next_block: 0,
        }
    }
}

/// Builds SSA functions and modules incrementally.
pub struct Builder {
    next_value: usize,
    pub func: FuncBuilder,
    pub current_block: Option<BlockId>,
    functions: HashMap<String, Function>,
    pub value_types: HashMap<Value, ScalarType>,
}

impl Builder {
    pub fn new() -> Self {
        Self {
            next_value: 0,
            func: FuncBuilder::new(),
            current_block: None,
            functions: HashMap::new(),
            value_types: HashMap::new(),
        }
    }

    pub const fn fresh_value(&mut self) -> Value {
        let v = Value(self.next_value);
        self.next_value += 1;
        v
    }

    pub fn set_type(&mut self, v: Value, ty: ScalarType) {
        self.value_types.insert(v, ty);
    }

    pub fn create_block(&mut self) -> BlockId {
        let id = BlockId(self.func.next_block);
        self.func.next_block += 1;
        self.func.pending.insert(id, PendingBlock {
            params: Vec::new(),
            insts: Vec::new(),
        });
        id
    }

    pub const fn switch_to(&mut self, block: BlockId) {
        self.current_block = Some(block);
    }

    pub fn add_block_param(&mut self, block: BlockId, ty: ScalarType) -> Value {
        let v = self.fresh_value();
        self.func.pending.get_mut(&block)
            .expect("add_block_param on non-pending block")
            .params.push(v);
        self.set_type(v, ty);
        v
    }

    // ---- Constants ----

    pub fn const_i64(&mut self, n: i64) -> Value {
        let v = self.fresh_value();
        self.push(Inst::Const(v, ScalarType::I64, n as u64));
        self.set_type(v, ScalarType::I64);
        v
    }

    pub fn const_u64(&mut self, n: u64) -> Value {
        let v = self.fresh_value();
        self.push(Inst::Const(v, ScalarType::U64, n));
        self.set_type(v, ScalarType::U64);
        v
    }

    pub fn const_f64(&mut self, n: f64) -> Value {
        let v = self.fresh_value();
        self.push(Inst::Const(v, ScalarType::F64, n.to_bits()));
        self.set_type(v, ScalarType::F64);
        v
    }

    pub fn const_u8(&mut self, n: u8) -> Value {
        let v = self.fresh_value();
        self.push(Inst::Const(v, ScalarType::U8, u64::from(n)));
        self.set_type(v, ScalarType::U8);
        v
    }

    pub fn const_i8(&mut self, n: i8) -> Value {
        let v = self.fresh_value();
        self.push(Inst::Const(v, ScalarType::I8, n as u64));
        self.set_type(v, ScalarType::I8);
        v
    }

    pub fn const_u16(&mut self, n: u16) -> Value {
        let v = self.fresh_value();
        self.push(Inst::Const(v, ScalarType::U16, u64::from(n)));
        self.set_type(v, ScalarType::U16);
        v
    }

    pub fn const_i16(&mut self, n: i16) -> Value {
        let v = self.fresh_value();
        self.push(Inst::Const(v, ScalarType::I16, n as u64));
        self.set_type(v, ScalarType::I16);
        v
    }

    pub fn const_u32(&mut self, n: u32) -> Value {
        let v = self.fresh_value();
        self.push(Inst::Const(v, ScalarType::U32, u64::from(n)));
        self.set_type(v, ScalarType::U32);
        v
    }

    pub fn const_i32(&mut self, n: i32) -> Value {
        let v = self.fresh_value();
        self.push(Inst::Const(v, ScalarType::I32, n as u64));
        self.set_type(v, ScalarType::I32);
        v
    }

    pub fn const_bool(&mut self, b: bool) -> Value {
        let v = self.fresh_value();
        self.push(Inst::Const(v, ScalarType::Bool, u64::from(b)));
        self.set_type(v, ScalarType::Bool);
        v
    }

    pub fn const_ptr_null(&mut self) -> Value {
        let v = self.fresh_value();
        self.push(Inst::Const(v, ScalarType::Ptr, 0));
        self.set_type(v, ScalarType::Ptr);
        v
    }

    // ---- Arithmetic ----

    pub fn binop(&mut self, op: BinaryOp, lhs: Value, rhs: Value, ty: ScalarType) -> Value {
        let v = self.fresh_value();
        self.push(Inst::BinOp(v, op, lhs, rhs));
        self.set_type(v, ty);
        v
    }

    // ---- Calls ----

    pub fn call(&mut self, func: &str, args: Vec<Value>, ret_ty: ScalarType) -> Value {
        let v = self.fresh_value();
        self.push(Inst::Call(v, func.to_owned(), args));
        self.set_type(v, ret_ty);
        v
    }

    // ---- Memory ----

    pub fn alloc(&mut self, size: usize) -> Value {
        let v = self.fresh_value();
        self.push(Inst::Alloc(v, size));
        self.set_type(v, ScalarType::Ptr);
        v
    }

    pub fn load(&mut self, ptr: Value, offset: usize, ty: ScalarType) -> Value {
        let v = self.fresh_value();
        self.push(Inst::Load(v, ptr, offset));
        self.set_type(v, ty);
        v
    }

    pub fn store(&mut self, ptr: Value, offset: usize, val: Value) {
        self.push(Inst::Store(ptr, offset, val));
    }

    pub fn load_dyn(&mut self, ptr: Value, idx: Value, ty: ScalarType) -> Value {
        let v = self.fresh_value();
        self.push(Inst::LoadDyn(v, ptr, idx));
        self.set_type(v, ty);
        v
    }

    pub fn store_dyn(&mut self, ptr: Value, idx: Value, val: Value) {
        self.push(Inst::StoreDyn(ptr, idx, val));
    }

    pub fn rc_inc(&mut self, ptr: Value) {
        self.push(Inst::RcInc(ptr));
    }

    pub fn rc_dec(&mut self, ptr: Value) {
        self.push(Inst::RcDec(ptr));
    }

    // ---- Terminators ----
    //
    // Each terminator method finalizes the current block: it takes the
    // pending block, combines it with the terminator to produce a
    // complete Block, and moves it into the finished map.

    pub fn ret(&mut self, value: Value) {
        self.seal(Terminator::Return(value));
    }

    pub fn jump(&mut self, target: BlockId, args: Vec<Value>) {
        self.seal(Terminator::Jump(target, args));
    }

    pub fn branch(
        &mut self,
        cond: Value,
        then_block: BlockId,
        then_args: Vec<Value>,
        else_block: BlockId,
        else_args: Vec<Value>,
    ) {
        self.seal(Terminator::Branch {
            cond,
            then_block,
            then_args,
            else_block,
            else_args,
        });
    }

    pub fn switch_int(
        &mut self,
        scrutinee: Value,
        arms: Vec<(u64, BlockId, Vec<Value>)>,
        default: Option<(BlockId, Vec<Value>)>,
    ) {
        self.seal(Terminator::SwitchInt {
            scrutinee,
            arms,
            default,
        });
    }

    // ---- Function building ----

    pub fn finish_function(
        &mut self,
        name: &str,
        params: Vec<Value>,
        param_types: Vec<ScalarType>,
        return_type: ScalarType,
    ) {
        assert!(
            self.func.pending.is_empty(),
            "finish_function({name}): {} blocks still pending terminators",
            self.func.pending.len(),
        );
        let fb = std::mem::replace(&mut self.func, FuncBuilder::new());
        let value_types = std::mem::take(&mut self.value_types);
        self.functions.insert(
            name.to_owned(),
            Function {
                name: name.to_owned(),
                params,
                blocks: fb.finished,
                param_types,
                return_type,
                value_types,
                entry: BlockId(0),
                next_block: fb.next_block,
            },
        );
        self.current_block = None;
    }

    pub fn build(self, entry: &str) -> Module {
        Module {
            functions: self.functions,
            statics: Vec::new(),
            entry: entry.to_owned(),
        }
    }

    // ---- Internal ----

    fn push(&mut self, inst: Inst) {
        let bid = self.current_block.expect("no current block");
        self.func.pending.get_mut(&bid)
            .expect("push to non-pending block")
            .insts.push(inst);
    }

    fn seal(&mut self, terminator: Terminator) {
        let bid = self.current_block.expect("no current block");
        let pending = self.func.pending.remove(&bid)
            .expect("seal on non-pending block");
        self.func.finished.insert(bid, Block {
            params: pending.params,
            insts: pending.insts,
            terminator,
        });
    }
}
