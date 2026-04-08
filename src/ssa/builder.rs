use super::{Block, Function, Module};
use crate::ssa::instruction::{BinaryOp, BlockId, Inst, ScalarType, Terminator, Value};
use std::collections::HashMap;

/// Builds SSA functions and modules incrementally.
pub struct Builder {
    next_value: usize,
    pub blocks: Vec<Block>,
    pub current_block: Option<BlockId>,
    functions: HashMap<String, Function>,
}

impl Builder {
    pub fn new() -> Self {
        Self {
            next_value: 0,
            blocks: Vec::new(),
            current_block: None,
            functions: HashMap::new(),
        }
    }

    pub const fn fresh_value(&mut self) -> Value {
        let v = Value(self.next_value);
        self.next_value += 1;
        v
    }

    pub fn create_block(&mut self) -> BlockId {
        let id = BlockId(self.blocks.len());
        self.blocks.push(Block {
            params: Vec::new(),
            insts: Vec::new(),
            terminator: Terminator::None,
        });
        id
    }

    pub const fn switch_to(&mut self, block: BlockId) {
        self.current_block = Some(block);
    }

    pub fn add_block_param(&mut self, block: BlockId) -> Value {
        let v = self.fresh_value();
        self.blocks[block.0].params.push(v);
        v
    }

    // ---- Constants ----

    pub fn const_i64(&mut self, n: i64) -> Value {
        let v = self.fresh_value();
        self.push(Inst::Const(v, ScalarType::I64, n as u64));
        v
    }

    pub fn const_u64(&mut self, n: u64) -> Value {
        let v = self.fresh_value();
        self.push(Inst::Const(v, ScalarType::U64, n));
        v
    }

    pub fn const_f64(&mut self, n: f64) -> Value {
        let v = self.fresh_value();
        self.push(Inst::Const(v, ScalarType::F64, n.to_bits()));
        v
    }

    pub fn const_u8(&mut self, n: u8) -> Value {
        let v = self.fresh_value();
        self.push(Inst::Const(v, ScalarType::U8, u64::from(n)));
        v
    }

    pub fn const_i8(&mut self, n: i8) -> Value {
        let v = self.fresh_value();
        self.push(Inst::Const(v, ScalarType::I8, n as u64));
        v
    }

    pub fn const_bool(&mut self, b: bool) -> Value {
        let v = self.fresh_value();
        self.push(Inst::Const(v, ScalarType::Bool, u64::from(b)));
        v
    }

    pub fn const_ptr_null(&mut self) -> Value {
        let v = self.fresh_value();
        self.push(Inst::Const(v, ScalarType::Ptr, 0));
        v
    }

    // ---- Arithmetic ----

    pub fn binop(&mut self, op: BinaryOp, lhs: Value, rhs: Value) -> Value {
        let v = self.fresh_value();
        self.push(Inst::BinOp(v, op, lhs, rhs));
        v
    }

    // ---- Calls ----

    pub fn call(&mut self, func: &str, args: Vec<Value>) -> Value {
        let v = self.fresh_value();
        self.push(Inst::Call(v, func.to_owned(), args));
        v
    }

    // ---- Memory ----

    pub fn alloc(&mut self, size: usize) -> Value {
        let v = self.fresh_value();
        self.push(Inst::Alloc(v, size));
        v
    }

    pub fn load(&mut self, ptr: Value, offset: usize) -> Value {
        let v = self.fresh_value();
        self.push(Inst::Load(v, ptr, offset));
        v
    }

    pub fn store(&mut self, ptr: Value, offset: usize, val: Value) {
        self.push(Inst::Store(ptr, offset, val));
    }

    pub fn load_dyn(&mut self, ptr: Value, idx: Value) -> Value {
        let v = self.fresh_value();
        self.push(Inst::LoadDyn(v, ptr, idx));
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

    pub fn ret(&mut self, value: Value) {
        self.set_terminator(Terminator::Return(value));
    }

    pub fn jump(&mut self, target: BlockId, args: Vec<Value>) {
        self.set_terminator(Terminator::Jump(target, args));
    }

    pub fn branch(
        &mut self,
        cond: Value,
        then_block: BlockId,
        then_args: Vec<Value>,
        else_block: BlockId,
        else_args: Vec<Value>,
    ) {
        self.set_terminator(Terminator::Branch {
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
        self.set_terminator(Terminator::SwitchInt {
            scrutinee,
            arms,
            default,
        });
    }

    // ---- Function building ----

    pub fn finish_function(&mut self, name: &str, params: Vec<Value>) {
        let blocks = std::mem::take(&mut self.blocks);
        self.functions.insert(
            name.to_owned(),
            Function {
                name: name.to_owned(),
                params,
                blocks,
            },
        );
        self.current_block = None;
    }

    pub fn build(self, entry: &str) -> Module {
        Module {
            functions: self.functions,
            entry: entry.to_owned(),
        }
    }

    // ---- Internal ----

    fn push(&mut self, inst: Inst) {
        let block = self.current_block.expect("no current block");
        self.blocks[block.0].insts.push(inst);
    }

    fn set_terminator(&mut self, term: Terminator) {
        let block = self.current_block.expect("no current block");
        self.blocks[block.0].terminator = term;
    }
}
