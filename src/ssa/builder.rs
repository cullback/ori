use super::{Block, Function, Module};
use crate::ssa::instruction::{BinaryOp, BlockId, Inst, Terminator, Value};
use std::collections::HashMap;

/// Builds SSA functions and modules incrementally.
pub struct Builder {
    next_value: usize,
    pub blocks: Vec<Block>,
    pub current_block: Option<BlockId>,
    functions: HashMap<String, Function>,
    data: Vec<u8>,
}

impl Builder {
    pub fn new() -> Self {
        Self {
            next_value: 0,
            blocks: Vec::new(),
            current_block: None,
            functions: HashMap::new(),
            data: Vec::new(),
        }
    }

    /// Allocate a fresh SSA value.
    pub const fn fresh_value(&mut self) -> Value {
        let v = Value(self.next_value);
        self.next_value += 1;
        v
    }

    /// Create a new basic block, returning its id.
    pub fn create_block(&mut self) -> BlockId {
        let id = BlockId(self.blocks.len());
        self.blocks.push(Block {
            params: Vec::new(),
            insts: Vec::new(),
            terminator: Terminator::None,
        });
        id
    }

    /// Set the current block for instruction emission.
    pub const fn switch_to(&mut self, block: BlockId) {
        self.current_block = Some(block);
    }

    /// Add a parameter to a block, returning the value it binds.
    pub fn add_block_param(&mut self, block: BlockId) -> Value {
        let v = self.fresh_value();
        self.blocks[block.0].params.push(v);
        v
    }

    // ---- Instruction builders ----

    pub fn const_i64(&mut self, n: i64) -> Value {
        let v = self.fresh_value();
        self.push(Inst::Const(v, n));
        v
    }

    pub fn const_u64(&mut self, n: u64) -> Value {
        let v = self.fresh_value();
        self.push(Inst::ConstU64(v, n));
        v
    }

    pub fn const_f64(&mut self, n: f64) -> Value {
        let v = self.fresh_value();
        self.push(Inst::ConstF64(v, n));
        v
    }

    pub fn const_u8(&mut self, n: u8) -> Value {
        let v = self.fresh_value();
        self.push(Inst::ConstU8(v, n));
        v
    }

    pub fn const_i8(&mut self, n: i8) -> Value {
        let v = self.fresh_value();
        self.push(Inst::ConstI8(v, n));
        v
    }

    pub fn binop(&mut self, op: BinaryOp, lhs: Value, rhs: Value) -> Value {
        let v = self.fresh_value();
        self.push(Inst::BinOp(v, op, lhs, rhs));
        v
    }

    pub fn call(&mut self, func: &str, args: Vec<Value>) -> Value {
        let v = self.fresh_value();
        self.push(Inst::Call(v, func.to_owned(), args));
        v
    }

    pub fn construct(&mut self, tag: &str, fields: Vec<Value>) -> Value {
        let v = self.fresh_value();
        self.push(Inst::Construct(v, tag.to_owned(), fields));
        v
    }

    pub fn record_new(&mut self, fields: Vec<(String, Value)>) -> Value {
        let v = self.fresh_value();
        self.push(Inst::RecordNew(v, fields));
        v
    }

    pub fn field_get(&mut self, record: Value, field: &str) -> Value {
        let v = self.fresh_value();
        self.push(Inst::FieldGet(v, record, field.to_owned()));
        v
    }

    pub fn list_new(&mut self, elements: Vec<Value>) -> Value {
        let v = self.fresh_value();
        self.push(Inst::ListNew(v, elements));
        v
    }

    pub fn list_get(&mut self, list: Value, index: Value) -> Value {
        let v = self.fresh_value();
        self.push(Inst::ListGet(v, list, index));
        v
    }

    pub fn list_set(&mut self, list: Value, index: Value, elem: Value) -> Value {
        let v = self.fresh_value();
        self.push(Inst::ListSet(v, list, index, elem));
        v
    }

    pub fn list_append(&mut self, list: Value, elem: Value) -> Value {
        let v = self.fresh_value();
        self.push(Inst::ListAppend(v, list, elem));
        v
    }

    pub fn list_len(&mut self, list: Value) -> Value {
        let v = self.fresh_value();
        self.push(Inst::ListLen(v, list));
        v
    }

    pub fn num_to_str(&mut self, num: Value) -> Value {
        let v = self.fresh_value();
        self.push(Inst::NumToStr(v, num));
        v
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

    pub fn switch(&mut self, scrutinee: Value, arms: Vec<(String, BlockId)>) {
        self.set_terminator(Terminator::Switch { scrutinee, arms });
    }

    // ---- Function & module building ----

    /// Finish the current function, collecting its blocks.
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

    /// Add data to the static data section, returning the offset.
    pub fn add_data(&mut self, bytes: &[u8]) -> usize {
        let offset = self.data.len();
        self.data.extend_from_slice(bytes);
        offset
    }

    /// Build the final module.
    pub fn build(self, entry: &str) -> Module {
        Module {
            functions: self.functions,
            entry: entry.to_owned(),
            data: self.data,
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
