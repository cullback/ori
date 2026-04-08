mod builder;
mod display;
pub mod eval;
mod instruction;
pub mod lower;

#[allow(unused_imports)]
pub use builder::Builder;
#[allow(unused_imports)]
pub use instruction::{BinaryOp, BlockId, Inst, ScalarType, Terminator, Value};

/// An SSA basic block with parameters, instructions, and a terminator.
#[derive(Debug, Clone)]
pub struct Block {
    pub params: Vec<Value>,
    pub insts: Vec<Inst>,
    pub terminator: Terminator,
}

/// A function in the SSA IR.
#[derive(Debug, Clone)]
pub struct Function {
    pub name: String,
    pub params: Vec<Value>,
    pub blocks: Vec<Block>,
}

/// Top-level SSA module — all functions.
#[derive(Debug)]
pub struct Module {
    pub functions: std::collections::HashMap<String, Function>,
    pub entry: String,
}
