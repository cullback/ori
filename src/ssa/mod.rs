mod builder;
pub mod const_eval;
mod display;
pub mod eval;
pub mod inline;
mod instruction;
pub mod lower;
pub mod opt;
pub mod rc;
pub mod static_promote;

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

/// A function in the SSA IR. Blocks are stored in a BTreeMap keyed by
/// BlockId so that insertion and removal don't invalidate existing IDs.
#[derive(Debug, Clone)]
pub struct Function {
    pub name: String,
    pub params: Vec<Value>,
    pub blocks: std::collections::BTreeMap<BlockId, Block>,
    pub param_types: Vec<ScalarType>,
    pub return_type: ScalarType,
    pub value_types: std::collections::HashMap<Value, ScalarType>,
    /// Entry block ID (always the first block created).
    pub entry: BlockId,
    /// Counter for generating fresh BlockIds.
    pub next_block: usize,
    /// Number of SSA values (for register file sizing). Set by `cache_num_values`.
    pub num_values: usize,
}

/// A static (permanent) heap object. Allocated once before execution,
/// never freed (sentinel refcount). Used for string/list literals
/// whose contents are known at compile time.
#[derive(Debug, Clone)]
pub struct StaticObject {
    pub slots: Vec<StaticSlot>,
}

/// A slot value in a static object.
#[derive(Debug, Clone)]
pub enum StaticSlot {
    U8(u8),
    U32(u32),
    U64(u64),
    I64(i64),
    /// Reference to another static object by index.
    StaticPtr(usize),
}

impl Function {
    /// Compute the register file size (max Value index + 1).
    pub fn compute_num_values(&mut self) {
        let from_types = self.value_types.keys().map(|v| v.0 + 1).max().unwrap_or(0);
        let from_params = self.params.iter().map(|v| v.0 + 1).max().unwrap_or(0);
        let from_blocks = self.blocks.values()
            .flat_map(|b| b.params.iter())
            .map(|v| v.0 + 1)
            .max()
            .unwrap_or(0);
        self.num_values = from_types.max(from_params).max(from_blocks);
    }
}

/// Top-level SSA module — all functions plus static data.
#[derive(Debug)]
pub struct Module {
    pub functions: std::collections::HashMap<String, Function>,
    pub statics: Vec<StaticObject>,
    pub entry: String,
}
