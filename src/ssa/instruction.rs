use std::fmt;

/// An SSA value — assigned exactly once.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Value(pub usize);

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "v{}", self.0)
    }
}

/// A basic block identifier.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct BlockId(pub usize);

impl fmt::Display for BlockId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "b{}", self.0)
    }
}

/// Binary operations.
#[derive(Debug, Clone, Copy)]
pub enum BinaryOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    Eq,
    Neq,
    Max,
}

/// An SSA instruction. Each produces at most one value.
#[derive(Debug, Clone)]
pub enum Inst {
    /// dest = constant i64
    Const(Value, i64),
    /// dest = constant u64
    ConstU64(Value, u64),
    /// dest = constant f64
    ConstF64(Value, f64),
    /// dest = constant u8
    ConstU8(Value, u8),
    /// dest = constant i8
    ConstI8(Value, i8),
    /// dest = lhs op rhs
    BinOp(Value, BinaryOp, Value, Value),
    /// dest = func(args...)
    Call(Value, String, Vec<Value>),
    /// dest = construct tag variant with fields
    Construct(Value, String, Vec<Value>),
    /// dest = record from named fields
    RecordNew(Value, Vec<(String, Value)>),
    /// dest = record.field
    FieldGet(Value, Value, String),
    /// dest = list from elements
    ListNew(Value, Vec<Value>),
    /// dest = list[index]
    ListGet(Value, Value, Value),
    /// dest = list with element at index replaced
    ListSet(Value, Value, Value, Value),
    /// dest = list with element appended
    ListAppend(Value, Value, Value),
    /// dest = list length
    ListLen(Value, Value),
    /// dest = number converted to string (Str = List(U8))
    NumToStr(Value, Value),
}

impl Inst {
    pub const fn dest(&self) -> Value {
        match self {
            Self::Const(v, _)
            | Self::ConstU64(v, _)
            | Self::ConstF64(v, _)
            | Self::ConstU8(v, _)
            | Self::ConstI8(v, _)
            | Self::BinOp(v, _, _, _)
            | Self::Call(v, _, _)
            | Self::Construct(v, _, _)
            | Self::RecordNew(v, _)
            | Self::FieldGet(v, _, _)
            | Self::ListNew(v, _)
            | Self::ListGet(v, _, _)
            | Self::ListSet(v, _, _, _)
            | Self::ListAppend(v, _, _)
            | Self::ListLen(v, _)
            | Self::NumToStr(v, _) => *v,
        }
    }
}

/// How a basic block ends.
#[derive(Debug, Clone)]
pub enum Terminator {
    /// Block is incomplete.
    None,
    /// Return a value from the function.
    Return(Value),
    /// Unconditional jump with block arguments.
    Jump(BlockId, Vec<Value>),
    /// Conditional branch: if cond then (block, args) else (block, args).
    Branch {
        cond: Value,
        then_block: BlockId,
        then_args: Vec<Value>,
        else_block: BlockId,
        else_args: Vec<Value>,
    },
    /// Multi-way dispatch on a constructed value's tag.
    /// Fields are passed as block parameters to the target block.
    Switch {
        scrutinee: Value,
        arms: Vec<(String, BlockId)>,
    },
}
