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

/// Scalar types that fit in a register.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ScalarType {
    I8,
    U8,
    I64,
    U64,
    F64,
    Bool,
    Ptr,
}

/// Binary operations on scalars.
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

/// An SSA instruction.
///
/// Instructions that produce a value have it as their first field.
/// `Store`, `RcInc`, and `RcDec` are side-effecting and produce no value.
#[derive(Debug, Clone)]
pub enum Inst {
    /// dest = typed constant.
    Const(Value, ScalarType, u64),
    /// dest = lhs op rhs (same scalar type).
    BinOp(Value, BinaryOp, Value, Value),
    /// dest = func(args...).
    Call(Value, String, Vec<Value>),
    /// dest = heap allocate `size` bytes (refcount starts at 1).
    Alloc(Value, usize),
    /// dest = read `ty` from `ptr + offset`.
    Load(Value, ScalarType, Value, usize),
    /// Write `val` to `ptr + offset`. No result.
    Store(Value, usize, Value),
    /// Increment reference count of `ptr`.
    RcInc(Value),
    /// Decrement reference count of `ptr`, free if zero.
    RcDec(Value),
}

impl Inst {
    /// Returns the destination value, if any.
    pub const fn dest(&self) -> Option<Value> {
        match self {
            Self::Const(v, _, _)
            | Self::BinOp(v, _, _, _)
            | Self::Call(v, _, _)
            | Self::Alloc(v, _)
            | Self::Load(v, _, _, _) => Some(*v),
            Self::Store(..) | Self::RcInc(_) | Self::RcDec(_) => None,
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
    /// Conditional branch on a Bool value.
    Branch {
        cond: Value,
        then_block: BlockId,
        then_args: Vec<Value>,
        else_block: BlockId,
        else_args: Vec<Value>,
    },
    /// Multi-way switch on an integer tag value.
    SwitchInt {
        scrutinee: Value,
        arms: Vec<(u64, BlockId, Vec<Value>)>,
        default: Option<(BlockId, Vec<Value>)>,
    },
}
