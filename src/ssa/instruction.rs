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
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ScalarType {
    I8,
    U8,
    I16,
    U16,
    I32,
    U32,
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
    Lt,
    Le,
    Gt,
    Ge,
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
    /// dest = heap allocate `num_slots` scalar slots (refcount starts at 1).
    Alloc(Value, usize),
    /// dest = read from `ptr` at static slot `offset`.
    Load(Value, Value, usize),
    /// Write `val` to `ptr` at static slot `offset`. No result.
    Store(Value, usize, Value),
    /// dest = read from `ptr` at dynamic slot index `idx_val`.
    LoadDyn(Value, Value, Value),
    /// Write `val` to `ptr` at dynamic slot index `idx_val`. No result.
    StoreDyn(Value, Value, Value),
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
            | Self::Load(v, _, _)
            | Self::LoadDyn(v, _, _) => Some(*v),
            Self::Store(..) | Self::StoreDyn(..) | Self::RcInc(_) | Self::RcDec(_) => None,
        }
    }

    /// All values used as operands (not the destination).
    pub fn operands(&self) -> Vec<Value> {
        match self {
            Self::Const(..) | Self::Alloc(..) => vec![],
            Self::BinOp(_, _, lhs, rhs) => vec![*lhs, *rhs],
            Self::Call(_, _, args) => args.clone(),
            Self::Load(_, ptr, _) => vec![*ptr],
            Self::Store(ptr, _, val) => vec![*ptr, *val],
            Self::LoadDyn(_, ptr, idx) => vec![*ptr, *idx],
            Self::StoreDyn(ptr, idx, val) => vec![*ptr, *idx, *val],
            Self::RcInc(v) | Self::RcDec(v) => vec![*v],
        }
    }
}

impl Terminator {
    /// All values used as operands in the terminator.
    pub fn operands(&self) -> Vec<Value> {
        match self {
            Self::None => vec![],
            Self::Return(v) => vec![*v],
            Self::Jump(_, args) => args.clone(),
            Self::Branch {
                cond,
                then_args,
                else_args,
                ..
            } => {
                let mut vals = vec![*cond];
                vals.extend(then_args);
                vals.extend(else_args);
                vals
            }
            Self::SwitchInt {
                scrutinee,
                arms,
                default,
            } => {
                let mut vals = vec![*scrutinee];
                for (_, _, args) in arms {
                    vals.extend(args);
                }
                if let Some((_, args)) = default {
                    vals.extend(args);
                }
                vals
            }
        }
    }

    /// Successor blocks and the values passed to each.
    pub fn successors(&self) -> Vec<(BlockId, &[Value])> {
        match self {
            Self::None | Self::Return(_) => vec![],
            Self::Jump(target, args) => vec![(*target, args)],
            Self::Branch {
                then_block,
                then_args,
                else_block,
                else_args,
                ..
            } => vec![(*then_block, then_args), (*else_block, else_args)],
            Self::SwitchInt { arms, default, .. } => {
                let mut succs: Vec<(BlockId, &[Value])> =
                    arms.iter().map(|(_, b, args)| (*b, args.as_slice())).collect();
                if let Some((b, args)) = default {
                    succs.push((*b, args));
                }
                succs
            }
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
