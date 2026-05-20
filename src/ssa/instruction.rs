use std::fmt;
use std::hash::{Hash, Hasher};

/// An SSA value — assigned exactly once. Carries its scalar type so
/// every use site knows the type without a side-table lookup.
/// Identity (Eq / Hash) is on `id` only; the type is carried data.
#[derive(Debug, Clone, Copy)]
pub struct Value {
    pub id: usize,
    pub ty: ScalarType,
}

impl PartialEq for Value {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}
impl Eq for Value {}
impl Hash for Value {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.id.hash(state);
    }
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "v{}", self.id)
    }
}

/// A basic block identifier.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct BlockId(pub usize);

impl fmt::Display for BlockId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "b{}", self.0)
    }
}

/// Scalar types that fit in a register.
///
/// `RcPtr` is a heap pointer that participates in reference counting:
/// every owning Load increments rc, every Store releases the previous
/// occupant, and Drop cascades through RcPtr-typed slots. `Ptr` is a
/// raw 8-byte heap index with no automatic rc semantics — reserved
/// for future raw-pointer use (currently unused; all heap pointers
/// flow as `RcPtr`).
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
    Ptr,
    RcPtr,
}

impl ScalarType {
    /// Byte width of this type when stored on the heap.
    pub fn byte_width(self) -> usize {
        match self {
            Self::I8 | Self::U8 => 1,
            Self::I16 | Self::U16 => 2,
            Self::I32 | Self::U32 => 4,
            Self::I64 | Self::U64 | Self::F64 | Self::Ptr | Self::RcPtr => 8,
        }
    }

    /// True for any heap-pointer type (Ptr or RcPtr). Most code that
    /// asked "is this a pointer?" today checks `== Ptr`; after the
    /// split, it should use this so RcPtr is handled too.
    pub fn is_heap_ptr(self) -> bool {
        matches!(self, Self::Ptr | Self::RcPtr)
    }
}

/// Compute a packed field layout sorted by size descending (stable).
/// Returns byte offsets indexed by original field position.
///
/// Fields of equal size keep their original order. Larger fields
/// come first, so no alignment padding is needed.
pub fn compute_layout(field_types: &[ScalarType]) -> Vec<usize> {
    let mut indices: Vec<usize> = (0..field_types.len()).collect();
    indices.sort_by(|&a, &b| field_types[b].byte_width().cmp(&field_types[a].byte_width()));
    let mut offsets = vec![0usize; field_types.len()];
    let mut pos = 0;
    for &i in &indices {
        offsets[i] = pos;
        pos += field_types[i].byte_width();
    }
    offsets
}

/// Total byte size of a packed layout.
pub fn total_byte_size(field_types: &[ScalarType]) -> usize {
    field_types.iter().map(|t| t.byte_width()).sum()
}

/// Binary operations on scalars.
#[derive(Debug, Clone, Copy)]
pub enum BinaryOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    And,
    Or,
    Xor,
    Shl,
    Shr,
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
/// `Store`, `StoreDyn`, `RcInc`, and `RcDec` are side-effecting and
/// produce no value.
#[derive(Debug, Clone)]
pub enum Inst {
    /// dest = constant (type comes from dest.ty).
    Const(Value, u64),
    /// dest = lhs op rhs (same scalar type).
    BinOp(Value, BinaryOp, Value, Value),
    /// dest = func(args...).
    Call(Value, String, Vec<Value>),
    /// dest = heap allocate `num_bytes` bytes (refcount starts at 1).
    Alloc(Value, usize),
    /// dest = heap allocate `num_bytes_val` bytes (runtime size).
    /// Used for `List` and other data whose size isn't known at lower time.
    AllocDyn(Value, Value),
    /// dest = read from `ptr` at static byte `offset`.
    ///
    /// When `dest.ty` is `RcPtr`, the loaded value is an *owning*
    /// reference: eval rc-inc's it so the local SSA value gets its
    /// own claim, independent of the slot's. The caller still needs
    /// to release it (`rc_dec`) at end of scope. Use `MoveOut` instead
    /// when the slot's claim should transfer to the local (no net rc
    /// change, slot left null).
    Load(Value, Value, usize),
    /// Write `val` to `ptr` at static byte `offset`. No result.
    ///
    /// For RcPtr-typed slots, eval auto-balances rc:
    /// - rc_decs the previous occupant (release slot's old claim).
    /// - rc_incs `val` (slot mints its own claim; caller still owns
    ///   the local). Net: rc(val) += 1, rc(old) -= 1.
    Store(Value, usize, Value),
    /// dest = read from `ptr` at dynamic slot index `idx_val`.
    /// Auto-rc semantics match `Load`.
    LoadDyn(Value, Value, Value),
    /// Write `val` to `ptr` at dynamic slot index `idx_val`. No result.
    /// Auto-rc semantics match `Store`.
    StoreDyn(Value, Value, Value),
    /// dest = read from `ptr` at static byte `offset`, then write null
    /// to the slot. No rc change — the slot's claim on the loaded
    /// value transfers to `dest`, and the slot now holds null (so
    /// cascade-free won't double-drop). Used for FBIP's "move out"
    /// pattern: take a child out of a parent so the parent's storage
    /// can be reused without the child being incidentally freed.
    MoveOut(Value, Value, usize),
    /// Increment reference count of `ptr`.
    RcInc(Value),
    /// Decrement reference count of `ptr`, free if zero. On free,
    /// cascade-decrements RcPtr-typed children (per the heap object's
    /// recorded `ptr_offsets`).
    RcDec(Value),
    /// dest = FBIP "reuse-or-clone": if `src.rc == 1`, return `src`
    /// directly (in-place mutation path, contents preserved). If
    /// `src.rc > 1`, allocate a fresh `size`-byte object and clone
    /// src's contents into it (with `rc_inc` on each Ptr child),
    /// then `rc_dec(src)`. Either way the caller gets a Ptr they
    /// own with rc=1; what differs is whether src's storage is
    /// reused or a copy was made. Used for functional updates
    /// (`list.set`, `record_update`, etc.) to enable in-place
    /// mutation when uniqueness allows.
    ReuseOrClone(Value, Value, usize),
    /// Dynamic-size version of `ReuseOrClone`. `size_val` carries
    /// the byte count at runtime. Used for data buffer reuse where
    /// list length isn't statically known.
    ReuseOrCloneDyn(Value, Value, Value),
    /// dest = pointer to a pre-allocated static object by index.
    /// The object lives in `Module::statics` and is never freed.
    StaticRef(Value, usize),
    /// dest = src converted to `dest`'s scalar type. Integer widening
    /// (e.g. `U8 → U64`) zero-extends; narrowing truncates. Source and
    /// destination must both be integer types — no float/Ptr coercion.
    Cast(Value, Value),
    /// dest = src reinterpreted as `dest`'s scalar type (same width).
    /// Pure register move at the machine level; no arithmetic. Used
    /// for `F64 ↔ U64` IEEE 754 bit access and similar.
    BitCast(Value, Value),
}

impl Inst {
    /// Returns the destination value, if any.
    pub fn dest(&self) -> Option<Value> {
        match self {
            Self::Const(v, _)
            | Self::BinOp(v, _, _, _)
            | Self::Call(v, _, _)
            | Self::Alloc(v, _)
            | Self::AllocDyn(v, _)
            | Self::Load(v, _, _)
            | Self::LoadDyn(v, _, _)
            | Self::MoveOut(v, _, _)
            | Self::ReuseOrClone(v, _, _)
            | Self::ReuseOrCloneDyn(v, _, _)
            | Self::StaticRef(v, _)
            | Self::Cast(v, _)
            | Self::BitCast(v, _) => Some(*v),
            Self::Store(..) | Self::StoreDyn(..) | Self::RcInc(_) | Self::RcDec(_) => None,
        }
    }

    /// Mutable reference to the destination slot, if any.
    pub fn dest_mut(&mut self) -> Option<&mut Value> {
        match self {
            Self::Const(v, _)
            | Self::BinOp(v, _, _, _)
            | Self::Call(v, _, _)
            | Self::Alloc(v, _)
            | Self::AllocDyn(v, _)
            | Self::Load(v, _, _)
            | Self::LoadDyn(v, _, _)
            | Self::MoveOut(v, _, _)
            | Self::ReuseOrClone(v, _, _)
            | Self::ReuseOrCloneDyn(v, _, _)
            | Self::StaticRef(v, _)
            | Self::Cast(v, _)
            | Self::BitCast(v, _) => Some(v),
            Self::Store(..) | Self::StoreDyn(..) | Self::RcInc(_) | Self::RcDec(_) => None,
        }
    }

    /// All values used as operands (not the destination).
    pub fn operands(&self) -> Vec<Value> {
        match self {
            Self::Const(..) | Self::Alloc(..) => vec![],
            Self::AllocDyn(_, size) => vec![*size],
            Self::BinOp(_, _, lhs, rhs) => vec![*lhs, *rhs],
            Self::Call(_, _, args) => args.clone(),
            Self::Load(_, ptr, _) => vec![*ptr],
            Self::Store(ptr, _, val) => vec![*ptr, *val],
            Self::LoadDyn(_, ptr, idx) => vec![*ptr, *idx],
            Self::StoreDyn(ptr, idx, val) => vec![*ptr, *idx, *val],
            Self::MoveOut(_, ptr, _) => vec![*ptr],
            Self::RcInc(v) | Self::RcDec(v) => vec![*v],
            Self::ReuseOrClone(_, src, _) => vec![*src],
            Self::ReuseOrCloneDyn(_, src, size) => vec![*src, *size],
            Self::StaticRef(..) => vec![],
            Self::Cast(_, src) | Self::BitCast(_, src) => vec![*src],
        }
    }

    /// Apply `f` to every operand slot in place (not the destination).
    pub fn map_operands_mut(&mut self, mut f: impl FnMut(&mut Value)) {
        match self {
            Self::Const(..) | Self::Alloc(..) | Self::StaticRef(..) => {}
            Self::AllocDyn(_, size) => f(size),
            Self::BinOp(_, _, lhs, rhs) => { f(lhs); f(rhs); }
            Self::Call(_, _, args) => args.iter_mut().for_each(&mut f),
            Self::Load(_, ptr, _) => f(ptr),
            Self::Store(ptr, _, val) => { f(ptr); f(val); }
            Self::LoadDyn(_, ptr, idx) => { f(ptr); f(idx); }
            Self::StoreDyn(ptr, idx, val) => { f(ptr); f(idx); f(val); }
            Self::MoveOut(_, ptr, _) => f(ptr),
            Self::RcInc(v) | Self::RcDec(v) => f(v),
            Self::ReuseOrClone(_, src, _) => f(src),
            Self::ReuseOrCloneDyn(_, src, size) => { f(src); f(size); }
            Self::Cast(_, src) | Self::BitCast(_, src) => f(src),
        }
    }
}

impl Terminator {
    /// All values used as operands in the terminator.
    pub fn operands(&self) -> Vec<Value> {
        match self {
            Self::Return(v) => vec![*v],
            Self::Jump(edge) => edge.args.clone(),
            Self::Branch {
                cond,
                then_edge,
                else_edge,
            } => {
                let mut vals = vec![*cond];
                vals.extend(&then_edge.args);
                vals.extend(&else_edge.args);
                vals
            }
            Self::SwitchInt {
                scrutinee,
                arms,
                default,
            } => {
                let mut vals = vec![*scrutinee];
                for (_, edge) in arms {
                    vals.extend(&edge.args);
                }
                if let Some(edge) = default {
                    vals.extend(&edge.args);
                }
                vals
            }
        }
    }

    /// Apply `f` to every value operand in place (including edge args).
    pub fn map_operands_mut(&mut self, mut f: impl FnMut(&mut Value)) {
        match self {
            Self::Return(v) => f(v),
            Self::Jump(edge) => edge.args.iter_mut().for_each(&mut f),
            Self::Branch { cond, then_edge, else_edge } => {
                f(cond);
                then_edge.args.iter_mut().for_each(&mut f);
                else_edge.args.iter_mut().for_each(&mut f);
            }
            Self::SwitchInt { scrutinee, arms, default } => {
                f(scrutinee);
                for (_, edge) in arms {
                    edge.args.iter_mut().for_each(&mut f);
                }
                if let Some(edge) = default {
                    edge.args.iter_mut().for_each(&mut f);
                }
            }
        }
    }

    /// All successor edges.
    pub fn successors(&self) -> Vec<&BlockEdge> {
        match self {
            Self::Return(_) => vec![],
            Self::Jump(edge) => vec![edge],
            Self::Branch { then_edge, else_edge, .. } => {
                vec![then_edge, else_edge]
            }
            Self::SwitchInt { arms, default, .. } => {
                let mut succs: Vec<&BlockEdge> =
                    arms.iter().map(|(_, edge)| edge).collect();
                if let Some(edge) = default {
                    succs.push(edge);
                }
                succs
            }
        }
    }
}

/// A control flow edge: target block plus the values passed as block arguments.
#[derive(Debug, Clone)]
pub struct BlockEdge {
    pub target: BlockId,
    pub args: Vec<Value>,
}

/// How a basic block ends.
#[derive(Debug, Clone)]
pub enum Terminator {
    /// Return a value from the function.
    Return(Value),
    /// Unconditional jump with block arguments.
    Jump(BlockEdge),
    /// Conditional branch: nonzero → then, zero → else.
    Branch {
        cond: Value,
        then_edge: BlockEdge,
        else_edge: BlockEdge,
    },
    /// Multi-way switch on an integer tag value.
    SwitchInt {
        scrutinee: Value,
        arms: Vec<(u64, BlockEdge)>,
        default: Option<BlockEdge>,
    },
}
