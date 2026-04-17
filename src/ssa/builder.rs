use super::{Block, Function, Module};
use crate::ssa::instruction::{BinaryOp, BlockId, Inst, ScalarType, Terminator, Value};
use std::collections::{BTreeMap, HashMap};

/// Coercion direction between Agg(n) and Ptr at terminator edges.
enum CoerceDir {
    /// Pack register values into a heap object.
    AggToPtr(usize),
    /// Load heap object fields into a pack.
    PtrToAgg(usize),
}

/// `jump`/`branch`/`switch_int`/`ret` coerce arguments flowing
/// between `Agg(n)` and `Ptr` representations. Boxing (Agg→Ptr)
/// allocates a heap object and stores fields. Unboxing (Ptr→Agg)
/// loads fields from a heap object into a Pack.
fn coerce_kind(src: ScalarType, dst: ScalarType) -> Option<CoerceDir> {
    match (src, dst) {
        (ScalarType::Agg(n), ScalarType::Ptr) => Some(CoerceDir::AggToPtr(n)),
        (ScalarType::Ptr, ScalarType::Agg(n)) => Some(CoerceDir::PtrToAgg(n)),
        _ => None,
    }
}

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
    /// Function parameters, in declaration order. Types live in
    /// `Builder::value_types`. Populated via `add_func_param`.
    pub params: Vec<Value>,
    /// Function return type, set before lowering the body so `ret`
    /// can coerce the returned value if its type doesn't match.
    /// `None` during the brief window between `new` and `start_function`.
    pub return_type: Option<ScalarType>,
}

impl FuncBuilder {
    pub fn new() -> Self {
        Self {
            pending: BTreeMap::new(),
            finished: BTreeMap::new(),
            next_block: 0,
            params: Vec::new(),
            return_type: None,
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

    /// Allocate a fresh typed SSA value. Every value must have a type
    /// — pass it at creation so the invariant holds by construction.
    fn fresh_value(&mut self, ty: ScalarType) -> Value {
        let v = Value(self.next_value);
        self.next_value += 1;
        self.value_types.insert(v, ty);
        v
    }

    /// Add a function parameter with the given type. Returns the
    /// Value. The builder tracks params so `finish_function` doesn't
    /// need the caller to pass them in separately.
    pub fn add_func_param(&mut self, ty: ScalarType) -> Value {
        let v = self.fresh_value(ty);
        self.func.params.push(v);
        v
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
        let v = self.fresh_value(ty);
        self.func.pending.get_mut(&block)
            .expect("add_block_param on non-pending block")
            .params.push(v);
        v
    }

    // ---- Constants ----

    pub fn const_i64(&mut self, n: i64) -> Value {
        let v = self.fresh_value(ScalarType::I64);
        self.push(Inst::Const(v, ScalarType::I64, n as u64));
        v
    }

    pub fn const_u64(&mut self, n: u64) -> Value {
        let v = self.fresh_value(ScalarType::U64);
        self.push(Inst::Const(v, ScalarType::U64, n));
        v
    }

    pub fn const_f64(&mut self, n: f64) -> Value {
        let v = self.fresh_value(ScalarType::F64);
        self.push(Inst::Const(v, ScalarType::F64, n.to_bits()));
        v
    }

    pub fn const_u8(&mut self, n: u8) -> Value {
        let v = self.fresh_value(ScalarType::U8);
        self.push(Inst::Const(v, ScalarType::U8, u64::from(n)));
        v
    }

    pub fn const_i8(&mut self, n: i8) -> Value {
        let v = self.fresh_value(ScalarType::I8);
        self.push(Inst::Const(v, ScalarType::I8, n as u64));
        v
    }

    pub fn const_u16(&mut self, n: u16) -> Value {
        let v = self.fresh_value(ScalarType::U16);
        self.push(Inst::Const(v, ScalarType::U16, u64::from(n)));
        v
    }

    pub fn const_i16(&mut self, n: i16) -> Value {
        let v = self.fresh_value(ScalarType::I16);
        self.push(Inst::Const(v, ScalarType::I16, n as u64));
        v
    }

    pub fn const_u32(&mut self, n: u32) -> Value {
        let v = self.fresh_value(ScalarType::U32);
        self.push(Inst::Const(v, ScalarType::U32, u64::from(n)));
        v
    }

    pub fn const_i32(&mut self, n: i32) -> Value {
        let v = self.fresh_value(ScalarType::I32);
        self.push(Inst::Const(v, ScalarType::I32, n as u64));
        v
    }

    pub fn const_ptr_null(&mut self) -> Value {
        let v = self.fresh_value(ScalarType::Ptr);
        self.push(Inst::Const(v, ScalarType::Ptr, 0));
        v
    }

    // ---- Arithmetic ----

    pub fn binop(&mut self, op: BinaryOp, lhs: Value, rhs: Value, ty: ScalarType) -> Value {
        let v = self.fresh_value(ty);
        self.push(Inst::BinOp(v, op, lhs, rhs));
        v
    }

    // ---- Calls ----

    pub fn call(&mut self, func: &str, args: Vec<Value>, ret_ty: ScalarType) -> Value {
        let has_agg = args.iter().any(|a| matches!(self.value_types.get(a), Some(ScalarType::Agg(_))));
        let args = if has_agg {
            args.into_iter()
                .map(|a| self.coerce_to(a, ScalarType::Ptr))
                .collect()
        } else {
            args
        };
        let v = self.fresh_value(ret_ty);
        self.push(Inst::Call(v, func.to_owned(), args));
        v
    }

    // ---- Memory ----

    pub fn alloc(&mut self, size: usize) -> Value {
        let v = self.fresh_value(ScalarType::Ptr);
        self.push(Inst::Alloc(v, size));
        v
    }

    pub fn alloc_dyn(&mut self, size_val: Value) -> Value {
        let v = self.fresh_value(ScalarType::Ptr);
        self.push(Inst::AllocDyn(v, size_val));
        v
    }

    pub fn load(&mut self, ptr: Value, offset: usize, ty: ScalarType) -> Value {
        let v = self.fresh_value(ty);
        self.push(Inst::Load(v, ptr, offset));
        v
    }

    pub fn store(&mut self, ptr: Value, offset: usize, val: Value) {
        self.push(Inst::Store(ptr, offset, val));
    }

    pub fn load_dyn(&mut self, ptr: Value, idx: Value, ty: ScalarType) -> Value {
        let v = self.fresh_value(ty);
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

    // ---- Aggregates ----

    pub fn pack(&mut self, fields: Vec<Value>) -> Value {
        let n = fields.len();
        let v = self.fresh_value(ScalarType::Agg(n));
        self.push(Inst::Pack(v, fields));
        v
    }

    pub fn extract(&mut self, agg: Value, index: usize, ty: ScalarType) -> Value {
        let v = self.fresh_value(ty);
        self.push(Inst::Extract(v, agg, index));
        v
    }

    pub fn insert(&mut self, agg: Value, index: usize, val: Value) -> Value {
        let agg_ty = self.value_types.get(&agg).copied().unwrap_or(ScalarType::Ptr);
        let v = self.fresh_value(agg_ty);
        self.push(Inst::Insert(v, agg, index, val));
        v
    }

    // ---- Terminators ----
    //
    // Each terminator method finalizes the current block: it takes the
    // pending block, combines it with the terminator to produce a
    // complete Block, and moves it into the finished map. Args are
    // coerced in-line for `Agg→Ptr` edges so the emitted IR matches
    // declared types without needing a later cleanup pass.

    pub fn set_return_type(&mut self, ty: ScalarType) {
        self.func.return_type = Some(ty);
    }

    pub fn ret(&mut self, value: Value) {
        let ret_ty = self.func.return_type;
        let coerced = match ret_ty {
            Some(ty) => self.coerce_to(value, ty),
            None => value,
        };
        self.seal(Terminator::Return(coerced));
    }

    pub fn jump(&mut self, target: BlockId, args: Vec<Value>) {
        let args = self.coerce_args(target, args);
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
        let then_args = self.coerce_args(then_block, then_args);
        let else_args = self.coerce_args(else_block, else_args);
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
        let arms = arms
            .into_iter()
            .map(|(v, bid, args)| (v, bid, self.coerce_args(bid, args)))
            .collect();
        let default = default.map(|(bid, args)| (bid, self.coerce_args(bid, args)));
        self.seal(Terminator::SwitchInt {
            scrutinee,
            arms,
            default,
        });
    }

    fn coerce_args(&mut self, target: BlockId, args: Vec<Value>) -> Vec<Value> {
        let param_tys = self.block_param_types(target);
        if param_tys.len() != args.len() {
            // Dead fallthrough in match lowering passes mismatched
            // counts on purpose. Let the validator flag it rather
            // than guessing which positions to coerce.
            return args;
        }
        args.into_iter()
            .zip(param_tys)
            .map(|(v, ty)| self.coerce_to(v, ty))
            .collect()
    }

    fn block_param_types(&self, bid: BlockId) -> Vec<ScalarType> {
        let params: &[Value] = if let Some(b) = self.func.pending.get(&bid) {
            &b.params
        } else if let Some(b) = self.func.finished.get(&bid) {
            &b.params
        } else {
            return Vec::new();
        };
        params
            .iter()
            .map(|p| *self.value_types.get(p).unwrap_or(&ScalarType::Ptr))
            .collect()
    }

    fn coerce_to(&mut self, value: Value, dst_ty: ScalarType) -> Value {
        let src_ty = match self.value_types.get(&value) {
            Some(t) => *t,
            None => return value,
        };
        let Some(dir) = coerce_kind(src_ty, dst_ty) else {
            return value;
        };
        match dir {
            CoerceDir::AggToPtr(n) => {
                let ptr = self.fresh_value(ScalarType::Ptr);
                self.push(Inst::Alloc(ptr, n));
                for i in 0..n {
                    let field = self.fresh_value(ScalarType::U64);
                    self.push(Inst::Extract(field, value, i));
                    self.push(Inst::Store(ptr, i, field));
                }
                ptr
            }
            CoerceDir::PtrToAgg(n) => {
                let mut fields = Vec::with_capacity(n);
                for i in 0..n {
                    let field = self.fresh_value(ScalarType::U64);
                    self.push(Inst::Load(field, value, i));
                    fields.push(field);
                }
                self.pack(fields)
            }
        }
    }

    // ---- Function building ----

    /// Finalize the current function. Params are the ones added via
    /// `add_func_param` (in order); their types come from
    /// `value_types`. The caller only supplies the return type.
    pub fn finish_function(&mut self, name: &str, return_type: ScalarType) {
        assert!(
            self.func.pending.is_empty(),
            "finish_function({name}): {} blocks still pending terminators",
            self.func.pending.len(),
        );
        let fb = std::mem::replace(&mut self.func, FuncBuilder::new());
        let declared_ret = fb.return_type.unwrap_or(return_type);
        debug_assert!(
            declared_ret == return_type,
            "finish_function({name}): return type mismatch (set_return_type={declared_ret:?}, finish_function arg={return_type:?})"
        );
        let value_types = std::mem::take(&mut self.value_types);
        let param_types = fb.params
            .iter()
            .map(|v| {
                *value_types.get(v).unwrap_or_else(|| {
                    panic!("finish_function({name}): param {v:?} has no type")
                })
            })
            .collect();
        self.functions.insert(
            name.to_owned(),
            Function {
                name: name.to_owned(),
                params: fb.params,
                blocks: fb.finished,
                param_types,
                return_type: declared_ret,
                value_types,
                entry: BlockId(0),
                next_block: fb.next_block,
                num_values: 0,
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
