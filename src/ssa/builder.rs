use super::{Block, Function, Module};
use crate::ssa::instruction::{BinaryOp, BlockEdge, BlockId, Inst, ScalarType, Terminator, Value};
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
    /// Function parameters, in declaration order. Each Value carries
    /// its type. Populated via `add_func_param`.
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
    /// Per-block store-load forwarding cache: maps (ptr, byte_offset)
    /// to the last value stored there, so subsequent `load()` calls
    /// can return that value directly without emitting a Load.
    ///
    /// Cleared on `switch_to(block)` (block boundary), on `call()`
    /// (callee may mutate), and on `store_dyn()` for the given ptr
    /// (dynamic offset unknown). `reuse_or_clone()` propagates the
    /// src's entries to its dest (the primitive preserves contents).
    recent_stores: HashMap<(Value, usize), Value>,
}

impl Builder {
    pub fn new() -> Self {
        Self {
            next_value: 0,
            func: FuncBuilder::new(),
            current_block: None,
            functions: HashMap::new(),
            recent_stores: HashMap::new(),
        }
    }

    /// Allocate a fresh typed SSA value.
    fn fresh_value(&mut self, ty: ScalarType) -> Value {
        let v = Value { id: self.next_value, ty };
        self.next_value += 1;
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

    pub fn switch_to(&mut self, block: BlockId) {
        self.current_block = Some(block);
        // Forwarding cache is per-block — crossing a block boundary
        // means values stored before may not be in the slot anymore
        // (other predecessors of `block` may have written different
        // values, or the stores may not dominate this block).
        self.recent_stores.clear();
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
        self.push(Inst::Const(v, n as u64));
        v
    }

    pub fn const_u64(&mut self, n: u64) -> Value {
        let v = self.fresh_value(ScalarType::U64);
        self.push(Inst::Const(v, n));
        v
    }

    pub fn const_f64(&mut self, n: f64) -> Value {
        let v = self.fresh_value(ScalarType::F64);
        self.push(Inst::Const(v, n.to_bits()));
        v
    }

    pub fn const_u8(&mut self, n: u8) -> Value {
        let v = self.fresh_value(ScalarType::U8);
        self.push(Inst::Const(v, u64::from(n)));
        v
    }

    pub fn const_i8(&mut self, n: i8) -> Value {
        let v = self.fresh_value(ScalarType::I8);
        self.push(Inst::Const(v, n as u64));
        v
    }

    pub fn const_u16(&mut self, n: u16) -> Value {
        let v = self.fresh_value(ScalarType::U16);
        self.push(Inst::Const(v, u64::from(n)));
        v
    }

    pub fn const_i16(&mut self, n: i16) -> Value {
        let v = self.fresh_value(ScalarType::I16);
        self.push(Inst::Const(v, n as u64));
        v
    }

    pub fn const_u32(&mut self, n: u32) -> Value {
        let v = self.fresh_value(ScalarType::U32);
        self.push(Inst::Const(v, u64::from(n)));
        v
    }

    pub fn const_i32(&mut self, n: i32) -> Value {
        let v = self.fresh_value(ScalarType::I32);
        self.push(Inst::Const(v, n as u64));
        v
    }

    pub fn const_ptr_null(&mut self) -> Value {
        let v = self.fresh_value(ScalarType::RcPtr);
        self.push(Inst::Const(v, 0));
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
        let v = self.fresh_value(ret_ty);
        self.push(Inst::Call(v, func.to_owned(), args));
        // Callee may mutate any heap object reachable via its args.
        // Conservative: clear all forwarding entries.
        self.recent_stores.clear();
        v
    }

    // ---- Memory ----

    pub fn alloc(&mut self, size: usize) -> Value {
        let v = self.fresh_value(ScalarType::RcPtr);
        self.push(Inst::Alloc(v, size));
        v
    }

    pub fn alloc_dyn(&mut self, size_val: Value) -> Value {
        let v = self.fresh_value(ScalarType::RcPtr);
        self.push(Inst::AllocDyn(v, size_val));
        v
    }

    /// FBIP `reuse_or_clone`: returns a RcPtr the caller owns at rc=1.
    /// In-place if `src.rc == 1` (contents preserved), cloned + src
    /// `rc_dec`'d otherwise. Consumes the caller's owning slot on
    /// `src`.
    pub fn reuse_or_clone(&mut self, src: Value, size: usize) -> Value {
        let v = self.fresh_value(ScalarType::RcPtr);
        self.push(Inst::ReuseOrClone(v, src, size));
        // The primitive preserves contents in both paths (in-place
        // literally; clone copies). Propagate src's forwarding
        // entries to the result so subsequent loads through `v`
        // can forward to the same values.
        self.propagate_recent_stores(src, v);
        v
    }

    pub fn reuse_or_clone_dyn(&mut self, src: Value, size_val: Value) -> Value {
        let v = self.fresh_value(ScalarType::RcPtr);
        self.push(Inst::ReuseOrCloneDyn(v, src, size_val));
        self.propagate_recent_stores(src, v);
        v
    }

    fn propagate_recent_stores(&mut self, src: Value, dest: Value) {
        let propagations: Vec<(usize, Value)> = self
            .recent_stores
            .iter()
            .filter_map(|((p, off), v)| (*p == src).then_some((*off, *v)))
            .collect();
        for (off, v) in propagations {
            self.recent_stores.insert((dest, off), v);
        }
    }

    pub fn load(&mut self, ptr: Value, offset: usize, ty: ScalarType) -> Value {
        // Store-load forwarding: if this slot was just stored to with
        // a value of matching type, return that value directly. For
        // RcPtr loads the auto-rc_inc would normally mint a fresh
        // owning ref, so emit one explicitly when forwarding to keep
        // rc accounting balanced.
        if let Some(&stored) = self.recent_stores.get(&(ptr, offset)) {
            if stored.ty == ty {
                if ty == ScalarType::RcPtr {
                    self.push(Inst::RcInc(stored));
                }
                return stored;
            }
        }
        let v = self.fresh_value(ty);
        self.push(Inst::Load(v, ptr, offset));
        v
    }

    pub fn store(&mut self, ptr: Value, offset: usize, val: Value) {
        self.push(Inst::Store(ptr, offset, val));
        self.recent_stores.insert((ptr, offset), val);
    }

    pub fn load_dyn(&mut self, ptr: Value, idx: Value, ty: ScalarType) -> Value {
        let v = self.fresh_value(ty);
        self.push(Inst::LoadDyn(v, ptr, idx));
        v
    }

    pub fn store_dyn(&mut self, ptr: Value, idx: Value, val: Value) {
        self.push(Inst::StoreDyn(ptr, idx, val));
        // Dynamic offset — we don't know which slot was written.
        // Clear all forwarding for this ptr to be safe.
        self.recent_stores.retain(|(p, _), _| *p != ptr);
    }

    /// Move a value out of a slot: load it, write null back. No rc
    /// change — the slot's claim transfers to the returned local.
    /// Used in FBIP patterns to take a child out of a parent before
    /// reusing the parent's storage.
    pub fn move_out(&mut self, ptr: Value, offset: usize, ty: ScalarType) -> Value {
        let v = self.fresh_value(ty);
        self.push(Inst::MoveOut(v, ptr, offset));
        // Slot is now null — invalidate the forwarding entry.
        self.recent_stores.remove(&(ptr, offset));
        v
    }

    pub fn rc_inc(&mut self, ptr: Value) {
        self.push(Inst::RcInc(ptr));
    }

    pub fn rc_dec(&mut self, ptr: Value) {
        self.push(Inst::RcDec(ptr));
    }

    pub fn cast(&mut self, src: Value, dest_ty: ScalarType) -> Value {
        let v = self.fresh_value(dest_ty);
        self.push(Inst::Cast(v, src));
        v
    }

    pub fn bitcast(&mut self, src: Value, dest_ty: ScalarType) -> Value {
        let v = self.fresh_value(dest_ty);
        self.push(Inst::BitCast(v, src));
        v
    }

    /// Emit a forward bulk-copy loop. Copies `count` elements from
    /// `src` to `dst` using `LoadDyn`/`StoreDyn` with 8-byte stride.
    /// For RcPtr elements, the rc accounting is automatic: the
    /// owning Load rc-incs the element (slot + local), the Store
    /// rc-incs again (dst slot claims it). At end of iteration the
    /// local goes out of scope and rc_emit emits an rc_dec — net
    /// result is one extra rc per element (the new dst slot), which
    /// is exactly what a clone needs.
    ///
    /// Layout: entry → header(i=0); header(i): i < count ? body(i) :
    /// exit; body(i): elem = load_dyn(src, i); store_dyn(dst, i, elem);
    /// jump header(i + 1); exit: ...
    pub fn copy_loop(&mut self, dst: Value, src: Value, count: Value, elem_ty: ScalarType) {
        let header = self.create_block();
        let body = self.create_block();
        let exit = self.create_block();

        let header_i = self.add_block_param(header, ScalarType::U64);
        let body_i = self.add_block_param(body, ScalarType::U64);

        let zero = self.const_u64(0);
        self.jump(header, vec![zero]);

        self.switch_to(header);
        let cond = self.binop(BinaryOp::Lt, header_i, count, ScalarType::U8);
        self.branch(cond, body, vec![header_i], exit, vec![]);

        self.switch_to(body);
        let elem = self.load_dyn(src, body_i, elem_ty);
        self.store_dyn(dst, body_i, elem);
        let one = self.const_u64(1);
        let next_i = self.binop(BinaryOp::Add, body_i, one, ScalarType::U64);
        self.jump(header, vec![next_i]);

        self.switch_to(exit);
    }

    // ---- Aggregates ----
    //
    // Phase A: aggregates are always heap-allocated. `pack` desugars
    // to Alloc + Stores; `extract` to Load. The Inst::Pack /
    // Inst::Extract / Inst::Insert variants and `ScalarType::Agg`
    // are gone — use these builder methods for source compatibility.

    pub fn pack(&mut self, fields: Vec<Value>) -> Value {
        let n = fields.len();
        let ptr = self.alloc(n * 8);
        for (i, f) in fields.into_iter().enumerate() {
            self.store(ptr, i * 8, f);
        }
        ptr
    }

    pub fn extract(&mut self, agg: Value, index: usize, ty: ScalarType) -> Value {
        self.load(agg, index * 8, ty)
    }

    // ---- Terminators ----

    pub fn set_return_type(&mut self, ty: ScalarType) {
        self.func.return_type = Some(ty);
    }

    pub fn ret(&mut self, value: Value) {
        self.seal(Terminator::Return(value));
    }

    pub fn jump(&mut self, target: BlockId, args: Vec<Value>) {
        self.seal(Terminator::Jump(BlockEdge { target, args }));
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
            then_edge: BlockEdge { target: then_block, args: then_args },
            else_edge: BlockEdge { target: else_block, args: else_args },
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
            .map(|(v, bid, args)| (v, BlockEdge { target: bid, args }))
            .collect();
        let default = default.map(|(bid, args)| BlockEdge { target: bid, args });
        self.seal(Terminator::SwitchInt {
            scrutinee,
            arms,
            default,
        });
    }

    // ---- Function building ----

    /// Finalize the current function. Params are the ones added via
    /// `add_func_param` (in order); each carries its type.
    /// The caller only supplies the return type.
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
        self.functions.insert(
            name.to_owned(),
            Function {
                name: name.to_owned(),
                params: fb.params,
                blocks: fb.finished,
                return_type: declared_ret,
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
