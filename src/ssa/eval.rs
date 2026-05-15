use crate::ssa::Module;
use crate::ssa::instruction::{BinaryOp, Inst, ScalarType, Terminator};

/// A scalar runtime value that fits in a register.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Scalar {
    I8(i8),
    U8(u8),
    I16(i16),
    U16(u16),
    I32(i32),
    U32(u32),
    I64(i64),
    U64(u64),
    F64(f64),
    Ptr(usize), // index into heap
}

/// Simulated heap for the interpreter.
/// Each allocation is a byte buffer. Ptr-typed fields are tracked
/// by byte offset so rc_dec can cascade-free children.
/// Sentinel refcount for static/permanent objects (never freed).
const RC_STATIC: usize = usize::MAX;

struct HeapObject {
    rc: usize,
    data: Vec<u8>,
    /// Byte offsets of Ptr-typed values within `data`.
    ptr_offsets: Vec<usize>,
    /// (byte_offset, ScalarType) for each stored value, so loads can
    /// recover the original type during the slot-to-byte transition.
    type_map: Vec<(usize, ScalarType)>,
}

pub struct Heap {
    objects: Vec<HeapObject>,
    /// Free-list of indices with refcount 0, available for reuse.
    free_list: Vec<usize>,
    /// Cumulative allocation count (fresh + freelist reuse). Statics
    /// don't count.
    pub alloc_count: u64,
    /// Cumulative allocations that grew the underlying object table
    /// (i.e. the freelist was empty). This is the "physical" measure
    /// of memory use; if a loop's `alloc_count` grows with iteration
    /// count but `fresh_alloc_count` stays small, the static-ownership
    /// reuse is doing its job.
    pub fresh_alloc_count: u64,
    /// Cumulative free count (refcount drops to zero). Statics don't
    /// count (sentinel refcount).
    pub free_count: u64,
    /// Maximum number of simultaneously-live non-static heap objects
    /// observed during execution. Useful for asserting that in-place
    /// mutation kept a program's memory usage bounded.
    pub peak_live: u64,
}

impl Heap {
    /// Number of non-static heap objects currently live.
    pub fn live_count(&self) -> u64 {
        self.alloc_count - self.free_count
    }
}

/// Get the ScalarType for a Scalar value.
fn scalar_type_of(val: Scalar) -> ScalarType {
    match val {
        Scalar::I8(_) => ScalarType::I8,
        Scalar::U8(_) => ScalarType::U8,
        Scalar::I16(_) => ScalarType::I16,
        Scalar::U16(_) => ScalarType::U16,
        Scalar::I32(_) => ScalarType::I32,
        Scalar::U32(_) => ScalarType::U32,
        Scalar::I64(_) => ScalarType::I64,
        Scalar::U64(_) => ScalarType::U64,
        Scalar::F64(_) => ScalarType::F64,
        Scalar::Ptr(_) => ScalarType::Ptr,
    }
}

/// Write a scalar value into a byte buffer at the given offset.
fn write_scalar(buf: &mut [u8], offset: usize, val: Scalar) {
    match val {
        Scalar::U8(n) => buf[offset] = n,
        Scalar::I8(n) => buf[offset] = n as u8,
        Scalar::U16(n) => buf[offset..offset + 2].copy_from_slice(&n.to_le_bytes()),
        Scalar::I16(n) => buf[offset..offset + 2].copy_from_slice(&n.to_le_bytes()),
        Scalar::U32(n) => buf[offset..offset + 4].copy_from_slice(&n.to_le_bytes()),
        Scalar::I32(n) => buf[offset..offset + 4].copy_from_slice(&n.to_le_bytes()),
        Scalar::U64(n) => buf[offset..offset + 8].copy_from_slice(&n.to_le_bytes()),
        Scalar::I64(n) => buf[offset..offset + 8].copy_from_slice(&n.to_le_bytes()),
        Scalar::F64(n) => buf[offset..offset + 8].copy_from_slice(&n.to_bits().to_le_bytes()),
        Scalar::Ptr(p) => buf[offset..offset + 8].copy_from_slice(&(p as u64).to_le_bytes()),
    }
}

/// Read a scalar value from a byte buffer at the given offset.
fn read_scalar(buf: &[u8], offset: usize, ty: ScalarType) -> Scalar {
    match ty {
        ScalarType::U8 => Scalar::U8(buf[offset]),
        ScalarType::I8 => Scalar::I8(buf[offset] as i8),
        ScalarType::U16 => Scalar::U16(u16::from_le_bytes(buf[offset..offset + 2].try_into().unwrap())),
        ScalarType::I16 => Scalar::I16(i16::from_le_bytes(buf[offset..offset + 2].try_into().unwrap())),
        ScalarType::U32 => Scalar::U32(u32::from_le_bytes(buf[offset..offset + 4].try_into().unwrap())),
        ScalarType::I32 => Scalar::I32(i32::from_le_bytes(buf[offset..offset + 4].try_into().unwrap())),
        ScalarType::U64 => Scalar::U64(u64::from_le_bytes(buf[offset..offset + 8].try_into().unwrap())),
        ScalarType::I64 => Scalar::I64(i64::from_le_bytes(buf[offset..offset + 8].try_into().unwrap())),
        ScalarType::F64 => Scalar::F64(f64::from_bits(u64::from_le_bytes(buf[offset..offset + 8].try_into().unwrap()))),
        ScalarType::Ptr => Scalar::Ptr(u64::from_le_bytes(buf[offset..offset + 8].try_into().unwrap()) as usize),
        ScalarType::Agg(_) => panic!("cannot read Agg from heap"),
    }
}

impl Heap {
    fn new() -> Self {
        // Index 0 is null
        Self {
            objects: vec![HeapObject { rc: 0, data: vec![], ptr_offsets: vec![], type_map: vec![] }],
            free_list: Vec::new(),
            alloc_count: 0,
            fresh_alloc_count: 0,
            free_count: 0,
            peak_live: 0,
        }
    }

    pub fn alloc(&mut self, num_bytes: usize) -> usize {
        self.alloc_count += 1;
        let live = self.alloc_count - self.free_count;
        if live > self.peak_live {
            self.peak_live = live;
        }
        if let Some(idx) = self.free_list.pop() {
            let obj = &mut self.objects[idx];
            obj.rc = 1;
            obj.data.clear();
            obj.data.resize(num_bytes, 0);
            obj.ptr_offsets.clear();
            obj.type_map.clear();
            idx
        } else {
            self.fresh_alloc_count += 1;
            let idx = self.objects.len();
            self.objects.push(HeapObject {
                rc: 1,
                data: vec![0; num_bytes],
                ptr_offsets: Vec::new(),
                type_map: Vec::new(),
            });
            idx
        }
    }

    /// Allocate a static (permanent) object that is never freed.
    pub fn alloc_static(&mut self, data: Vec<u8>, ptr_offsets: Vec<usize>) -> usize {
        let idx = self.objects.len();
        self.objects.push(HeapObject { rc: RC_STATIC, data, ptr_offsets, type_map: Vec::new() });
        idx
    }

    pub fn load(&self, idx: usize, byte_offset: usize, ty: ScalarType) -> Scalar {
        read_scalar(&self.objects[idx].data, byte_offset, ty)
    }

    pub fn store(&mut self, idx: usize, byte_offset: usize, val: Scalar) {
        let obj = &mut self.objects[idx];
        write_scalar(&mut obj.data, byte_offset, val);
        // Track Ptr offsets for cascade-free.
        if matches!(val, Scalar::Ptr(_)) {
            if !obj.ptr_offsets.contains(&byte_offset) {
                obj.ptr_offsets.push(byte_offset);
            }
        }
        // Record the type for auto-detection loads.
        let ty = scalar_type_of(val);
        if let Some(entry) = obj.type_map.iter_mut().find(|(off, _)| *off == byte_offset) {
            entry.1 = ty;
        } else {
            obj.type_map.push((byte_offset, ty));
        }
    }

    /// Load from a dynamic element index (uniform element array).
    /// Byte offset = element_index * element_type.byte_width().
    fn load_dyn(&self, idx: usize, elem_index: usize, ty: ScalarType) -> Scalar {
        let offset = elem_index * ty.byte_width();
        read_scalar(&self.objects[idx].data, offset, ty)
    }

    /// Look up the stored ScalarType for a byte offset, if any.
    fn lookup_type(&self, idx: usize, byte_offset: usize) -> Option<ScalarType> {
        self.objects[idx]
            .type_map
            .iter()
            .find(|(off, _)| *off == byte_offset)
            .map(|(_, ty)| *ty)
    }

    /// Load a value, using the type_map to recover the original ScalarType.
    /// Falls back to the hint when no type_map entry exists.
    fn load_auto(&self, idx: usize, byte_offset: usize, hint: ScalarType) -> Scalar {
        let ty = self.lookup_type(idx, byte_offset).unwrap_or(hint);
        read_scalar(&self.objects[idx].data, byte_offset, ty)
    }

    /// Load an element by index. All elements use 8-byte stride,
    /// matching the lowering's data buffer layout. The type_map
    /// recovers the original ScalarType so the Scalar variant is correct.
    fn load_dyn_auto(&self, idx: usize, elem_index: usize) -> Scalar {
        let offset = elem_index * 8;
        let ty = self.lookup_type(idx, offset).unwrap_or(ScalarType::I64);
        read_scalar(&self.objects[idx].data, offset, ty)
    }

    /// Store to a dynamic element index (uniform element array).
    /// All elements use 8-byte stride matching the lowering layout.
    /// Grows the buffer if needed.
    fn store_dyn(&mut self, idx: usize, elem_index: usize, val: Scalar, _elem_ty: ScalarType) {
        let offset = elem_index * 8;
        let needed = offset + 8;
        let obj = &mut self.objects[idx];
        if needed > obj.data.len() {
            obj.data.resize(needed, 0);
        }
        write_scalar(&mut obj.data, offset, val);
        if matches!(val, Scalar::Ptr(_)) {
            if !obj.ptr_offsets.contains(&offset) {
                obj.ptr_offsets.push(offset);
            }
        }
        // Record the type for auto-detection loads.
        let ty = scalar_type_of(val);
        if let Some(entry) = obj.type_map.iter_mut().find(|(off, _)| *off == offset) {
            entry.1 = ty;
        } else {
            obj.type_map.push((offset, ty));
        }
    }

    fn rc_inc(&mut self, idx: usize) {
        if idx != 0 && self.objects[idx].rc != RC_STATIC {
            self.objects[idx].rc += 1;
        }
    }

    fn rc_dec(&mut self, idx: usize) {
        if idx == 0 || self.objects[idx].rc == RC_STATIC || self.objects[idx].rc == 0 {
            return;
        }
        self.objects[idx].rc -= 1;
        if self.objects[idx].rc == 0 {
            self.free_count += 1;
            // Collect Ptr children before adding to free list.
            let children: Vec<usize> = self.objects[idx]
                .ptr_offsets
                .iter()
                .filter_map(|&off| {
                    match read_scalar(&self.objects[idx].data, off, ScalarType::Ptr) {
                        Scalar::Ptr(p) if p != 0 => Some(p),
                        _ => None,
                    }
                })
                .collect();
            self.free_list.push(idx);
            for child in children {
                self.rc_dec(child);
            }
        }
    }

    /// Clone a heap object, returning the new index.
    /// Increments refcounts of any Ptr children in the cloned data.
    pub fn clone_object(&mut self, idx: usize) -> usize {
        self.alloc_count += 1;
        let live = self.alloc_count - self.free_count;
        if live > self.peak_live {
            self.peak_live = live;
        }
        let data = self.objects[idx].data.clone();
        let ptr_offsets = self.objects[idx].ptr_offsets.clone();
        // The clone creates new references to all Ptr children.
        for &off in &ptr_offsets {
            if let Scalar::Ptr(child) = read_scalar(&data, off, ScalarType::Ptr) {
                if child != 0 {
                    self.rc_inc(child);
                }
            }
        }
        let type_map = self.objects[idx].type_map.clone();
        if let Some(new_idx) = self.free_list.pop() {
            let obj = &mut self.objects[new_idx];
            obj.rc = 1;
            obj.data = data;
            obj.ptr_offsets = ptr_offsets;
            obj.type_map = type_map;
            new_idx
        } else {
            self.fresh_alloc_count += 1;
            let new_idx = self.objects.len();
            self.objects.push(HeapObject { rc: 1, data, ptr_offsets, type_map });
            new_idx
        }
    }

    /// Get the byte length of an object.
    pub fn object_len(&self, idx: usize) -> usize {
        self.objects[idx].data.len()
    }

    /// Get the byte offsets of Ptr-typed values in an object.
    pub fn ptr_offsets(&self, idx: usize) -> &[usize] {
        &self.objects[idx].ptr_offsets
    }
}

type Env = Vec<Scalar>;

/// Pre-allocate static objects on the heap. Must be called before
/// any other heap allocations so that `StaticRef` indices are stable.
pub fn load_statics(module: &Module, heap: &mut Heap) {
    init_statics(module, heap);
}

/// Evaluate the entry function of an SSA module.
pub fn eval(module: &Module, heap: &mut Heap, args: &[Scalar]) -> Scalar {
    eval_function(module, heap, &module.entry, args)
}

/// Scratch space for register files, reused across calls to avoid allocation.
struct Scratch {
    envs: Vec<Vec<Scalar>>,
}

impl Scratch {
    fn new() -> Self {
        Self { envs: Vec::new() }
    }

    fn acquire(&mut self, size: usize) -> Vec<Scalar> {
        let mut env = self.envs.pop().unwrap_or_default();
        env.clear();
        env.resize(size, Scalar::I64(0));
        env
    }

    fn release(&mut self, env: Vec<Scalar>) {
        self.envs.push(env);
    }
}

/// Pre-allocate static objects on the heap. Static objects get
/// indices 1..=N (0 is null). They use a sentinel refcount so
/// RC operations are no-ops.
fn init_statics(module: &Module, heap: &mut Heap) {
    use super::StaticSlot;
    // First pass: allocate all static objects with placeholder byte buffers
    // so they have stable indices for cross-references.
    // Each slot occupies 8 bytes (all static values are stored full-width).
    let base = heap.objects.len();
    for obj in &module.statics {
        let num_bytes = obj.slots.len() * 8;
        heap.objects.push(HeapObject {
            rc: RC_STATIC,
            data: vec![0; num_bytes],
            ptr_offsets: Vec::new(),
            type_map: Vec::new(),
        });
    }
    // Second pass: fill in slot values now that all indices are known.
    for (i, obj) in module.statics.iter().enumerate() {
        for (si, slot) in obj.slots.iter().enumerate() {
            let scalar = match slot {
                StaticSlot::U8(b) => Scalar::U8(*b),
                StaticSlot::U32(n) => Scalar::U32(*n),
                StaticSlot::U64(n) => Scalar::U64(*n),
                StaticSlot::I64(n) => Scalar::I64(*n),
                StaticSlot::StaticPtr(id) => Scalar::Ptr(base + id),
            };
            let byte_offset = si * 8;
            heap.store(base + i, byte_offset, scalar);
        }
    }
}

/// Create a new heap for interpretation.
pub fn new_heap() -> Heap {
    Heap::new()
}

pub fn eval_function(module: &Module, heap: &mut Heap, name: &str, args: &[Scalar]) -> Scalar {
    let mut scratch = Scratch::new();
    eval_function_inner(module, heap, &mut scratch, name, args)
}

fn eval_function_inner(
    module: &Module,
    heap: &mut Heap,
    scratch: &mut Scratch,
    name: &str,
    args: &[Scalar],
) -> Scalar {
    // Check for runtime intrinsics
    if let Some(result) = eval_intrinsic(name, heap, args) {
        return result;
    }

    let func = module
        .functions
        .get(name)
        .unwrap_or_else(|| panic!("undefined SSA function: {name}"));
    let mut env = scratch.acquire(func.num_values());

    for (param, arg) in func.params.iter().zip(args) {
        env[param.id] = *arg;
    }

    let mut current = func.entry;
    let mut block_args: Vec<Scalar> = vec![];

    loop {
        let block = &func.blocks[&current];

        for (param, arg) in block.params.iter().zip(&block_args) {
            env[param.id] = *arg;
        }

        for inst in &block.insts {
            let val = eval_inst(module, heap, scratch, &env, inst);
            if let Some(dest) = inst.dest() {
                if let Some(v) = val {
                    env[dest.id] = v;
                }
            }
        }

        match &block.terminator {
            Terminator::Return(v) => {
                let result = env[v.id];
                scratch.release(env);
                return result;
            }

            Terminator::Jump(edge) => {
                block_args = edge.args.iter().map(|v| env[v.id]).collect();
                current = edge.target;
            }

            Terminator::Branch {
                cond,
                then_edge,
                else_edge,
            } => {
                if scalar_to_u64(env[cond.id]) != 0 {
                    block_args = then_edge.args.iter().map(|v| env[v.id]).collect();
                    current = then_edge.target;
                } else {
                    block_args = else_edge.args.iter().map(|v| env[v.id]).collect();
                    current = else_edge.target;
                }
            }

            Terminator::SwitchInt {
                scrutinee,
                arms,
                default,
            } => {
                let tag = scalar_to_u64(env[scrutinee.id]);
                if let Some((_, edge)) = arms.iter().find(|(v, _)| *v == tag) {
                    block_args = edge.args.iter().map(|v| env[v.id]).collect();
                    current = edge.target;
                } else if let Some(edge) = default {
                    block_args = edge.args.iter().map(|v| env[v.id]).collect();
                    current = edge.target;
                } else {
                    panic!("no matching arm for tag {tag}");
                }
            }

        }
    }
}

fn eval_inst(module: &Module, heap: &mut Heap, scratch: &mut Scratch, env: &Env, inst: &Inst) -> Option<Scalar> {
    match inst {
        Inst::Const(dest, bits) => Some(bits_to_scalar(dest.ty, *bits)),

        Inst::BinOp(_, op, lhs, rhs) => Some(eval_binop(*op, env[lhs.id], env[rhs.id])),

        Inst::Call(_, name, args) => {
            let arg_vals: Vec<Scalar> = args.iter().map(|v| env[v.id]).collect();
            Some(eval_function_inner(module, heap, scratch, name, &arg_vals))
        }

        Inst::Alloc(_, size) => {
            let idx = heap.alloc(*size);
            Some(Scalar::Ptr(idx))
        }

        Inst::AllocDyn(_, size_val) => {
            let size = scalar_to_usize(env[size_val.id]);
            let idx = heap.alloc(size);
            Some(Scalar::Ptr(idx))
        }

        Inst::Load(dest, ptr, offset) => {
            let Scalar::Ptr(idx) = env[ptr.id] else {
                panic!("load from non-ptr: {:?}", env[ptr.id]);
            };
            Some(heap.load_auto(idx, *offset, dest.ty))
        }

        Inst::Store(ptr, offset, val) => {
            let Scalar::Ptr(idx) = env[ptr.id] else {
                panic!("store to non-ptr: {:?}", env[ptr.id]);
            };
            heap.store(idx, *offset, env[val.id]);
            None
        }

        Inst::LoadDyn(dest, ptr, idx_val) => {
            let Scalar::Ptr(heap_idx) = env[ptr.id] else {
                panic!("load_dyn from non-ptr: {:?}", env[ptr.id]);
            };
            let slot = scalar_to_usize(env[idx_val.id]);
            // Data buffers use a uniform 8-byte stride (matches StoreDyn).
            let offset = slot * 8;
            // Dest type `Ptr` is the generic-element placeholder some
            // lowering paths use when they don't know the element type
            // (e.g. emit_list_get_checked). Recover the true type from
            // type_map. Concrete dest types are authoritative.
            if dest.ty == ScalarType::Ptr {
                Some(heap.load_dyn_auto(heap_idx, slot))
            } else {
                Some(heap.load(heap_idx, offset, dest.ty))
            }
        }

        Inst::StoreDyn(ptr, idx_val, val) => {
            let Scalar::Ptr(heap_idx) = env[ptr.id] else {
                panic!("store_dyn to non-ptr: {:?}", env[ptr.id]);
            };
            let slot = scalar_to_usize(env[idx_val.id]);
            // Detect element stride from the buffer's existing type_map.
            // U8 buffers (strings) use 1-byte stride; all others use 8-byte stride.
            let buf_elem_ty = heap.lookup_type(heap_idx, 0);
            let (elem_ty, store_val) = if buf_elem_ty == Some(ScalarType::U8) {
                // Coerce to U8 if needed (the lowering may have typed the literal as I64).
                let v = if matches!(env[val.id], Scalar::U8(_)) {
                    env[val.id]
                } else {
                    Scalar::U8(scalar_to_u64(env[val.id]) as u8)
                };
                (ScalarType::U8, v)
            } else {
                (ScalarType::I64, env[val.id])
            };
            heap.store_dyn(heap_idx, slot, store_val, elem_ty);
            None
        }

        Inst::RcInc(ptr) => {
            if let Scalar::Ptr(idx) = env[ptr.id] {
                heap.rc_inc(idx);
            }
            None
        }

        Inst::RcDec(ptr) => {
            if let Scalar::Ptr(idx) = env[ptr.id] {
                heap.rc_dec(idx);
            }
            None
        }

        Inst::Free(ptr) => {
            // Statically-resolved free: emit_drops has proven this
            // value is Unique and at its last use. The interpreter's
            // rc_dec path already cascade-frees children when rc
            // reaches 0; since static-ownership never inc'd this
            // value past 1, rc_dec drops it the same way Free should.
            if let Scalar::Ptr(idx) = env[ptr.id] {
                heap.rc_dec(idx);
            }
            None
        }

        Inst::Drop(ptr, slot_types) => {
            // Statically-resolved drop with an explicit slot mask:
            // cascade decrements only slots marked Ptr in slot_types.
            // Slots marked non-Ptr are moved-out; their children are
            // owned by independent local SSA values, so the cascade
            // must skip them.
            if let Scalar::Ptr(idx) = env[ptr.id] {
                if idx != 0 && heap.objects[idx].rc != RC_STATIC && heap.objects[idx].rc != 0 {
                    heap.objects[idx].rc -= 1;
                    if heap.objects[idx].rc == 0 {
                        heap.free_count += 1;
                        for (i, ty) in slot_types.iter().enumerate() {
                            if *ty == ScalarType::Ptr {
                                let offset = i * 8;
                                if let Scalar::Ptr(child) = heap.load(idx, offset, ScalarType::Ptr) {
                                    if child != 0 {
                                        heap.rc_dec(child);
                                    }
                                }
                            }
                        }
                        heap.free_list.push(idx);
                    }
                }
            }
            None
        }

        Inst::StaticRef(_dest, static_id) => {
            // Statics are pre-allocated starting at heap index 1
            // (index 0 is null). static_id 0 → heap index 1, etc.
            Some(Scalar::Ptr(1 + static_id))
        }

        Inst::Reset(_dest, ptr, slot_types) => {
            if let Scalar::Ptr(idx) = env[ptr.id] {
                if idx != 0 && heap.objects[idx].rc == 1 && heap.objects[idx].rc != RC_STATIC {
                    // Unique: dec pointer-typed fields, return address for reuse.
                    for (i, ty) in slot_types.iter().enumerate() {
                        if *ty == ScalarType::Ptr {
                            let offset = i * 8;
                            if let Scalar::Ptr(child) = heap.load(idx, offset, ScalarType::Ptr) {
                                heap.rc_dec(child);
                            }
                        }
                    }
                    heap.objects[idx].rc = 0;
                    // The object is conceptually freed; the matching
                    // Reuse will re-allocate in-place via reuse_or_alloc.
                    heap.free_count += 1;
                    Some(Scalar::Ptr(idx))
                } else {
                    // Shared: normal dec, return null.
                    heap.rc_dec(idx);
                    Some(Scalar::Ptr(0))
                }
            } else {
                Some(Scalar::Ptr(0))
            }
        }

        Inst::Reuse(_dest, token, num_slots) => {
            Some(Scalar::Ptr(reuse_or_alloc(heap, env[token.id], *num_slots)))
        }

        Inst::ReuseDyn(_dest, token, size_val) => {
            let size = scalar_to_usize(env[size_val.id]);
            Some(Scalar::Ptr(reuse_or_alloc(heap, env[token.id], size)))
        }

        Inst::Pack(_dest, fields) => {
            let n = fields.len();
            let idx = heap.alloc(n * 8);
            for (i, f) in fields.iter().enumerate() {
                heap.store(idx, i * 8, env[f.id]);
            }
            Some(Scalar::Ptr(idx))
        }

        Inst::Cast(dest, src) => {
            // Integer widening (zero-extend) / narrowing (truncate).
            // The destination type drives the result variant.
            let bits = scalar_to_u64(env[src.id]);
            Some(bits_to_scalar(dest.ty, bits))
        }

        Inst::BitCast(dest, src) => {
            // Same-width bit reinterpretation. `F64 ↔ U64` is the
            // canonical use; integer ↔ integer of equal width works too.
            let bits = match env[src.id] {
                Scalar::F64(n) => n.to_bits(),
                other => scalar_to_u64(other),
            };
            Some(bits_to_scalar(dest.ty, bits))
        }

        Inst::Extract(dest, agg, idx) => {
            if let Scalar::Ptr(p) = env[agg.id] {
                Some(heap.load_auto(p, *idx * 8, dest.ty))
            } else {
                panic!("extract from non-Ptr value v{}: {:?}", agg.id, env[agg.id])
            }
        }

        Inst::Insert(_dest, agg, idx, val) => {
            if let Scalar::Ptr(p) = env[agg.id] {
                let new_idx = heap.clone_object(p);
                heap.store(new_idx, *idx * 8, env[val.id]);
                Some(Scalar::Ptr(new_idx))
            } else {
                panic!("insert into non-Ptr value v{}: {:?}", agg.id, env[agg.id])
            }
        }
    }
}

// ---- Runtime intrinsics ----

fn eval_intrinsic(name: &str, heap: &mut Heap, args: &[Scalar]) -> Option<Scalar> {
    match name {
        "__crash" => {
            // args: [str_ptr] — print message to stderr and abort.
            let Scalar::Ptr(list_idx) = args[0] else {
                eprintln!("crash: <non-string argument>");
                std::process::exit(1);
            };
            let Scalar::U64(len) = heap.load(list_idx, 0, ScalarType::U64) else {
                eprintln!("crash: <malformed string>");
                std::process::exit(1);
            };
            let Scalar::Ptr(data_idx) = heap.load(list_idx, 16, ScalarType::Ptr) else {
                eprintln!("crash: <malformed string>");
                std::process::exit(1);
            };
            #[expect(clippy::cast_possible_truncation)]
            let len = len as usize;
            let mut bytes = Vec::with_capacity(len);
            for i in 0..len {
                let Scalar::U8(b) = heap.load(data_idx, i, ScalarType::U8) else {
                    bytes.push(b'?');
                    continue;
                };
                bytes.push(b);
            }
            let msg = String::from_utf8_lossy(&bytes);
            eprintln!("crash: {msg}");
            std::process::exit(1);
        }
        _ => None,
    }
}

// ---- Helpers ----

fn bits_to_scalar(ty: ScalarType, bits: u64) -> Scalar {
    match ty {
        ScalarType::I8 => Scalar::I8(bits as i8),
        ScalarType::U8 => Scalar::U8(bits as u8),
        ScalarType::I16 => Scalar::I16(bits as i16),
        ScalarType::U16 => Scalar::U16(bits as u16),
        ScalarType::I32 => Scalar::I32(bits as i32),
        ScalarType::U32 => Scalar::U32(bits as u32),
        ScalarType::I64 => Scalar::I64(bits as i64),
        ScalarType::U64 => Scalar::U64(bits),
        ScalarType::F64 => Scalar::F64(f64::from_bits(bits)),
        ScalarType::Ptr => Scalar::Ptr(bits as usize),
        ScalarType::Agg(_) => panic!("cannot create scalar from aggregate type"),
    }
}

fn scalar_to_u64(s: Scalar) -> u64 {
    match s {
        Scalar::I8(n) => n as u64,
        Scalar::U8(n) => u64::from(n),
        Scalar::I16(n) => n as u64,
        Scalar::U16(n) => u64::from(n),
        Scalar::I32(n) => n as u64,
        Scalar::U32(n) => u64::from(n),
        Scalar::I64(n) => n as u64,
        Scalar::U64(n) => n,
        Scalar::Ptr(p) => p as u64,
        Scalar::F64(_) => panic!("switch on float"),
    }
}

/// Reuse a Reset-produced token for a new allocation, or allocate
/// fresh when the token is null (shared object, reuse unsafe).
fn reuse_or_alloc(heap: &mut Heap, token: Scalar, num_bytes: usize) -> usize {
    if let Scalar::Ptr(idx) = token {
        if idx != 0 {
            // In-place reuse: count as a logical alloc (so `alloc_count`
            // reflects the program's allocation behavior) but NOT as a
            // fresh one (so `fresh_alloc_count` reflects real memory
            // growth).
            heap.alloc_count += 1;
            let live = heap.alloc_count - heap.free_count;
            if live > heap.peak_live {
                heap.peak_live = live;
            }
            heap.objects[idx].rc = 1;
            heap.objects[idx].data.resize(num_bytes, 0);
            heap.objects[idx].ptr_offsets.clear();
            heap.objects[idx].type_map.clear();
            return idx;
        }
    }
    heap.alloc(num_bytes)
}

fn scalar_to_usize(s: Scalar) -> usize {
    match s {
        Scalar::U64(n) => n as usize,
        Scalar::I64(n) => n as usize,
        Scalar::Ptr(p) => p,
        _ => panic!("expected integer index, got {s:?}"),
    }
}

fn eval_binop(op: BinaryOp, lhs: Scalar, rhs: Scalar) -> Scalar {
    match (op, lhs, rhs) {
        (BinaryOp::Add, Scalar::I64(a), Scalar::I64(b)) => Scalar::I64(a.wrapping_add(b)),
        (BinaryOp::Sub, Scalar::I64(a), Scalar::I64(b)) => Scalar::I64(a.wrapping_sub(b)),
        (BinaryOp::Mul, Scalar::I64(a), Scalar::I64(b)) => Scalar::I64(a.wrapping_mul(b)),
        (BinaryOp::Div, Scalar::I64(a), Scalar::I64(b)) => Scalar::I64(a / b),
        (BinaryOp::Rem, Scalar::I64(a), Scalar::I64(b)) => Scalar::I64(a % b),
        (BinaryOp::And, Scalar::I64(a), Scalar::I64(b)) => Scalar::I64(a & b),
        (BinaryOp::Or, Scalar::I64(a), Scalar::I64(b)) => Scalar::I64(a | b),
        (BinaryOp::Xor, Scalar::I64(a), Scalar::I64(b)) => Scalar::I64(a ^ b),
        (BinaryOp::Shl, Scalar::I64(a), Scalar::I64(b)) => Scalar::I64(a.wrapping_shl(b as u32)),
        (BinaryOp::Shr, Scalar::I64(a), Scalar::I64(b)) => Scalar::I64(a.wrapping_shr(b as u32)),
        (BinaryOp::Max, Scalar::I64(a), Scalar::I64(b)) => Scalar::I64(a.max(b)),
        (BinaryOp::Eq, Scalar::I64(a), Scalar::I64(b)) => Scalar::U8(u8::from(a == b)),
        (BinaryOp::Neq, Scalar::I64(a), Scalar::I64(b)) => Scalar::U8(u8::from(a != b)),
        (BinaryOp::Lt, Scalar::I64(a), Scalar::I64(b)) => Scalar::U8(u8::from(a < b)),
        (BinaryOp::Le, Scalar::I64(a), Scalar::I64(b)) => Scalar::U8(u8::from(a <= b)),
        (BinaryOp::Gt, Scalar::I64(a), Scalar::I64(b)) => Scalar::U8(u8::from(a > b)),
        (BinaryOp::Ge, Scalar::I64(a), Scalar::I64(b)) => Scalar::U8(u8::from(a >= b)),

        (BinaryOp::Add, Scalar::U64(a), Scalar::U64(b)) => Scalar::U64(a.wrapping_add(b)),
        (BinaryOp::Sub, Scalar::U64(a), Scalar::U64(b)) => Scalar::U64(a.wrapping_sub(b)),
        (BinaryOp::Mul, Scalar::U64(a), Scalar::U64(b)) => Scalar::U64(a.wrapping_mul(b)),
        (BinaryOp::Div, Scalar::U64(a), Scalar::U64(b)) => Scalar::U64(a / b),
        (BinaryOp::Rem, Scalar::U64(a), Scalar::U64(b)) => Scalar::U64(a % b),
        (BinaryOp::And, Scalar::U8(a), Scalar::U8(b)) => Scalar::U8(a & b),
        (BinaryOp::Or, Scalar::U8(a), Scalar::U8(b)) => Scalar::U8(a | b),
        (BinaryOp::Xor, Scalar::U8(a), Scalar::U8(b)) => Scalar::U8(a ^ b),
        (BinaryOp::Shl, Scalar::U8(a), Scalar::U8(b)) => Scalar::U8(a.wrapping_shl(u32::from(b))),
        (BinaryOp::Shr, Scalar::U8(a), Scalar::U8(b)) => Scalar::U8(a.wrapping_shr(u32::from(b))),
        (BinaryOp::And, Scalar::U64(a), Scalar::U64(b)) => Scalar::U64(a & b),
        (BinaryOp::Or, Scalar::U64(a), Scalar::U64(b)) => Scalar::U64(a | b),
        (BinaryOp::Xor, Scalar::U64(a), Scalar::U64(b)) => Scalar::U64(a ^ b),
        (BinaryOp::Shl, Scalar::U64(a), Scalar::U64(b)) => Scalar::U64(a.wrapping_shl(b as u32)),
        (BinaryOp::Shr, Scalar::U64(a), Scalar::U64(b)) => Scalar::U64(a.wrapping_shr(b as u32)),
        (BinaryOp::Max, Scalar::U64(a), Scalar::U64(b)) => Scalar::U64(a.max(b)),
        (BinaryOp::Eq, Scalar::U64(a), Scalar::U64(b)) => Scalar::U8(u8::from(a == b)),
        (BinaryOp::Neq, Scalar::U64(a), Scalar::U64(b)) => Scalar::U8(u8::from(a != b)),
        (BinaryOp::Lt, Scalar::U64(a), Scalar::U64(b)) => Scalar::U8(u8::from(a < b)),
        (BinaryOp::Le, Scalar::U64(a), Scalar::U64(b)) => Scalar::U8(u8::from(a <= b)),
        (BinaryOp::Gt, Scalar::U64(a), Scalar::U64(b)) => Scalar::U8(u8::from(a > b)),
        (BinaryOp::Ge, Scalar::U64(a), Scalar::U64(b)) => Scalar::U8(u8::from(a >= b)),

        (BinaryOp::Add, Scalar::U8(a), Scalar::U8(b)) => Scalar::U8(a.wrapping_add(b)),
        (BinaryOp::Sub, Scalar::U8(a), Scalar::U8(b)) => Scalar::U8(a.wrapping_sub(b)),
        (BinaryOp::Mul, Scalar::U8(a), Scalar::U8(b)) => Scalar::U8(a.wrapping_mul(b)),
        (BinaryOp::Div, Scalar::U8(a), Scalar::U8(b)) => Scalar::U8(a / b),
        (BinaryOp::Rem, Scalar::U8(a), Scalar::U8(b)) => Scalar::U8(a % b),
        (BinaryOp::Eq, Scalar::U8(a), Scalar::U8(b)) => Scalar::U8(u8::from(a == b)),
        (BinaryOp::Neq, Scalar::U8(a), Scalar::U8(b)) => Scalar::U8(u8::from(a != b)),
        (BinaryOp::Lt, Scalar::U8(a), Scalar::U8(b)) => Scalar::U8(u8::from(a < b)),
        (BinaryOp::Le, Scalar::U8(a), Scalar::U8(b)) => Scalar::U8(u8::from(a <= b)),
        (BinaryOp::Gt, Scalar::U8(a), Scalar::U8(b)) => Scalar::U8(u8::from(a > b)),
        (BinaryOp::Ge, Scalar::U8(a), Scalar::U8(b)) => Scalar::U8(u8::from(a >= b)),

        (BinaryOp::Add, Scalar::I8(a), Scalar::I8(b)) => Scalar::I8(a.wrapping_add(b)),
        (BinaryOp::Sub, Scalar::I8(a), Scalar::I8(b)) => Scalar::I8(a.wrapping_sub(b)),
        (BinaryOp::Mul, Scalar::I8(a), Scalar::I8(b)) => Scalar::I8(a.wrapping_mul(b)),
        (BinaryOp::Div, Scalar::I8(a), Scalar::I8(b)) => Scalar::I8(a / b),
        (BinaryOp::Rem, Scalar::I8(a), Scalar::I8(b)) => Scalar::I8(a % b),
        (BinaryOp::And, Scalar::I8(a), Scalar::I8(b)) => Scalar::I8(a & b),
        (BinaryOp::Or, Scalar::I8(a), Scalar::I8(b)) => Scalar::I8(a | b),
        (BinaryOp::Xor, Scalar::I8(a), Scalar::I8(b)) => Scalar::I8(a ^ b),
        (BinaryOp::Shl, Scalar::I8(a), Scalar::I8(b)) => Scalar::I8(a.wrapping_shl(b as u32)),
        (BinaryOp::Shr, Scalar::I8(a), Scalar::I8(b)) => Scalar::I8(a.wrapping_shr(b as u32)),
        (BinaryOp::Eq, Scalar::I8(a), Scalar::I8(b)) => Scalar::U8(u8::from(a == b)),
        (BinaryOp::Neq, Scalar::I8(a), Scalar::I8(b)) => Scalar::U8(u8::from(a != b)),
        (BinaryOp::Lt, Scalar::I8(a), Scalar::I8(b)) => Scalar::U8(u8::from(a < b)),
        (BinaryOp::Le, Scalar::I8(a), Scalar::I8(b)) => Scalar::U8(u8::from(a <= b)),
        (BinaryOp::Gt, Scalar::I8(a), Scalar::I8(b)) => Scalar::U8(u8::from(a > b)),
        (BinaryOp::Ge, Scalar::I8(a), Scalar::I8(b)) => Scalar::U8(u8::from(a >= b)),

        (BinaryOp::Add, Scalar::I16(a), Scalar::I16(b)) => Scalar::I16(a.wrapping_add(b)),
        (BinaryOp::Sub, Scalar::I16(a), Scalar::I16(b)) => Scalar::I16(a.wrapping_sub(b)),
        (BinaryOp::Mul, Scalar::I16(a), Scalar::I16(b)) => Scalar::I16(a.wrapping_mul(b)),
        (BinaryOp::Div, Scalar::I16(a), Scalar::I16(b)) => Scalar::I16(a / b),
        (BinaryOp::Rem, Scalar::I16(a), Scalar::I16(b)) => Scalar::I16(a % b),
        (BinaryOp::And, Scalar::I16(a), Scalar::I16(b)) => Scalar::I16(a & b),
        (BinaryOp::Or, Scalar::I16(a), Scalar::I16(b)) => Scalar::I16(a | b),
        (BinaryOp::Xor, Scalar::I16(a), Scalar::I16(b)) => Scalar::I16(a ^ b),
        (BinaryOp::Shl, Scalar::I16(a), Scalar::I16(b)) => Scalar::I16(a.wrapping_shl(b as u32)),
        (BinaryOp::Shr, Scalar::I16(a), Scalar::I16(b)) => Scalar::I16(a.wrapping_shr(b as u32)),
        (BinaryOp::Eq, Scalar::I16(a), Scalar::I16(b)) => Scalar::U8(u8::from(a == b)),
        (BinaryOp::Neq, Scalar::I16(a), Scalar::I16(b)) => Scalar::U8(u8::from(a != b)),
        (BinaryOp::Lt, Scalar::I16(a), Scalar::I16(b)) => Scalar::U8(u8::from(a < b)),
        (BinaryOp::Le, Scalar::I16(a), Scalar::I16(b)) => Scalar::U8(u8::from(a <= b)),
        (BinaryOp::Gt, Scalar::I16(a), Scalar::I16(b)) => Scalar::U8(u8::from(a > b)),
        (BinaryOp::Ge, Scalar::I16(a), Scalar::I16(b)) => Scalar::U8(u8::from(a >= b)),

        (BinaryOp::Add, Scalar::U16(a), Scalar::U16(b)) => Scalar::U16(a.wrapping_add(b)),
        (BinaryOp::Sub, Scalar::U16(a), Scalar::U16(b)) => Scalar::U16(a.wrapping_sub(b)),
        (BinaryOp::Mul, Scalar::U16(a), Scalar::U16(b)) => Scalar::U16(a.wrapping_mul(b)),
        (BinaryOp::Div, Scalar::U16(a), Scalar::U16(b)) => Scalar::U16(a / b),
        (BinaryOp::Rem, Scalar::U16(a), Scalar::U16(b)) => Scalar::U16(a % b),
        (BinaryOp::And, Scalar::U16(a), Scalar::U16(b)) => Scalar::U16(a & b),
        (BinaryOp::Or, Scalar::U16(a), Scalar::U16(b)) => Scalar::U16(a | b),
        (BinaryOp::Xor, Scalar::U16(a), Scalar::U16(b)) => Scalar::U16(a ^ b),
        (BinaryOp::Shl, Scalar::U16(a), Scalar::U16(b)) => Scalar::U16(a.wrapping_shl(u32::from(b))),
        (BinaryOp::Shr, Scalar::U16(a), Scalar::U16(b)) => Scalar::U16(a.wrapping_shr(u32::from(b))),
        (BinaryOp::Eq, Scalar::U16(a), Scalar::U16(b)) => Scalar::U8(u8::from(a == b)),
        (BinaryOp::Neq, Scalar::U16(a), Scalar::U16(b)) => Scalar::U8(u8::from(a != b)),
        (BinaryOp::Lt, Scalar::U16(a), Scalar::U16(b)) => Scalar::U8(u8::from(a < b)),
        (BinaryOp::Le, Scalar::U16(a), Scalar::U16(b)) => Scalar::U8(u8::from(a <= b)),
        (BinaryOp::Gt, Scalar::U16(a), Scalar::U16(b)) => Scalar::U8(u8::from(a > b)),
        (BinaryOp::Ge, Scalar::U16(a), Scalar::U16(b)) => Scalar::U8(u8::from(a >= b)),

        (BinaryOp::Add, Scalar::I32(a), Scalar::I32(b)) => Scalar::I32(a.wrapping_add(b)),
        (BinaryOp::Sub, Scalar::I32(a), Scalar::I32(b)) => Scalar::I32(a.wrapping_sub(b)),
        (BinaryOp::Mul, Scalar::I32(a), Scalar::I32(b)) => Scalar::I32(a.wrapping_mul(b)),
        (BinaryOp::Div, Scalar::I32(a), Scalar::I32(b)) => Scalar::I32(a / b),
        (BinaryOp::Rem, Scalar::I32(a), Scalar::I32(b)) => Scalar::I32(a % b),
        (BinaryOp::And, Scalar::I32(a), Scalar::I32(b)) => Scalar::I32(a & b),
        (BinaryOp::Or, Scalar::I32(a), Scalar::I32(b)) => Scalar::I32(a | b),
        (BinaryOp::Xor, Scalar::I32(a), Scalar::I32(b)) => Scalar::I32(a ^ b),
        (BinaryOp::Shl, Scalar::I32(a), Scalar::I32(b)) => Scalar::I32(a.wrapping_shl(b as u32)),
        (BinaryOp::Shr, Scalar::I32(a), Scalar::I32(b)) => Scalar::I32(a.wrapping_shr(b as u32)),
        (BinaryOp::Eq, Scalar::I32(a), Scalar::I32(b)) => Scalar::U8(u8::from(a == b)),
        (BinaryOp::Neq, Scalar::I32(a), Scalar::I32(b)) => Scalar::U8(u8::from(a != b)),
        (BinaryOp::Lt, Scalar::I32(a), Scalar::I32(b)) => Scalar::U8(u8::from(a < b)),
        (BinaryOp::Le, Scalar::I32(a), Scalar::I32(b)) => Scalar::U8(u8::from(a <= b)),
        (BinaryOp::Gt, Scalar::I32(a), Scalar::I32(b)) => Scalar::U8(u8::from(a > b)),
        (BinaryOp::Ge, Scalar::I32(a), Scalar::I32(b)) => Scalar::U8(u8::from(a >= b)),

        (BinaryOp::Add, Scalar::U32(a), Scalar::U32(b)) => Scalar::U32(a.wrapping_add(b)),
        (BinaryOp::Sub, Scalar::U32(a), Scalar::U32(b)) => Scalar::U32(a.wrapping_sub(b)),
        (BinaryOp::Mul, Scalar::U32(a), Scalar::U32(b)) => Scalar::U32(a.wrapping_mul(b)),
        (BinaryOp::Div, Scalar::U32(a), Scalar::U32(b)) => Scalar::U32(a / b),
        (BinaryOp::Rem, Scalar::U32(a), Scalar::U32(b)) => Scalar::U32(a % b),
        (BinaryOp::And, Scalar::U32(a), Scalar::U32(b)) => Scalar::U32(a & b),
        (BinaryOp::Or, Scalar::U32(a), Scalar::U32(b)) => Scalar::U32(a | b),
        (BinaryOp::Xor, Scalar::U32(a), Scalar::U32(b)) => Scalar::U32(a ^ b),
        (BinaryOp::Shl, Scalar::U32(a), Scalar::U32(b)) => Scalar::U32(a.wrapping_shl(b)),
        (BinaryOp::Shr, Scalar::U32(a), Scalar::U32(b)) => Scalar::U32(a.wrapping_shr(b)),
        (BinaryOp::Eq, Scalar::U32(a), Scalar::U32(b)) => Scalar::U8(u8::from(a == b)),
        (BinaryOp::Neq, Scalar::U32(a), Scalar::U32(b)) => Scalar::U8(u8::from(a != b)),
        (BinaryOp::Lt, Scalar::U32(a), Scalar::U32(b)) => Scalar::U8(u8::from(a < b)),
        (BinaryOp::Le, Scalar::U32(a), Scalar::U32(b)) => Scalar::U8(u8::from(a <= b)),
        (BinaryOp::Gt, Scalar::U32(a), Scalar::U32(b)) => Scalar::U8(u8::from(a > b)),
        (BinaryOp::Ge, Scalar::U32(a), Scalar::U32(b)) => Scalar::U8(u8::from(a >= b)),

        (BinaryOp::Add, Scalar::F64(a), Scalar::F64(b)) => Scalar::F64(a + b),
        (BinaryOp::Sub, Scalar::F64(a), Scalar::F64(b)) => Scalar::F64(a - b),
        (BinaryOp::Mul, Scalar::F64(a), Scalar::F64(b)) => Scalar::F64(a * b),
        (BinaryOp::Div, Scalar::F64(a), Scalar::F64(b)) => Scalar::F64(a / b),
        (BinaryOp::Eq, Scalar::F64(a), Scalar::F64(b)) => Scalar::U8(u8::from(a == b)),
        (BinaryOp::Neq, Scalar::F64(a), Scalar::F64(b)) => Scalar::U8(u8::from(a != b)),
        (BinaryOp::Lt, Scalar::F64(a), Scalar::F64(b)) => Scalar::U8(u8::from(a < b)),
        (BinaryOp::Le, Scalar::F64(a), Scalar::F64(b)) => Scalar::U8(u8::from(a <= b)),
        (BinaryOp::Gt, Scalar::F64(a), Scalar::F64(b)) => Scalar::U8(u8::from(a > b)),
        (BinaryOp::Ge, Scalar::F64(a), Scalar::F64(b)) => Scalar::U8(u8::from(a >= b)),

        // Pointer identity comparison (e.g., interned values, same object).
        (BinaryOp::Eq, Scalar::Ptr(a), Scalar::Ptr(b)) => Scalar::U8(u8::from(a == b)),
        (BinaryOp::Neq, Scalar::Ptr(a), Scalar::Ptr(b)) => Scalar::U8(u8::from(a != b)),

        _ => panic!("unsupported binop {op:?} on {lhs:?}, {rhs:?}"),
    }
}
