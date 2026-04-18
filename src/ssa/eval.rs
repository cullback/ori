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
        }
    }

    pub fn alloc(&mut self, num_bytes: usize) -> usize {
        if let Some(idx) = self.free_list.pop() {
            let obj = &mut self.objects[idx];
            obj.rc = 1;
            obj.data.clear();
            obj.data.resize(num_bytes, 0);
            obj.ptr_offsets.clear();
            obj.type_map.clear();
            idx
        } else {
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
            // For sub-8-byte types (e.g., U8 in strings), the dest type is
            // authoritative and determines the stride. For 8-byte types, the
            // lowering may use Ptr generically, so use load_dyn_auto which
            // checks the type_map to recover the actual stored type.
            if dest.ty.byte_width() < 8 {
                Some(heap.load_dyn(heap_idx, slot, dest.ty))
            } else {
                Some(heap.load_dyn_auto(heap_idx, slot))
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
        "__list_len" => {
            // args: [list_ptr] → U64 length
            let Scalar::Ptr(list_idx) = args[0] else {
                panic!("__list_len: expected Ptr");
            };
            let len = heap.load(list_idx, 0, ScalarType::U64);
            Some(len)
        }
        "__list_get" => {
            // args: [list_ptr, index_u64] → element (unchecked)
            let Scalar::Ptr(list_idx) = args[0] else {
                panic!("__list_get: expected Ptr");
            };
            let idx = scalar_to_usize(args[1]);
            let Scalar::Ptr(data_idx) = heap.load(list_idx, 16, ScalarType::Ptr) else {
                panic!("__list_get: data slot is not Ptr");
            };
            // Per Perceus, loading a `Ptr` from heap creates a new
            // alias and needs an extra reference. The RC pass inserts
            // `rc_inc` after `Load`/`LoadDyn` instructions; intrinsics
            // that do an implicit load (like this one) must do the
            // same internally, otherwise the caller's later `rc_dec`
            // on the returned value underflows the heap slot's
            // actual reference count and the original list's element
            // is freed while still in use.
            let elem = heap.load_dyn_auto(data_idx, idx);
            if let Scalar::Ptr(p) = elem {
                heap.rc_inc(p);
            }
            Some(elem)
        }
        "__list_set" => {
            // args: [list_ptr, index_u64, new_val] → new_list_ptr
            let Scalar::Ptr(list_idx) = args[0] else {
                panic!("__list_set: expected Ptr");
            };
            let idx = scalar_to_usize(args[1]);
            let len = heap.load(list_idx, 0, ScalarType::U64);
            let cap = heap.load(list_idx, 8, ScalarType::U64);
            let Scalar::Ptr(old_data) = heap.load(list_idx, 16, ScalarType::Ptr) else {
                panic!("__list_set: data is not Ptr");
            };
            // Clone data buffer and list header
            let new_data = heap.clone_object(old_data);
            // The old element at this index was rc_inc'd by clone;
            // we're replacing it, so dec the old and inc the new.
            let old_elem = heap.load_dyn_auto(new_data, idx);
            if let Scalar::Ptr(p) = old_elem { heap.rc_dec(p); }
            let val = args[2];
            if let Scalar::Ptr(p) = val { heap.rc_inc(p); }
            let data_elem_ty = heap.lookup_type(old_data, 0).unwrap_or(ScalarType::I64);
            let elem_ty = if data_elem_ty == ScalarType::U8 { ScalarType::U8 } else { ScalarType::I64 };
            let val = if elem_ty == ScalarType::U8 && !matches!(val, Scalar::U8(_)) {
                Scalar::U8(scalar_to_u64(val) as u8)
            } else {
                val
            };
            heap.store_dyn(new_data, idx, val, elem_ty);
            let new_list = heap.alloc(24);
            heap.store(new_list, 0, len);
            heap.store(new_list, 8, cap);
            heap.store(new_list, 16, Scalar::Ptr(new_data));
            Some(Scalar::Ptr(new_list))
        }
        "__list_copy_into" => {
            // args: [src_ptr, dst_ptr, count] → I64(0). Copies `count`
            // 8-byte elements from src to dst, bumping rc on any `Ptr` children.
            // Self-copy is a no-op (same heap index).
            let Scalar::Ptr(src) = args[0] else {
                panic!("__list_copy_into: expected Ptr for src");
            };
            let Scalar::Ptr(dst) = args[1] else {
                panic!("__list_copy_into: expected Ptr for dst");
            };
            if src == dst {
                return Some(Scalar::I64(0));
            }
            let n = scalar_to_usize(args[2]);
            let byte_count = n * 8;
            // Copy raw bytes
            let src_bytes = heap.objects[src].data[..byte_count].to_vec();
            heap.objects[dst].data[..byte_count].copy_from_slice(&src_bytes);
            // Copy ptr_offsets from src that fall in the copied range, and rc_inc each
            let src_ptr_offsets: Vec<usize> = heap.objects[src]
                .ptr_offsets
                .iter()
                .copied()
                .filter(|&off| off < byte_count)
                .collect();
            let src_type_entries: Vec<(usize, ScalarType)> = heap.objects[src]
                .type_map
                .iter()
                .copied()
                .filter(|(off, _)| *off < byte_count)
                .collect();
            for &off in &src_ptr_offsets {
                if let Scalar::Ptr(p) = read_scalar(&heap.objects[dst].data, off, ScalarType::Ptr) {
                    if p != 0 {
                        heap.rc_inc(p);
                    }
                }
                if !heap.objects[dst].ptr_offsets.contains(&off) {
                    heap.objects[dst].ptr_offsets.push(off);
                }
            }
            for (off, ty) in src_type_entries {
                if let Some(entry) = heap.objects[dst].type_map.iter_mut().find(|(o, _)| *o == off) {
                    entry.1 = ty;
                } else {
                    heap.objects[dst].type_map.push((off, ty));
                }
            }
            Some(Scalar::I64(0))
        }
        "__list_append" => {
            // args: [list_ptr, val] → new_list_ptr
            let Scalar::Ptr(list_idx) = args[0] else {
                panic!("__list_append: expected Ptr");
            };
            let Scalar::U64(len) = heap.load(list_idx, 0, ScalarType::U64) else {
                panic!("__list_append: len is not U64");
            };
            let Scalar::Ptr(old_data) = heap.load(list_idx, 16, ScalarType::Ptr) else {
                panic!("__list_append: data is not Ptr");
            };
            let new_len = len + 1;
            let new_data = heap.clone_object(old_data);
            if let Scalar::Ptr(p) = args[1] { heap.rc_inc(p); }
            // Detect element stride from existing data buffer (U8 for strings, 8 otherwise).
            let data_elem_ty = heap.lookup_type(old_data, 0).unwrap_or(ScalarType::I64);
            let elem_ty = if data_elem_ty == ScalarType::U8 { ScalarType::U8 } else { ScalarType::I64 };
            // Coerce value to match buffer element type if needed.
            let val = if elem_ty == ScalarType::U8 && !matches!(args[1], Scalar::U8(_)) {
                Scalar::U8(scalar_to_u64(args[1]) as u8)
            } else {
                args[1]
            };
            heap.store_dyn(new_data, len as usize, val, elem_ty);
            let new_list = heap.alloc(24);
            heap.store(new_list, 0, Scalar::U64(new_len));
            heap.store(new_list, 8, Scalar::U64(new_len));
            heap.store(new_list, 16, Scalar::Ptr(new_data));
            Some(Scalar::Ptr(new_list))
        }
        "__list_reverse" => {
            // args: [list_ptr] → new_list_ptr with elements in reverse order
            let Scalar::Ptr(list_idx) = args[0] else {
                panic!("__list_reverse: expected Ptr");
            };
            let Scalar::U64(len) = heap.load(list_idx, 0, ScalarType::U64) else {
                panic!("__list_reverse: len is not U64");
            };
            let Scalar::Ptr(old_data) = heap.load(list_idx, 16, ScalarType::Ptr) else {
                panic!("__list_reverse: data is not Ptr");
            };
            #[expect(clippy::cast_possible_truncation)]
            let len_usize = len as usize;
            let new_data = heap.alloc(len_usize * 8);
            for i in 0..len_usize {
                let elem = heap.load_dyn_auto(old_data, i);
                if let Scalar::Ptr(p) = elem { heap.rc_inc(p); }
                heap.store(new_data, (len_usize - 1 - i) * 8, elem);
            }
            let new_list = heap.alloc(24);
            heap.store(new_list, 0, Scalar::U64(len));
            heap.store(new_list, 8, Scalar::U64(len));
            heap.store(new_list, 16, Scalar::Ptr(new_data));
            Some(Scalar::Ptr(new_list))
        }
        "__list_sublist" => {
            // args: [list_ptr, start_u64, count_u64] → new_list_ptr
            let Scalar::Ptr(list_idx) = args[0] else {
                panic!("__list_sublist: expected Ptr");
            };
            let start = scalar_to_usize(args[1]);
            let count = scalar_to_usize(args[2]);
            let Scalar::Ptr(old_data) = heap.load(list_idx, 16, ScalarType::Ptr) else {
                panic!("__list_sublist: data is not Ptr");
            };
            let new_data = heap.alloc(count * 8);
            for i in 0..count {
                let elem = heap.load_dyn_auto(old_data, start + i);
                if let Scalar::Ptr(p) = elem { heap.rc_inc(p); }
                heap.store(new_data, i * 8, elem);
            }
            let new_list = heap.alloc(24);
            let count_u64 = count as u64;
            heap.store(new_list, 0, Scalar::U64(count_u64));
            heap.store(new_list, 8, Scalar::U64(count_u64));
            heap.store(new_list, 16, Scalar::Ptr(new_data));
            Some(Scalar::Ptr(new_list))
        }
        "__list_repeat" => {
            // args: [val, count] → list_ptr
            let val = args[0];
            let Scalar::U64(count) = args[1] else {
                panic!("__list_repeat: expected U64 count");
            };
            #[expect(clippy::cast_possible_truncation)]
            let n = count as usize;
            let data = heap.alloc(n * 8);
            for i in 0..n {
                if let Scalar::Ptr(p) = val { heap.rc_inc(p); }
                heap.store(data, i * 8, val);
            }
            let list = heap.alloc(24);
            heap.store(list, 0, Scalar::U64(count));
            heap.store(list, 8, Scalar::U64(count));
            heap.store(list, 16, Scalar::Ptr(data));
            Some(Scalar::Ptr(list))
        }
        "__list_range" => {
            // args: [start, end] → list_ptr of U64s
            let Scalar::U64(start) = args[0] else {
                panic!("__list_range: expected U64 start");
            };
            let Scalar::U64(end) = args[1] else {
                panic!("__list_range: expected U64 end");
            };
            let n = if end > start { end - start } else { 0 };
            #[expect(clippy::cast_possible_truncation)]
            let n_usize = n as usize;
            let data = heap.alloc(n_usize * 8);
            for i in 0..n_usize {
                heap.store(data, i * 8, Scalar::U64(start + i as u64));
            }
            let list = heap.alloc(24);
            heap.store(list, 0, Scalar::U64(n));
            heap.store(list, 8, Scalar::U64(n));
            heap.store(list, 16, Scalar::Ptr(data));
            Some(Scalar::Ptr(list))
        }
        "__num_to_str" => {
            // args: [number] → str_ptr (List(U8))
            let s = match args[0] {
                Scalar::I8(n) => n.to_string(),
                Scalar::U8(n) => n.to_string(),
                Scalar::I16(n) => n.to_string(),
                Scalar::U16(n) => n.to_string(),
                Scalar::I32(n) => n.to_string(),
                Scalar::U32(n) => n.to_string(),
                Scalar::I64(n) => n.to_string(),
                Scalar::U64(n) => n.to_string(),
                Scalar::F64(n) => n.to_string(),
                _ => panic!("__num_to_str: expected number"),
            };
            let bytes = s.into_bytes();
            let len = bytes.len();
            let data = heap.alloc(len * 8);
            for (i, b) in bytes.into_iter().enumerate() {
                heap.store(data, i * 8, Scalar::U8(b));
            }
            let list = heap.alloc(24);
            heap.store(list, 0, Scalar::U64(len as u64));
            heap.store(list, 8, Scalar::U64(len as u64));
            heap.store(list, 16, Scalar::Ptr(data));
            Some(Scalar::Ptr(list))
        }
        "__num_hash" => {
            // args: [number] → U64 hash
            // FNV-1a-style bit mixing: cast to u64, then mix.
            #[expect(clippy::cast_sign_loss)]
            let bits: u64 = match args[0] {
                Scalar::I64(n) => n as u64,
                Scalar::U64(n) => n,
                Scalar::I32(n) => n as u64,
                Scalar::U32(n) => u64::from(n),
                Scalar::I16(n) => n as u64,
                Scalar::U16(n) => u64::from(n),
                Scalar::I8(n) => n as u64,
                Scalar::U8(n) => u64::from(n),
                Scalar::F64(n) => n.to_bits(),
                // Bool is now U8, handled above.
                Scalar::Ptr(idx) => idx as u64,
            };
            // FNV-1a: hash one u64 value
            let hash = (14695981039346656037_u64 ^ bits).wrapping_mul(1099511628211);
            Some(Scalar::U64(hash))
        }
        "__str_concat" => {
            // args: [str_a, str_b] → str_ptr (List(U8))
            let Scalar::Ptr(a_idx) = args[0] else {
                panic!("__str_concat: expected Ptr");
            };
            let Scalar::Ptr(b_idx) = args[1] else {
                panic!("__str_concat: expected Ptr");
            };
            let Scalar::U64(a_len) = heap.load(a_idx, 0, ScalarType::U64) else {
                panic!("__str_concat: expected U64 len");
            };
            let Scalar::U64(b_len) = heap.load(b_idx, 0, ScalarType::U64) else {
                panic!("__str_concat: expected U64 len");
            };
            let Scalar::Ptr(a_data) = heap.load(a_idx, 16, ScalarType::Ptr) else {
                panic!("__str_concat: expected Ptr data");
            };
            let Scalar::Ptr(b_data) = heap.load(b_idx, 16, ScalarType::Ptr) else {
                panic!("__str_concat: expected Ptr data");
            };
            let total = a_len + b_len;
            let data = heap.alloc(total as usize * 8);
            for i in 0..a_len as usize {
                heap.store(data, i * 8, heap.load(a_data, i * 8, ScalarType::U8));
            }
            for i in 0..b_len as usize {
                heap.store(data, (a_len as usize + i) * 8, heap.load(b_data, i * 8, ScalarType::U8));
            }
            let list = heap.alloc(24);
            heap.store(list, 0, Scalar::U64(total));
            heap.store(list, 8, Scalar::U64(total));
            heap.store(list, 16, Scalar::Ptr(data));
            Some(Scalar::Ptr(list))
        }
        "__u64_from_u8" => {
            // args: [u8] → u64 (widening conversion)
            let Scalar::U8(n) = args[0] else {
                panic!("__u64_from_u8: expected U8, got {:?}", args[0]);
            };
            Some(Scalar::U64(u64::from(n)))
        }
        "__u32_from_u8" => {
            let Scalar::U8(n) = args[0] else {
                panic!("__u32_from_u8: expected U8, got {:?}", args[0]);
            };
            Some(Scalar::U32(u32::from(n)))
        }
        #[expect(clippy::cast_possible_truncation)]
        "__to_u8" => {
            let n = match args[0] {
                Scalar::U32(n) => n as u8,
                Scalar::U64(n) => n as u8,
                other => panic!("__to_u8: unexpected {other:?}"),
            };
            Some(Scalar::U8(n))
        }
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
