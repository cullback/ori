//! Compile-time constant evaluation pass.
//!
//! Since Ori is System T (all functions terminate), any zero-argument
//! function can be safely evaluated at compile time. This pass finds
//! such functions, runs the interpreter on them, converts the results
//! to static objects, and replaces call sites with `StaticRef`.

use std::collections::HashMap;

use super::eval::{self, Heap, Scalar};
use super::instruction::{Inst, ScalarType};
use super::{Module, StaticObject, StaticSlot};

/// Evaluate zero-argument pure functions at compile time and replace
/// their call sites with static references.
pub fn evaluate(module: &mut Module) {
    let eligible = find_eligible(module);
    if eligible.is_empty() {
        return;
    }

    // Process in order (no inter-dependencies since they're all zero-arg
    // and can't call each other in System T without parameters).
    let mut replacements: HashMap<String, Replacement> = HashMap::new();

    for func_name in &eligible {
        let mut heap = eval::new_heap();
        eval::load_statics(module, &mut heap);

        let result = eval::eval_function(module, &mut heap, func_name, &[]);

        let replacement = match result {
            Scalar::Ptr(idx) => {
                let num_existing = module.statics.len();
                let root_static = heap_to_statics(&heap, idx, num_existing, &mut module.statics);
                Replacement::Static(root_static)
            }
            scalar => Replacement::Scalar(scalar),
        };

        replacements.insert(func_name.clone(), replacement);
    }

    // Rewrite call sites across all functions.
    for func in module.functions.values_mut() {
        for block in func.blocks.values_mut() {
            for inst in &mut block.insts {
                if let Inst::Call(dest, name, args) = inst {
                    if args.is_empty() {
                        if let Some(repl) = replacements.get(name.as_str()) {
                            match repl {
                                Replacement::Static(static_id) => {
                                    *inst = Inst::StaticRef(*dest, *static_id);
                                }
                                Replacement::Scalar(scalar) => {
                                    let (_, bits) = scalar_to_bits(*scalar);
                                    *inst = Inst::Const(*dest, bits);
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    // Remove the now-dead functions.
    for name in &eligible {
        module.functions.remove(name);
    }
}

enum Replacement {
    Static(usize),
    Scalar(Scalar),
}

/// Find zero-argument functions eligible for compile-time evaluation.
/// Excludes the entry function and intrinsics.
fn find_eligible(module: &Module) -> Vec<String> {
    module
        .functions
        .iter()
        .filter(|(name, func)| {
            func.params.is_empty()
                && *name != &module.entry
                && !name.starts_with("__")
        })
        .map(|(name, _)| name.clone())
        .collect()
}

/// Convert a heap object tree (rooted at `root`) into StaticObjects.
/// Returns the static index of the root. Pre-existing statics
/// (heap indices 1..=num_existing) are mapped to their original indices.
fn heap_to_statics(
    heap: &Heap,
    root: usize,
    num_existing: usize,
    statics: &mut Vec<StaticObject>,
) -> usize {
    let mut heap_to_static: HashMap<usize, usize> = HashMap::new();
    let mut to_visit = vec![root];
    let mut visit_order = Vec::new();

    // Discover all reachable heap objects.
    while let Some(idx) = to_visit.pop() {
        if idx == 0 || heap_to_static.contains_key(&idx) {
            continue;
        }
        // Pre-existing static: heap index N maps to static index N-1.
        if idx <= num_existing {
            heap_to_static.insert(idx, idx - 1);
            continue;
        }
        // Mark as visited (placeholder index, filled below).
        heap_to_static.insert(idx, usize::MAX);
        visit_order.push(idx);

        // Queue child pointers via ptr_offsets.
        for &off in heap.ptr_offsets(idx) {
            if let Scalar::Ptr(child) = heap.load(idx, off, ScalarType::Ptr) {
                if child != 0 && !heap_to_static.contains_key(&child) {
                    to_visit.push(child);
                }
            }
        }
    }

    // Assign static indices.
    let base = statics.len();
    for (i, &heap_idx) in visit_order.iter().enumerate() {
        heap_to_static.insert(heap_idx, base + i);
    }

    // Build StaticObjects.
    for &heap_idx in &visit_order {
        let byte_len = heap.object_len(heap_idx);
        let num_slots = byte_len / 8;
        let ptr_offs = heap.ptr_offsets(heap_idx);
        let mut slots = Vec::with_capacity(num_slots);
        for i in 0..num_slots {
            let off = i * 8;
            let ty = if ptr_offs.contains(&off) {
                ScalarType::Ptr
            } else {
                ScalarType::I64
            };
            slots.push(scalar_to_slot(heap.load(heap_idx, off, ty), &heap_to_static));
        }
        statics.push(StaticObject { slots });
    }

    heap_to_static[&root]
}

fn scalar_to_slot(s: Scalar, heap_to_static: &HashMap<usize, usize>) -> StaticSlot {
    match s {
        Scalar::U8(b) => StaticSlot::U8(b),
        Scalar::U32(n) => StaticSlot::U32(n),
        Scalar::U64(n) => StaticSlot::U64(n),
        Scalar::I64(n) => StaticSlot::I64(n),
        Scalar::Ptr(0) => StaticSlot::U64(0),
        Scalar::Ptr(idx) => StaticSlot::StaticPtr(heap_to_static[&idx]),
        // For types without a dedicated StaticSlot, store as I64 bits.
        Scalar::I8(n) => StaticSlot::I64(n as i64),
        Scalar::I16(n) => StaticSlot::I64(n as i64),
        Scalar::U16(n) => StaticSlot::U64(n as u64),
        Scalar::I32(n) => StaticSlot::I64(n as i64),
        Scalar::F64(n) => StaticSlot::I64(n.to_bits() as i64),
    }
}

fn scalar_to_bits(s: Scalar) -> (ScalarType, u64) {
    match s {
        Scalar::I8(n) => (ScalarType::I8, n as u64),
        Scalar::U8(n) => (ScalarType::U8, n as u64),
        Scalar::I16(n) => (ScalarType::I16, n as u64),
        Scalar::U16(n) => (ScalarType::U16, n as u64),
        Scalar::I32(n) => (ScalarType::I32, n as u64),
        Scalar::U32(n) => (ScalarType::U32, n as u64),
        Scalar::I64(n) => (ScalarType::I64, n as u64),
        Scalar::U64(n) => (ScalarType::U64, n),
        Scalar::F64(n) => (ScalarType::F64, n.to_bits()),
        Scalar::Ptr(_) => (ScalarType::Ptr, 0),
    }
}
