//! Promote constant allocations to the module's static section.
//!
//! Detects allocations where every slot is filled with a constant
//! value (or a pointer to another constant allocation) and moves
//! them to `Module::statics`. The alloc+stores are replaced with a
//! single `StaticRef` instruction. Static objects use a sentinel
//! refcount and never participate in RC operations at runtime.
//!
//! ## How
//!
//! Per function, scan blocks in order. For each `Alloc(dest, n)`:
//! - Track the Const values flowing into `Store(dest, off, val)` and
//!   `StaticRef` values from earlier promotions.
//! - If every slot is filled with a known constant (or a pointer
//!   into the existing static set), allocate a `StaticObject` in
//!   `Module::statics`, replace the `Alloc` with a `StaticRef`, and
//!   drop the now-redundant `Store`s.
//!
//! ## Input invariants
//!
//! - Explicit-block-params (from `ssa_construct`). Required so we can
//!   identify which Stores correspond to which Alloc by SSA value
//!   id without cross-block aliasing.
//!
//! ## Output invariants
//!
//! - Promoted allocations become `StaticRef` instructions; their
//!   `Store`s are removed.
//! - `Module::statics` contains the resulting frozen objects.
//! - All other invariants from upstream are preserved.
//!
//! ## Notes
//!
//! - Runs before `optimize` so subsequent constant folding and DCE
//!   can lean on `StaticRef` values being trivially known.
//! - `emit_drops` and `elide_static_rc` later treat `StaticRef`
//!   values as no-ops (sentinel refcount means Free/RcDec do nothing).

use std::collections::{HashMap, HashSet};

use crate::ssa::instruction::{Inst, ScalarType, Value};
use crate::ssa::{Function, Module, StaticObject, StaticSlot};

/// Promote constant allocations to the module's static section.
pub fn promote(module: &mut Module) {
    for func in module.functions.values_mut() {
        promote_function(func, &mut module.statics);
    }
}

fn promote_function(func: &mut Function, statics: &mut Vec<StaticObject>) {
    for block in func.blocks.values_mut() {
        promote_block(block, statics);
    }
}

fn promote_block(block: &mut crate::ssa::Block, statics: &mut Vec<StaticObject>) {
    // Step 1: index all Const definitions.
    let mut const_vals: HashMap<Value, (ScalarType, u64)> = HashMap::new();
    for inst in &block.insts {
        if let Inst::Const(dest, bits) = inst {
            const_vals.insert(*dest, (dest.ty, *bits));
        }
    }

    // Step 2: index all Alloc+Store sequences. Track which allocs
    // have all-constant slots. After the byte-backed-heap refactor,
    // store offsets are byte offsets but each store covers
    // `val.ty.byte_width()` bytes (typically 8). Track stores by
    // offset and verify full coverage in step 3.
    let mut allocs: HashMap<Value, AllocEntry> = HashMap::new();
    for (idx, inst) in block.insts.iter().enumerate() {
        if let Inst::Alloc(dest, size) = inst {
            allocs.insert(
                *dest,
                AllocEntry {
                    inst_idx: idx,
                    size: *size,
                    stores: Vec::new(),
                    store_indices: Vec::new(),
                },
            );
        }
        if let Inst::Store(ptr, offset, val) = inst {
            if let Some(entry) = allocs.get_mut(ptr) {
                if *offset < entry.size {
                    entry.stores.push((*offset, *val));
                    entry.store_indices.push(idx);
                }
            }
        }
    }

    // Step 3: determine which allocs are fully constant (bottom-up).
    // An alloc is constant if every stored value is either:
    // - A Const instruction result
    // - Another fully-constant alloc (nested static)
    // AND the stores tile the entire allocation without gaps.
    let mut promoted: HashMap<Value, usize> = HashMap::new(); // alloc_val → static_id
    let mut remove: HashSet<usize> = HashSet::new();

    // Process allocs in instruction order (data arrays before headers).
    let mut ordered: Vec<Value> = allocs.keys().copied().collect();
    ordered.sort_by_key(|v| allocs[v].inst_idx);

    for alloc_val in ordered {
        let entry = &allocs[&alloc_val];
        // Sort stores by offset and verify they cover [0, size)
        // contiguously without overlap. Use byte widths derived from
        // each stored value's type.
        let mut stores: Vec<(usize, Value)> = entry.stores.clone();
        stores.sort_by_key(|(off, _)| *off);
        let mut cursor = 0usize;
        let mut fully_covered = true;
        for (offset, val) in &stores {
            if *offset != cursor {
                fully_covered = false;
                break;
            }
            cursor += val.ty.byte_width();
        }
        if !fully_covered || cursor != entry.size {
            continue;
        }

        let mut slots: Vec<StaticSlot> = Vec::with_capacity(stores.len());
        let mut all_const = true;

        for (_, stored_val) in &stores {
            if let Some((ty, bits)) = const_vals.get(stored_val) {
                match ty {
                    ScalarType::U8 => slots.push(StaticSlot::U8(*bits as u8)),
                    ScalarType::U32 => slots.push(StaticSlot::U32(*bits as u32)),
                    ScalarType::U64 => slots.push(StaticSlot::U64(*bits)),
                    ScalarType::I64 => slots.push(StaticSlot::I64(*bits as i64)),
                    _ => {
                        all_const = false;
                        break;
                    }
                }
            } else if let Some(&nested_id) = promoted.get(stored_val) {
                slots.push(StaticSlot::StaticPtr(nested_id));
            } else {
                all_const = false;
                break;
            }
        }

        if all_const {
            let static_id = statics.len();
            statics.push(StaticObject { slots });
            promoted.insert(alloc_val, static_id);
            remove.insert(entry.inst_idx);
            for &si in &entry.store_indices {
                remove.insert(si);
            }
        }
    }

    if promoted.is_empty() {
        return;
    }

    // Step 4: rewrite instructions.
    let old = std::mem::take(&mut block.insts);
    let mut new_insts = Vec::with_capacity(old.len());
    for (idx, inst) in old.into_iter().enumerate() {
        if remove.contains(&idx) {
            if let Inst::Alloc(dest, _) = &inst {
                if let Some(&static_id) = promoted.get(dest) {
                    new_insts.push(Inst::StaticRef(*dest, static_id));
                    continue;
                }
            }
            continue; // Drop stores for promoted allocs.
        }
        new_insts.push(inst);
    }
    block.insts = new_insts;
}

struct AllocEntry {
    inst_idx: usize,
    size: usize,
    /// `(byte_offset, value)` pairs in the order stores were emitted.
    /// Step 3 sorts by offset and checks contiguous coverage.
    stores: Vec<(usize, Value)>,
    store_indices: Vec<usize>,
}
