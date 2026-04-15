//! Promote constant list/string literals to static data.
//!
//! Detects allocations where every slot is filled with a constant
//! value (or a pointer to another constant allocation) and moves
//! them to `Module::statics`. The alloc+stores are replaced with
//! a single `StaticRef` instruction.

use std::collections::{HashMap, HashSet};

use super::instruction::{Inst, ScalarType, Value};
use super::{Function, Module, StaticObject, StaticSlot};

/// Promote constant allocations to the module's static section.
pub fn promote(module: &mut Module) {
    for func in module.functions.values_mut() {
        promote_function(func, &mut module.statics);
    }
}

fn promote_function(func: &mut Function, statics: &mut Vec<StaticObject>) {
    for block in &mut func.blocks {
        promote_block(block, statics);
    }
}

fn promote_block(block: &mut super::Block, statics: &mut Vec<StaticObject>) {
    // Step 1: index all Const definitions.
    let mut const_vals: HashMap<Value, (ScalarType, u64)> = HashMap::new();
    for inst in &block.insts {
        if let Inst::Const(dest, ty, bits) = inst {
            const_vals.insert(*dest, (*ty, *bits));
        }
    }

    // Step 2: index all Alloc+Store sequences. Track which allocs
    // have all-constant slots.
    let mut allocs: HashMap<Value, AllocEntry> = HashMap::new();
    for (idx, inst) in block.insts.iter().enumerate() {
        if let Inst::Alloc(dest, size) = inst {
            allocs.insert(
                *dest,
                AllocEntry {
                    inst_idx: idx,
                    size: *size,
                    stores: vec![None; *size],
                    store_indices: Vec::new(),
                },
            );
        }
        if let Inst::Store(ptr, offset, val) = inst {
            if let Some(entry) = allocs.get_mut(ptr) {
                if *offset < entry.size {
                    entry.stores[*offset] = Some(*val);
                    entry.store_indices.push(idx);
                }
            }
        }
    }

    // Step 3: determine which allocs are fully constant (bottom-up).
    // An alloc is constant if every stored value is either:
    // - A Const instruction result
    // - Another fully-constant alloc (nested static)
    let mut promoted: HashMap<Value, usize> = HashMap::new(); // alloc_val → static_id
    let mut remove: HashSet<usize> = HashSet::new();

    // Process allocs in instruction order (data arrays before headers).
    let mut ordered: Vec<Value> = allocs.keys().copied().collect();
    ordered.sort_by_key(|v| allocs[v].inst_idx);

    for alloc_val in ordered {
        let entry = &allocs[&alloc_val];
        if entry.stores.iter().any(|s| s.is_none()) {
            continue; // Not all slots filled.
        }
        let mut slots: Vec<StaticSlot> = Vec::with_capacity(entry.size);
        let mut all_const = true;

        for stored_val in entry.stores.iter().flatten() {
            if let Some((ty, bits)) = const_vals.get(stored_val) {
                match ty {
                    ScalarType::U8 => slots.push(StaticSlot::U8(*bits as u8)),
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
    stores: Vec<Option<Value>>,
    store_indices: Vec<usize>,
}
