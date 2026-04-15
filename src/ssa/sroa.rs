//! Scalar Replacement of Aggregates (SROA).
//!
//! Decomposes small, non-escaping heap allocations into individual
//! scalar SSA values. An `Alloc(N)` that is only used in fixed-offset
//! `Store`/`Load` instructions and as block arguments can be replaced
//! by N separate values threaded through block parameters.
//!
//! Runs after inlining (so step-function bodies are visible) and
//! before RC insertion (so we don't need to worry about RC ops).

use std::collections::{HashMap, HashSet};

use super::instruction::{BlockId, Inst, ScalarType, Terminator, Value};
use super::{Function, Module};

const MAX_SROA_SLOTS: usize = 0; // TODO: fix decompose logic and re-enable

pub fn run(module: &mut Module) {
    let func_names: Vec<String> = module.functions.keys().cloned().collect();
    for name in func_names {
        let mut func = module.functions.remove(&name).unwrap();
        sroa_function(&mut func);
        module.functions.insert(name, func);
    }
}

fn sroa_function(func: &mut Function) {
    // Iterate until no more candidates (each decomposition may expose more).
    loop {
        if let Some((param_block, param_idx, num_slots)) = find_candidate(func) {
            decompose(func, param_block, param_idx, num_slots);
        } else {
            break;
        }
    }
}

/// Find a block parameter that carries a small aggregate and is safe to
/// decompose. Returns (block_id, param_index, num_slots).
fn find_candidate(func: &Function) -> Option<(BlockId, usize, usize)> {
    for (&bid, block) in &func.blocks {
        for (pi, &param) in block.params.iter().enumerate() {
            if let Some(size) = is_decomposable_param(func, bid, pi, param) {
                return Some((bid, pi, size));
            }
        }
    }
    None
}

/// Check if a block param carries a non-escaping aggregate of uniform size.
/// All values flowing into this param must be allocs of the same size,
/// and all uses must be Load/Store with constant offsets, RcInc/RcDec,
/// or passing to other decomposable block params.
fn is_decomposable_param(
    func: &Function,
    target_bid: BlockId,
    param_idx: usize,
    param_val: Value,
) -> Option<usize> {
    // Collect all values that flow into this param from predecessors.
    let mut sources: Vec<Value> = Vec::new();
    for block in func.blocks.values() {
        for (_, args) in block.terminator.successors() {
            // Check if this edge targets our block at the right param index.
        }
        let succs = block.terminator.successors();
        for (succ_id, args) in &succs {
            if *succ_id == target_bid && param_idx < args.len() {
                sources.push(args[param_idx]);
            }
        }
    }

    // All sources must be Alloc of the same size.
    let mut size = None;
    for src in &sources {
        if let Some(s) = alloc_size(func, *src) {
            if s > MAX_SROA_SLOTS {
                return None;
            }
            match size {
                None => size = Some(s),
                Some(prev) if prev == s => {}
                _ => return None, // Different sizes
            }
        } else {
            return None; // Source is not an alloc
        }
    }
    let num_slots = size?;

    // Check that the param value is only used in safe ways.
    // Collect all alias values: the param itself, plus any other params
    // it flows to.
    let mut aliases: HashSet<Value> = HashSet::new();
    aliases.insert(param_val);
    for &src in &sources {
        aliases.insert(src);
    }

    if !all_uses_safe(func, &aliases, target_bid, param_idx) {
        return None;
    }

    Some(num_slots)
}

/// Get the Alloc size for a value, if it's defined by an Alloc instruction.
fn alloc_size(func: &Function, val: Value) -> Option<usize> {
    for block in func.blocks.values() {
        for inst in &block.insts {
            if let Inst::Alloc(dest, size) = inst {
                if *dest == val {
                    return Some(*size);
                }
            }
        }
    }
    None
}

/// Check that all uses of the alias set are safe for SROA.
/// The param must only be used in Load/Store/RcInc/RcDec within blocks,
/// and when passed as a block arg, it must only go back to the same
/// target block (loop back-edge). Any other escape is rejected.
fn all_uses_safe(func: &Function, aliases: &HashSet<Value>, target_bid: BlockId, param_idx: usize) -> bool {
    for block in func.blocks.values() {
        for inst in &block.insts {
            match inst {
                Inst::Load(_, ptr, _) if aliases.contains(ptr) => {}
                Inst::Store(ptr, _, _) if aliases.contains(ptr) => {}
                Inst::RcInc(v) if aliases.contains(v) => {}
                Inst::RcDec(v) if aliases.contains(v) => {}
                Inst::Call(_, _, args) => {
                    if args.iter().any(|a| aliases.contains(a)) {
                        return false;
                    }
                }
                Inst::LoadDyn(_, ptr, _) if aliases.contains(ptr) => return false,
                Inst::StoreDyn(ptr, _, _) if aliases.contains(ptr) => return false,
                Inst::Reset(_, ptr, _) if aliases.contains(ptr) => return false,
                Inst::Reuse(_, ptr, _) if aliases.contains(ptr) => return false,
                _ => {}
            }
        }
        // Check terminator: block args carrying an alias must only
        // target the same header block (loop back-edge).
        for (succ_id, args) in block.terminator.successors() {
            for (i, arg) in args.iter().enumerate() {
                if aliases.contains(arg) {
                    if succ_id != target_bid || i != param_idx {
                        return false;
                    }
                }
            }
        }
        if let Terminator::Return(v) = &block.terminator {
            if aliases.contains(v) {
                return false;
            }
        }
    }
    true
}

/// Decompose a block parameter into N scalar parameters.
fn decompose(func: &mut Function, target_bid: BlockId, param_idx: usize, num_slots: usize) {
    let param_val = func.blocks[&target_bid].params[param_idx];

    // Collect all source allocs and the values they store per slot.
    let mut alloc_stores: HashMap<Value, Vec<Value>> = HashMap::new();

    // Find alloc → stored values for each source.
    for block in func.blocks.values() {
        // Track stores in this block: alloc_val → per-slot value
        let mut local_stores: HashMap<Value, Vec<Option<Value>>> = HashMap::new();
        for inst in &block.insts {
            if let Inst::Alloc(dest, size) = inst {
                if *size == num_slots {
                    local_stores.insert(*dest, vec![None; num_slots]);
                }
            }
            if let Inst::Store(ptr, offset, val) = inst {
                if let Some(slots) = local_stores.get_mut(ptr) {
                    if *offset < slots.len() {
                        slots[*offset] = Some(*val);
                    }
                }
            }
        }
        // Check which of these allocs flow into our target param.
        for (_, args) in block.terminator.successors() {
            if args.len() > param_idx {
                let arg = args[param_idx];
                if let Some(slots) = local_stores.get(&arg) {
                    let filled: Vec<Value> = slots.iter().map(|s| s.unwrap_or(Value(0))).collect();
                    alloc_stores.insert(arg, filled);
                }
            }
        }
    }

    // Fresh value generator.
    let mut next_val = func.value_types.keys().map(|v| v.0 + 1).max().unwrap_or(0);
    let mut fresh = || {
        let v = Value(next_val);
        next_val += 1;
        func.value_types.insert(v, ScalarType::Ptr);
        v
    };

    // Create N new block params for the target block.
    let new_params: Vec<Value> = (0..num_slots).map(|_| fresh()).collect();

    // Build a replacement map: loads from param_val[i] → new_params[i]
    let mut replacements: HashMap<Value, Value> = HashMap::new();
    for block in func.blocks.values() {
        for inst in &block.insts {
            if let Inst::Load(dest, ptr, offset) = inst {
                if *ptr == param_val && *offset < num_slots {
                    replacements.insert(*dest, new_params[*offset]);
                }
            }
        }
    }

    // Rewrite the target block's params: replace the single Ptr param with N scalars.
    {
        let block = func.blocks.get_mut(&target_bid).unwrap();
        let mut new_block_params = Vec::new();
        for (i, p) in block.params.iter().enumerate() {
            if i == param_idx {
                new_block_params.extend_from_slice(&new_params);
            } else {
                new_block_params.push(*p);
            }
        }
        block.params = new_block_params;
    }

    // Rewrite all edges targeting this block: expand the Ptr arg into N slot values.
    let block_ids: Vec<BlockId> = func.blocks.keys().copied().collect();
    for bid in &block_ids {
        let block = func.blocks.get_mut(bid).unwrap();
        expand_edge_args(&mut block.terminator, target_bid, param_idx, &alloc_stores, &new_params);
    }

    // Remove dead instructions: Alloc, Store, RcInc/RcDec on the decomposed allocs.
    let dead_allocs: HashSet<Value> = alloc_stores.keys().copied().collect();
    let mut dead_with_param = dead_allocs.clone();
    dead_with_param.insert(param_val);

    for bid in &block_ids {
        let block = func.blocks.get_mut(bid).unwrap();
        block.insts.retain(|inst| {
            match inst {
                Inst::Alloc(dest, _) if dead_allocs.contains(dest) => false,
                Inst::Store(ptr, _, _) if dead_with_param.contains(ptr) => false,
                Inst::Load(_, ptr, _) if dead_with_param.contains(ptr) => false,
                Inst::RcInc(v) if dead_with_param.contains(v) => false,
                Inst::RcDec(v) if dead_with_param.contains(v) => false,
                _ => true,
            }
        });
        // Apply value replacements.
        for inst in &mut block.insts {
            apply_replacements(inst, &replacements);
        }
        apply_replacements_terminator(&mut block.terminator, &replacements);
    }
}

fn expand_edge_args(
    term: &mut Terminator,
    target_bid: BlockId,
    param_idx: usize,
    alloc_stores: &HashMap<Value, Vec<Value>>,
    new_params: &[Value],
) {
    match term {
        Terminator::Jump(bid, args) if *bid == target_bid => {
            expand_one_edge(args, param_idx, alloc_stores, new_params);
        }
        Terminator::Branch { then_block, then_args, else_block, else_args, .. } => {
            if *then_block == target_bid {
                expand_one_edge(then_args, param_idx, alloc_stores, new_params);
            }
            if *else_block == target_bid {
                expand_one_edge(else_args, param_idx, alloc_stores, new_params);
            }
        }
        Terminator::SwitchInt { arms, default, .. } => {
            for (_, bid, args) in arms {
                if *bid == target_bid {
                    expand_one_edge(args, param_idx, alloc_stores, new_params);
                }
            }
            if let Some((bid, args)) = default {
                if *bid == target_bid {
                    expand_one_edge(args, param_idx, alloc_stores, new_params);
                }
            }
        }
        _ => {}
    }
}

fn expand_one_edge(
    args: &mut Vec<Value>,
    param_idx: usize,
    alloc_stores: &HashMap<Value, Vec<Value>>,
    fallback_params: &[Value],
) {
    if param_idx >= args.len() {
        return;
    }
    let old_arg = args[param_idx];
    let slot_values = alloc_stores.get(&old_arg)
        .map(|v| v.as_slice())
        .unwrap_or(fallback_params);
    let mut new_args = Vec::with_capacity(args.len() - 1 + slot_values.len());
    for (i, arg) in args.iter().enumerate() {
        if i == param_idx {
            new_args.extend_from_slice(slot_values);
        } else {
            new_args.push(*arg);
        }
    }
    *args = new_args;
}

fn apply_replacements(inst: &mut Inst, map: &HashMap<Value, Value>) {
    match inst {
        Inst::BinOp(_, _, lhs, rhs) => {
            if let Some(&r) = map.get(lhs) { *lhs = r; }
            if let Some(&r) = map.get(rhs) { *rhs = r; }
        }
        Inst::Call(_, _, args) => {
            for a in args { if let Some(&r) = map.get(a) { *a = r; } }
        }
        Inst::Load(_, ptr, _) => { if let Some(&r) = map.get(ptr) { *ptr = r; } }
        Inst::Store(ptr, _, val) => {
            if let Some(&r) = map.get(ptr) { *ptr = r; }
            if let Some(&r) = map.get(val) { *val = r; }
        }
        Inst::LoadDyn(_, ptr, idx) => {
            if let Some(&r) = map.get(ptr) { *ptr = r; }
            if let Some(&r) = map.get(idx) { *idx = r; }
        }
        Inst::StoreDyn(ptr, idx, val) => {
            if let Some(&r) = map.get(ptr) { *ptr = r; }
            if let Some(&r) = map.get(idx) { *idx = r; }
            if let Some(&r) = map.get(val) { *val = r; }
        }
        Inst::RcInc(v) | Inst::RcDec(v) => { if let Some(&r) = map.get(v) { *v = r; } }
        Inst::Reset(_, ptr, _) => { if let Some(&r) = map.get(ptr) { *ptr = r; } }
        Inst::Reuse(_, tok, _) => { if let Some(&r) = map.get(tok) { *tok = r; } }
        Inst::Const(_, _, _) | Inst::Alloc(_, _) | Inst::StaticRef(_, _) => {}
    }
}

fn apply_replacements_terminator(term: &mut Terminator, map: &HashMap<Value, Value>) {
    match term {
        Terminator::Return(v) => { if let Some(&r) = map.get(v) { *v = r; } }
        Terminator::Jump(_, args) => {
            for a in args { if let Some(&r) = map.get(a) { *a = r; } }
        }
        Terminator::Branch { cond, then_args, else_args, .. } => {
            if let Some(&r) = map.get(cond) { *cond = r; }
            for a in then_args { if let Some(&r) = map.get(a) { *a = r; } }
            for a in else_args { if let Some(&r) = map.get(a) { *a = r; } }
        }
        Terminator::SwitchInt { scrutinee, arms, default } => {
            if let Some(&r) = map.get(scrutinee) { *scrutinee = r; }
            for (_, _, args) in arms {
                for a in args { if let Some(&r) = map.get(a) { *a = r; } }
            }
            if let Some((_, args)) = default {
                for a in args { if let Some(&r) = map.get(a) { *a = r; } }
            }
        }
    }
}
