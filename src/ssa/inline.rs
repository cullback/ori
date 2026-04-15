//! SSA function inlining pass.
//!
//! Replaces `Call` instructions with the callee's body spliced inline.
//! Callee parameters are substituted with the call arguments, callee
//! blocks are renumbered and appended to the caller, and `Return`
//! terminators become `Jump`s to a continuation block.
//!
//! Inline candidates are small non-recursive user functions. Intrinsics
//! (prefixed `__`) are never inlined.

use std::collections::{HashMap, HashSet};

use super::instruction::{BlockId, Inst, Terminator, Value};
use super::{Block, Function, Module};

/// Maximum number of instructions in a callee for it to be inlined.
const MAX_INLINE_INSTS: usize = 12;

/// Run inlining on all functions in the module.
pub fn inline(module: &mut Module) {
    // Snapshot callee bodies before mutating — we inline from these
    // immutable copies so we never read a function while writing it.
    let candidates = find_candidates(module);
    if candidates.is_empty() {
        return;
    }
    let snapshots: HashMap<String, Function> = candidates
        .iter()
        .map(|name| (name.clone(), module.functions[name].clone()))
        .collect();

    for func in module.functions.values_mut() {
        inline_calls_in_function(func, &snapshots);
    }
}

/// Identify functions small enough to inline.
fn find_candidates(module: &Module) -> HashSet<String> {
    let mut candidates = HashSet::new();
    for (name, func) in &module.functions {
        // Skip the entry point.
        if name == &module.entry {
            continue;
        }
        let inst_count: usize = func.blocks.values().map(|b| b.insts.len()).sum();
        if inst_count <= MAX_INLINE_INSTS {
            candidates.insert(name.clone());
        }
    }
    candidates
}

/// Inline all eligible calls within a single function.
fn inline_calls_in_function(caller: &mut Function, snapshots: &HashMap<String, Function>) {
    // Iterate until no more inlining happens (handles transitive inlining).
    loop {
        let Some((block_id, inst_idx, callee_name)) = find_inline_site(caller, snapshots) else {
            break;
        };
        let callee = &snapshots[&callee_name];
        perform_inline(caller, block_id, inst_idx, callee);
    }
}

/// Find the first Call instruction that targets an inlineable callee.
fn find_inline_site(
    caller: &Function,
    snapshots: &HashMap<String, Function>,
) -> Option<(BlockId, usize, String)> {
    for (&bid, block) in &caller.blocks {
        for (ii, inst) in block.insts.iter().enumerate() {
            if let Inst::Call(_, name, _) = inst {
                if snapshots.contains_key(name) && name != &caller.name {
                    return Some((bid, ii, name.clone()));
                }
            }
        }
    }
    None
}

/// Splice the callee's body into the caller at the given call site.
fn perform_inline(
    caller: &mut Function,
    block_id: BlockId,
    inst_idx: usize,
    callee: &Function,
) {
    let Inst::Call(call_dest, _, ref call_args) = caller.blocks[&block_id].insts[inst_idx] else {
        panic!("expected Call instruction at inline site");
    };
    let call_dest = call_dest;
    let call_args: Vec<Value> = call_args.clone();

    // --- Step 1: compute remapping for Values and BlockIds ---

    // Find the max Value index in the caller to avoid collisions.
    let mut max_val = 0_usize;
    for block in caller.blocks.values() {
        for &p in &block.params {
            max_val = max_val.max(p.0 + 1);
        }
        for inst in &block.insts {
            if let Some(d) = inst.dest() {
                max_val = max_val.max(d.0 + 1);
            }
        }
    }
    for &p in &caller.params {
        max_val = max_val.max(p.0 + 1);
    }

    // Build Value remap: callee params → call args, callee locals → fresh values.
    let mut val_map: HashMap<Value, Value> = HashMap::new();
    for (cp, ca) in callee.params.iter().zip(&call_args) {
        val_map.insert(*cp, *ca);
    }

    // Remap all other values in the callee to fresh values.
    let mut next_val = max_val;
    let mut fresh = |v: Value, map: &mut HashMap<Value, Value>| -> Value {
        if let Some(&mapped) = map.get(&v) {
            return mapped;
        }
        let new_v = Value(next_val);
        next_val += 1;
        map.insert(v, new_v);
        new_v
    };

    // Pre-scan all callee values to allocate fresh IDs.
    for block in callee.blocks.values() {
        for &p in &block.params {
            fresh(p, &mut val_map);
        }
        for inst in &block.insts {
            if let Some(d) = inst.dest() {
                fresh(d, &mut val_map);
            }
        }
    }

    // BlockId remap: callee non-entry blocks → fresh BlockIds in the caller.
    let mut block_map: HashMap<BlockId, BlockId> = HashMap::new();
    for &bid in callee.blocks.keys() {
        if bid == callee.entry {
            continue; // Entry block is merged into the call site block.
        }
        let new_bid = BlockId(caller.next_block);
        caller.next_block += 1;
        block_map.insert(bid, new_bid);
    }

    let remap_block = |bid: BlockId| -> BlockId {
        debug_assert!(
            bid != callee.entry,
            "callee entry block should not appear as jump target"
        );
        block_map[&bid]
    };

    // --- Step 2: create continuation block ---

    // The continuation block receives the return value as a parameter.
    let cont_block_id = BlockId(caller.next_block);
    caller.next_block += 1;
    let cont_param = Value(next_val);

    // Split the caller block: instructions after the call go into the continuation.
    let remaining_insts: Vec<Inst> = caller.blocks.get_mut(&block_id).unwrap()
        .insts
        .split_off(inst_idx + 1);
    // Remove the Call instruction itself.
    caller.blocks.get_mut(&block_id).unwrap().insts.pop();

    // --- Step 3: copy callee entry block instructions into caller block ---

    let callee_entry = &callee.blocks[&callee.entry];

    // Compute the new terminator first so we can swap in one step.
    let new_terminator =
        remap_terminator(&callee_entry.terminator, &val_map, &remap_block, cont_block_id);
    let original_terminator = std::mem::replace(
        &mut caller.blocks.get_mut(&block_id).unwrap().terminator,
        new_terminator,
    );

    for inst in &callee_entry.insts {
        let remapped = remap_inst(inst, &val_map);
        if let Some(d) = inst.dest() {
            if let Some(ty) = callee.value_types.get(&d) {
                caller.value_types.insert(val_map[&d], *ty);
            }
        }
        caller.blocks.get_mut(&block_id).unwrap().insts.push(remapped);
    }

    // --- Step 4: copy non-entry callee blocks ---

    for (&callee_bid, callee_block) in &callee.blocks {
        if callee_bid == callee.entry {
            continue;
        }
        let new_bid = block_map[&callee_bid];
        // Copy param types.
        for &p in &callee_block.params {
            if let Some(ty) = callee.value_types.get(&p) {
                caller.value_types.insert(val_map[&p], *ty);
            }
        }
        let mut insts = Vec::new();
        for inst in &callee_block.insts {
            let remapped = remap_inst(inst, &val_map);
            if let Some(d) = inst.dest() {
                if let Some(ty) = callee.value_types.get(&d) {
                    caller.value_types.insert(val_map[&d], *ty);
                }
            }
            insts.push(remapped);
        }
        let new_block = Block {
            params: callee_block
                .params
                .iter()
                .map(|p| val_map[p])
                .collect(),
            insts,
            terminator: remap_terminator(
                &callee_block.terminator,
                &val_map,
                &remap_block,
                cont_block_id,
            ),
        };
        caller.blocks.insert(new_bid, new_block);
    }

    // --- Step 5: create continuation block with remaining instructions ---

    let ret_ty = callee.return_type;
    caller.value_types.insert(cont_param, ret_ty);
    // Map the original call destination to the continuation parameter
    // in remaining instructions and the original terminator.
    let dest_map: HashMap<Value, Value> = [(call_dest, cont_param)].into();

    let cont_block = Block {
        params: vec![cont_param],
        insts: remaining_insts
            .into_iter()
            .map(|mut inst| {
                rewrite_operands(&mut inst, &dest_map);
                inst
            })
            .collect(),
        terminator: {
            let mut t = original_terminator;
            rewrite_terminator_operands(&mut t, &dest_map);
            t
        },
    };
    caller.blocks.insert(cont_block_id, cont_block);
}

// ---- Remapping helpers ----

fn remap_value(v: Value, map: &HashMap<Value, Value>) -> Value {
    map.get(&v).copied().unwrap_or(v)
}

fn remap_inst(inst: &Inst, map: &HashMap<Value, Value>) -> Inst {
    match inst {
        Inst::Const(d, ty, bits) => Inst::Const(remap_value(*d, map), *ty, *bits),
        Inst::BinOp(d, op, l, r) => {
            Inst::BinOp(remap_value(*d, map), *op, remap_value(*l, map), remap_value(*r, map))
        }
        Inst::Call(d, name, args) => Inst::Call(
            remap_value(*d, map),
            name.clone(),
            args.iter().map(|v| remap_value(*v, map)).collect(),
        ),
        Inst::Alloc(d, sz) => Inst::Alloc(remap_value(*d, map), *sz),
        Inst::Load(d, ptr, off) => {
            Inst::Load(remap_value(*d, map), remap_value(*ptr, map), *off)
        }
        Inst::Store(ptr, off, val) => {
            Inst::Store(remap_value(*ptr, map), *off, remap_value(*val, map))
        }
        Inst::LoadDyn(d, ptr, idx) => Inst::LoadDyn(
            remap_value(*d, map),
            remap_value(*ptr, map),
            remap_value(*idx, map),
        ),
        Inst::StoreDyn(ptr, idx, val) => Inst::StoreDyn(
            remap_value(*ptr, map),
            remap_value(*idx, map),
            remap_value(*val, map),
        ),
        Inst::RcInc(v) => Inst::RcInc(remap_value(*v, map)),
        Inst::RcDec(v) => Inst::RcDec(remap_value(*v, map)),
        Inst::Reset(d, ptr, slots) => {
            Inst::Reset(remap_value(*d, map), remap_value(*ptr, map), slots.clone())
        }
        Inst::Reuse(d, tok, sz) => {
            Inst::Reuse(remap_value(*d, map), remap_value(*tok, map), *sz)
        }
        Inst::StaticRef(d, id) => Inst::StaticRef(remap_value(*d, map), *id),
    }
}

fn remap_terminator(
    term: &Terminator,
    val_map: &HashMap<Value, Value>,
    remap_block: &dyn Fn(BlockId) -> BlockId,
    cont_block: BlockId,
) -> Terminator {
    match term {
        Terminator::Return(v) => {
            // Return becomes a jump to the continuation block.
            Terminator::Jump(cont_block, vec![remap_value(*v, val_map)])
        }
        Terminator::Jump(target, args) => Terminator::Jump(
            remap_block(*target),
            args.iter().map(|v| remap_value(*v, val_map)).collect(),
        ),
        Terminator::Branch {
            cond,
            then_block,
            then_args,
            else_block,
            else_args,
        } => Terminator::Branch {
            cond: remap_value(*cond, val_map),
            then_block: remap_block(*then_block),
            then_args: then_args.iter().map(|v| remap_value(*v, val_map)).collect(),
            else_block: remap_block(*else_block),
            else_args: else_args.iter().map(|v| remap_value(*v, val_map)).collect(),
        },
        Terminator::SwitchInt {
            scrutinee,
            arms,
            default,
        } => Terminator::SwitchInt {
            scrutinee: remap_value(*scrutinee, val_map),
            arms: arms
                .iter()
                .map(|(tag, bid, args)| {
                    (
                        *tag,
                        remap_block(*bid),
                        args.iter().map(|v| remap_value(*v, val_map)).collect(),
                    )
                })
                .collect(),
            default: default.as_ref().map(|(bid, args)| {
                (
                    remap_block(*bid),
                    args.iter().map(|v| remap_value(*v, val_map)).collect(),
                )
            }),
        },
    }
}

fn rewrite_operands(inst: &mut Inst, map: &HashMap<Value, Value>) {
    // Reuse the same logic as opt.rs
    super::opt::rewrite_operands(inst, map);
}

fn rewrite_terminator_operands(term: &mut Terminator, map: &HashMap<Value, Value>) {
    super::opt::rewrite_terminator_operands(term, map);
}
