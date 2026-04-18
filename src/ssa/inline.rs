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

use super::instruction::{BlockEdge, BlockId, Inst, Terminator, Value};
use super::{Block, Function, Module};

/// Maximum number of instructions in a callee for it to be inlined.
pub const MAX_INLINE_INSTS: usize = 30;

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
///
/// Excludes functions involved in any call cycle (direct or mutual
/// recursion). Inlining a member of a cycle would produce unbounded
/// expansion, since each inlined body reintroduces a call that maps
/// back to another inlineable cycle member.
fn find_candidates(module: &Module) -> HashSet<String> {
    let recursive = cyclic_functions(module);
    let mut candidates = HashSet::new();
    for (name, func) in &module.functions {
        // Skip the entry point.
        if name == &module.entry {
            continue;
        }
        if recursive.contains(name) {
            continue;
        }
        let inst_count: usize = func.blocks.values().map(|b| b.insts.len()).sum();
        if inst_count <= MAX_INLINE_INSTS {
            candidates.insert(name.clone());
        }
    }
    candidates
}

/// Find all functions that participate in any call cycle.
/// Uses Tarjan-style reachability: a function f is in a cycle if
/// f is reachable from one of its callees.
fn cyclic_functions(module: &Module) -> HashSet<String> {
    // Build call graph: caller → set of callees.
    let mut callees: HashMap<&str, HashSet<&str>> = HashMap::new();
    for (name, func) in &module.functions {
        let mut cs = HashSet::new();
        for block in func.blocks.values() {
            for inst in &block.insts {
                if let Inst::Call(_, callee, _) = inst {
                    if module.functions.contains_key(callee) {
                        cs.insert(callee.as_str());
                    }
                }
            }
        }
        callees.insert(name.as_str(), cs);
    }

    // A function is cyclic if it's reachable from any of its callees.
    let mut cyclic = HashSet::new();
    for name in module.functions.keys() {
        if reaches(&callees, name, name) {
            cyclic.insert(name.clone());
        }
    }
    cyclic
}

/// True if `target` is reachable from `start` by following callee edges.
fn reaches(callees: &HashMap<&str, HashSet<&str>>, start: &str, target: &str) -> bool {
    let mut stack: Vec<&str> = callees.get(start).map(|s| s.iter().copied().collect()).unwrap_or_default();
    let mut seen: HashSet<&str> = HashSet::new();
    while let Some(n) = stack.pop() {
        if n == target { return true; }
        if !seen.insert(n) { continue; }
        if let Some(next) = callees.get(n) {
            stack.extend(next.iter().copied());
        }
    }
    false
}

/// Inline all eligible calls within a single function.
fn inline_calls_in_function(caller: &mut Function, snapshots: &HashMap<String, Function>) {
    loop {
        let Some((block_id, inst_idx, callee_name)) = find_inline_site(caller, snapshots) else {
            break;
        };
        let callee = &snapshots[&callee_name];
        perform_inline(caller, block_id, inst_idx, callee);
    }
    // After inlining, callee function params that mapped to caller-local
    // values may have become cross-block references. Repair them by
    // threading through block params.
    repair_cross_block_refs(caller);
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
            max_val = max_val.max(p.id + 1);
        }
        for inst in &block.insts {
            if let Some(d) = inst.dest() {
                max_val = max_val.max(d.id + 1);
            }
        }
    }
    for &p in &caller.params {
        max_val = max_val.max(p.id + 1);
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
        let new_v = Value { id: next_val, ty: v.ty };
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
    let cont_param = Value { id: next_val, ty: callee.return_type };

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
        caller.blocks.get_mut(&block_id).unwrap().insts.push(remapped);
    }

    // --- Step 4: copy non-entry callee blocks ---

    for (&callee_bid, callee_block) in &callee.blocks {
        if callee_bid == callee.entry {
            continue;
        }
        let new_bid = block_map[&callee_bid];
        let mut insts = Vec::new();
        for inst in &callee_block.insts {
            let remapped = remap_inst(inst, &val_map);
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

    // Map the original call destination to the continuation parameter
    // in remaining instructions and the original terminator.
    let dest_map: HashMap<Value, Value> = [(call_dest, cont_param)].into();

    // Rewrite call_dest → cont_param in ALL existing caller blocks,
    // not just the continuation. The call result may be used in blocks
    // that were already present (e.g., blocks after the call's block
    // in the original control flow).
    for block in caller.blocks.values_mut() {
        for inst in &mut block.insts {
            rewrite_operands(inst, &dest_map);
        }
        rewrite_terminator_operands(&mut block.terminator, &dest_map);
    }

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
    let mut remapped = inst.clone();
    // Remap destination.
    if let Some(d) = remapped.dest_mut() {
        if let Some(&new_d) = map.get(d) {
            *d = new_d;
        }
    }
    // Remap operands.
    remapped.map_operands_mut(|v| { if let Some(&r) = map.get(v) { *v = r; } });
    remapped
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
            Terminator::Jump(BlockEdge {
                target: cont_block,
                args: vec![remap_value(*v, val_map)],
            })
        }
        Terminator::Jump(edge) => Terminator::Jump(BlockEdge {
            target: remap_block(edge.target),
            args: edge.args.iter().map(|v| remap_value(*v, val_map)).collect(),
        }),
        Terminator::Branch {
            cond,
            then_edge,
            else_edge,
        } => Terminator::Branch {
            cond: remap_value(*cond, val_map),
            then_edge: BlockEdge {
                target: remap_block(then_edge.target),
                args: then_edge.args.iter().map(|v| remap_value(*v, val_map)).collect(),
            },
            else_edge: BlockEdge {
                target: remap_block(else_edge.target),
                args: else_edge.args.iter().map(|v| remap_value(*v, val_map)).collect(),
            },
        },
        Terminator::SwitchInt {
            scrutinee,
            arms,
            default,
        } => Terminator::SwitchInt {
            scrutinee: remap_value(*scrutinee, val_map),
            arms: arms
                .iter()
                .map(|(tag, edge)| {
                    (
                        *tag,
                        BlockEdge {
                            target: remap_block(edge.target),
                            args: edge.args.iter().map(|v| remap_value(*v, val_map)).collect(),
                        },
                    )
                })
                .collect(),
            default: default.as_ref().map(|edge| {
                BlockEdge {
                    target: remap_block(edge.target),
                    args: edge.args.iter().map(|v| remap_value(*v, val_map)).collect(),
                }
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

/// Repair cross-block references by threading values through block
/// params. After inlining, callee function params that were remapped
/// to caller-local values may appear as cross-block references.
/// This pass iteratively adds block params until every block is
/// self-contained.
fn repair_cross_block_refs(func: &mut Function) {
    let func_param_set: HashSet<Value> = func.params.iter().copied().collect();
    let mut next_val: usize = {
        let mut m = 0_usize;
        for &p in &func.params {
            m = m.max(p.id + 1);
        }
        for block in func.blocks.values() {
            for &p in &block.params {
                m = m.max(p.id + 1);
            }
            for inst in &block.insts {
                if let Some(d) = inst.dest() {
                    m = m.max(d.id + 1);
                }
            }
        }
        m
    };

    loop {
        // Find the first cross-block reference.
        let mut violation: Option<(BlockId, Value)> = None;
        'outer: for (&bid, block) in &func.blocks {
            let mut local: HashSet<Value> = block.params.iter().copied().collect();
            for inst in &block.insts {
                for v in inst.operands() {
                    if !local.contains(&v) && !func_param_set.contains(&v) {
                        violation = Some((bid, v));
                        break 'outer;
                    }
                }
                if let Some(d) = inst.dest() {
                    local.insert(d);
                }
            }
            for v in block.terminator.operands() {
                if !local.contains(&v) && !func_param_set.contains(&v) {
                    violation = Some((bid, v));
                    break 'outer;
                }
            }
        }

        let Some((bid, val)) = violation else {
            break;
        };

        // Create a fresh block param for `val` in block `bid`.
        let new_param = Value { id: next_val, ty: val.ty };
        next_val += 1;
        func.blocks.get_mut(&bid).unwrap().params.push(new_param);

        // Rewrite uses of `val` in this block to `new_param`.
        let remap: HashMap<Value, Value> = [(val, new_param)].into();
        let block = func.blocks.get_mut(&bid).unwrap();
        for inst in &mut block.insts {
            super::opt::rewrite_operands(inst, &remap);
        }
        super::opt::rewrite_terminator_operands(&mut block.terminator, &remap);

        // Update every edge that targets `bid` to pass `val` as an
        // extra arg. If `val` isn't available in the predecessor,
        // it'll be caught as a violation on the next iteration.
        let all_bids: Vec<BlockId> = func.blocks.keys().copied().collect();
        for pred_bid in all_bids {
            let block = func.blocks.get_mut(&pred_bid).unwrap();
            match &mut block.terminator {
                Terminator::Jump(edge) if edge.target == bid => {
                    edge.args.push(val);
                }
                Terminator::Branch {
                    then_edge,
                    else_edge,
                    ..
                } => {
                    if then_edge.target == bid {
                        then_edge.args.push(val);
                    }
                    if else_edge.target == bid {
                        else_edge.args.push(val);
                    }
                }
                Terminator::SwitchInt { arms, default, .. } => {
                    for (_, edge) in arms.iter_mut() {
                        if edge.target == bid {
                            edge.args.push(val);
                        }
                    }
                    if let Some(edge) = default {
                        if edge.target == bid {
                            edge.args.push(val);
                        }
                    }
                }
                _ => {}
            }
        }
    }
}
