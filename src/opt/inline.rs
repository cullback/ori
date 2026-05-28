//! SSA function inlining pass.
//!
//! Replaces `Call` instructions with the callee's body spliced inline.
//! Callee parameters are substituted with the call arguments, callee
//! blocks are renumbered and appended to the caller, and `Return`
//! terminators become `Jump`s to a continuation block. System T's DAG
//! call graph means there's no recursion to worry about — inlining is
//! always terminating.
//!
//! ## How
//!
//! For each `Call(dest, name, args)` in each function, if `name`
//! resolves to a user-defined `Function` with ≤ `MAX_INLINE_INSTS`
//! instructions:
//! 1. Allocate fresh `Value` and `BlockId`s for the callee.
//! 2. Substitute callee params with the call args; rename all other
//!    callee values and block ids.
//! 3. Split the caller block at the call site, creating a
//!    continuation block holding the post-call instructions.
//! 4. Jump from the caller's entry-split into the renamed callee
//!    entry block. Each callee `Return(v)` becomes
//!    `Jump(continuation, [v])`.
//!
//! ## Input invariants
//!
//! - Explicit-block-params (from `ssa_construct`). The splice relies
//!   on cross-block values being threaded explicitly.
//! - Calls reference callees by string name; `__`-prefixed callees
//!   are intrinsics and are always skipped.
//!
//! ## Output invariants
//!
//! - All input invariants preserved.
//! - Inlined calls are gone; their bodies are spliced into the
//!   caller. The original callee `Function` may become unreachable
//!   (cleaned up by `dead_functions` inside `opt`).
//!
//! ## Notes
//!
//! - `MAX_INLINE_INSTS = 30`. Tunable. Higher unlocks more
//!   optimization opportunities but bloats SSA size.
//! - Splicing produces Agg/Ptr type mismatches that subsequent opt
//!   passes (`load_of_agg`, `split_agg_params`, `extract_of_pack`)
//!   clean up. Inline alone isn't a "clean" transformation; the opt
//!   pipeline that runs after it is part of the contract.

use std::collections::{HashMap, HashSet};

use crate::ssa::instruction::{BlockEdge, BlockId, Inst, ScalarType, Terminator, Value};
use crate::ssa::{Block, Function, Module};

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
                if let Inst::Call { target: callee, .. } = inst {
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
    // Cross-block refs introduced by inlining are repaired in bulk by
    // the `ssa_construct` pass that runs after `inline` in the
    // pipeline. Don't do it here (the old O(N²) repair chokes on
    // medium-large functions like F64.to_str post-inline).
}

/// Find the first Call instruction that targets an inlineable callee.
fn find_inline_site(
    caller: &Function,
    snapshots: &HashMap<String, Function>,
) -> Option<(BlockId, usize, String)> {
    for (&bid, block) in &caller.blocks {
        for (ii, inst) in block.insts.iter().enumerate() {
            if let Inst::Call { target, .. } = inst {
                if snapshots.contains_key(target) && target != &caller.name {
                    return Some((bid, ii, target.clone()));
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
    let Inst::Call { ref results, ref args, .. } = caller.blocks[&block_id].insts[inst_idx] else {
        panic!("expected Call instruction at inline site");
    };
    debug_assert_eq!(results.len(), 1, "inline: multi-result Call not yet supported");
    let call_dest = results[0];
    let call_args: Vec<Value> = args.clone();

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
    debug_assert_eq!(
        callee.return_type.len(),
        1,
        "inline: multi-value return not yet supported"
    );
    let cont_param = Value { id: next_val, ty: callee.return_type[0] };

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

    // Compensate for the removed Call's auto-rc-on-Call semantics.
    // Eval would have rc_inc'd each RcPtr arg before transferring
    // control to the callee, minting a fresh owning ref for the
    // callee's local. The callee body's rc accounting was emitted
    // assuming that bump. Splice in an RcInc for each RcPtr arg now
    // that the Call (and its implicit bump) is gone.
    for arg in &call_args {
        if arg.ty == ScalarType::RcPtr {
            caller
                .blocks
                .get_mut(&block_id)
                .unwrap()
                .insts
                .push(Inst::RcInc(*arg));
        }
    }

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
        Terminator::Return(vs) => {
            debug_assert_eq!(
                vs.len(),
                1,
                "inline: multi-value Return not yet supported"
            );
            // Return becomes a jump to the continuation block.
            Terminator::Jump(BlockEdge {
                target: cont_block,
                args: vec![remap_value(vs[0], val_map)],
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
    crate::opt::rewrite_operands(inst, map);
}

fn rewrite_terminator_operands(term: &mut Terminator, map: &HashMap<Value, Value>) {
    crate::opt::rewrite_terminator_operands(term, map);
}

