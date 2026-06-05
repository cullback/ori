//! SSA construction — establish the explicit-block-params invariant.
//!
//! `lower` emits straight-line SSA where blocks may reference values
//! defined in earlier blocks without threading them through block
//! parameters. This pass repairs that. Standard liveness-based SSA
//! construction; same shape as LLVM's mem2reg.
//!
//! ## How
//!
//! 1. For each block, compute "live-in" values — operands used in the
//!    block (instructions or terminator) but not defined locally and
//!    not function parameters.
//! 2. Propagate live-ins backwards through predecessors until each
//!    reaches a defining block (or function entry).
//! 3. For every (block, live-in value) pair: allocate a fresh SSA
//!    value, append it to the block's `params`, rewrite uses inside
//!    the block to reference it, and append the matching edge arg to
//!    every predecessor's terminator.
//!
//! ## Input invariants
//!
//! - Functional SSA structure (blocks, params, instructions with
//!   typed `Value` operands, terminators with edges).
//! - Function parameters are exempt — they're considered in scope
//!   from any block. All other values are conceptually block-scoped.
//!
//! ## Output invariants
//!
//! - **Explicit-block-params:** every cross-block value flow goes
//!   through block parameters. A non-function-param value defined in
//!   block B is only used inside B itself.
//! - Function structure (instruction sequences, terminator targets)
//!   is otherwise unchanged.
//!
//! ## Notes
//!
//! - Block param positions are deterministic (sorted by value id).
//! - Re-runnable: if any downstream pass breaks the invariant, this
//!   pass would repair it. In practice we prefer to fix the pass
//!   (see `branch_switch_fold` in `opt.rs` for an example).
//! - See OWNERSHIP.md — the static-ownership analysis depends on this
//!   invariant for its "scope = defining block" assumption.

use std::collections::{HashMap, HashSet};

use crate::ssa::instruction::{BlockEdge, BlockId, Terminator, Value};
use crate::ssa::{Function, Module};

pub fn run(module: &mut Module) {
    for func in module.functions.values_mut() {
        construct_function(func);
    }
}

fn construct_function(func: &mut Function) {
    let func_params: HashSet<Value> = func.params.iter().copied().collect();

    let local_defs = compute_local_defs(func);
    let block_uses = compute_block_uses(func);
    let predecessors = compute_predecessors(func);

    let live_in = compute_live_in(func, &local_defs, &block_uses, &predecessors, &func_params);

    // Allocate fresh ids for each (block, value) live-in.
    let mut next_id = func.num_values();
    let mut promoted: HashMap<(BlockId, Value), Value> = HashMap::new();
    let mut sorted_live_in: HashMap<BlockId, Vec<Value>> = HashMap::new();
    for (&bid, li) in &live_in {
        let mut sorted: Vec<Value> = li.iter().copied().collect();
        // Stable order by id keeps block-param positions deterministic.
        sorted.sort_by_key(|v| v.id);
        for &v in &sorted {
            let new_v = Value { id: next_id, ty: v.ty };
            next_id += 1;
            promoted.insert((bid, v), new_v);
        }
        sorted_live_in.insert(bid, sorted);
    }

    // Phase A: append new block params to each block.
    for (&bid, sorted) in &sorted_live_in {
        if sorted.is_empty() {
            continue;
        }
        let block = func.blocks.get_mut(&bid).unwrap();
        for v in sorted {
            block.params.push(promoted[&(bid, *v)]);
        }
    }

    // Phase B: rewrite uses inside each block to the new params.
    // Operates on existing operands only; the terminator's edge args
    // get rewritten here too, but the *new* edge args appended in
    // Phase C deliberately bypass this map.
    let block_ids: Vec<BlockId> = func.blocks.keys().copied().collect();
    for bid in &block_ids {
        let li = &live_in[bid];
        if li.is_empty() {
            continue;
        }
        let rename: HashMap<Value, Value> = li
            .iter()
            .map(|v| (*v, promoted[&(*bid, *v)]))
            .collect();
        let block = func.blocks.get_mut(bid).unwrap();
        for inst in &mut block.insts {
            inst.map_operands_mut(|operand| {
                if let Some(&new_v) = rename.get(operand) {
                    *operand = new_v;
                }
            });
        }
        block.terminator.map_operands_mut(|operand| {
            if let Some(&new_v) = rename.get(operand) {
                *operand = new_v;
            }
        });
    }

    // Phase C: for each block P, append edge args to every successor edge
    // covering that successor's live-ins.
    for pid in &block_ids {
        // Look up "in-P version" of each value: if v is in live_in[P],
        // it's the promoted block param at P; otherwise (v is defined
        // in P or is a function param) v itself.
        let in_p_view: HashMap<Value, Value> = live_in[pid]
            .iter()
            .map(|v| (*v, promoted[&(*pid, *v)]))
            .collect();
        let resolve = |v: Value| -> Value { in_p_view.get(&v).copied().unwrap_or(v) };

        let block = func.blocks.get_mut(pid).unwrap();
        append_edge_args(&mut block.terminator, &sorted_live_in, resolve);
    }
}

fn append_edge_args(
    term: &mut Terminator,
    sorted_live_in: &HashMap<BlockId, Vec<Value>>,
    resolve: impl Fn(Value) -> Value,
) {
    let extend = |edge: &mut BlockEdge| {
        if let Some(sorted) = sorted_live_in.get(&edge.target) {
            for v in sorted {
                edge.args.push(resolve(*v));
            }
        }
    };
    match term {
        Terminator::Return(_) => {}
        Terminator::Jump(edge) => extend(edge),
        Terminator::Branch { then_edge, else_edge, .. } => {
            extend(then_edge);
            extend(else_edge);
        }
        Terminator::SwitchInt { arms, default, .. } => {
            for (_, edge) in arms {
                extend(edge);
            }
            if let Some(edge) = default {
                extend(edge);
            }
        }
    }
}

fn compute_local_defs(func: &Function) -> HashMap<BlockId, HashSet<Value>> {
    let mut map = HashMap::new();
    for (&bid, block) in &func.blocks {
        let mut s: HashSet<Value> = HashSet::new();
        for &p in &block.params {
            s.insert(p);
        }
        for inst in &block.insts {
            for &d in inst.dests() {
                s.insert(d);
            }
        }
        map.insert(bid, s);
    }
    map
}

fn compute_block_uses(func: &Function) -> HashMap<BlockId, HashSet<Value>> {
    let mut map = HashMap::new();
    for (&bid, block) in &func.blocks {
        let mut s: HashSet<Value> = HashSet::new();
        for inst in &block.insts {
            for v in inst.operands() {
                s.insert(v);
            }
        }
        for v in block.terminator.operands() {
            s.insert(v);
        }
        map.insert(bid, s);
    }
    map
}

fn compute_predecessors(func: &Function) -> HashMap<BlockId, Vec<BlockId>> {
    let mut map: HashMap<BlockId, Vec<BlockId>> = HashMap::new();
    for (&bid, block) in &func.blocks {
        for edge in block.terminator.successors() {
            map.entry(edge.target).or_default().push(bid);
        }
    }
    map
}

fn compute_live_in(
    func: &Function,
    local_defs: &HashMap<BlockId, HashSet<Value>>,
    block_uses: &HashMap<BlockId, HashSet<Value>>,
    predecessors: &HashMap<BlockId, Vec<BlockId>>,
    func_params: &HashSet<Value>,
) -> HashMap<BlockId, HashSet<Value>> {
    let mut live_in: HashMap<BlockId, HashSet<Value>> = HashMap::new();
    for (&bid, used) in block_uses {
        let mut li = used.clone();
        for d in &local_defs[&bid] {
            li.remove(d);
        }
        for p in func_params {
            li.remove(p);
        }
        // Agg-typed values shouldn't appear at block boundaries in
        // this analysis — but if they do, treat them the same way.
        live_in.insert(bid, li);
    }

    // Propagate to predecessors until fixpoint.
    loop {
        let mut changed = false;
        let block_ids: Vec<BlockId> = func.blocks.keys().copied().collect();
        for bid in block_ids {
            let li = live_in[&bid].clone();
            let preds = predecessors.get(&bid).cloned().unwrap_or_default();
            for p in preds {
                let p_defs = &local_defs[&p];
                let entry = live_in.entry(p).or_default();
                for v in &li {
                    if p_defs.contains(v) || func_params.contains(v) {
                        continue;
                    }
                    if entry.insert(*v) {
                        changed = true;
                    }
                }
            }
        }
        if !changed {
            break;
        }
    }

    live_in
}
