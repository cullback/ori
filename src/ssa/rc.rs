//! Reference counting insertion pass (Perceus-style).
//!
//! Inserts `RcInc` and `RcDec` instructions so that every heap
//! allocation is freed when no longer reachable. Runs after
//! `ssa::lower` and before `ssa::eval`.
//!
//! ## Ownership model
//!
//! Each `Ptr`-typed SSA value holds exactly one ownership token.
//! The token is created at the value's definition (Alloc, Call
//! result, block param) and must be released when the value dies
//! (via `RcDec`). Extra tokens are created with `RcInc` when a
//! value is needed on multiple paths or stored into the heap.
//!
//! **Calling convention: borrow-by-default.** Call arguments are
//! borrowed — the caller retains ownership and the callee must
//! `RcInc` if it needs to keep a reference (e.g. storing into a
//! heap object or returning). This is natural for an immutable
//! language where most calls just inspect their arguments.
//!
//! ## Heap references
//!
//! - `Store(ptr, offset, val)` where val is Ptr: the heap slot
//!   becomes an additional reference → emit `RcInc(val)`.
//! - `Load(dest, ptr, offset)` where dest is Ptr: creates a new
//!   alias from the heap slot → emit `RcInc(dest)`.

use std::collections::HashSet;

use super::instruction::{Inst, ScalarType, Terminator, Value, BlockId};
use super::{Function, Module};

/// Insert reference counting operations into every function.
pub fn insert_rc(module: &mut Module) {
    for func in module.functions.values_mut() {
        insert_rc_function(func);
    }
}

fn insert_rc_function(func: &mut Function) {
    let num_blocks = func.blocks.len();
    if num_blocks == 0 {
        return;
    }

    let is_ptr = |v: Value| func.value_types.get(&v) == Some(&ScalarType::Ptr);

    // Phase 1: compute liveness.
    let (live_in, _live_out) = compute_liveness(func);

    // Phase 2: rewrite each block.
    // Edge decs: (block_idx, edge_idx) → values to RcDec on that edge.
    // Applied in phase 3 by inserting trampoline blocks.
    let mut edge_decs: std::collections::HashMap<(usize, usize), Vec<Value>> =
        std::collections::HashMap::new();

    for bi in 0..num_blocks {
        // Collect ALL Ptr values visible in this block: live-in +
        // block params + instruction defs.
        let mut alive: HashSet<Value> = live_in[bi]
            .iter()
            .copied()
            .filter(|v| is_ptr(*v))
            .collect();
        for &p in &func.blocks[bi].params {
            if is_ptr(p) {
                alive.insert(p);
            }
        }
        for inst in &func.blocks[bi].insts {
            if let Some(d) = inst.dest() {
                if is_ptr(d) {
                    alive.insert(d);
                }
            }
        }

        // Count how many successor edges each value needs a token
        // for. A value needs a token on an edge if it's either:
        // - passed as a block arg on that edge, or
        // - live-in to the successor via dominance (not a block param).
        let successors = func.blocks[bi].terminator.successors();
        let num_succ = successors.len();

        // Per-edge token needs for each value.
        let mut edge_needs: Vec<HashSet<Value>> = Vec::with_capacity(num_succ);
        for (succ_id, edge_args) in &successors {
            let mut needs: HashSet<Value> = HashSet::new();
            for &v in *edge_args {
                if is_ptr(v) {
                    needs.insert(v);
                }
            }
            let succ_params: HashSet<Value> =
                func.blocks[succ_id.0].params.iter().copied().collect();
            for &v in &live_in[succ_id.0] {
                if is_ptr(v) && !succ_params.contains(&v) && alive.contains(&v) {
                    needs.insert(v);
                }
            }
            edge_needs.push(needs);
        }

        // Total tokens needed = number of edges needing this value.
        let mut successor_tokens: std::collections::HashMap<Value, usize> =
            std::collections::HashMap::new();
        for needs in &edge_needs {
            for &v in needs {
                *successor_tokens.entry(v).or_insert(0) += 1;
            }
        }
        if let Terminator::Return(v) = &func.blocks[bi].terminator {
            if is_ptr(*v) {
                *successor_tokens.entry(*v).or_insert(0) += 1;
            }
        }

        // For values alive but only needed on SOME edges, we need
        // RcDec on the edges where they're NOT needed. Collect
        // per-edge decs and create trampoline blocks later.
        for &v in &alive {
            let total = successor_tokens.get(&v).copied().unwrap_or(0);
            if total > 0 && total < num_succ {
                for (ei, (_succ_id, _)) in successors.iter().enumerate() {
                    if !edge_needs[ei].contains(&v) {
                        edge_decs
                            .entry((bi, ei))
                            .or_insert_with(Vec::new)
                            .push(v);
                    }
                }
            }
        }

        // Build new instruction list with RC operations.
        let old_insts = func.blocks[bi].insts.clone();
        let mut new_insts: Vec<Inst> = Vec::new();

        for inst in &old_insts {
            match inst {
                Inst::Store(_, _, val) | Inst::StoreDyn(_, _, val) if is_ptr(*val) => {
                    new_insts.push(Inst::RcInc(*val));
                }
                _ => {}
            }

            new_insts.push(inst.clone());

            match inst {
                Inst::Load(dest, _, _) | Inst::LoadDyn(dest, _, _) if is_ptr(*dest) => {
                    new_insts.push(Inst::RcInc(*dest));
                }
                _ => {}
            }
        }

        // Before the terminator: emit RC ops for each alive value.
        for &v in &alive {
            let tokens_needed = successor_tokens.get(&v).copied().unwrap_or(0);
            if tokens_needed == 0 {
                // Value dies in this block entirely.
                new_insts.push(Inst::RcDec(v));
            } else if tokens_needed > 1 {
                // Value needed on multiple edges — create extra tokens.
                for _ in 0..tokens_needed - 1 {
                    new_insts.push(Inst::RcInc(v));
                }
            }
        }

        func.blocks[bi].insts = new_insts;
    }

    // Phase 3: for each edge that needs decs, insert a trampoline
    // block that dec's the values and jumps to the original target.
    // Process in reverse order so block indices stay valid.
    let mut edges: Vec<((usize, usize), Vec<Value>)> = edge_decs.into_iter().collect();
    edges.sort_by(|a, b| b.0.cmp(&a.0));
    for ((block_idx, edge_idx), decs) in edges {
        let successors = func.blocks[block_idx].terminator.successors();
        let (target, target_args) = &successors[edge_idx];
        let target_id = *target;
        let target_args = target_args.to_vec();

        // Create trampoline: dec values, then jump to original target.
        let tramp_id = BlockId(func.blocks.len());
        let tramp_insts: Vec<Inst> = decs.into_iter().map(Inst::RcDec).collect();
        func.blocks.push(super::Block {
            params: vec![],
            insts: tramp_insts,
            terminator: Terminator::Jump(target_id, target_args.clone()),
        });

        // Rewrite the edge in the original terminator to point at the trampoline.
        rewrite_edge(&mut func.blocks[block_idx].terminator, edge_idx, tramp_id, target_args);
    }
}

/// Rewrite the `edge_idx`-th successor of a terminator to point at
/// `new_target` with no block args (the trampoline handles them).
fn rewrite_edge(term: &mut Terminator, edge_idx: usize, new_target: BlockId, _original_args: Vec<Value>) {
    match term {
        Terminator::Jump(target, args) => {
            assert_eq!(edge_idx, 0);
            *target = new_target;
            args.clear();
        }
        Terminator::Branch {
            then_block,
            then_args,
            else_block,
            else_args,
            ..
        } => match edge_idx {
            0 => {
                *then_block = new_target;
                then_args.clear();
            }
            1 => {
                *else_block = new_target;
                else_args.clear();
            }
            _ => unreachable!(),
        },
        Terminator::SwitchInt { arms, default, .. } => {
            if edge_idx < arms.len() {
                arms[edge_idx].1 = new_target;
                arms[edge_idx].2.clear();
            } else if let Some((target, args)) = default {
                *target = new_target;
                args.clear();
            }
        }
        _ => unreachable!(),
    }
}

// ---- Liveness analysis ----

/// Compute live-in and live-out sets for each block. Only tracks
/// Ptr-typed values since those are the only ones needing RC.
fn compute_liveness(func: &Function) -> (Vec<HashSet<Value>>, Vec<HashSet<Value>>) {
    let n = func.blocks.len();
    let is_ptr = |v: Value| func.value_types.get(&v) == Some(&ScalarType::Ptr);

    // Compute defs and upward-exposed uses per block.
    let mut defs: Vec<HashSet<Value>> = vec![HashSet::new(); n];
    let mut ue_uses: Vec<HashSet<Value>> = vec![HashSet::new(); n];

    for (bi, block) in func.blocks.iter().enumerate() {
        // Block params are defs.
        for &p in &block.params {
            if is_ptr(p) {
                defs[bi].insert(p);
            }
        }
        // Walk instructions: a use is upward-exposed if not preceded
        // by a def in this block.
        for inst in &block.insts {
            for v in inst.operands() {
                if is_ptr(v) && !defs[bi].contains(&v) {
                    ue_uses[bi].insert(v);
                }
            }
            if let Some(d) = inst.dest() {
                if is_ptr(d) {
                    defs[bi].insert(d);
                }
            }
        }
        // Terminator operands.
        for v in block.terminator.operands() {
            if is_ptr(v) && !defs[bi].contains(&v) {
                ue_uses[bi].insert(v);
            }
        }
    }

    // Backward dataflow to fixpoint.
    let mut live_in: Vec<HashSet<Value>> = vec![HashSet::new(); n];
    let mut live_out: Vec<HashSet<Value>> = vec![HashSet::new(); n];

    loop {
        let mut changed = false;
        for bi in (0..n).rev() {
            // live_out = union of live_in of all successors.
            let mut new_out: HashSet<Value> = HashSet::new();
            for (succ, _) in func.blocks[bi].terminator.successors() {
                new_out.extend(&live_in[succ.0]);
            }
            if new_out != live_out[bi] {
                live_out[bi] = new_out;
                changed = true;
            }

            // live_in = ue_uses ∪ (live_out \ defs).
            let mut new_in: HashSet<Value> = ue_uses[bi].clone();
            for &v in &live_out[bi] {
                if !defs[bi].contains(&v) {
                    new_in.insert(v);
                }
            }
            if new_in != live_in[bi] {
                live_in[bi] = new_in;
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }

    (live_in, live_out)
}
