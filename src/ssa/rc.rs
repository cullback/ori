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

use std::collections::{HashMap, HashSet};

use super::instruction::{BlockId, Inst, ScalarType, Terminator, Value};
use super::{Function, Module};

/// Insert reference counting operations into every function.
pub fn insert_rc(module: &mut Module) {
    for func in module.functions.values_mut() {
        insert_rc_function(func);
    }
}

/// Cancel `rc_inc(v)` / `rc_dec(v)` pairs within the same block
/// where the refcount elevation isn't observed between them.
///
/// The rc_inc/rc_dec bracket around a use of `v` exists to keep
/// `v` alive even if a parent object gets decremented in between
/// (Perceus-style "keep loaded child alive across parent's death").
/// Removing the bracket is only safe if nothing between them can
/// drop `v`'s refcount — specifically, no `Reset` or `RcDec` of
/// *any* value (either could cascade-free `v` via a child slot),
/// and no matching op on `v` itself (another observation).
pub fn fuse_inc_dec(module: &mut Module) {
    for func in module.functions.values_mut() {
        for (_, block) in &mut func.blocks {
            loop {
                if !fuse_one_pair(&mut block.insts) {
                    break;
                }
            }
        }
    }
}

/// Find and remove one rc_inc/rc_dec pair. Returns true if a pair
/// was removed.
fn fuse_one_pair(insts: &mut Vec<Inst>) -> bool {
    for i in 0..insts.len() {
        let (is_inc, v) = match &insts[i] {
            Inst::RcInc(v) => (true, *v),
            Inst::RcDec(v) => (false, *v),
            _ => continue,
        };
        let target = if is_inc { Inst::RcDec(v) } else { Inst::RcInc(v) };
        for j in (i + 1)..insts.len() {
            let is_match = match (&insts[j], &target) {
                (Inst::RcInc(a), Inst::RcInc(b)) | (Inst::RcDec(a), Inst::RcDec(b)) => a == b,
                _ => false,
            };
            if is_match {
                insts.remove(j);
                insts.remove(i);
                return true;
            }
            // Any op that can lower v's refcount (directly or via a
            // parent's child-slot cascade) invalidates the bracket.
            // Another inc/dec on v also counts as an observation.
            match &insts[j] {
                Inst::Reset(..) | Inst::RcDec(_) => break,
                Inst::RcInc(w) if *w == v => break,
                _ => {}
            }
        }
    }
    false
}

/// Remove RcInc/RcDec on values defined by StaticRef, since
/// static objects have a sentinel refcount and RC is a no-op.
pub fn elide_static_rc(module: &mut Module) {
    for func in module.functions.values_mut() {
        let statics: HashSet<Value> = func
            .blocks
            .values()
            .flat_map(|b| &b.insts)
            .filter_map(|inst| {
                if let Inst::StaticRef(dest, _) = inst {
                    Some(*dest)
                } else {
                    None
                }
            })
            .collect();
        if statics.is_empty() {
            continue;
        }
        for (_, block) in &mut func.blocks {
            block.insts.retain(|inst| {
                !matches!(
                    inst,
                    Inst::RcInc(v) | Inst::RcDec(v) if statics.contains(v)
                )
            });
        }
    }
}

/// Replace RcDec+Alloc pairs with Reset+Reuse when the allocation
/// sizes match, enabling in-place mutation of unique values.
pub fn insert_reuse(module: &mut Module) {
    for func in module.functions.values_mut() {
        insert_reuse_function(func);
    }
}

fn insert_reuse_function(func: &mut Function) {
    // Build a map: Value → alloc size, for values defined by Alloc.
    // Build a map: Value → slot types, for computing Reset field decs.
    let mut alloc_slot_types: HashMap<Value, Vec<ScalarType>> = HashMap::new();
    // Values passed as arguments to calls — these may have been stored
    // in heap objects by the callee, making the uniqueness check in
    // Reset unreliable. Exclude them from reuse.
    let mut call_args: HashSet<Value> = HashSet::new();
    // Track the next available Value ID for fresh tokens.
    let mut next_value: usize = func
        .value_types
        .keys()
        .map(|v| v.0 + 1)
        .max()
        .unwrap_or(0);

    // Track where each `Ptr` value was allocated. `Some(n)` means it
    // came from a static-size `Alloc(size=n)`; `None` means
    // `AllocDyn`. The pairing prefers same-kind matches: static decs
    // pair with same-size static allocs; dynamic decs pair with
    // dynamic allocs. This avoids wasting a same-size reuse on a
    // differently-sized alloc.
    let mut alloc_kind: HashMap<Value, Option<usize>> = HashMap::new();
    for (_, block) in &func.blocks {
        for inst in &block.insts {
            match inst {
                Inst::Alloc(dest, size) => {
                    alloc_kind.insert(*dest, Some(*size));
                    alloc_slot_types.insert(*dest, vec![ScalarType::Ptr; *size]);
                }
                Inst::AllocDyn(dest, _) => {
                    alloc_kind.insert(*dest, None);
                    alloc_slot_types.insert(*dest, Vec::new());
                }
                Inst::Store(ptr, offset, val) => {
                    if let Some(slots) = alloc_slot_types.get_mut(ptr) {
                        if let Some(ty) = func.value_types.get(val) {
                            if *offset < slots.len() {
                                slots[*offset] = *ty;
                            }
                        }
                    }
                }
                Inst::Call(_, _, args) => {
                    for arg in args {
                        call_args.insert(*arg);
                    }
                }
                _ => {}
            }
        }
    }

    for (_, block) in &mut func.blocks {
        let mut new_insts: Vec<Inst> = Vec::with_capacity(block.insts.len());
        let mut reset_for_dec: HashMap<usize, (Value, Vec<ScalarType>)> = HashMap::new();
        let mut reuse_for_alloc: HashMap<usize, Value> = HashMap::new();

        for (i, inst) in block.insts.iter().enumerate() {
            if let Inst::RcDec(ptr) = inst {
                if call_args.contains(ptr) {
                    continue;
                }
                let Some(dec_kind) = alloc_kind.get(ptr).copied() else {
                    continue;
                };
                for (j, later) in block.insts[i + 1..].iter().enumerate() {
                    let j = i + 1 + j;
                    if reuse_for_alloc.contains_key(&j) {
                        continue;
                    }
                    let compatible = match (dec_kind, later) {
                        (Some(dec_n), Inst::Alloc(_, alloc_n)) => dec_n == *alloc_n,
                        (None, Inst::AllocDyn(..)) => true,
                        _ => false,
                    };
                    if compatible {
                        let token = Value(next_value);
                        next_value += 1;
                        func.value_types.insert(token, ScalarType::Ptr);
                        let slot_types = alloc_slot_types
                            .get(ptr)
                            .cloned()
                            .unwrap_or_default();
                        reset_for_dec.insert(i, (token, slot_types));
                        reuse_for_alloc.insert(j, token);
                        break;
                    }
                }
            }
        }

        for (i, inst) in block.insts.iter().enumerate() {
            if let Some((token, slot_types)) = reset_for_dec.get(&i) {
                if let Inst::RcDec(ptr) = inst {
                    new_insts.push(Inst::Reset(*token, *ptr, slot_types.clone()));
                }
            } else if let Some(token) = reuse_for_alloc.get(&i) {
                match inst {
                    Inst::Alloc(dest, size) => {
                        new_insts.push(Inst::Reuse(*dest, *token, *size));
                    }
                    Inst::AllocDyn(dest, size_val) => {
                        new_insts.push(Inst::ReuseDyn(*dest, *token, *size_val));
                    }
                    _ => new_insts.push(inst.clone()),
                }
            } else {
                new_insts.push(inst.clone());
            }
        }

        block.insts = new_insts;
    }
}

fn insert_rc_function(func: &mut Function) {
    if func.blocks.is_empty() {
        return;
    }

    let is_ptr = |v: Value| func.value_types.get(&v) == Some(&ScalarType::Ptr);

    // Fresh value counter for trampoline block params.
    let mut next_value: usize = func
        .value_types
        .keys()
        .map(|v| v.0 + 1)
        .max()
        .unwrap_or(0);

    // Function params are borrowed from the caller. We emit rc_inc
    // on Store of a param (the heap needs its own reference), but
    // we must not emit rc_dec on param death — the caller owns the
    // token and will release it. Excluding params from dies_in_block
    // and edge_decs preserves this invariant.
    let func_param_ptrs: HashSet<Value> =
        func.params.iter().copied().filter(|v| is_ptr(*v)).collect();

    // Phase 1: compute liveness.
    let (live_in, _live_out) = compute_liveness(func);

    // Phase 2: rewrite each block.
    // Edge decs: (block_id, edge_idx) → values to RcDec on that edge.
    // Applied in phase 3 by inserting trampoline blocks.
    let mut edge_decs: HashMap<(BlockId, usize), Vec<Value>> = HashMap::new();

    let block_ids: Vec<BlockId> = func.blocks.keys().copied().collect();
    for bid in &block_ids {
        // Collect ALL Ptr values visible in this block: live-in +
        // block params + instruction defs.
        let mut alive: HashSet<Value> = live_in[bid]
            .iter()
            .copied()
            .filter(|v| is_ptr(*v))
            .collect();
        for &p in &func.blocks[bid].params {
            if is_ptr(p) {
                alive.insert(p);
            }
        }
        for inst in &func.blocks[bid].insts {
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
        let successors = func.blocks[bid].terminator.successors();
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
                func.blocks[succ_id].params.iter().copied().collect();
            for &v in &live_in[succ_id] {
                if is_ptr(v) && !succ_params.contains(&v) && alive.contains(&v) {
                    needs.insert(v);
                }
            }
            edge_needs.push(needs);
        }

        // Total tokens needed = number of edges needing this value.
        let mut successor_tokens: HashMap<Value, usize> = HashMap::new();
        for needs in &edge_needs {
            for &v in needs {
                *successor_tokens.entry(v).or_insert(0) += 1;
            }
        }
        if let Terminator::Return(v) = &func.blocks[bid].terminator {
            if is_ptr(*v) {
                *successor_tokens.entry(*v).or_insert(0) += 1;
            }
        }

        // For values alive but only needed on SOME edges, we need
        // RcDec on the edges where they're NOT needed. Skip function
        // params — the caller owns their tokens.
        for &v in &alive {
            if func_param_ptrs.contains(&v) { continue; }
            let total = successor_tokens.get(&v).copied().unwrap_or(0);
            if total > 0 && total < num_succ {
                for (ei, (_succ_id, _)) in successors.iter().enumerate() {
                    if !edge_needs[ei].contains(&v) {
                        edge_decs
                            .entry((*bid, ei))
                            .or_insert_with(Vec::new)
                            .push(v);
                    }
                }
            }
        }

        // Find the last instruction index where each Ptr value is
        // used as an operand.
        let old_insts = func.blocks[bid].insts.clone();
        let mut last_use: HashMap<Value, usize> = HashMap::new();
        for (idx, inst) in old_insts.iter().enumerate() {
            for v in inst.operands() {
                if is_ptr(v) {
                    last_use.insert(v, idx);
                }
            }
        }

        // Values that die in this block: alive here, not needed by
        // any successor edge, and not used in the terminator.
        let term_operands: HashSet<Value> = func.blocks[bid]
            .terminator
            .operands()
            .into_iter()
            .filter(|v| is_ptr(*v))
            .collect();
        let mut dies_in_block: HashSet<Value> = HashSet::new();
        for &v in &alive {
            let tokens = successor_tokens.get(&v).copied().unwrap_or(0);
            if tokens == 0 && !term_operands.contains(&v) && !func_param_ptrs.contains(&v) {
                dies_in_block.insert(v);
            }
        }

        // Build new instruction list. Insert RcDec right after each
        // value's last use (not at block end) to enable reset/reuse.
        let mut new_insts: Vec<Inst> = Vec::new();

        for (idx, inst) in old_insts.iter().enumerate() {
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

            // Insert RcDec right after a value's last use.
            for &v in &dies_in_block {
                if last_use.get(&v) == Some(&idx) {
                    new_insts.push(Inst::RcDec(v));
                }
            }
        }

        // Values that die but have NO instruction uses (e.g. defined
        // but unused). Dec at block end.
        for &v in &dies_in_block {
            if !last_use.contains_key(&v) {
                new_insts.push(Inst::RcDec(v));
            }
        }

        // Values needed on multiple successor edges: emit extra incs.
        for &v in &alive {
            let tokens_needed = successor_tokens.get(&v).copied().unwrap_or(0);
            if tokens_needed > 1 {
                for _ in 0..tokens_needed - 1 {
                    new_insts.push(Inst::RcInc(v));
                }
            }
        }

        func.blocks.get_mut(bid).unwrap().insts = new_insts;
    }

    // Phase 3: for each edge that needs decs, insert a trampoline
    // block that dec's the values and jumps to the original target.
    // The trampoline receives all needed values as block params to
    // satisfy the explicit-block-params invariant.
    let func_param_set: HashSet<Value> = func.params.iter().copied().collect();
    let mut edges: Vec<((BlockId, usize), Vec<Value>)> = edge_decs.into_iter().collect();
    edges.sort_by(|a, b| b.0.cmp(&a.0));
    for ((block_id, edge_idx), decs) in edges {
        let successors = func.blocks[&block_id].terminator.successors();
        let (target, target_args) = &successors[edge_idx];
        let target_id = *target;
        let target_args = target_args.to_vec();

        // Collect all values the trampoline needs: dec values + target args.
        // Exclude function params (always accessible) and deduplicate.
        let mut needed: Vec<Value> = Vec::new();
        let mut seen: HashSet<Value> = HashSet::new();
        for &v in decs.iter().chain(target_args.iter()) {
            if !func_param_set.contains(&v) && seen.insert(v) {
                needed.push(v);
            }
        }

        // Create block params for the trampoline, mapping originals to fresh values.
        let tramp_id = BlockId(func.next_block);
        func.next_block += 1;
        let mut tramp_remap: HashMap<Value, Value> = HashMap::new();
        let mut tramp_params: Vec<Value> = Vec::new();
        for &v in &needed {
            let fresh = Value(next_value);
            next_value += 1;
            func.value_types.insert(fresh, *func.value_types.get(&v).unwrap_or(&ScalarType::Ptr));
            tramp_remap.insert(v, fresh);
            tramp_params.push(fresh);
        }

        let remap = |v: Value| -> Value {
            tramp_remap.get(&v).copied().unwrap_or(v)
        };

        let tramp_insts: Vec<Inst> = decs.into_iter().map(|v| Inst::RcDec(remap(v))).collect();
        let tramp_target_args: Vec<Value> = target_args.iter().map(|v| remap(*v)).collect();
        func.blocks.insert(tramp_id, super::Block {
            params: tramp_params,
            insts: tramp_insts,
            terminator: Terminator::Jump(target_id, tramp_target_args),
        });

        // Rewrite the edge to pass the needed values as args.
        rewrite_edge(&mut func.blocks.get_mut(&block_id).unwrap().terminator, edge_idx, tramp_id, needed);
    }
}

/// Rewrite the `edge_idx`-th successor of a terminator to point at
/// `new_target` with the given block args.
fn rewrite_edge(term: &mut Terminator, edge_idx: usize, new_target: BlockId, new_args: Vec<Value>) {
    match term {
        Terminator::Jump(target, args) => {
            assert_eq!(edge_idx, 0);
            *target = new_target;
            *args = new_args;
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
                *then_args = new_args;
            }
            1 => {
                *else_block = new_target;
                *else_args = new_args;
            }
            _ => unreachable!(),
        },
        Terminator::SwitchInt { arms, default, .. } => {
            if edge_idx < arms.len() {
                arms[edge_idx].1 = new_target;
                arms[edge_idx].2 = new_args;
            } else if let Some((target, args)) = default {
                *target = new_target;
                *args = new_args;
            }
        }
        _ => unreachable!(),
    }
}

// ---- Liveness analysis ----

/// Compute live-in and live-out sets for each block. Only tracks
/// Ptr-typed values since those are the only ones needing RC.
fn compute_liveness(func: &Function) -> (HashMap<BlockId, HashSet<Value>>, HashMap<BlockId, HashSet<Value>>) {
    let is_ptr = |v: Value| func.value_types.get(&v) == Some(&ScalarType::Ptr);

    // Compute defs and upward-exposed uses per block.
    let mut defs: HashMap<BlockId, HashSet<Value>> = HashMap::new();
    let mut ue_uses: HashMap<BlockId, HashSet<Value>> = HashMap::new();

    for (&bid, block) in &func.blocks {
        let block_defs = defs.entry(bid).or_insert_with(HashSet::new);
        let block_ue = ue_uses.entry(bid).or_insert_with(HashSet::new);
        // Block params are defs.
        for &p in &block.params {
            if is_ptr(p) {
                block_defs.insert(p);
            }
        }
        // Walk instructions: a use is upward-exposed if not preceded
        // by a def in this block.
        for inst in &block.insts {
            for v in inst.operands() {
                if is_ptr(v) && !block_defs.contains(&v) {
                    block_ue.insert(v);
                }
            }
            if let Some(d) = inst.dest() {
                if is_ptr(d) {
                    block_defs.insert(d);
                }
            }
        }
        // Terminator operands.
        for v in block.terminator.operands() {
            if is_ptr(v) && !block_defs.contains(&v) {
                block_ue.insert(v);
            }
        }
    }

    // Backward dataflow to fixpoint.
    let block_ids: Vec<BlockId> = func.blocks.keys().copied().collect();
    let mut live_in: HashMap<BlockId, HashSet<Value>> = block_ids.iter().map(|&bid| (bid, HashSet::new())).collect();
    let mut live_out: HashMap<BlockId, HashSet<Value>> = block_ids.iter().map(|&bid| (bid, HashSet::new())).collect();

    loop {
        let mut changed = false;
        for &bid in block_ids.iter().rev() {
            // live_out = union of live_in of all successors.
            let mut new_out: HashSet<Value> = HashSet::new();
            for (succ, _) in func.blocks[&bid].terminator.successors() {
                new_out.extend(&live_in[&succ]);
            }
            if new_out != live_out[&bid] {
                live_out.insert(bid, new_out);
                changed = true;
            }

            // live_in = ue_uses ∪ (live_out \ defs).
            let empty = HashSet::new();
            let block_ue = ue_uses.get(&bid).unwrap_or(&empty);
            let block_defs = defs.get(&bid).unwrap_or(&empty);
            let mut new_in: HashSet<Value> = block_ue.clone();
            for &v in &live_out[&bid] {
                if !block_defs.contains(&v) {
                    new_in.insert(v);
                }
            }
            if new_in != live_in[&bid] {
                live_in.insert(bid, new_in);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }

    (live_in, live_out)
}
