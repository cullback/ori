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

use super::instruction::{BlockId, Inst, ScalarType, Terminator, Value};
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
    let (live_in, live_out) = compute_liveness(func);

    // Phase 2: rewrite each block.
    for bi in 0..num_blocks {
        // Collect the set of Ptr values alive at block entry.
        // These are: live-in values (from dominance) + block params.
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

        // Count how many successor edges each surviving value needs
        // a token for. A value passed as a block arg transfers its
        // token to the block param. A value that is live-in to a
        // successor via dominance (not as a block arg) needs a token
        // for that edge too.
        let mut successor_tokens: std::collections::HashMap<Value, usize> =
            std::collections::HashMap::new();
        for (succ_id, edge_args) in func.blocks[bi].terminator.successors() {
            // Values explicitly transferred via block args.
            for &v in edge_args {
                if is_ptr(v) {
                    *successor_tokens.entry(v).or_insert(0) += 1;
                }
            }
            // Values live-in to successor via dominance (not block args).
            // These are in live_in[succ] but not block params of succ.
            let succ_params: HashSet<Value> =
                func.blocks[succ_id.0].params.iter().copied().collect();
            for &v in &live_in[succ_id.0] {
                if is_ptr(v) && !succ_params.contains(&v) && alive.contains(&v) {
                    *successor_tokens.entry(v).or_insert(0) += 1;
                }
            }
        }

        // Also count Return as consuming 1 token.
        if let Terminator::Return(v) = &func.blocks[bi].terminator {
            if is_ptr(*v) {
                *successor_tokens.entry(*v).or_insert(0) += 1;
            }
        }

        // Build the new instruction list.
        let old_insts = func.blocks[bi].insts.clone();
        let mut new_insts: Vec<Inst> = Vec::new();

        for inst in &old_insts {
            // Before Store-of-Ptr: RcInc the stored value (heap slot
            // becomes an additional reference).
            match inst {
                Inst::Store(_, _, val) | Inst::StoreDyn(_, _, val) if is_ptr(*val) => {
                    new_insts.push(Inst::RcInc(*val));
                }
                _ => {}
            }

            new_insts.push(inst.clone());

            // After Load-of-Ptr: RcInc the loaded value (new alias
            // from heap slot).
            match inst {
                Inst::Load(dest, _, _) | Inst::LoadDyn(dest, _, _) if is_ptr(*dest) => {
                    new_insts.push(Inst::RcInc(*dest));
                }
                _ => {}
            }

            // Track new Ptr definitions.
            if let Some(dest) = inst.dest() {
                if is_ptr(dest) {
                    alive.insert(dest);
                }
            }
        }

        // Before the terminator: handle RC for values leaving the block.
        for &v in &alive {
            let tokens_needed = successor_tokens.get(&v).copied().unwrap_or(0);
            if tokens_needed == 0 {
                // Value dies in this block — release its token.
                new_insts.push(Inst::RcDec(v));
            } else if tokens_needed > 1 {
                // Value needs multiple tokens (branching to multiple
                // successors that need it). Create extras.
                for _ in 0..tokens_needed - 1 {
                    new_insts.push(Inst::RcInc(v));
                }
            }
            // tokens_needed == 1: no extra ops, the single token
            // transfers naturally.
        }

        func.blocks[bi].insts = new_insts;
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
