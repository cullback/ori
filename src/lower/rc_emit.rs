//! Naïve Perceus reference-counting emission.
//!
//! Establishes the invariant: **every Ptr value has correct rc
//! traffic by construction.** Inserts `RcInc` before each non-last
//! *consuming* use, `RcDec` at scope-end where the last use was a
//! borrow, and `RcInc` after every `Load`/`LoadDyn` whose dest is a
//! Ptr (owning-load convention).
//!
//! After this pass, the program is correct AND leak-free with zero
//! optimization. The `opt/rc_*` passes are pure eliminators —
//! removing rc traffic that this pass over-emits.
//!
//! ## Operand classification
//!
//! Per-instruction, each Ptr operand is *consuming* or *borrowing*:
//!
//! | Instruction          | Consuming operands               | Borrowing operands       |
//! |----------------------|----------------------------------|--------------------------|
//! | `Call(_, _, args)`   | every Ptr arg                    | —                        |
//! | `Store(p, _, v)`     | v (when Ptr)                     | p                        |
//! | `StoreDyn(p, i, v)`  | v (when Ptr)                     | p, i                     |
//! | `Pack(_, fields)`    | every Ptr field                  | —                        |
//! | `Insert(_, a, _, v)` | a (if Ptr), v (if Ptr)           | —                        |
//! | `Reset(_, p, _)`     | p                                | —                        |
//! | `RcDec(p)`           | p                                | —                        |
//! | `Drop(p, _)`         | p                                | —                        |
//! | `Free(p)`            | p                                | —                        |
//! | `Load(_, p, _)`      | —                                | p                        |
//! | `LoadDyn(_, p, i)`   | —                                | p, i                     |
//! | `Extract(_, a, _)`   | —                                | a                        |
//! | `BinOp(_, _, l, r)`  | —                                | l, r                     |
//! | `Cast`/`BitCast`     | —                                | src                      |
//! | `RcInc(p)`           | —                                | p                        |
//! | `Reuse(_, t, _)`     | —                                | t                        |
//! | `ReuseDyn(_, t, s)`  | —                                | t, s                     |
//!
//! Terminator: `Return(v)` consumes v; `Jump`/`Branch`/`SwitchInt`
//! edge args consume each Ptr arg; Branch cond and Switch scrutinee
//! are borrows.

use std::collections::{HashMap, HashSet};

use crate::ssa::instruction::{BlockId, Inst, ScalarType, Terminator, Value};
use crate::ssa::{Function, Module};

/// Run naïve RC emission on every function in `module`.
pub fn run(module: &mut Module) {
    for func in module.functions.values_mut() {
        emit_function(func);
    }
}

fn emit_function(func: &mut Function) {
    // Function params are an exception to the explicit-block-param
    // invariant: they're implicitly visible in every block. We need
    // their cross-block liveness to know where they die.
    let func_param_liveness = compute_func_param_liveness(func);

    let block_ids: Vec<BlockId> = func.blocks.keys().copied().collect();
    for bid in block_ids {
        emit_block(func, bid, &func_param_liveness);
    }
}

/// For each Ptr function param, compute per-block live-out (whether
/// the param is needed in some path forward from the block).
fn compute_func_param_liveness(func: &Function) -> HashMap<Value, HashMap<BlockId, bool>> {
    let mut result: HashMap<Value, HashMap<BlockId, bool>> = HashMap::new();
    let block_ids: Vec<BlockId> = func.blocks.keys().copied().collect();

    for p in &func.params {
        if !p.ty.is_heap_ptr() {
            continue;
        }

        // Phase 1: mark blocks where p is directly used.
        let mut used: HashMap<BlockId, bool> = HashMap::new();
        for &bid in &block_ids {
            let block = &func.blocks[&bid];
            let in_insts = block.insts.iter().any(|i| i.operands().contains(p));
            let in_term = block.terminator.operands().contains(p);
            used.insert(bid, in_insts || in_term);
        }

        // Phase 2: live_in[B] = used[B] || any(live_in[succ] for succ in succs).
        // Iterate to fixpoint, propagating backward through CFG.
        let mut live_in: HashMap<BlockId, bool> = used.clone();
        loop {
            let mut changed = false;
            for &bid in &block_ids {
                let block = &func.blocks[&bid];
                let any_succ_live = block
                    .terminator
                    .successors()
                    .iter()
                    .any(|e| *live_in.get(&e.target).unwrap_or(&false));
                let new_val = *live_in.get(&bid).unwrap_or(&false) || any_succ_live;
                if new_val != *live_in.get(&bid).unwrap_or(&false) {
                    live_in.insert(bid, new_val);
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }

        // live_out[B] = any(live_in[succ] for succ in succs)
        let mut live_out: HashMap<BlockId, bool> = HashMap::new();
        for &bid in &block_ids {
            let block = &func.blocks[&bid];
            let any_succ_live = block
                .terminator
                .successors()
                .iter()
                .any(|e| *live_in.get(&e.target).unwrap_or(&false));
            live_out.insert(bid, any_succ_live);
        }

        result.insert(*p, live_out);
    }

    result
}

fn emit_block(
    func: &mut Function,
    bid: BlockId,
    func_param_liveness: &HashMap<Value, HashMap<BlockId, bool>>,
) {
    // Pending edits: insert `inst` at position `pos` (before the
    // instruction currently at `pos`). We accumulate and apply in
    // reverse so earlier positions stay stable.
    let mut inserts: Vec<(usize, Inst)> = Vec::new();

    let block = &func.blocks[&bid];

    // Ptr-typed values "born" in this block: block params + Ptr dests.
    let mut defined: Vec<(Value, bool)> = block
        .params
        .iter()
        .filter(|p| p.ty.is_heap_ptr())
        .map(|p| (*p, false))
        .collect();
    for inst in &block.insts {
        if let Some(d) = inst.dest() {
            if d.ty.is_heap_ptr() {
                defined.push((d, false));
            }
        }
    }
    // Function params: implicitly visible in every block (SSA exception).
    // They're "available" here if cross-block liveness says they're
    // needed somewhere reachable from this block, OR they're directly
    // used in this block.
    for p in &func.params {
        if !p.ty.is_heap_ptr() {
            continue;
        }
        let used_here = block.insts.iter().any(|i| i.operands().contains(p))
            || block.terminator.operands().contains(p);
        if used_here {
            defined.push((*p, true));
        }
    }

    let term_ops: HashSet<Value> =
        block.terminator.operands().into_iter().collect();

    for (v, is_func_param) in defined {
        // Walk instructions to find each use of v with its kind.
        let mut uses: Vec<(usize, Kind)> = Vec::new();
        for (idx, inst) in block.insts.iter().enumerate() {
            let (cons, borr) = classify(inst);
            if cons.contains(&v) {
                uses.push((idx, Kind::Consume));
            } else if borr.contains(&v) {
                uses.push((idx, Kind::Borrow));
            }
        }

        let in_term = term_ops.contains(&v);
        // For function params, "later need" extends into successors via
        // live_out.
        let live_out = if is_func_param {
            *func_param_liveness
                .get(&v)
                .and_then(|m| m.get(&bid))
                .unwrap_or(&false)
        } else {
            false
        };

        // Walk uses tracking owning slots. Start at 1 (the SSA value
        // itself owns one). Emit RcInc before each consuming use that
        // has a later need.
        let mut own_count: i32 = 1;
        for (i, (pos, kind)) in uses.iter().enumerate() {
            let has_later_need = i + 1 < uses.len() || in_term || live_out;
            match kind {
                Kind::Consume => {
                    if has_later_need {
                        inserts.push((*pos, Inst::RcInc(v)));
                        own_count += 1;
                    }
                    own_count -= 1;
                }
                Kind::Borrow => {
                    // owning slot unchanged
                }
            }
        }

        // Where does v's slot end?
        if in_term {
            // Terminator transfer takes the slot. No rc_dec needed.
            debug_assert!(own_count >= 0, "own_count went negative for v{}", v.id);
        } else if live_out {
            // Function param needed by a successor — we're carrying
            // its slot forward (implicitly, since func params aren't
            // edge-threaded). No rc_dec here. own_count should be 1.
            debug_assert!(own_count >= 0, "own_count went negative for v{}", v.id);
        } else if own_count == 1 {
            // Last use was a borrow (or there were no uses), and v
            // isn't needed in successors. Release.
            inserts.push((block.insts.len(), Inst::RcDec(v)));
        }
    }

    // Owning-load convention: after each Ptr-returning Load/LoadDyn,
    // emit RcInc(dest). This makes the loaded child an independent
    // owning slot rather than aliasing the parent's.
    //
    // Exceptions (skip the post-load RcInc):
    // - lower's `copy_loop` (for list elements) already emits
    //   `RcInc(elem)` immediately after the Load.
    // - FBIP move-out pattern: `Load(ptr, off)` immediately followed
    //   by `Store(ptr, off, null_ptr)` is a "move" — the loaded
    //   value is being transferred out of the slot, and the parent's
    //   slot is cleared so cascade-free won't double-drop. No rc
    //   traffic needed; the existing slot's ownership transfers to
    //   the loaded SSA value.
    for (idx, inst) in block.insts.iter().enumerate() {
        let (dest, src_ptr, src_off) = match inst {
            Inst::Load(d, p, off) if d.ty.is_heap_ptr() => (*d, Some(*p), Some(*off)),
            Inst::LoadDyn(d, _, _) if d.ty.is_heap_ptr() => (*d, None, None),
            _ => continue,
        };
        let next = block.insts.get(idx + 1);
        let already_owning = next.is_some_and(|n| matches!(n, Inst::RcInc(v) if *v == dest));
        let move_out = matches!(
            (src_ptr, src_off, next),
            (Some(p), Some(off), Some(Inst::Store(sp, soff, sv)))
                if *sp == p && *soff == off && is_const_null(block, *sv)
        );
        let already_owning = already_owning || move_out;
        if !already_owning {
            inserts.push((idx + 1, Inst::RcInc(dest)));
        }
    }

    // Apply inserts in reverse position order so earlier indices stay
    // valid as we shift later instructions.
    inserts.sort_by_key(|(idx, _)| std::cmp::Reverse(*idx));
    let block_mut = func.blocks.get_mut(&bid).unwrap();
    for (idx, inst) in inserts {
        block_mut.insts.insert(idx, inst);
    }
}

/// Walk `block.insts` for a `Const(v, 0)` definition where `v == val`
/// and `v.ty == Ptr`. Used to detect the FBIP move-out marker —
/// `Store(_, _, null_ptr)` immediately after a `Load` of the same
/// slot.
fn is_const_null(block: &super::super::ssa::Block, val: Value) -> bool {
    if !val.ty.is_heap_ptr() {
        return false;
    }
    block.insts.iter().any(|inst| {
        matches!(inst, Inst::Const(d, bits) if *d == val && *bits == 0)
    })
}

#[derive(Debug, Clone, Copy)]
enum Kind {
    Consume,
    Borrow,
}

/// Classify each operand of `inst` as consuming or borrowing.
/// Returned vectors hold only Ptr-typed operands.
fn classify(inst: &Inst) -> (Vec<Value>, Vec<Value>) {
    let mut cons = Vec::new();
    let mut borr = Vec::new();
    let is_ptr = |v: &Value| v.ty.is_heap_ptr();
    match inst {
        Inst::Const(..) | Inst::Alloc(..) | Inst::StaticRef(..) => {}
        Inst::AllocDyn(_, size) => {
            if is_ptr(size) {
                borr.push(*size);
            }
        }
        Inst::BinOp(_, _, l, r) => {
            for v in [l, r] {
                if is_ptr(v) {
                    borr.push(*v);
                }
            }
        }
        Inst::Call(_, _, args) => {
            for a in args {
                if is_ptr(a) {
                    cons.push(*a);
                }
            }
        }
        Inst::Load(_, ptr, _) => {
            if is_ptr(ptr) {
                borr.push(*ptr);
            }
        }
        Inst::Store(ptr, _, val) => {
            if is_ptr(ptr) {
                borr.push(*ptr);
            }
            if is_ptr(val) {
                cons.push(*val);
            }
        }
        Inst::LoadDyn(_, ptr, idx) => {
            for v in [ptr, idx] {
                if is_ptr(v) {
                    borr.push(*v);
                }
            }
        }
        Inst::StoreDyn(ptr, idx, val) => {
            for v in [ptr, idx] {
                if is_ptr(v) {
                    borr.push(*v);
                }
            }
            if is_ptr(val) {
                cons.push(*val);
            }
        }
        Inst::RcInc(v) => {
            if is_ptr(v) {
                borr.push(*v);
            }
        }
        Inst::RcDec(v) | Inst::Free(v) | Inst::Drop(v, _) => {
            if is_ptr(v) {
                cons.push(*v);
            }
        }
        Inst::Reset(_, ptr, _) => {
            if is_ptr(ptr) {
                cons.push(*ptr);
            }
        }
        Inst::Reuse(_, token, _) => {
            if is_ptr(token) {
                borr.push(*token);
            }
        }
        Inst::ReuseDyn(_, token, size) => {
            for v in [token, size] {
                if is_ptr(v) {
                    borr.push(*v);
                }
            }
        }
        Inst::ReuseOrClone(_, src, _) => {
            // ReuseOrClone consumes its src: either reuses storage
            // in place (rc=1 path) or clones + rc_dec'es src (rc>1
            // path). Either way the SSA's owning slot for src is
            // transferred into the result.
            if is_ptr(src) {
                cons.push(*src);
            }
        }
        Inst::ReuseOrCloneDyn(_, src, size) => {
            if is_ptr(src) {
                cons.push(*src);
            }
            if is_ptr(size) {
                borr.push(*size);
            }
        }
        Inst::Cast(_, src) | Inst::BitCast(_, src) => {
            if is_ptr(src) {
                borr.push(*src);
            }
        }
    }
    (cons, borr)
}

/// Test-only helper: classify terminator operands the same way.
/// Currently unused by the emission walk — terminator operand
/// classification is handled implicitly via the `in_term` check.
#[allow(dead_code)]
fn classify_terminator(term: &Terminator) -> Vec<Value> {
    // Every Ptr operand of a terminator is consuming (Return value,
    // edge args). Branch cond / Switch scrutinee are borrows but they
    // can't be Ptr (they're U8/U64) — so we ignore them here.
    let mut cons = Vec::new();
    let is_ptr = |v: &Value| v.ty.is_heap_ptr();
    match term {
        Terminator::Return(v) => {
            if is_ptr(v) {
                cons.push(*v);
            }
        }
        Terminator::Jump(edge) => {
            for v in &edge.args {
                if is_ptr(v) {
                    cons.push(*v);
                }
            }
        }
        Terminator::Branch { then_edge, else_edge, .. } => {
            for v in then_edge.args.iter().chain(else_edge.args.iter()) {
                if is_ptr(v) {
                    cons.push(*v);
                }
            }
        }
        Terminator::SwitchInt { arms, default, .. } => {
            for (_, edge) in arms {
                for v in &edge.args {
                    if is_ptr(v) {
                        cons.push(*v);
                    }
                }
            }
            if let Some(edge) = default {
                for v in &edge.args {
                    if is_ptr(v) {
                        cons.push(*v);
                    }
                }
            }
        }
    }
    cons
}
