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
//! | `Reset(_, p, _)`     | p                                | —                        |
//! | `RcDec(p)`           | p                                | —                        |
//! | `Drop(p, _)`         | p                                | —                        |
//! | `Free(p)`            | p                                | —                        |
//! | `Load(_, p, _)`      | —                                | p                        |
//! | `LoadDyn(_, p, i)`   | —                                | p, i                     |
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

use crate::ssa::instruction::{BlockId, Inst, ScalarType, Value};
use crate::ssa::{Function, Module};

/// Values whose lifetime rc_emit must track. `RcPtr` participates in
/// reference counting and gets explicit `rc_inc`/`rc_dec`; `Ptr` is a
/// raw pointer (statics, never freed) and emits no rc traffic.
fn needs_rc_emit(ty: ScalarType) -> bool {
    matches!(ty, ScalarType::RcPtr)
}

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
        if !needs_rc_emit(p.ty) {
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
        .filter(|p| needs_rc_emit(p.ty))
        .map(|p| (*p, false))
        .collect();
    for inst in &block.insts {
        for &d in inst.dests() {
            if needs_rc_emit(d.ty) {
                defined.push((d, false));
            }
        }
    }
    // Function params: implicitly visible in every block (SSA exception).
    // They're "available" here if cross-block liveness says they're
    // needed somewhere reachable from this block, OR they're directly
    // used in this block.
    for p in &func.params {
        if !needs_rc_emit(p.ty) {
            continue;
        }
        let used_here = block.insts.iter().any(|i| i.operands().contains(p))
            || block.terminator.operands().contains(p);
        if used_here {
            defined.push((*p, true));
        }
    }

    let term_op_list: Vec<Value> = block.terminator.operands();
    let term_ops: HashSet<Value> = term_op_list.iter().copied().collect();
    // Per-RcPtr "consumption count" at terminator. For a Jump the
    // count is the number of times v appears in jump args (each is
    // taken). For Branch / SwitchInt, only one edge fires at
    // runtime — so the count is the *max* multiplicity across edges
    // (the value reaches each successor block-param N times, but
    // only one successor runs). Cond / scrutinee are borrows (eval
    // doesn't consume them) — exclude.
    let term_count: HashMap<Value, usize> =
        per_value_terminator_consumption(&block.terminator);

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
        let term_uses = term_count.get(&v).copied().unwrap_or(0);
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
            // Terminator transfer takes one slot per appearance. If v
            // appears N times we need own_count == N going in; emit
            // (N - own_count) rc_incs before the terminator.
            let needed = term_uses as i32;
            while own_count < needed {
                inserts.push((block.insts.len(), Inst::RcInc(v)));
                own_count += 1;
            }
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

    // Note: the "owning-load convention" (post-load RcInc) is now
    // intrinsic to eval — RcPtr-typed Load/LoadDyn auto-rc_inc the
    // loaded value. The FBIP move-out pattern is now an explicit
    // `Inst::MoveOut` primitive rather than a load+null-store dance.
    // rc_emit no longer needs to handle either.

    // Apply inserts in reverse position order so earlier indices stay
    // valid as we shift later instructions.
    inserts.sort_by_key(|(idx, _)| std::cmp::Reverse(*idx));
    let block_mut = func.blocks.get_mut(&bid).unwrap();
    for (idx, inst) in inserts {
        block_mut.insts.insert(idx, inst);
    }
}

/// For each Ptr value, how many consuming uses it has in this
/// terminator. Jump sums across args; Branch / SwitchInt takes the
/// max across edges (since only one fires). Cond / scrutinee are
/// borrows and don't contribute.
fn per_value_terminator_consumption(
    term: &crate::ssa::instruction::Terminator,
) -> HashMap<Value, usize> {
    use crate::ssa::instruction::Terminator;
    let mut count: HashMap<Value, usize> = HashMap::new();
    let count_edge = |edge_args: &[Value], out: &mut HashMap<Value, usize>| {
        let mut local: HashMap<Value, usize> = HashMap::new();
        for v in edge_args {
            if needs_rc_emit(v.ty) {
                *local.entry(*v).or_insert(0) += 1;
            }
        }
        for (v, n) in local {
            let cur = out.entry(v).or_insert(0);
            if n > *cur {
                *cur = n;
            }
        }
    };
    match term {
        Terminator::Return(vs) => {
            for v in vs {
                if needs_rc_emit(v.ty) {
                    *count.entry(*v).or_insert(0) += 1;
                }
            }
        }
        Terminator::Jump(edge) => {
            for v in &edge.args {
                if needs_rc_emit(v.ty) {
                    *count.entry(*v).or_insert(0) += 1;
                }
            }
        }
        Terminator::Branch { then_edge, else_edge, .. } => {
            count_edge(&then_edge.args, &mut count);
            count_edge(&else_edge.args, &mut count);
        }
        Terminator::SwitchInt { arms, default, .. } => {
            for (_, edge) in arms {
                count_edge(&edge.args, &mut count);
            }
            if let Some(edge) = default {
                count_edge(&edge.args, &mut count);
            }
        }
    }
    count
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
    let is_ptr = |v: &Value| needs_rc_emit(v.ty);
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
        Inst::Call { args, .. } => {
            // Call args are a *borrow* with respect to rc_emit: eval
            // auto-rc_incs each RcPtr arg, minting a fresh ref for
            // the callee. Caller's local keeps its claim; rc_emit's
            // normal end-of-scope rc_dec releases it.
            for a in args {
                if is_ptr(a) {
                    borr.push(*a);
                }
            }
        }
        Inst::Load(_, ptr, _) => {
            if is_ptr(ptr) {
                borr.push(*ptr);
            }
        }
        Inst::Store(ptr, _, val) => {
            // Store's `val` is a *borrow*, not a consume: eval
            // auto-rc_incs the new occupant when the slot is RcPtr.
            // Treating it as borrow lets the caller keep its local
            // claim (rc_emit emits an end-of-scope rc_dec normally).
            for v in [ptr, val] {
                if is_ptr(v) {
                    borr.push(*v);
                }
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
            // Same auto-rc reasoning as Store.
            for v in [ptr, idx, val] {
                if is_ptr(v) {
                    borr.push(*v);
                }
            }
        }
        Inst::RcInc(v) => {
            if is_ptr(v) {
                borr.push(*v);
            }
        }
        Inst::RcDec(v) => {
            if is_ptr(v) {
                cons.push(*v);
            }
        }
        Inst::CowStore(_, ptr, _, val) => {
            // ptr is CONSUMED: either reused as the result (in-place
            // path) or rc_dec'd inside the eval (clone path). Caller
            // gets a new SSA value for the result. If caller wants
            // to use ptr after, rc_emit inserts rc_inc(ptr) before,
            // which makes the rc check see >1 and forces clone path.
            if is_ptr(ptr) {
                cons.push(*ptr);
            }
            // val: borrow (auto-rc on the cow_write inside).
            if is_ptr(val) {
                borr.push(*val);
            }
        }
        Inst::CowStoreDyn(_, ptr, idx, val) => {
            if is_ptr(ptr) {
                cons.push(*ptr);
            }
            for v in [idx, val] {
                if is_ptr(v) {
                    borr.push(*v);
                }
            }
        }
        Inst::CowMoveOut { src, .. } => {
            // CowMoveOut consumes src (cow_preps it).
            if is_ptr(src) {
                cons.push(*src);
            }
        }
        Inst::CowResizeDyn(_, ptr, size) => {
            // Same as CowStore: ptr is CONSUMED.
            if is_ptr(ptr) {
                cons.push(*ptr);
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
