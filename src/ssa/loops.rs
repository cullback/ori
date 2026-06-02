//! Loop structure analysis over SSA functions.
//!
//! Recognizes the natural loop shape lower emits — header with
//! explicit block params (the induction variable plus zero or more
//! accumulators), one back-edge from the body, one exit edge to a
//! follow-on block. Recovers the induction variable, its iteration
//! domain `(start, end, step)`, and the accumulator slots.
//!
//! This is a **pure analysis** — it never mutates the IR. Consumers
//! call `analyze(func)` and read the returned `LoopInfo`. Each call
//! is `O(blocks + edges + insts in headers/bodies)`, which is linear
//! in function size.
//!
//! ## Pre-conditions
//!
//! - Explicit block params (the validator already enforces this).
//! - Reducible control flow. Lambda-lifted Ori from structured
//!   source is reducible by construction; we don't verify, but
//!   irreducible loops are quietly skipped (they won't show up in
//!   the result).
//!
//! ## Post-conditions
//!
//! - Each `Loop` in `LoopInfo::loops` has:
//!   - `header` with at least one back-edge predecessor
//!   - `iv` is one of `header`'s block params
//!   - on the back-edge, the arg in `iv`'s slot is `Add(<value flowing
//!     from iv>, Const(step))`
//!   - `start` is the same-slot arg from the entry predecessor
//!   - `end` is the comparison operand in the header's `Branch`
//!     terminator that isn't the IV
//! - Loops that don't fit this shape (multi-back-edge, non-affine IV,
//!   non-comparison header terminator, multi-exit) are silently
//!   excluded. Consumers should not assume coverage of every loop.
//!
//! ## What this is for
//!
//! Loop-aware opt passes (deforestation/fusion, LICM, unrolling).
//! Each pass calls `analyze` on demand; the result is cheap enough
//! that caching across pass invocations isn't worth the staleness
//! risk after rewrites.

use std::collections::{HashMap, HashSet};

use super::{Block, Function};
use super::instruction::{BinaryOp, BlockId, Inst, Terminator, Value};

/// A single recognized loop with its induction-variable structure.
#[derive(Debug, Clone)]
pub struct Loop {
    /// The loop header — block whose back-edge predecessor is in
    /// `back_edge_pred`. Has block params for the IV and accumulators.
    pub header: BlockId,
    /// The predecessor on the back edge (the body's terminator jumps
    /// to `header` from here).
    pub back_edge_pred: BlockId,
    /// The block control falls to when the loop exits (the header's
    /// non-back-edge successor).
    pub exit: BlockId,
    /// The induction variable: one of `header`'s block params.
    pub iv: Value,
    /// Initial value of `iv` on the entry edge.
    pub start: Value,
    /// Loop bound. The header's branch fires the exit when
    /// `iv cmp end` resolves to "exit" (we don't normalize the
    /// comparison direction here — consumers read the header's
    /// terminator if they need the relation).
    pub end: Value,
    /// Per-iteration step. For `Add(iv, k)` with `k` const, this is
    /// `k`. For `Sub`, we currently skip — keep it simple.
    pub step: u64,
    /// Other header block params that get rewritten on the back
    /// edge — the "accumulators" being folded by the loop.
    pub accumulators: Vec<Value>,
}

/// Per-function loop analysis result.
#[derive(Debug, Clone, Default)]
pub struct LoopInfo {
    pub loops: Vec<Loop>,
}

/// Linear-time loop recognition over `func`. See module docs for the
/// shape covered.
pub fn analyze(func: &Function) -> LoopInfo {
    let predecessors = compute_predecessors(func);
    let postorder_idx = compute_postorder_indices(func);

    let mut loops = Vec::new();
    for (&header_id, header_block) in &func.blocks {
        let Some(preds) = predecessors.get(&header_id) else { continue };

        // A back-edge here is one whose source comes "later" in
        // postorder than the header. Reducible-CFG assumption: at
        // most one such edge per header.
        let header_po = postorder_idx[&header_id];
        let back_preds: Vec<BlockId> = preds
            .iter()
            .copied()
            .filter(|p| postorder_idx.get(p).is_some_and(|&po| po <= header_po))
            .collect();
        if back_preds.len() != 1 {
            continue;
        }
        let back_edge_pred = back_preds[0];

        // Entry predecessor: the non-back-edge predecessor. For the
        // simple shape we cover, there's exactly one.
        let entry_preds: Vec<BlockId> = preds
            .iter()
            .copied()
            .filter(|p| !back_preds.contains(p))
            .collect();
        let [entry_pred] = entry_preds.as_slice() else { continue };

        let Some(recognized) = recognize_loop(
            func,
            header_id,
            header_block,
            *entry_pred,
            back_edge_pred,
        ) else { continue };
        loops.push(recognized);
    }
    LoopInfo { loops }
}

/// Try to recognize a single loop given its structural pieces. Returns
/// `None` if the shape doesn't match (no IV, multi-exit, etc.).
fn recognize_loop(
    func: &Function,
    header_id: BlockId,
    header: &Block,
    entry_pred: BlockId,
    back_edge_pred: BlockId,
) -> Option<Loop> {
    // The header must end in a Branch whose two successors are: one
    // back into the loop body (transitively reaching `back_edge_pred`),
    // and one exit. We don't trace transitively — the common shape
    // lower emits has the body block as a *direct* successor of the
    // header, so the header's Branch's "body" arm is the block whose
    // tail jumps to `header`. The other arm is the exit.
    let Terminator::Branch { cond, then_edge, else_edge } = &header.terminator
    else { return None };

    // Identify the exit arm: the header arm that doesn't reach
    // `back_edge_pred` without going through `header` itself. For
    // the common one-block-body shape, `back_edge_pred` is the body
    // block and is a direct successor of the header.
    let exit_target = if reaches_within_loop(
        func, then_edge.target, header_id, back_edge_pred,
    ) {
        else_edge.target
    } else if reaches_within_loop(
        func, else_edge.target, header_id, back_edge_pred,
    ) {
        then_edge.target
    } else {
        return None;
    };

    let back_jump = jump_args_from(func, back_edge_pred, header_id)?;
    let entry_jump = jump_args_from(func, entry_pred, header_id)?;
    if back_jump.len() != header.params.len() || entry_jump.len() != header.params.len() {
        return None;
    }

    // Identify the IV via the header's branch condition. Both operands
    // of the comparison may be header params (lower commonly threads
    // both the counter and the bound through block params). We pick
    // the one with an affine back-edge update — that's the IV; the
    // other is the bound. If neither operand is a header param, or
    // if both have affine updates, the shape is ambiguous and we bail.
    let (cmp_l, cmp_r) = find_compare_operands(header, *cond)?;
    let candidates: Vec<Value> = [cmp_l, cmp_r]
        .into_iter()
        .filter(|v| header.params.contains(v))
        .collect();
    if candidates.is_empty() { return None; }

    let mut iv_choice: Option<(Value, u64, usize)> = None;
    for &cand in &candidates {
        let slot = header.params.iter().position(|&p| p == cand)?;
        if let Some(step) = ind_var_step(func, cand, back_jump[slot]) {
            if iv_choice.is_some() { return None; }  // ambiguous
            iv_choice = Some((cand, step, slot));
        }
    }
    let (iv, step, iv_slot) = iv_choice?;
    let end = if cmp_l == iv { cmp_r } else { cmp_l };
    let start = entry_jump[iv_slot];

    let accumulators: Vec<Value> = header
        .params
        .iter()
        .enumerate()
        .filter_map(|(i, &p)| if i == iv_slot { None } else { Some(p) })
        .collect();

    Some(Loop {
        header: header_id,
        back_edge_pred,
        exit: exit_target,
        iv,
        start,
        end,
        step,
        accumulators,
    })
}

/// If `back_arg = Add(x, Const(k))` and `x` is `header_param` (directly
/// — no transitive chasing), return `k`. Otherwise return None.
///
/// The "directly" restriction is sound for the natural shape: the
/// body's terminator passes `Add(body_iv_param, k)` to the header,
/// where `body_iv_param` is the body's first param, which is the
/// header's IV-param passed through the forward edge unchanged. So
/// we look for `Add(v, Const(k))` where `v` flows from the header's
/// IV through one level of block-arg passing.
fn ind_var_step(func: &Function, header_param: Value, back_arg: Value) -> Option<u64> {
    // Find the def of back_arg — it must be a BinOp::Add with a Const
    // operand and the other operand traceably equal to header_param.
    let def = find_def(func, back_arg)?;
    let Inst::BinOp(_, BinaryOp::Add, lhs, rhs) = def else { return None };
    let (other, const_v) = match (find_const(func, *lhs), find_const(func, *rhs)) {
        (Some(k), _) => (*rhs, k),
        (_, Some(k)) => (*lhs, k),
        _ => return None,
    };
    if flows_from(func, other, header_param) { Some(const_v) } else { None }
}

/// Does `v` resolve to `header_param`, either directly or by walking
/// one level of block-arg passing through the forward edge? Bounded
/// to one hop — enough for the natural shape lower emits (body block
/// receives the IV through the header's forward edge unchanged).
fn flows_from(func: &Function, v: Value, header_param: Value) -> bool {
    if v == header_param { return true; }
    // Find the block in which `v` is a block param, if any. The
    // body block's IV-slot is the only place `v` can be defined for
    // the shape we cover.
    let Some((host_bid, slot)) = func.blocks.iter().find_map(|(bid, block)| {
        block.params.iter().position(|&p| p == v).map(|s| (*bid, s))
    }) else { return false };

    // Walk every edge into `host_bid`; if any of them passes
    // `header_param` in slot `slot`, we're connected.
    for src_block in func.blocks.values() {
        for edge in src_block.terminator.successors() {
            if edge.target == host_bid && edge.args.get(slot) == Some(&header_param) {
                return true;
            }
        }
    }
    false
}

/// Find the defining instruction of `v` anywhere in the function.
/// Returns None for function/block params (no defining instruction).
fn find_def<'f>(func: &'f Function, v: Value) -> Option<&'f Inst> {
    for block in func.blocks.values() {
        for inst in &block.insts {
            if inst.dests().iter().any(|&d| d == v) {
                return Some(inst);
            }
        }
    }
    None
}

/// If `v` is defined by `Inst::Const(_, k)`, return `k`.
fn find_const(func: &Function, v: Value) -> Option<u64> {
    let Some(Inst::Const(_, k)) = find_def(func, v) else { return None };
    Some(*k)
}

/// Find the comparison `BinOp` that defines `cond` in `header`,
/// returning its `(lhs, rhs)` operands. Returns None if `cond`'s
/// definition isn't one of the comparison operators.
fn find_compare_operands(header: &Block, cond: Value) -> Option<(Value, Value)> {
    header.insts.iter().find_map(|inst| {
        if let Inst::BinOp(dest, op, l, r) = inst
            && *dest == cond
            && matches!(op, BinaryOp::Eq | BinaryOp::Neq | BinaryOp::Lt
                | BinaryOp::Le | BinaryOp::Gt | BinaryOp::Ge)
        {
            Some((*l, *r))
        } else { None }
    })
}

/// Args of the jump from `from_block` to `to_block`. Returns None if
/// the terminator doesn't have a single edge to `to_block`.
fn jump_args_from(func: &Function, from_block: BlockId, to_block: BlockId) -> Option<Vec<Value>> {
    let block = func.blocks.get(&from_block)?;
    let edges: Vec<_> = block.terminator.successors()
        .into_iter()
        .filter(|e| e.target == to_block)
        .collect();
    let [edge] = edges.as_slice() else { return None };
    Some(edge.args.clone())
}

/// Does `start` reach `target` without revisiting `forbidden`?
/// Bounded DFS, used to disambiguate which arm of the header's
/// Branch leads back into the loop.
fn reaches_within_loop(
    func: &Function,
    start: BlockId,
    forbidden: BlockId,
    target: BlockId,
) -> bool {
    let mut stack = vec![start];
    let mut seen: HashSet<BlockId> = HashSet::new();
    seen.insert(forbidden);
    while let Some(b) = stack.pop() {
        if b == target { return true; }
        if !seen.insert(b) { continue; }
        let Some(block) = func.blocks.get(&b) else { continue };
        for edge in block.terminator.successors() {
            stack.push(edge.target);
        }
    }
    false
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

/// Postorder of blocks reachable from entry. The returned map gives
/// each block its postorder index — higher = visited later in DFS.
/// A back-edge `u → v` is one where `po[v] <= po[u]`.
fn compute_postorder_indices(func: &Function) -> HashMap<BlockId, usize> {
    let mut order = Vec::new();
    let mut seen: HashSet<BlockId> = HashSet::new();
    walk_postorder(func, func.entry, &mut seen, &mut order);
    order.into_iter().enumerate().map(|(i, b)| (b, i)).collect()
}

fn walk_postorder(
    func: &Function,
    bid: BlockId,
    seen: &mut HashSet<BlockId>,
    out: &mut Vec<BlockId>,
) {
    if !seen.insert(bid) { return; }
    let Some(block) = func.blocks.get(&bid) else { return };
    for edge in block.terminator.successors() {
        walk_postorder(func, edge.target, seen, out);
    }
    out.push(bid);
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ssa::Builder;
    use crate::ssa::instruction::ScalarType;

    /// Build:
    ///
    ///   b0:                              entry
    ///     jump b1(0, 0)
    ///   b1(iv: U64, acc: U64):
    ///     cond = iv == end_param
    ///     branch cond ? b3(acc) : b2(iv, acc)
    ///   b2(iv2: U64, acc2: U64):
    ///     acc' = acc2 + 1
    ///     iv'  = iv2  + 1
    ///     jump b1(iv', acc')
    ///   b3(final_acc: U64):
    ///     ret final_acc
    fn build_simple_loop() -> Function {
        let mut b = Builder::new();
        let end_param = b.add_func_param(ScalarType::U64);

        let b0 = b.create_block();
        let b1 = b.create_block();
        let b2 = b.create_block();
        let b3 = b.create_block();

        let iv = b.add_block_param(b1, ScalarType::U64);
        let acc = b.add_block_param(b1, ScalarType::U64);
        let iv2 = b.add_block_param(b2, ScalarType::U64);
        let acc2 = b.add_block_param(b2, ScalarType::U64);
        let final_acc = b.add_block_param(b3, ScalarType::U64);

        b.switch_to(b0);
        let zero = b.const_u64(0);
        let zero2 = b.const_u64(0);
        b.jump(b1, vec![zero, zero2]);

        b.switch_to(b1);
        let cond = b.binop(BinaryOp::Eq, iv, end_param, ScalarType::U8);
        b.branch(cond, b3, vec![acc], b2, vec![iv, acc]);

        b.switch_to(b2);
        let one1 = b.const_u64(1);
        let acc_new = b.binop(BinaryOp::Add, acc2, one1, ScalarType::U64);
        let one2 = b.const_u64(1);
        let iv_new = b.binop(BinaryOp::Add, iv2, one2, ScalarType::U64);
        b.jump(b1, vec![iv_new, acc_new]);

        b.switch_to(b3);
        b.ret(final_acc);

        b.finish_function("test_loop", ScalarType::U64);
        b.build("test_loop").functions.remove("test_loop").unwrap()
    }

    #[test]
    fn recognizes_simple_loop() {
        let func = build_simple_loop();
        let info = analyze(&func);
        assert_eq!(info.loops.len(), 1, "expected one loop, got {info:?}");
        let lp = &info.loops[0];
        assert_eq!(lp.step, 1);
        assert_eq!(lp.iv, func.blocks[&BlockId(1)].params[0]);
        assert_eq!(lp.accumulators.len(), 1);
    }

    #[test]
    fn straight_line_function_yields_no_loops() {
        let mut b = Builder::new();
        let p = b.add_func_param(ScalarType::U64);
        let _b0 = b.create_block();
        b.switch_to(BlockId(0));
        b.ret(p);
        b.finish_function("noloop", ScalarType::U64);
        let func = b.build("noloop").functions.remove("noloop").unwrap();
        let info = analyze(&func);
        assert!(info.loops.is_empty());
    }
}
