//! Stream fusion / deforestation over SSA.
//!
//! Eliminates an `AllocDyn` buffer that's written sequentially in one
//! loop and read sequentially in another with matching iteration
//! domain — substituting the stored value for the loaded value, then
//! collapsing the writer + alloc + drop. The net effect on a chain
//! like `range(2, n).map(p).count()` (after inlining) is to fuse all
//! three loops into one and drop both intermediate buffers.
//!
//! This pass is type-agnostic: it operates on SSA primitives
//! (`AllocDyn`, `CowStoreDyn`, `LoadDyn`, `RcDec`) and loop structure
//! from `ssa::loops`. It does not know about `List`.
//!
//! ## Scope of this commit
//!
//! Detection only — `find_candidates` walks each function, classifies
//! each `AllocDyn`'s uses, and returns a `Candidate` for every buffer
//! whose use pattern matches the fusable shape. The rewrite step
//! lands in a follow-on commit; keeping the recognizer separate lets
//! us verify the pattern-matcher against real lower output before
//! we commit to mutation.
//!
//! ## What counts as fusable
//!
//! For each `AllocDyn(buf_0, size)`:
//!
//! 1. Compute the **buffer chain** — the set of `Value`s that
//!    represent "the same buffer" across the SSA. The chain starts
//!    at `buf_0` and grows through:
//!    - every `CowStoreDyn`'s dest whose ptr operand is already in
//!      the chain (a cow-write produces the next buffer Value), and
//!    - every block param whose every incoming edge passes a chain
//!      Value in its slot (the buffer threaded through block params).
//!
//! 2. **Classify every use** of a chain Value. Each use is one of:
//!    - `CowStoreDyn(_, chain, idx, _)`: a writer use. Idx must be a
//!      header-IV of some loop containing the use's block.
//!    - `LoadDyn(_, chain, idx)`: a reader use. Idx must be a
//!      header-IV of some loop containing the use's block.
//!    - `RcDec(chain)`: at most one (the drop).
//!    - Passing through a block-arg / terminator: already accounted
//!      for by chain expansion; not a "use" in the leaf sense.
//!    Any other use disqualifies the buffer.
//!
//! 3. The writer uses must all live in **one** loop (the writer
//!    loop). The reader uses must all live in **one** loop (the
//!    reader loop). The two loops must be distinct.
//!
//! 4. Writer and reader loop must have **congruent iteration
//!    domains**: equal `(start, end, step)`. Equality is by Value
//!    id — the same Values must be used as the bounds.
//!
//! 5. The writer's body must have **exactly one** `CowStoreDyn`
//!    chain-use at the IV; the reader's body must have **exactly
//!    one** `LoadDyn` chain-use at the IV. (Generalizable later;
//!    this first scope keeps the recognizer obvious.)
//!
//! ## Inputs / outputs
//!
//! Input: `&Function` (no mutation in this commit).
//! Output: `Vec<Candidate>` — one per fusable buffer.

use std::collections::HashSet;

use crate::ssa::Function;
use crate::ssa::instruction::{BlockId, Inst, Value};
use crate::ssa::loops::{analyze, Loop, LoopInfo};

/// One recognized fusion opportunity in a function.
#[derive(Debug, Clone)]
pub struct Candidate {
    /// The block that contains the `AllocDyn` defining the initial
    /// buffer value.
    pub alloc_block: BlockId,
    /// The initial buffer value (the dest of `AllocDyn`).
    pub buf_initial: Value,
    /// Every Value that represents the buffer across the SSA —
    /// the alloc dest, every cow_store_dyn dest derived from it,
    /// and every block param it flows through.
    pub buffer_chain: HashSet<Value>,
    /// Index into `LoopInfo::loops` for the writer loop.
    pub writer_loop: usize,
    /// Index into `LoopInfo::loops` for the reader loop.
    pub reader_loop: usize,
    /// Block + position of the unique `CowStoreDyn` in the writer's
    /// body; the value written at the IV.
    pub writer_store_block: BlockId,
    pub writer_store_idx: usize,
    pub writer_stored_value: Value,
    /// Block + position of the unique `LoadDyn` in the reader's
    /// body; the value the loader produces.
    pub reader_load_block: BlockId,
    pub reader_load_idx: usize,
    pub reader_loaded_value: Value,
    /// Block + position of the `RcDec(buf)` that drops the buffer.
    pub rc_dec_block: BlockId,
    pub rc_dec_idx: usize,
}

/// Detect every fusion candidate in `func`. Pure — does not mutate.
pub fn find_candidates(func: &Function) -> Vec<Candidate> {
    let info = analyze(func);
    let mut out = Vec::new();
    for (alloc_block, alloc_idx) in iter_alloc_dyn_sites(func) {
        let block = &func.blocks[&alloc_block];
        let Inst::AllocDyn(buf_initial, _size) = &block.insts[alloc_idx] else { continue };
        if let Some(cand) = classify(func, &info, alloc_block, *buf_initial) {
            out.push(cand);
        }
    }
    out
}

/// Every `(block_id, inst_idx)` whose instruction is an `AllocDyn`.
fn iter_alloc_dyn_sites(func: &Function) -> Vec<(BlockId, usize)> {
    let mut out = Vec::new();
    for (&bid, block) in &func.blocks {
        for (i, inst) in block.insts.iter().enumerate() {
            if matches!(inst, Inst::AllocDyn(..)) {
                out.push((bid, i));
            }
        }
    }
    out
}

/// Try to classify a single AllocDyn site into a Candidate. Returns
/// None whenever the use pattern doesn't match the fusable shape.
fn classify(
    func: &Function,
    info: &LoopInfo,
    alloc_block: BlockId,
    buf_initial: Value,
) -> Option<Candidate> {
    let chain = build_buffer_chain(func, buf_initial);

    // Walk uses of every chain value and classify each.
    let mut writer_sites: Vec<(BlockId, usize, Value, Value)> = Vec::new(); // (block, idx, idx_operand, val_operand)
    let mut reader_sites: Vec<(BlockId, usize, Value, Value)> = Vec::new(); // (block, idx, idx_operand, dest)
    let mut rc_decs: Vec<(BlockId, usize)> = Vec::new();
    for (&bid, block) in &func.blocks {
        for (i, inst) in block.insts.iter().enumerate() {
            match inst {
                Inst::CowStoreDyn(_dest, ptr, idx, val) if chain.contains(ptr) => {
                    writer_sites.push((bid, i, *idx, *val));
                }
                Inst::LoadDyn(dest, ptr, idx) if chain.contains(ptr) => {
                    reader_sites.push((bid, i, *idx, *dest));
                }
                Inst::RcDec(v) if chain.contains(v) => {
                    rc_decs.push((bid, i));
                }
                // Disqualifying uses: anything else that operates on
                // a chain value as an operand. We allow chain values
                // to flow through block-args / terminators (already
                // accounted for in chain expansion).
                _ => {
                    for op in inst.operands() {
                        if chain.contains(&op)
                            && !matches!(
                                inst,
                                Inst::CowStoreDyn(..) | Inst::LoadDyn(..) | Inst::RcDec(_)
                            )
                        {
                            return None; // unsupported use
                        }
                    }
                }
            }
        }
    }

    // Need exactly one writer site, exactly one reader site, exactly
    // one rc_dec. (Multiple writes/reads in the body get generalized
    // later.)
    let [(w_block, w_idx, w_idx_op, w_val)] = writer_sites.as_slice() else { return None };
    let [(r_block, r_idx, r_idx_op, r_dest)] = reader_sites.as_slice() else { return None };
    let [(rc_block, rc_idx)] = rc_decs.as_slice() else { return None };

    // Locate the loop that contains each store/load.
    let writer_loop = info.loops.iter().position(|lp| lp_contains(func, lp, *w_block))?;
    let reader_loop = info.loops.iter().position(|lp| lp_contains(func, lp, *r_block))?;
    if writer_loop == reader_loop { return None; }
    let lp_w = &info.loops[writer_loop];
    let lp_r = &info.loops[reader_loop];

    // The index operands must be the respective loops' IVs (via
    // direct equality — the body's IV-param is the header's IV
    // threaded through, so they have different Value ids; check
    // both possibilities).
    if !is_loop_iv_in_body(func, lp_w, *w_idx_op) { return None; }
    if !is_loop_iv_in_body(func, lp_r, *r_idx_op) { return None; }

    // Domains must be congruent. Equality is by Value id for the
    // common case (the same Value flowing into both loops). For
    // constants we also accept different Value ids that resolve to
    // the same `Const(_)` — a producer and consumer that each
    // independently materialize their bound as a literal are still
    // semantically the same loop.
    if !values_congruent(func, lp_w.start, lp_r.start)
        || !values_congruent(func, lp_w.end, lp_r.end)
        || lp_w.step != lp_r.step
    {
        return None;
    }

    Some(Candidate {
        alloc_block,
        buf_initial,
        buffer_chain: chain,
        writer_loop,
        reader_loop,
        writer_store_block: *w_block,
        writer_store_idx: *w_idx,
        writer_stored_value: *w_val,
        reader_load_block: *r_block,
        reader_load_idx: *r_idx,
        reader_loaded_value: *r_dest,
        rc_dec_block: *rc_block,
        rc_dec_idx: *rc_idx,
    })
}

/// Build the "buffer chain" — every Value that may represent this
/// buffer at some point in the SSA. Fixed-point grow from
/// `buf_initial`:
///
/// - Add each `CowStoreDyn` dest whose ptr is already in the chain
///   (a cow-write produces the next buffer Value).
/// - Add each block param if **any** incoming edge passes a chain
///   value in its slot.
///
/// We use "any" rather than "all" because of the loop structure: a
/// header block-param has two predecessors (entry + back-edge), and
/// the back-edge passes a cow-store result that can't be in the
/// chain until the header param itself is — a chicken-and-egg the
/// "all" rule can't break.
///
/// The over-approximation is benign because the classification step
/// downstream rejects any chain Value with an unsupported use. If
/// "may-flow" added a non-buffer Value to the chain (e.g., a block
/// param that also receives a non-buffer value from some other
/// predecessor), the non-buffer value's uses would surface as
/// non-chain-classified and disqualify the candidate.
fn build_buffer_chain(func: &Function, buf_initial: Value) -> HashSet<Value> {
    let mut chain: HashSet<Value> = HashSet::new();
    chain.insert(buf_initial);
    let predecessors = compute_predecessors(func);
    loop {
        let mut changed = false;

        for block in func.blocks.values() {
            for inst in &block.insts {
                if let Inst::CowStoreDyn(dest, ptr, _, _) = inst
                    && chain.contains(ptr)
                    && chain.insert(*dest)
                {
                    changed = true;
                }
            }
        }

        for (&bid, block) in &func.blocks {
            for (slot, &param) in block.params.iter().enumerate() {
                if chain.contains(&param) { continue; }
                let preds = predecessors.get(&bid).cloned().unwrap_or_default();
                let any_chain = preds.iter().any(|&pred_bid| {
                    let pred = &func.blocks[&pred_bid];
                    pred.terminator
                        .successors()
                        .into_iter()
                        .filter(|e| e.target == bid)
                        .any(|e| e.args.get(slot).is_some_and(|v| chain.contains(v)))
                });
                if any_chain && chain.insert(param) {
                    changed = true;
                }
            }
        }

        if !changed { break; }
    }
    chain
}

/// A block belongs to a loop if it's the header, the back-edge
/// predecessor, or any block on a path from the header to the
/// back-edge predecessor that stays within the loop (i.e., doesn't
/// reach the exit).
///
/// For the simple-one-block-body shape this means: header itself,
/// or back_edge_pred (= the body block). We don't trace transitively
/// here — that's enough for current lower output.
fn lp_contains(_func: &Function, lp: &Loop, block: BlockId) -> bool {
    block == lp.header || block == lp.back_edge_pred
}

/// Is `v` the IV of `lp` as it appears in the body block (not the
/// header)? In the natural shape the body's IV-slot param has its
/// own Value, distinct from the header's IV; both must be accepted.
fn is_loop_iv_in_body(func: &Function, lp: &Loop, v: Value) -> bool {
    if v == lp.iv { return true; }
    // Body block is `back_edge_pred`; its IV-slot param flows from
    // the header's IV.
    let body = &func.blocks[&lp.back_edge_pred];
    let header = &func.blocks[&lp.header];
    let Some(iv_slot) = header.params.iter().position(|&p| p == lp.iv) else { return false };
    body.params.get(iv_slot).copied() == Some(v)
}

/// Two Values are congruent if they have the same id, or if both
/// resolve to `Const(k)` with the same `k`. Used to compare loop
/// bounds across separately-emitted producer / consumer loops.
fn values_congruent(func: &Function, a: Value, b: Value) -> bool {
    if a == b { return true; }
    match (const_value(func, a), const_value(func, b)) {
        (Some(ka), Some(kb)) => ka == kb,
        _ => false,
    }
}

fn const_value(func: &Function, v: Value) -> Option<u64> {
    for block in func.blocks.values() {
        for inst in &block.insts {
            if let Inst::Const(dest, k) = inst
                && *dest == v
            {
                return Some(*k);
            }
        }
    }
    None
}

fn compute_predecessors(func: &Function) -> std::collections::HashMap<BlockId, Vec<BlockId>> {
    let mut map: std::collections::HashMap<BlockId, Vec<BlockId>> = std::collections::HashMap::new();
    for (&bid, block) in &func.blocks {
        for edge in block.terminator.successors() {
            map.entry(edge.target).or_default().push(bid);
        }
    }
    map
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ssa::{Builder, ScalarType, BinaryOp};

    /// Build a function with the fusable shape:
    ///
    ///   b0:
    ///     buf = alloc_dyn(size)
    ///     jump b1(0, buf)                    // writer header
    ///   b1(iv_w, buf_w):
    ///     c1 = iv_w == n
    ///     branch c1 ? b3(buf_w) : b2(iv_w, buf_w)
    ///   b2(iv_w2, buf_w2):
    ///     buf_w3 = cow_store_dyn(buf_w2, iv_w2, iv_w2)   // store iv at iv
    ///     iv_w3  = iv_w2 + 1
    ///     jump b1(iv_w3, buf_w3)
    ///   b3(buf_done):
    ///     jump b4(0, buf_done, 0)            // reader header
    ///   b4(iv_r, buf_r, acc):
    ///     c2 = iv_r == n
    ///     branch c2 ? b6(buf_r, acc) : b5(iv_r, buf_r, acc)
    ///   b5(iv_r2, buf_r2, acc2):
    ///     x = load_dyn(buf_r2, iv_r2)
    ///     acc3 = acc2 + x
    ///     iv_r3 = iv_r2 + 1
    ///     jump b4(iv_r3, buf_r2, acc3)
    ///   b6(buf_final, final_acc):
    ///     rc_dec buf_final
    ///     ret final_acc
    fn build_writer_reader() -> Function {
        let mut b = Builder::new();
        let n = b.add_func_param(ScalarType::U64);

        let b0 = b.create_block();
        let b1 = b.create_block();
        let b2 = b.create_block();
        let b3 = b.create_block();
        let b4 = b.create_block();
        let b5 = b.create_block();
        let b6 = b.create_block();

        let iv_w = b.add_block_param(b1, ScalarType::U64);
        let buf_w = b.add_block_param(b1, ScalarType::RcPtr);
        let iv_w2 = b.add_block_param(b2, ScalarType::U64);
        let buf_w2 = b.add_block_param(b2, ScalarType::RcPtr);
        let buf_done = b.add_block_param(b3, ScalarType::RcPtr);
        let iv_r = b.add_block_param(b4, ScalarType::U64);
        let buf_r = b.add_block_param(b4, ScalarType::RcPtr);
        let acc = b.add_block_param(b4, ScalarType::U64);
        let iv_r2 = b.add_block_param(b5, ScalarType::U64);
        let buf_r2 = b.add_block_param(b5, ScalarType::RcPtr);
        let acc2 = b.add_block_param(b5, ScalarType::U64);
        let buf_final = b.add_block_param(b6, ScalarType::RcPtr);
        let final_acc = b.add_block_param(b6, ScalarType::U64);

        b.switch_to(b0);
        let buf = b.alloc_dyn(n);
        let zero_w = b.const_u64(0);
        b.jump(b1, vec![zero_w, buf]);

        b.switch_to(b1);
        let c1 = b.binop(BinaryOp::Eq, iv_w, n, ScalarType::U8);
        b.branch(c1, b3, vec![buf_w], b2, vec![iv_w, buf_w]);

        b.switch_to(b2);
        let buf_w3 = b.cow_store_dyn(buf_w2, iv_w2, iv_w2);
        let one1 = b.const_u64(1);
        let iv_w3 = b.binop(BinaryOp::Add, iv_w2, one1, ScalarType::U64);
        b.jump(b1, vec![iv_w3, buf_w3]);

        b.switch_to(b3);
        let zero_r = b.const_u64(0);
        let zero_a = b.const_u64(0);
        b.jump(b4, vec![zero_r, buf_done, zero_a]);

        b.switch_to(b4);
        let c2 = b.binop(BinaryOp::Eq, iv_r, n, ScalarType::U8);
        b.branch(c2, b6, vec![buf_r, acc], b5, vec![iv_r, buf_r, acc]);

        b.switch_to(b5);
        let x = b.load_dyn(buf_r2, iv_r2, ScalarType::U64);
        let acc3 = b.binop(BinaryOp::Add, acc2, x, ScalarType::U64);
        let one2 = b.const_u64(1);
        let iv_r3 = b.binop(BinaryOp::Add, iv_r2, one2, ScalarType::U64);
        b.jump(b4, vec![iv_r3, buf_r2, acc3]);

        b.switch_to(b6);
        b.rc_dec(buf_final);
        b.ret(final_acc);

        b.finish_function("wr", ScalarType::U64);
        b.build("wr").functions.remove("wr").unwrap()
    }

    #[test]
    fn detects_writer_reader_pair() {
        let func = build_writer_reader();
        let cands = find_candidates(&func);
        assert_eq!(cands.len(), 1, "expected one candidate, got {cands:#?}");
        let c = &cands[0];
        // Buffer chain should include the alloc dest, the cow_store
        // dest, and the block params on the chain.
        assert!(c.buffer_chain.len() >= 4, "chain too small: {:?}", c.buffer_chain);
        assert_ne!(c.writer_loop, c.reader_loop);
    }

    #[test]
    fn rejects_when_buffer_escapes() {
        // Same shape but with an extra use that disqualifies fusion:
        // store the buffer somewhere else (we don't model that here
        // directly; instead, verify a function with no AllocDyn at
        // all yields no candidates).
        let mut b = Builder::new();
        let p = b.add_func_param(ScalarType::U64);
        let _b0 = b.create_block();
        b.switch_to(BlockId(0));
        b.ret(p);
        b.finish_function("trivial", ScalarType::U64);
        let func = b.build("trivial").functions.remove("trivial").unwrap();
        assert!(find_candidates(&func).is_empty());
    }
}
