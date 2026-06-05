//! Eliminate allocations whose contents are never observed.
//!
//! After `rc_emit` runs, some blocks contain an `Alloc(v)` whose
//! only uses are `Store`s into `v` and a final `RcDec(v)` — no `Load`
//! ever reads the value back, no other instruction observes `v`.
//! That happens when an intermediate aggregate is materialized purely
//! to be immediately consumed (after load-forwarding rewires the
//! consumer to use the SSA values directly), then dropped.
//!
//! Removing the whole chain is local and mechanical: classify each
//! use of every `Alloc`/`AllocDyn` result; if every use is either
//! a `Store` writing into `v`, an `RcInc(v)`, or an `RcDec(v)`, and
//! there's at least one `RcDec(v)` (so the slot is actually being
//! released here), drop the alloc, its stores, and its rc traffic.
//!
//! ## Why this is rc-safe
//!
//! Each `Store(v, _, val)` with an RcPtr `val` has an auto-`rc_inc`
//! on `val` at eval time. The matching `RcDec(v)` cascades through
//! `v`'s `ptr_offsets` and emits one `rc_dec` per RcPtr-typed slot.
//! These cancel: removing both leaves rc traffic on `val` unchanged.
//! For non-RcPtr stores, there's no rc traffic to balance, so dropping
//! the store is trivially safe.

use std::collections::HashSet;

use crate::ssa::Module;
use crate::ssa::instruction::{Inst, Value};

pub fn run(module: &mut Module) {
    // Iterate to fixpoint: eliminating one dead alloc may unblock
    // another (an alloc that was kept alive only by a Store into the
    // freshly-eliminated alloc becomes dead once that Store is gone).
    for func in module.functions.values_mut() {
        for block in func.blocks.values_mut() {
            loop {
                let len_before = block.insts.len();
                elim_in_block(block);
                if block.insts.len() == len_before {
                    break;
                }
            }
        }
    }
}

fn elim_in_block(block: &mut crate::ssa::Block) {
    // Collect every Alloc/AllocDyn result in this block.
    let candidates: HashSet<Value> = block.insts.iter().filter_map(|inst| match inst {
        Inst::Alloc(v, _) | Inst::AllocDyn(v, _) => Some(*v),
        _ => None,
    }).collect();
    if candidates.is_empty() {
        return;
    }

    // Walk the block. For each use of a candidate value, mark it as
    // escaped (used in some way that observes the storage) unless the
    // use is just a Store writing into v or rc traffic on v itself.
    let mut escaped: HashSet<Value> = HashSet::new();
    let mut has_rc_dec: HashSet<Value> = HashSet::new();

    let mark = |escaped: &mut HashSet<Value>, v: &Value| {
        if candidates.contains(v) {
            escaped.insert(*v);
        }
    };

    for inst in &block.insts {
        match inst {
            Inst::Alloc(..) | Inst::AllocDyn(_, _) => {
                // The Alloc itself doesn't use anything that escapes;
                // AllocDyn's size operand could be a candidate alloc
                // result, but that would be a weird shape and treating
                // it as escape is the safe default.
                if let Inst::AllocDyn(_, size) = inst {
                    mark(&mut escaped, size);
                }
            }
            Inst::Store(_p, _, val) => {
                // `_p` as a Store target is OK — that's a write
                // *into* the candidate's slot, exactly what we're
                // trying to detect. But `val` flowing into a Store
                // is the value escaping into someone else's slot.
                mark(&mut escaped, val);
            }
            Inst::StoreDyn(_p, idx, val) => {
                mark(&mut escaped, idx);
                mark(&mut escaped, val);
            }
            Inst::Load(_, p, _) | Inst::LoadDyn(_, p, _) => {
                // Reading from a candidate observes its data — escape.
                mark(&mut escaped, p);
            }
            Inst::Call { args, .. } => {
                for a in args {
                    mark(&mut escaped, a);
                }
            }
            Inst::CowStore(_, ptr, _, val) => {
                mark(&mut escaped, ptr);
                mark(&mut escaped, val);
            }
            Inst::CowStoreDyn(_, ptr, idx, val) => {
                mark(&mut escaped, ptr);
                mark(&mut escaped, idx);
                mark(&mut escaped, val);
            }
            Inst::CowMoveOut { src, .. } => mark(&mut escaped, src),
            Inst::CowResizeDyn(_, ptr, size) => {
                mark(&mut escaped, ptr);
                mark(&mut escaped, size);
            }
            Inst::BinOp(_, _, l, r) => {
                mark(&mut escaped, l);
                mark(&mut escaped, r);
            }
            Inst::Cast(_, src) | Inst::BitCast(_, src) => mark(&mut escaped, src),
            Inst::RcInc(v) => {
                // RcInc on a candidate is OK if we end up removing
                // the alloc anyway (the inc/dec pair cancels). Don't
                // mark it as escape.
                let _ = v;
            }
            Inst::RcDec(v) => {
                if candidates.contains(v) {
                    has_rc_dec.insert(*v);
                }
            }
            Inst::Const(..) | Inst::StaticRef(..) => {}
        }
        // Also: dynamic-size operand from AllocDyn (handled above).
    }

    // Any candidate appearing in the terminator escapes.
    for op in block.terminator.operands() {
        mark(&mut escaped, &op);
    }

    let to_remove: HashSet<Value> = candidates
        .iter()
        .filter(|v| !escaped.contains(v) && has_rc_dec.contains(v))
        .copied()
        .collect();
    if to_remove.is_empty() {
        return;
    }

    block.insts.retain(|inst| match inst {
        Inst::Alloc(v, _) | Inst::AllocDyn(v, _) if to_remove.contains(v) => false,
        Inst::Store(p, _, _) | Inst::StoreDyn(p, _, _) if to_remove.contains(p) => false,
        Inst::RcInc(v) | Inst::RcDec(v) if to_remove.contains(v) => false,
        _ => true,
    });
}
