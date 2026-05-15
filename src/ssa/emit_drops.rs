//! Emit `RcInc` / `Free` / `Reset` / `Reuse` for statically-owned values.
//!
//! Consumes the per-function `ownership::Analysis` and inserts
//! drop, reuse, and scoped rc_inc instructions. The transformation
//! half of the static-ownership pipeline — analysis lives in
//! `ownership.rs`. See OWNERSHIP.md §3-4 for the full design.
//!
//! ## How
//!
//! Three phases per function:
//!
//! **A. rc_inc fallback.** For each `RcIncSite { block, inst_idx, value }`
//! from the analysis, insert `RcInc(value)` immediately before the
//! flagged `Store`/`StoreDyn`. These are the data-dependent aliasing
//! sites the static analysis couldn't resolve.
//!
//! **B. Reuse-pair rewrite.** For each `ReusePair { drop_val, alloc_val }`
//! whose drop_val passes the safety filters and whose origin is an
//! `Alloc(_, size)` (so we can recover slot types), allocate a fresh
//! token `Value`. Rewrite the `alloc_val`-defining `Alloc`/`AllocDyn`
//! to `Reuse`/`ReuseDyn` taking the token.
//!
//! **C. Drop emission.** Per block, for each Ptr value defined in the
//! block that is Unique and not transferred to a successor/Return:
//! - If it's in a viable reuse pair, emit `Reset(token, v, slot_types)`
//!   right after its last use (defines the token consumed in Phase B).
//! - Otherwise (and only if safe — no Ptr children loaded out, not
//!   cleanly-transferred to a new owner), emit `Free(v)`.
//!
//! ## Input invariants
//!
//! - Explicit-block-params (from `ssa_construct`). Required so that
//!   "last use in defining block" is a well-defined concept.
//! - `Analysis` matches the current SSA shape (ownership, alloc
//!   kinds, reuse pairs, rc_inc sites). Don't reorder instructions
//!   between `ownership::analyze_module` and this pass.
//!
//! ## Output invariants
//!
//! - Every input invariant preserved.
//! - Each emitted `Free(v)` corresponds to a Unique value whose
//!   ownership we've proven static.
//!
//! ## Notes — v0 scope
//!
//! Anything not matching the criteria above is left alone. Programs
//! that rely on those cases (shared stores, move-out from Unique
//! parents, reuse pairs) will leak in the interpreter until later
//! slices land. The interpreter's cascade-free path means leaks are
//! safe — no use-after-free — they just hold memory longer than
//! optimal.
//!
//! Planned extensions:
//! - Block-param drop_vals (loop accumulators) — currently skipped
//!   because slot_types can't be recovered without dominator analysis.
//! - Move-out semantics for Unique parents with loaded Ptr children
//!   or passed to Calls that return Ptr children (`__list_get` style).
//!   Until then, Call args are conservatively skipped (leaks instead
//!   of use-after-free).
//! - Whole-program ownership signatures (borrowed vs consumed params)
//!   to remove the conservative Call-args treatment.

use std::collections::{HashMap, HashSet};

use super::instruction::{BlockId, Inst, ScalarType, Terminator, Value};
use super::ownership::{Analysis, Ownership};
use super::{Function, Module};

/// Run emit_drops over every function in `module`, using the per-
/// function analyses produced by `ownership::analyze_module`.
pub fn run(module: &mut Module, analyses: &HashMap<String, Analysis>) {
    for (name, func) in &mut module.functions {
        if let Some(analysis) = analyses.get(name) {
            emit_drops_function(func, analysis);
        }
    }
}

fn emit_drops_function(func: &mut Function, analysis: &Analysis) {
    // Phase RC: emit RcInc at each flagged store site (in reverse
    // order per block so earlier instruction indices stay stable).
    emit_rc_inc_fallback(func, &analysis.rc_inc_sites);

    // Values from which a Ptr child is Loaded anywhere in the function.
    // Cascade-freeing those would invalidate the borrowed child.
    let parents_with_loaded_ptr_children = parents_with_loaded_ptr_children(func);

    // Values whose true last instruction use is an ownership transfer
    // (Store/StoreDyn val, Pack/Insert field). Those should not be
    // Free'd locally — the new owner cascade-frees them via its own
    // drop. Stores that *aren't* a value's last use are handled by
    // the rc_inc fallback above (which emits RcInc before the store).
    let cleanly_transferred = cleanly_transferred(func, &analysis.ownership);

    // Identify viable reuse pairs and reserve tokens.
    let (reuse_for_drop, reuse_for_alloc) = collect_reuse_pairs(
        func,
        analysis,
        &parents_with_loaded_ptr_children,
        &cleanly_transferred,
    );

    // Phase A: rewrite each alloc_val's defining instruction to Reuse/ReuseDyn.
    for block in func.blocks.values_mut() {
        for inst in &mut block.insts {
            let Some(dest) = inst.dest() else { continue };
            let Some(&token) = reuse_for_alloc.get(&dest) else { continue };
            *inst = match inst {
                Inst::Alloc(_, size) => Inst::Reuse(dest, token, *size),
                Inst::AllocDyn(_, size_val) => Inst::ReuseDyn(dest, token, *size_val),
                _ => continue,
            };
        }
    }

    // Phase B: per block, emit Reset (for reuse-pair drops) or Free
    // (for other unique deaths) at each last-use site.
    let block_ids: Vec<BlockId> = func.blocks.keys().copied().collect();
    for bid in block_ids {
        let mut drops: Vec<(usize, Inst)> = Vec::new();
        let block = &func.blocks[&bid];

        // Ptr values defined in this block (params + instruction dests).
        let mut local_ptrs: Vec<Value> = Vec::new();
        for &p in &block.params {
            if p.ty == ScalarType::Ptr {
                local_ptrs.push(p);
            }
        }
        for inst in &block.insts {
            if let Some(d) = inst.dest() {
                if d.ty == ScalarType::Ptr {
                    local_ptrs.push(d);
                }
            }
        }

        // Values that leave this block alive: successor edge args + return operand.
        let transferred = terminator_transferred(&block.terminator);

        for v in local_ptrs {
            if analysis.ownership.get(&v).copied() != Some(Ownership::Unique) {
                continue;
            }
            if transferred.contains(&v) {
                continue;
            }
            // Reuse-pair drops get Reset emission; non-pair drops get Free.
            let reuse_info = reuse_for_drop.get(&v);
            if reuse_info.is_none() {
                if parents_with_loaded_ptr_children.contains(&v) {
                    continue;
                }
                if cleanly_transferred.contains(&v) {
                    continue;
                }
            }
            // A Ptr used as the cond of a Branch (etc.) without being
            // transferred would need a post-terminator drop. Out of scope.
            if block.terminator.operands().contains(&v) {
                continue;
            }

            // Last instruction index that uses v as an operand.
            let last_idx = block
                .insts
                .iter()
                .enumerate()
                .filter(|(_, inst)| inst.operands().contains(&v))
                .map(|(i, _)| i)
                .last();
            let Some(idx) = last_idx else { continue };

            let inst = match reuse_info {
                Some(info) => Inst::Reset(info.token, v, info.slot_types.clone()),
                None => Inst::Free(v),
            };
            drops.push((idx, inst));
        }

        // Insert in reverse order so earlier indices stay stable.
        drops.sort_by_key(|(idx, _)| std::cmp::Reverse(*idx));
        let block_mut = func.blocks.get_mut(&bid).unwrap();
        for (idx, inst) in drops {
            block_mut.insts.insert(idx + 1, inst);
        }
    }
}

struct ReuseInfo {
    token: Value,
    slot_types: Vec<ScalarType>,
}

/// Pick reuse pairs whose drop_val passes the same safety filters as
/// `Free` emission. For each, allocate a fresh token Value and compute
/// the drop_val's slot type layout.
///
/// Restriction (v0): drop_val must be defined by an `Alloc(_, size)`
/// or `AllocDyn` in the function (not a block param), so we can
/// observe its Stores and recover slot types. Block-param drop_vals
/// (loop accumulators) need a richer analysis — deferred.
fn collect_reuse_pairs(
    func: &Function,
    analysis: &Analysis,
    parents_with_loaded_ptr_children: &HashSet<Value>,
    cleanly_transferred: &HashSet<Value>,
) -> (HashMap<Value, ReuseInfo>, HashMap<Value, Value>) {
    let mut reuse_for_drop: HashMap<Value, ReuseInfo> = HashMap::new();
    let mut reuse_for_alloc: HashMap<Value, Value> = HashMap::new();
    let mut next_id = func.num_values();

    // For Alloc-defined values, scan all Stores to recover slot types
    // (so Reset knows which slots are Ptr-typed for cascade-free).
    let slot_types_by_drop = compute_slot_types_for_allocs(func);

    for pair in &analysis.reuse_pairs {
        if parents_with_loaded_ptr_children.contains(&pair.drop_val) {
            continue;
        }
        if cleanly_transferred.contains(&pair.drop_val) {
            continue;
        }
        // Only handle drops whose origin is a static-size Alloc in
        // this function. AllocDyn and block-param drops need a more
        // careful slot_types derivation.
        let Some(slot_types) = slot_types_by_drop.get(&pair.drop_val) else {
            continue;
        };
        // Skip if this alloc_val is already claimed by another pair.
        if reuse_for_alloc.contains_key(&pair.alloc_val) {
            continue;
        }
        let token = Value { id: next_id, ty: ScalarType::Ptr };
        next_id += 1;
        reuse_for_drop.insert(pair.drop_val, ReuseInfo { token, slot_types: slot_types.clone() });
        reuse_for_alloc.insert(pair.alloc_val, token);
    }

    (reuse_for_drop, reuse_for_alloc)
}

/// For each `Alloc(dest, size)`, compute the per-slot ScalarType by
/// scanning subsequent `Store(dest, offset, val)` instructions in the
/// same block. Slot count is `size / 8` (uniform 8-byte stride that
/// lower currently emits). Slots without an observed Store default to
/// `Ptr` — conservative, so the cascade-free path still triggers if
/// we got the layout wrong.
fn compute_slot_types_for_allocs(func: &Function) -> HashMap<Value, Vec<ScalarType>> {
    let mut map: HashMap<Value, Vec<ScalarType>> = HashMap::new();
    for block in func.blocks.values() {
        for inst in &block.insts {
            if let Inst::Alloc(dest, size) = inst {
                let num_slots = size / 8;
                map.insert(*dest, vec![ScalarType::Ptr; num_slots]);
            }
        }
        for inst in &block.insts {
            if let Inst::Store(ptr, offset, val) = inst {
                if let Some(slots) = map.get_mut(ptr) {
                    let slot_idx = offset / 8;
                    if slot_idx < slots.len() {
                        slots[slot_idx] = val.ty;
                    }
                }
            }
        }
    }
    map
}

/// Find every Ptr value `p` such that some `Load(_, p, _)` (or
/// `LoadDyn`) in the function produces a Ptr-typed result. Those
/// children would be cascade-freed if `p` is `Free`'d while still in
/// use elsewhere.
fn parents_with_loaded_ptr_children(func: &Function) -> HashSet<Value> {
    let mut parents = HashSet::new();
    for block in func.blocks.values() {
        for inst in &block.insts {
            match inst {
                Inst::Load(dest, ptr, _) | Inst::LoadDyn(dest, ptr, _) => {
                    if dest.ty == ScalarType::Ptr {
                        parents.insert(*ptr);
                    }
                }
                _ => {}
            }
        }
    }
    parents
}

/// Insert `RcInc(value)` immediately before each flagged store. The
/// fallback for store sites the ownership analysis couldn't resolve
/// statically — typically Ptrs stored into heap objects where the
/// value continues to live in the caller after the store (so the
/// store creates a true second reference).
///
/// Sites are sorted within each block by descending `inst_idx` so
/// earlier indices stay stable as we insert.
fn emit_rc_inc_fallback(func: &mut Function, sites: &[super::ownership::RcIncSite]) {
    if sites.is_empty() {
        return;
    }
    let mut by_block: HashMap<BlockId, Vec<(usize, Value)>> = HashMap::new();
    for site in sites {
        by_block.entry(site.block).or_default().push((site.inst_idx, site.value));
    }
    for (bid, mut entries) in by_block {
        entries.sort_by_key(|(idx, _)| std::cmp::Reverse(*idx));
        let Some(block) = func.blocks.get_mut(&bid) else { continue };
        for (idx, v) in entries {
            block.insts.insert(idx, Inst::RcInc(v));
        }
    }
}

/// Values that `emit_drops` must not Free locally. Two categories
/// fold into one set:
///
/// 1. **True transfers:** the value's last instruction use is a
///    Store/StoreDyn val, Pack field, or Insert val. The new owner
///    cascade-frees it on its own drop. Non-transfer Stores of the
///    same value are handled by the rc_inc fallback.
///
/// 2. **Call args (conservative):** any value passed to a `Call` is
///    skipped. The callee may return a Ptr that aliases a child of
///    this value (e.g. `__list_get` returning a list element). Move-
///    out semantics for that case aren't built yet; freeing here
///    would cascade-free the still-aliased child. Cost: leaks the
///    Call-arg value. v0 acceptable.
fn cleanly_transferred(
    func: &Function,
    ownership: &HashMap<Value, Ownership>,
) -> HashSet<Value> {
    let is_ptr = |v: Value| v.ty == ScalarType::Ptr;
    let mut s = HashSet::new();
    for block in func.blocks.values() {
        let mut last_inst_use: HashMap<Value, usize> = HashMap::new();
        for (idx, inst) in block.insts.iter().enumerate() {
            for v in inst.operands() {
                if is_ptr(v) {
                    last_inst_use.insert(v, idx);
                }
            }
        }
        let mut term_uses: HashSet<Value> = HashSet::new();
        for v in block.terminator.operands() {
            term_uses.insert(v);
        }

        // Category 1: true transfers (last use is transfer-shaped).
        for (v, idx) in last_inst_use {
            if ownership.get(&v).copied() != Some(Ownership::Unique) {
                continue;
            }
            if term_uses.contains(&v) {
                continue;
            }
            let inst = &block.insts[idx];
            let is_transfer = match inst {
                Inst::Store(_, _, val) | Inst::StoreDyn(_, _, val) => *val == v,
                Inst::Pack(_, fields) => fields.contains(&v),
                Inst::Insert(_, _, _, val) => *val == v,
                _ => false,
            };
            if is_transfer {
                s.insert(v);
            }
        }

        // Category 2: Call args. Conservative until move-out lands.
        for inst in &block.insts {
            if let Inst::Call(_, _, args) = inst {
                for a in args {
                    if is_ptr(*a) {
                        s.insert(*a);
                    }
                }
            }
        }
    }
    s
}

fn terminator_transferred(term: &Terminator) -> HashSet<Value> {
    let mut s = HashSet::new();
    for edge in term.successors() {
        s.extend(edge.args.iter().copied());
    }
    // Returned values transfer ownership to the caller.
    if let Terminator::Return(v) = term {
        s.insert(*v);
    }
    s
}
