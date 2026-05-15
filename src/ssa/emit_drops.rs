//! Emit `RcInc` / `Drop` / `Free` / `Reset` / `Reuse` for statically-
//! owned values.
//!
//! Consumes the per-function `ownership::Analysis` and the whole-
//! program `layouts::ModuleLayouts`, and inserts drop, reuse, and
//! scoped rc_inc instructions. The transformation half of the static-
//! ownership pipeline — analysis lives in `ownership.rs` and
//! `layouts.rs`. See OWNERSHIP.md §3-4 for the full design.
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
//! - Compute the *effective last use* = max of v's direct last use
//!   and the last use of each Ptr child Loaded from v in this block.
//!   This is move-out: deferring the drop until after Borrowed
//!   children are dead so the cascade-free doesn't corrupt them. If
//!   any child escapes the block (appears in the terminator), skip.
//! - If v is in a viable reuse pair, emit `Reset(token, v, slot_types)`
//!   at the effective last use (defines the token consumed in Phase B).
//! - Otherwise, when the whole-program layouts pass produced a
//!   slot_types vector for `v`, emit `Drop(v, slots)` with moved-out
//!   slots masked so the cascade skips them. Falls back to `Free(v)`
//!   (runtime cascade via `heap.ptr_offsets`) when no static layout
//!   is available.
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
//! - Move-out for Calls that return a Ptr aliasing a child of an arg
//!   (`__list_get` style). Until then, Call args are conservatively
//!   skipped (leaks instead of use-after-free).
//! - Whole-program ownership signatures (borrowed vs consumed params)
//!   to remove the conservative Call-args treatment.
//! - Size-resilient reuse pairing (`AllocDyn` with growing capacity)
//!   so list data buffers reuse in-place across `append`.

use std::collections::{HashMap, HashSet};

use super::instruction::{BlockId, Inst, ScalarType, Terminator, Value};
use super::layouts::{Layout, ModuleLayouts};
use super::ownership::{Analysis, Ownership};
use super::param_usage::{ModuleUsage, ParamUsage};
use super::{Function, Module};

/// Run emit_drops over every function in `module`, using the per-
/// function analyses produced by `ownership::analyze_module`, the
/// whole-program layout signatures from `layouts::analyze`, and the
/// whole-program param-usage classification from
/// `param_usage::analyze`.
pub fn run(
    module: &mut Module,
    analyses: &HashMap<String, Analysis>,
    layouts: &ModuleLayouts,
    usage: &ModuleUsage,
) {
    // Take ownership of per-function layout maps so we can hand them
    // into each `emit_drops_function` without re-borrowing `module`.
    let mut value_layouts = layouts.values.clone();
    for (name, func) in &mut module.functions {
        if let Some(analysis) = analyses.get(name) {
            let func_layouts = value_layouts.remove(name).unwrap_or_default();
            emit_drops_function(func, analysis, &func_layouts, usage);
        }
    }
}

fn emit_drops_function(
    func: &mut Function,
    analysis: &Analysis,
    layouts: &HashMap<Value, Layout>,
    usage: &ModuleUsage,
) {
    // Phase RC: emit RcInc at each flagged store site (in reverse
    // order per block so earlier instruction indices stay stable).
    emit_rc_inc_fallback(func, &analysis.rc_inc_sites);

    // Identify slots that are "moved out" from their parent — a single
    // Load extracts a Ptr child, and the parent's slot is left
    // evacuated. The loaded child becomes its own Unique value.
    let (moved_out_slots, moved_out_children) = compute_moved_out(func);

    // Effective Unique set: refine analysis.ownership with the move-out
    // promotion (Loaded-from-Unique-single-Load → Unique) and re-run
    // block-param propagation to cover the children's renamings at
    // SSA join points.
    let effective_unique = compute_effective_unique(func, &analysis.ownership, &moved_out_children);

    // Whole-program slot layout per Ptr-typed Value: covers Allocs,
    // function entry params, Call results, and block params (via
    // propagation across block-param edges).
    let slot_types_by_value: HashMap<Value, Vec<ScalarType>> = layouts.clone();

    // Values whose true last instruction use is an ownership transfer
    // (Store/StoreDyn val, Pack/Insert field) — or a Call arg
    // (conservative for now). The new owner cascade-frees on its own
    // drop. Non-last-use stores are handled by the rc_inc fallback.
    let cleanly_transferred = cleanly_transferred(func, &analysis.ownership, usage);

    // Identify viable reuse pairs and reserve tokens.
    let (reuse_for_drop, reuse_for_alloc) = collect_reuse_pairs(
        func,
        analysis,
        &effective_unique,
        &moved_out_slots,
        &slot_types_by_value,
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

    // Phase B: per block, emit Reset (for reuse-pair drops) or
    // Drop/Free (otherwise) at each value's effective last use,
    // deferred past any loaded children's last uses. When the
    // whole-program layouts pass produces slot_types for `v`, emit
    // `Drop(v, slot_types)` with moved-out slots masked to non-Ptr so
    // the cascade skips them. Falls back to `Free(v)` (runtime cascade
    // via heap.ptr_offsets) when the layout is unknown.
    let loaded_ptr_children = loaded_ptr_children_map(func);
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
            if !effective_unique.contains(&v) {
                continue;
            }
            if transferred.contains(&v) {
                continue;
            }
            let reuse_info = reuse_for_drop.get(&v);
            if reuse_info.is_none() && cleanly_transferred.contains(&v) {
                continue;
            }
            if block.terminator.operands().contains(&v) {
                continue;
            }

            let descendants = transitive_loaded_descendants(v, &loaded_ptr_children);
            let Some(idx) = effective_last_use(block, v, &descendants) else { continue };

            let inst = match reuse_info {
                Some(info) => Inst::Reset(info.token, v, info.slot_types.clone()),
                None => match drop_slot_types(v, &slot_types_by_value, &moved_out_slots) {
                    Some(slots) => Inst::Drop(v, slots),
                    None => Inst::Free(v),
                },
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

/// Effective last use of `v` within `block`, factoring in move-out
/// over a set of transitively-loaded descendants. If any descendant
/// crosses the block boundary (appears in the terminator's operands),
/// returns `None` — the drop can't be deferred safely within this
/// block.
fn effective_last_use(
    block: &super::Block,
    v: Value,
    descendants: &HashSet<Value>,
) -> Option<usize> {
    let direct_last = block
        .insts
        .iter()
        .enumerate()
        .filter(|(_, inst)| inst.operands().contains(&v))
        .map(|(i, _)| i)
        .last()?;

    let term_ops: Vec<Value> = block.terminator.operands();
    for d in descendants {
        if term_ops.contains(d) {
            return None;
        }
    }

    let mut effective = direct_last;
    for &d in descendants {
        if let Some(d_last) = block
            .insts
            .iter()
            .enumerate()
            .filter(|(_, inst)| inst.operands().contains(&d))
            .map(|(i, _)| i)
            .last()
        {
            effective = effective.max(d_last);
        }
    }
    Some(effective)
}

/// All values transitively reachable from `v` via `Load(_, p, _)` /
/// `LoadDyn(_, p, _)` of Ptr-typed results. Cascade-free of `v`
/// touches every descendant, so they must all be dead at the drop
/// point.
fn transitive_loaded_descendants(
    v: Value,
    loaded_ptr_children: &HashMap<Value, Vec<Value>>,
) -> HashSet<Value> {
    let mut result: HashSet<Value> = HashSet::new();
    let mut stack: Vec<Value> = vec![v];
    while let Some(cur) = stack.pop() {
        if let Some(children) = loaded_ptr_children.get(&cur) {
            for &c in children {
                if result.insert(c) {
                    stack.push(c);
                }
            }
        }
    }
    result
}

struct ReuseInfo {
    token: Value,
    slot_types: Vec<ScalarType>,
}

/// Pick reuse pairs whose drop_val passes the same safety filters as
/// `Free`/`Drop`/`Reset` emission. For each viable pair, allocate a
/// fresh token Value and compute the drop_val's slot type layout
/// (with moved-out slots masked to non-Ptr so the cascade skips
/// them — the children are independent Unique values now).
fn collect_reuse_pairs(
    func: &Function,
    analysis: &Analysis,
    effective_unique: &HashSet<Value>,
    moved_out_slots: &HashMap<Value, HashSet<usize>>,
    slot_types_by_value: &HashMap<Value, Vec<ScalarType>>,
    cleanly_transferred: &HashSet<Value>,
) -> (HashMap<Value, ReuseInfo>, HashMap<Value, Value>) {
    let mut reuse_for_drop: HashMap<Value, ReuseInfo> = HashMap::new();
    let mut reuse_for_alloc: HashMap<Value, Value> = HashMap::new();
    let mut next_id = func.num_values();

    for pair in &analysis.reuse_pairs {
        if !effective_unique.contains(&pair.drop_val) {
            continue;
        }
        if cleanly_transferred.contains(&pair.drop_val) {
            continue;
        }
        let Some(slot_types) =
            drop_slot_types(pair.drop_val, slot_types_by_value, moved_out_slots)
        else {
            continue;
        };
        // Skip if this alloc_val is already claimed by another pair.
        if reuse_for_alloc.contains_key(&pair.alloc_val) {
            continue;
        }
        let token = Value { id: next_id, ty: ScalarType::Ptr };
        next_id += 1;
        reuse_for_drop.insert(pair.drop_val, ReuseInfo { token, slot_types });
        reuse_for_alloc.insert(pair.alloc_val, token);
    }

    (reuse_for_drop, reuse_for_alloc)
}

/// Compute the slot_types vector for a Drop/Reset of `v`, with any
/// moved-out slots masked to a non-Ptr type so the cascade skips
/// them. Returns `None` if `v` has no known slot layout (e.g. Call
/// result the layouts pass couldn't see into); the caller then emits
/// a plain `Free` that uses heap.ptr_offsets metadata at runtime.
fn drop_slot_types(
    v: Value,
    slot_types_by_value: &HashMap<Value, Vec<ScalarType>>,
    moved_out_slots: &HashMap<Value, HashSet<usize>>,
) -> Option<Vec<ScalarType>> {
    let mut slots = slot_types_by_value.get(&v).cloned()?;
    if let Some(moved) = moved_out_slots.get(&v) {
        for &slot_idx in moved {
            if slot_idx < slots.len() {
                slots[slot_idx] = ScalarType::U64;
            }
        }
    }
    Some(slots)
}

/// For each `Load(child, parent, off)` with `child.ty == Ptr` that is
/// the *only* Load (and no `LoadDyn` of Ptr from the same parent),
/// record `(parent, slot_idx)` as moved-out and `child → (parent, slot_idx)`
/// for use in ownership refinement.
///
/// Restriction (single-Load only): multi-Load of the same slot would
/// require an RcInc per extra Load to maintain refcounts. Skipping
/// those keeps emit_drops conservative (still safe, just leakier).
fn compute_moved_out(
    func: &Function,
) -> (HashMap<Value, HashSet<usize>>, HashMap<Value, (Value, usize)>) {
    // Pass 1: count Loads per (parent, slot_idx).
    let mut load_count: HashMap<(Value, usize), usize> = HashMap::new();
    let mut loaddyn_ptr_parents: HashSet<Value> = HashSet::new();
    for block in func.blocks.values() {
        for inst in &block.insts {
            match inst {
                Inst::Load(dest, ptr, off) if dest.ty == ScalarType::Ptr => {
                    *load_count.entry((*ptr, off / 8)).or_insert(0) += 1;
                }
                Inst::LoadDyn(dest, ptr, _) if dest.ty == ScalarType::Ptr => {
                    // Dynamic index: any slot could be loaded. Conservatively
                    // disable move-out for this parent.
                    loaddyn_ptr_parents.insert(*ptr);
                }
                _ => {}
            }
        }
    }

    // Pass 2: collect single-Load Ptr children.
    let mut slots: HashMap<Value, HashSet<usize>> = HashMap::new();
    let mut children: HashMap<Value, (Value, usize)> = HashMap::new();
    for block in func.blocks.values() {
        for inst in &block.insts {
            if let Inst::Load(dest, ptr, off) = inst {
                if dest.ty != ScalarType::Ptr {
                    continue;
                }
                if loaddyn_ptr_parents.contains(ptr) {
                    continue;
                }
                let slot_idx = off / 8;
                if load_count[&(*ptr, slot_idx)] != 1 {
                    continue;
                }
                slots.entry(*ptr).or_default().insert(slot_idx);
                children.insert(*dest, (*ptr, slot_idx));
            }
        }
    }

    (slots, children)
}

/// Effective Unique set. Starts with `analysis.ownership`'s Unique
/// entries, then promotes single-Load Ptr children of Unique parents
/// to Unique. Block params receive transitive promotion: if every
/// incoming edge args is now Unique, the param is too.
///
/// The promotion is sound because:
/// - A single-Load child from a Unique parent inherits the parent's
///   refcount slot — the runtime never incs at Load, so the slot's
///   "owner" passes from parent to child.
/// - The parent's Drop is emitted with the moved-out slot masked to
///   non-Ptr (via `drop_slot_types`), so the parent's cascade skips
///   the slot and doesn't double-decrement the child.
///
/// The child's own Drop/Free at its last use handles its onward
/// substructure (via runtime metadata if no static layout is known).
fn compute_effective_unique(
    func: &Function,
    ownership: &HashMap<Value, Ownership>,
    moved_out_children: &HashMap<Value, (Value, usize)>,
) -> HashSet<Value> {
    let mut unique: HashSet<Value> = ownership
        .iter()
        .filter(|(_, o)| **o == Ownership::Unique)
        .map(|(v, _)| *v)
        .collect();

    // Promote moved-out children of Unique parents to Unique.
    for (&child, &(parent, _slot)) in moved_out_children {
        if unique.contains(&parent) {
            unique.insert(child);
        }
    }

    // Propagate across block-param edges: a block param becomes Unique
    // if *every* incoming edge passes a Unique value. Iterate to
    // fixpoint; the lattice is monotone (params only ever join into
    // Unique).
    loop {
        let mut candidates: HashMap<Value, bool> = HashMap::new();
        for block in func.blocks.values() {
            for edge in block.terminator.successors() {
                let succ = &func.blocks[&edge.target];
                for (param, arg) in succ.params.iter().zip(edge.args.iter()) {
                    if param.ty != ScalarType::Ptr || unique.contains(param) {
                        continue;
                    }
                    let arg_unique = unique.contains(arg);
                    candidates
                        .entry(*param)
                        .and_modify(|all| *all = *all && arg_unique)
                        .or_insert(arg_unique);
                }
            }
        }
        let mut changed = false;
        for (param, all_unique) in candidates {
            if all_unique && unique.insert(param) {
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }

    unique
}

/// Map each parent value to the set of Ptr children Loaded from it.
/// Used for move-out semantics: when emitting a drop on a parent, we
/// defer to after the last use of any such child, so the cascade-free
/// path doesn't invalidate still-borrowed children.
fn loaded_ptr_children_map(func: &Function) -> HashMap<Value, Vec<Value>> {
    let mut map: HashMap<Value, Vec<Value>> = HashMap::new();
    for block in func.blocks.values() {
        for inst in &block.insts {
            match inst {
                Inst::Load(dest, ptr, _) | Inst::LoadDyn(dest, ptr, _) => {
                    if dest.ty == ScalarType::Ptr {
                        map.entry(*ptr).or_default().push(*dest);
                    }
                }
                _ => {}
            }
        }
    }
    map
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
    usage: &ModuleUsage,
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

        // Category 2: Call args. Mark as transferred only at positions
        // the callee declares `Transferring` per `ModuleUsage`. Args
        // passed to `Borrowing` positions stay drop-eligible in this
        // function — the callee promises not to take ownership.
        for inst in &block.insts {
            if let Inst::Call(_, callee, args) = inst {
                for (i, a) in args.iter().enumerate() {
                    if !is_ptr(*a) {
                        continue;
                    }
                    if usage.usage(callee, i) == ParamUsage::Transferring {
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
