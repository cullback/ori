//! Static ownership analysis — experimental.
//!
//! Replaces Perceus-style runtime reference counting with
//! compile-time ownership tracking. See OWNERSHIP.md for the full
//! design rationale.
//!
//! For each Ptr-typed SSA value, determines whether it's Unique
//! (can be dropped/reused at last use) or Borrowed (reference into
//! a living object, do not free).
//!
//! Relies on the explicit-block-params invariant: every cross-block
//! value flow goes through block params. This means a value's scope
//! is its defining block — no liveness analysis needed.

use std::collections::{HashMap, HashSet};

use super::instruction::{BlockId, Inst, ScalarType, Value};
use super::{Function, Module};

// ── Types ──────────────────────────────────────────────────────

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Ownership {
    /// Exactly one reference exists. Can be dropped at last use,
    /// producing a reuse token.
    Unique,
    /// Reference into a living object. Do not free.
    Borrowed,
}

/// What size allocation a Ptr value originated from.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum AllocKind {
    /// `Alloc(n)` — fixed-size header (e.g. 3-word list header).
    Static(usize),
    /// `AllocDyn` — runtime-sized buffer.
    Dynamic,
}

/// A drop-reuse pair: dropping `drop_val` produces a token that
/// feeds the allocation of `alloc_val`.
#[derive(Debug)]
pub struct ReusePair {
    pub drop_val: Value,
    pub alloc_val: Value,
    pub block: BlockId,
    pub kind: AllocKind,
}

/// A store of a Ptr value into a heap object that needs runtime
/// rc_inc — the store creates a new reference that can't be
/// resolved statically.
#[derive(Debug)]
pub struct RcIncSite {
    pub block: BlockId,
    /// The Ptr value being stored (gains a new reference).
    pub value: Value,
}

/// Full analysis result for one function.
#[derive(Debug)]
pub struct Analysis {
    pub ownership: HashMap<Value, Ownership>,
    pub alloc_kinds: HashMap<Value, AllocKind>,
    pub reuse_pairs: Vec<ReusePair>,
    /// Stores where runtime rc_inc is needed. These are the only
    /// sites that can't be handled by static ownership.
    pub rc_inc_sites: Vec<RcIncSite>,
}

/// Which alloc kinds need a runtime RC field in their layout.
/// Determined by whole-program analysis: if any rc_inc site stores
/// a value with a given alloc kind, that kind needs RC.
#[derive(Debug)]
pub struct RcLayout {
    /// Alloc kinds that need an RC prefix field.
    pub needs_rc: HashSet<AllocKind>,
}

impl std::fmt::Display for RcLayout {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.needs_rc.is_empty() {
            write!(f, "No types need RC (fully static).")
        } else {
            write!(f, "Types needing RC field: ")?;
            let mut kinds: Vec<_> = self.needs_rc.iter().collect();
            kinds.sort_by_key(|k| match k {
                AllocKind::Static(n) => (0, *n),
                AllocKind::Dynamic => (1, 0),
            });
            for (i, kind) in kinds.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                match kind {
                    AllocKind::Static(n) => write!(f, "alloc {n}")?,
                    AllocKind::Dynamic => write!(f, "alloc_dyn")?,
                }
            }
            Ok(())
        }
    }
}

/// Whole-module analysis: analyze every function, then determine
/// which alloc kinds need an RC field based on rc_inc sites.
pub fn analyze_module(module: &Module) -> (HashMap<String, Analysis>, RcLayout) {
    let mut analyses: HashMap<String, Analysis> = HashMap::new();
    let mut needs_rc: HashSet<AllocKind> = HashSet::new();

    for (name, func) in &module.functions {
        let result = analyze(func);

        for site in &result.rc_inc_sites {
            if let Some(&kind) = result.alloc_kinds.get(&site.value) {
                needs_rc.insert(kind);
            } else {
                // Value's alloc kind is unknown (e.g. function param
                // whose origin we can't trace within this function).
                // Conservatively mark all dynamic allocs as needing RC.
                needs_rc.insert(AllocKind::Dynamic);
            }
        }

        analyses.insert(name.clone(), result);
    }

    (analyses, RcLayout { needs_rc })
}

// ── Per-function entry point ───────────────────────────────────

pub fn analyze(func: &Function) -> Analysis {
    let ownership = classify_ownership(func);
    let alloc_kinds = compute_alloc_kinds(func);
    let reuse_pairs = find_reuse_pairs(func, &ownership, &alloc_kinds);
    let rc_inc_sites = find_rc_inc_sites(func, &ownership);
    Analysis {
        ownership,
        alloc_kinds,
        reuse_pairs,
        rc_inc_sites,
    }
}

// ── Phase 1: Classify ownership ────────────────────────────────

fn classify_ownership(func: &Function) -> HashMap<Value, Ownership> {
    let is_ptr = |v: Value| v.ty == ScalarType::Ptr;

    let mut own: HashMap<Value, Ownership> = HashMap::new();

    // Function params are borrowed (caller owns them).
    for &p in &func.params {
        if is_ptr(p) {
            own.insert(p, Ownership::Borrowed);
        }
    }

    // Instructions.
    for (_, block) in &func.blocks {
        for inst in &block.insts {
            match inst {
                Inst::Alloc(dest, _) | Inst::AllocDyn(dest, _) => {
                    own.insert(*dest, Ownership::Unique);
                }
                Inst::Load(dest, _, _) | Inst::LoadDyn(dest, _, _) if is_ptr(*dest) => {
                    own.insert(*dest, Ownership::Borrowed);
                }
                Inst::Call(dest, _, _) if is_ptr(*dest) => {
                    own.insert(*dest, Ownership::Unique);
                }
                _ => {}
            }
        }
    }

    // Block params: start as Unique, downgrade to Borrowed if any
    // incoming value is Borrowed. Iterate to fixpoint (loops).
    for (_, block) in &func.blocks {
        for &p in &block.params {
            if is_ptr(p) && !own.contains_key(&p) {
                own.insert(p, Ownership::Unique);
            }
        }
    }

    loop {
        let mut changed = false;
        for (_, block) in &func.blocks {
            for edge in block.terminator.successors() {
                let succ_params = &func.blocks[&edge.target].params;
                for (param, &arg) in succ_params.iter().zip(edge.args.iter()) {
                    if !is_ptr(*param) {
                        continue;
                    }
                    let arg_own = own.get(&arg).copied().unwrap_or(Ownership::Borrowed);
                    if arg_own == Ownership::Borrowed {
                        if own.get(param).copied() != Some(Ownership::Borrowed) {
                            own.insert(*param, Ownership::Borrowed);
                            changed = true;
                        }
                    }
                }
            }
        }
        if !changed {
            break;
        }
    }

    own
}

// ── Phase 2: Track alloc kinds through phis ────────────────────

fn compute_alloc_kinds(func: &Function) -> HashMap<Value, AllocKind> {
    let mut kinds: HashMap<Value, AllocKind> = HashMap::new();

    // Direct allocations.
    for (_, block) in &func.blocks {
        for inst in &block.insts {
            match inst {
                Inst::Alloc(dest, size) => {
                    kinds.insert(*dest, AllocKind::Static(*size));
                }
                Inst::AllocDyn(dest, _) => {
                    kinds.insert(*dest, AllocKind::Dynamic);
                }
                _ => {}
            }
        }
    }

    // Propagate through phis. If all incoming values have the same
    // kind, the block param inherits it. Conflict → remove.
    let mut conflict: HashSet<Value> = HashSet::new();

    loop {
        let mut changed = false;
        for (_, block) in &func.blocks {
            for edge in block.terminator.successors() {
                let succ_params = &func.blocks[&edge.target].params;
                for (param, &arg) in succ_params.iter().zip(edge.args.iter()) {
                    if conflict.contains(param) {
                        continue;
                    }
                    let Some(&arg_kind) = kinds.get(&arg) else {
                        continue;
                    };
                    match kinds.get(param).copied() {
                        None => {
                            kinds.insert(*param, arg_kind);
                            changed = true;
                        }
                        Some(existing) if existing != arg_kind => {
                            kinds.remove(param);
                            conflict.insert(*param);
                            changed = true;
                        }
                        _ => {}
                    }
                }
            }
        }
        if !changed {
            break;
        }
    }

    kinds
}

// ── Phase 3: Find reuse pairs ──────────────────────────────────
//
// With explicit block params, a value dies in its defining block
// if it's not passed to any successor via terminator args.
// No liveness analysis needed.

fn find_reuse_pairs(
    func: &Function,
    ownership: &HashMap<Value, Ownership>,
    alloc_kinds: &HashMap<Value, AllocKind>,
) -> Vec<ReusePair> {
    let is_ptr = |v: Value| v.ty == ScalarType::Ptr;

    let mut pairs = Vec::new();

    for (&bid, block) in &func.blocks {
        // Collect Ptr values defined in this block (params + inst dests).
        let mut local_ptrs: Vec<Value> = Vec::new();
        for &p in &block.params {
            if is_ptr(p) {
                local_ptrs.push(p);
            }
        }
        for inst in &block.insts {
            if let Some(d) = inst.dest() {
                if is_ptr(d) {
                    local_ptrs.push(d);
                }
            }
        }

        // A value dies here if it's not in the terminator args.
        let term_args: HashSet<Value> = block
            .terminator
            .successors()
            .iter()
            .flat_map(|edge| edge.args.iter().copied())
            .collect();

        // Find Unique values that die in this block.
        let mut dying_unique: Vec<(Value, usize)> = Vec::new();
        for &v in &local_ptrs {
            if ownership.get(&v).copied() != Some(Ownership::Unique) {
                continue;
            }
            if term_args.contains(&v) {
                continue;
            }
            // Find last instruction index that uses this value.
            let mut last_idx = None;
            for (idx, inst) in block.insts.iter().enumerate() {
                if inst.operands().contains(&v) {
                    last_idx = Some(idx);
                }
            }
            if let Some(idx) = last_idx {
                dying_unique.push((v, idx));
            }
        }

        // For each dying Unique value with a known alloc kind, find
        // a compatible alloc later in the same block.
        for &(drop_val, last_use_idx) in &dying_unique {
            let Some(&drop_kind) = alloc_kinds.get(&drop_val) else {
                continue;
            };

            for (idx, inst) in block.insts.iter().enumerate() {
                if idx <= last_use_idx {
                    continue;
                }
                let compatible = match (drop_kind, inst) {
                    (AllocKind::Static(n), Inst::Alloc(_, m)) => n == *m,
                    (AllocKind::Dynamic, Inst::AllocDyn(..)) => true,
                    _ => false,
                };
                if compatible {
                    let alloc_val = inst.dest().unwrap();
                    pairs.push(ReusePair {
                        drop_val,
                        alloc_val,
                        block: bid,
                        kind: drop_kind,
                    });
                    break;
                }
            }
        }
    }

    pairs
}

// ── Phase 4: Find rc_inc sites ─────────────────────────────────
//
// A store of a Ptr into a heap object needs rc_inc unless it's an
// ownership transfer: the stored value is Unique, this is its last
// use, and it's not passed to any successor.

fn find_rc_inc_sites(
    func: &Function,
    ownership: &HashMap<Value, Ownership>,
) -> Vec<RcIncSite> {
    let is_ptr = |v: Value| v.ty == ScalarType::Ptr;

    let mut sites = Vec::new();

    for (&bid, block) in &func.blocks {
        let term_args: HashSet<Value> = block
            .terminator
            .successors()
            .iter()
            .flat_map(|edge| edge.args.iter().copied())
            .collect();

        // Last instruction index where each Ptr value is used.
        let mut last_use: HashMap<Value, usize> = HashMap::new();
        for (idx, inst) in block.insts.iter().enumerate() {
            for v in inst.operands() {
                if is_ptr(v) {
                    last_use.insert(v, idx);
                }
            }
        }

        for (idx, inst) in block.insts.iter().enumerate() {
            let stored_val = match inst {
                Inst::Store(_, _, val) if is_ptr(*val) => *val,
                Inst::StoreDyn(_, _, val) if is_ptr(*val) => *val,
                _ => continue,
            };

            // Ownership transfer: Unique, last use, not passed to successor.
            if ownership.get(&stored_val).copied() == Some(Ownership::Unique) {
                let is_last = last_use.get(&stored_val) == Some(&idx)
                    && !term_args.contains(&stored_val);
                if is_last {
                    continue;
                }
            }

            sites.push(RcIncSite {
                block: bid,
                value: stored_val,
            });
        }
    }

    sites
}

// ── Display ────────────────────────────────────────────────────

impl std::fmt::Display for Analysis {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "Ownership:")?;
        let mut entries: Vec<_> = self.ownership.iter().collect();
        entries.sort_by_key(|(v, _)| v.id);
        for (v, own) in &entries {
            let kind_str = match self.alloc_kinds.get(v) {
                Some(AllocKind::Static(n)) => format!(" [alloc {n}]"),
                Some(AllocKind::Dynamic) => " [alloc_dyn]".to_string(),
                None => String::new(),
            };
            writeln!(f, "  {v}: {own:?}{kind_str}")?;
        }
        if self.reuse_pairs.is_empty() {
            writeln!(f, "\nNo reuse pairs found.")?;
        } else {
            writeln!(f, "\nReuse pairs:")?;
            for pair in &self.reuse_pairs {
                writeln!(
                    f,
                    "  drop {} -> reuse {} (in {}, {:?})",
                    pair.drop_val, pair.alloc_val, pair.block, pair.kind
                )?;
            }
        }
        if self.rc_inc_sites.is_empty() {
            writeln!(f, "\nNo rc_inc sites (fully static).")?;
        } else {
            writeln!(f, "\nrc_inc sites (runtime RC needed):")?;
            for site in &self.rc_inc_sites {
                writeln!(f, "  rc_inc {} (in {})", site.value, site.block)?;
            }
        }
        Ok(())
    }
}

// ── Tests ──────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ssa::instruction::BinaryOp;
    use crate::ssa::Builder;

    /// Build the list-map accumulator loop:
    ///
    ///   fn map_inc(input: ptr) -> ptr
    ///     Iterates over input, applies +1 to each I32 element,
    ///     builds output by appending to an accumulator.
    ///
    /// This is the pattern that currently fails to get reuse
    /// because the accumulator flows through block params.
    fn build_map_loop() -> crate::ssa::Module {
        let mut b = Builder::new();

        let input = b.add_func_param(ScalarType::Ptr);
        b.set_return_type(ScalarType::Ptr);

        let b0 = b.create_block(); // entry
        let b1 = b.create_block(); // loop header
        let b2 = b.create_block(); // loop body
        let b3 = b.create_block(); // exit

        // b1 params: (i, acc, len, data)
        let i = b.add_block_param(b1, ScalarType::U64);
        let acc = b.add_block_param(b1, ScalarType::Ptr);
        let h_len = b.add_block_param(b1, ScalarType::U64);
        let h_data = b.add_block_param(b1, ScalarType::Ptr);

        // b2 params: (i2, acc2, len2, data2) — explicit threading
        let i2 = b.add_block_param(b2, ScalarType::U64);
        let acc2 = b.add_block_param(b2, ScalarType::Ptr);
        let len2 = b.add_block_param(b2, ScalarType::U64);
        let data2 = b.add_block_param(b2, ScalarType::Ptr);

        // b3 params: (result: ptr)
        let result = b.add_block_param(b3, ScalarType::Ptr);

        // ── b0: entry ──
        b.switch_to(b0);
        let len = b.load(input, 0, ScalarType::U64);
        let data = b.load(input, 2, ScalarType::Ptr);
        let zero = b.const_u64(0);
        let empty_data = b.alloc_dyn(zero);
        let empty = b.alloc(3);
        b.store(empty, 0, zero);
        b.store(empty, 1, zero);
        b.store(empty, 2, empty_data);
        b.jump(b1, vec![zero, empty, len, data]);

        // ── b1: loop header ──
        b.switch_to(b1);
        let done = b.binop(BinaryOp::Eq, i, h_len, ScalarType::U8);
        b.branch(done, b3, vec![acc], b2, vec![i, acc, h_len, h_data]);

        // ── b2: loop body ──
        b.switch_to(b2);
        let elem = b.load_dyn(data2, i2, ScalarType::I32);
        let one_i32 = b.const_i32(1);
        let mapped = b.binop(BinaryOp::Add, elem, one_i32, ScalarType::I32);

        let old_len = b.load(acc2, 0, ScalarType::U64);
        let old_data = b.load(acc2, 2, ScalarType::Ptr);
        let one_u64 = b.const_u64(1);
        let new_len = b.binop(BinaryOp::Add, old_len, one_u64, ScalarType::U64);
        let new_data = b.alloc_dyn(new_len);
        let _copy =
            b.call("__list_copy_into", vec![old_data, new_data, old_len], ScalarType::I64);
        b.store_dyn(new_data, old_len, mapped);
        let new_acc = b.alloc(3);
        b.store(new_acc, 0, new_len);
        b.store(new_acc, 1, new_len);
        b.store(new_acc, 2, new_data);
        let next_i = b.binop(BinaryOp::Add, i2, one_u64, ScalarType::U64);
        b.jump(b1, vec![next_i, new_acc, len2, data2]);

        // ── b3: exit ──
        b.switch_to(b3);
        b.ret(result);

        b.finish_function("map_inc", ScalarType::Ptr);
        b.build("map_inc")
    }

    #[test]
    fn map_loop_ownership() {
        let module = build_map_loop();
        let func = &module.functions["map_inc"];
        eprintln!("{func}");

        let result = analyze(func);
        eprintln!("{result}");

        // input (func param) is Borrowed.
        let input = func.params[0];
        assert_eq!(result.ownership[&input], Ownership::Borrowed);

        // data (loaded from input) is Borrowed.
        let data = find_load(func, input, 2).expect("data = load input[2]");
        assert_eq!(result.ownership[&data], Ownership::Borrowed);

        // acc (block param of b1) should be Unique.
        let acc = func.blocks[&BlockId(1)].params[1];
        assert_eq!(result.ownership[&acc], Ownership::Unique);
        assert_eq!(result.alloc_kinds[&acc], AllocKind::Static(3));

        // acc2 (block param of b2, threaded from b1) should also be
        // Unique with the same alloc kind — this is where reuse happens.
        let acc2 = func.blocks[&BlockId(2)].params[1];
        assert_eq!(result.ownership[&acc2], Ownership::Unique);
        assert_eq!(result.alloc_kinds[&acc2], AllocKind::Static(3));

        // Reuse pair: drop acc2 → reuse new_acc in b2.
        let header_pair = result
            .reuse_pairs
            .iter()
            .find(|p| p.drop_val == acc2)
            .expect("should find reuse pair for acc2 → new_acc");
        assert_eq!(header_pair.kind, AllocKind::Static(3));
        assert_eq!(header_pair.block, BlockId(2));
    }

    /// Build the list-repeat pattern:
    ///
    ///   fn repeat(n: u64, val: ptr) -> ptr
    ///     Creates a list of n copies of val. Each iteration stores
    ///     the same `val` pointer into the data buffer — this is the
    ///     one case where runtime RC is needed.
    fn build_list_repeat() -> crate::ssa::Module {
        let mut b = Builder::new();

        let n = b.add_func_param(ScalarType::U64);
        let val = b.add_func_param(ScalarType::Ptr);
        b.set_return_type(ScalarType::Ptr);

        let b0 = b.create_block(); // entry
        let b1 = b.create_block(); // loop header
        let b2 = b.create_block(); // loop body
        let b3 = b.create_block(); // exit

        let i = b.add_block_param(b1, ScalarType::U64);
        let acc = b.add_block_param(b1, ScalarType::Ptr);

        // b2 params: (i2, acc2) — n and val are func params, always accessible
        let i2 = b.add_block_param(b2, ScalarType::U64);
        let acc2 = b.add_block_param(b2, ScalarType::Ptr);

        let result = b.add_block_param(b3, ScalarType::Ptr);

        // ── b0: entry ──
        b.switch_to(b0);
        let zero = b.const_u64(0);
        let empty_data = b.alloc_dyn(zero);
        let empty = b.alloc(3);
        b.store(empty, 0, zero);
        b.store(empty, 1, zero);
        b.store(empty, 2, empty_data);
        b.jump(b1, vec![zero, empty]);

        // ── b1: loop header ──
        b.switch_to(b1);
        let done = b.binop(BinaryOp::Eq, i, n, ScalarType::U8);
        b.branch(done, b3, vec![acc], b2, vec![i, acc]);

        // ── b2: loop body — append val to acc ──
        b.switch_to(b2);
        let old_len = b.load(acc2, 0, ScalarType::U64);
        let old_data = b.load(acc2, 2, ScalarType::Ptr);
        let one = b.const_u64(1);
        let new_len = b.binop(BinaryOp::Add, old_len, one, ScalarType::U64);
        let new_data = b.alloc_dyn(new_len);
        let _copy =
            b.call("__list_copy_into", vec![old_data, new_data, old_len], ScalarType::I64);
        b.store_dyn(new_data, old_len, val); // <-- val stored into list!
        let new_acc = b.alloc(3);
        b.store(new_acc, 0, new_len);
        b.store(new_acc, 1, new_len);
        b.store(new_acc, 2, new_data);
        let next_i = b.binop(BinaryOp::Add, i2, one, ScalarType::U64);
        b.jump(b1, vec![next_i, new_acc]);

        // ── b3: exit ──
        b.switch_to(b3);
        b.ret(result);

        b.finish_function("repeat", ScalarType::Ptr);
        b.build("repeat")
    }

    #[test]
    fn list_repeat_needs_rc() {
        let module = build_list_repeat();
        let func = &module.functions["repeat"];
        eprintln!("{func}");

        let result = analyze(func);
        eprintln!("{result}");

        let val = func.params[1];
        assert_eq!(result.ownership[&val], Ownership::Borrowed);

        // acc2 in the body block is where reuse happens.
        let acc2 = func.blocks[&BlockId(2)].params[1];
        assert_eq!(result.ownership[&acc2], Ownership::Unique);
        assert!(
            result.reuse_pairs.iter().any(|p| p.drop_val == acc2),
            "header reuse should still work"
        );

        assert!(
            result.rc_inc_sites.iter().any(|s| s.value == val),
            "storing val into list should require rc_inc"
        );
    }

    #[test]
    fn map_loop_no_rc_inc() {
        let module = build_map_loop();
        let func = &module.functions["map_inc"];
        let result = analyze(func);

        assert!(
            result.rc_inc_sites.is_empty(),
            "map of I32 elements should need no rc_inc, got: {:?}",
            result.rc_inc_sites.iter().map(|s| s.value).collect::<Vec<_>>()
        );
    }

    #[test]
    fn module_level_rc_layout() {
        let map_module = build_map_loop();
        let (_, layout) = analyze_module(&map_module);
        eprintln!("map_inc: {layout}");
        assert!(layout.needs_rc.is_empty());

        let repeat_module = build_list_repeat();
        let (_, layout) = analyze_module(&repeat_module);
        eprintln!("repeat: {layout}");
        assert!(layout.needs_rc.contains(&AllocKind::Dynamic));
    }

    /// Helper: find the Value produced by `Load(_, ptr, offset)`.
    fn find_load(func: &Function, ptr: Value, offset: usize) -> Option<Value> {
        for block in func.blocks.values() {
            for inst in &block.insts {
                if let Inst::Load(dest, p, off) = inst {
                    if *p == ptr && *off == offset {
                        return Some(*dest);
                    }
                }
            }
        }
        None
    }
}
