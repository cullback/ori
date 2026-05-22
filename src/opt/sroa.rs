//! Scalar Replacement of Aggregates.
//!
//! Promote heap allocations whose result never escapes into
//! register-resident `Agg` values: `Alloc + Stores` → `Pack`, `Load`
//! → `Extract`, `RcInc`/`RcDec` dropped.
//!
//! ## Scope
//!
//! Handles allocs that flow within a function and out via Return —
//! including allocs that pass through block params (multiple
//! predecessors converging on the same param). When an alloc reaches
//! a function's Return, the function's return type changes from
//! `RcPtr` to `Agg(n)`; callers in other functions get their call
//! result and downstream Loads/rc traffic rewritten.
//!
//! ## What's "safe"
//!
//! An alloc is promotable if **every value derived from it** — the
//! alloc itself, any block param that receives it, the function's
//! return value if it reaches Return — has only these uses:
//!
//! - As the `ptr` of `Load(_, ptr, off)` or `Store(ptr, off, val)`
//!   (we'll rewrite into Extract / fold into Pack).
//! - As the operand of `RcInc` / `RcDec` (drops after promotion).
//! - As a terminator edge arg (flow continues to dest block param).
//! - As `Return(v)` (function sig changes).
//!
//! Anything else — Call arg, `val` of a Store, BinOp operand,
//! ReuseOrClone src, MoveOut, LoadDyn/StoreDyn, etc. — is escape:
//! the alloc must stay on the heap.
//!
//! ## Algorithm
//!
//! 1. Per function, find each Alloc and compute its layout from
//!    the stores into it. Allocs with mismatched layouts are skipped.
//! 2. Build a "flow set" of Values that are alloc-derived: each
//!    alloc, each block param that receives such an alloc on every
//!    incoming edge with matching layout, etc. Iterate to fixpoint.
//! 3. Walk uses of flow-set values. If any is "escape," remove that
//!    Value's flow group entirely.
//! 4. If a flow group reaches the function's Return, mark the
//!    function for a return-type change to `Agg(n)`.
//! 5. Rewrite intra-function: Alloc + Stores → Pack; Load → Extract;
//!    rc traffic dropped; block param types changed.
//! 6. After all functions are analyzed, propagate sig changes to
//!    callers: call dest is now Agg-typed; its Loads become Extract;
//!    rc traffic on it drops.

use std::collections::{HashMap, HashSet};

use crate::ssa::Module;
use crate::ssa::instruction::{BlockId, Inst, ScalarType, Terminator, Value};

pub fn run(module: &mut Module) {
    // Phase A: per-function analysis. For each function, determine
    // which Values are promotable to Agg and what the Agg layout is.
    // Also record functions whose return type should change.
    let mut per_func: HashMap<String, FuncAnalysis> = HashMap::new();
    for (name, func) in &module.functions {
        let a = analyze(func);
        per_func.insert(name.clone(), a);
    }

    // Phase B: cross-function fixpoint. If a function F now returns
    // Agg, all callers must be re-analyzed (their call dest is now
    // an Agg-derived Value, which can flow further). Loop until no
    // function's analysis changes.
    //
    // For simplicity here, we do a single pass — handles the common
    // case (caller doesn't itself thread the result into another
    // Return). Iterate if needed.
    loop {
        let mut changed = false;
        for (name, func) in &module.functions {
            // Inject knowledge of other functions' new return types.
            let a = analyze_with_callee_sigs(func, &per_func);
            if a != per_func[name] {
                per_func.insert(name.clone(), a);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }

    // Phase B.5: verify each candidate sig change is safe — every
    // call site in the module must use the result in a way that
    // tolerates an Agg-typed return (Load + rc_dec patterns only,
    // no escape into Call args / Stores / etc). Param changes are
    // verified separately: each caller's arg-feeding Value must be
    // promoted in the caller's own analysis with matching shape.
    let return_candidates: HashMap<String, Vec<ScalarType>> = per_func
        .iter()
        .filter_map(|(n, a)| a.new_return.as_ref().map(|tys| (n.clone(), tys.clone())))
        .collect();
    let return_sigs: HashMap<String, Vec<ScalarType>> = return_candidates
        .into_iter()
        // __main is the program entry — its return type is the ABI to
        // the Rust-side eval driver, which expects an RcPtr Result.
        // Keep that signature stable even when the Result alloc is
        // otherwise promotable.
        .filter(|(name, _)| name != "__main")
        .filter(|(callee_name, tys)| call_sites_safe(module, &per_func, callee_name, tys.len()))
        .collect();
    let param_candidates: HashMap<String, HashMap<usize, Vec<ScalarType>>> = per_func
        .iter()
        .filter(|(_, a)| !a.new_params.is_empty())
        .map(|(n, a)| (n.clone(), a.new_params.clone()))
        .collect();
    let param_sigs: HashMap<String, HashMap<usize, Vec<ScalarType>>> = param_candidates
        .into_iter()
        .filter(|(name, _)| name != "__main")
        .filter(|(callee_name, new_params)| {
            arg_promotion_call_sites_safe(module, &per_func, callee_name, new_params)
        })
        .collect();

    // If we rejected a candidate, the function's own body still
    // expects to be rewritten assuming the promotion — that would
    // produce inconsistent SSA. Demote rejected functions: clear
    // their promotable so the body stays as-is.
    for (name, a) in per_func.iter_mut() {
        let return_rejected = a.new_return.is_some() && !return_sigs.contains_key(name);
        let params_rejected = !a.new_params.is_empty() && !param_sigs.contains_key(name);
        if return_rejected || params_rejected {
            a.promotable.clear();
            a.alloc_layouts.clear();
            a.new_return = None;
            a.new_params.clear();
        }
    }
    for (name, func) in module.functions.iter_mut() {
        let a = &per_func[name];
        rewrite(func, a, &return_sigs);
        // If this function's own return type changed, update the
        // Function::return_type to match.
        if let Some(tys) = &a.new_return {
            func.return_type = ScalarType::Agg(tys.len());
        }
        // Same for its own params.
        for (i, tys) in &a.new_params {
            if let Some(p) = func.params.get_mut(*i) {
                p.ty = ScalarType::Agg(tys.len());
            }
        }
    }
}

/// Per-Value analysis results.
#[derive(Debug, Clone, PartialEq, Eq)]
struct FuncAnalysis {
    /// Values that are promotable to Agg, with their field count.
    /// The field types live in `field_types` keyed the same.
    promotable: HashMap<Value, usize>,
    /// For each Alloc value, the layout (offset → stored Value) used
    /// to construct its Pack. Only valid for promotable Allocs.
    alloc_layouts: HashMap<Value, Vec<Value>>,
    /// If the function's Return value is promotable, the new return
    /// layout (per-field scalar types).
    new_return: Option<Vec<ScalarType>>,
    /// For each function parameter index that should be promoted from
    /// `RcPtr` to `Agg(n)`, the per-field scalar types (inferred from
    /// the Loads on that param inside this function). Empty when no
    /// params change.
    new_params: HashMap<usize, Vec<ScalarType>>,
}

fn analyze(func: &crate::ssa::Function) -> FuncAnalysis {
    analyze_with_callee_sigs(func, &HashMap::new())
}

/// Map from function name to its new (post-sroa) return layout.
type CalleeSigs = HashMap<String, FuncAnalysis>;

fn analyze_with_callee_sigs(func: &crate::ssa::Function, callees: &CalleeSigs) -> FuncAnalysis {
    // Step 1: classify each Alloc by layout.
    //
    // `alloc_layout`: for each Alloc Value, the ordered list of
    // values stored into it (slot 0, slot 8, …). If the layout is
    // sparse or non-stride-8, the alloc is not promotable.
    let mut alloc_layouts: HashMap<Value, Vec<Value>> = HashMap::new();
    let mut alloc_sizes: HashMap<Value, usize> = HashMap::new();
    for block in func.blocks.values() {
        let mut stores: HashMap<Value, HashMap<usize, Value>> = HashMap::new();
        for inst in &block.insts {
            match inst {
                Inst::Alloc(v, size) => {
                    alloc_sizes.insert(*v, *size);
                }
                Inst::Store(p, off, val) => {
                    if alloc_sizes.contains_key(p) {
                        stores.entry(*p).or_default().insert(*off, *val);
                    }
                }
                _ => {}
            }
        }
        for (alloc, smap) in stores {
            let size = alloc_sizes[&alloc];
            if size % 8 != 0 {
                continue;
            }
            let n_slots = size / 8;
            let mut fields: Vec<Value> = Vec::with_capacity(n_slots);
            let mut ok = true;
            for i in 0..n_slots {
                if let Some(v) = smap.get(&(i * 8)) {
                    fields.push(*v);
                } else {
                    ok = false;
                    break;
                }
            }
            if ok {
                alloc_layouts.insert(alloc, fields);
            }
        }
    }
    // Also: allocs that have NO stores aren't promotable.
    alloc_layouts.retain(|_, v| !v.is_empty());

    // Step 2: track values that are part of the flow. Start with the
    // Allocs themselves. Then propagate through block params: a block
    // param is in the flow if EVERY predecessor's edge arg at that
    // param position is also in the flow AND has a matching layout.
    //
    // Also: call results from sig-changed functions are in the flow.
    let mut flow: HashMap<Value, Vec<Value>> = alloc_layouts.clone(); // val → fields (canonical per alloc)
    // For block params that join multiple allocs, we need a layout
    // SHAPE (field count). Per-field source values differ per
    // predecessor; we only care that the SHAPE matches.
    let mut shape: HashMap<Value, usize> = HashMap::new();
    for (v, fields) in &alloc_layouts {
        shape.insert(*v, fields.len());
    }
    // Also seed shape from sig-changed callees.
    for (name, callee_a) in callees {
        if let Some(tys) = &callee_a.new_return {
            // Find Call instructions targeting this callee in this func.
            for block in func.blocks.values() {
                for inst in &block.insts {
                    if let Inst::Call(d, n, _) = inst {
                        if n == name {
                            shape.insert(*d, tys.len());
                            // For call results, we don't have
                            // alloc_layouts (they come from the
                            // callee's Pack at runtime). Use an
                            // empty placeholder.
                            flow.insert(*d, Vec::new());
                        }
                    }
                }
            }
        }
    }
    // Seed function params that are loaded at a dense {0, 8, …} run
    // of offsets — tentative candidates for promotion from RcPtr to
    // Agg(n). If the escape check later catches an unsafe use of the
    // param, the whole flow group collapses and the param stays as-is.
    let param_load_offsets = collect_param_load_offsets(func);
    for p in &func.params {
        if p.ty != ScalarType::RcPtr {
            continue;
        }
        let Some(offsets) = param_load_offsets.get(p) else {
            continue;
        };
        let Some(n) = dense_shape(offsets) else {
            continue;
        };
        shape.insert(*p, n);
        flow.insert(*p, Vec::new());
    }
    // Fixpoint on block param propagation.
    let predecessors = build_predecessors(func);
    loop {
        let mut grew = false;
        for (&bid, block) in &func.blocks {
            for (pi, param) in block.params.iter().enumerate() {
                if shape.contains_key(param) {
                    continue;
                }
                // Look at every predecessor's edge arg at position pi.
                // (We assume params are positional and match across
                // edges by index.)
                let Some(preds) = predecessors.get(&bid) else { continue; };
                if preds.is_empty() {
                    continue;
                }
                let mut common_shape: Option<usize> = None;
                let mut all_match = true;
                for pred_bid in preds {
                    let pred_block = &func.blocks[pred_bid];
                    let edges_to_us = edges_to(pred_block, bid);
                    for edge_args in &edges_to_us {
                        if pi >= edge_args.len() {
                            all_match = false;
                            break;
                        }
                        let arg = edge_args[pi];
                        let Some(arg_shape) = shape.get(&arg) else {
                            all_match = false;
                            break;
                        };
                        match common_shape {
                            None => common_shape = Some(*arg_shape),
                            Some(s) if s == *arg_shape => {}
                            _ => {
                                all_match = false;
                                break;
                            }
                        }
                    }
                    if !all_match {
                        break;
                    }
                }
                if all_match {
                    if let Some(s) = common_shape {
                        shape.insert(*param, s);
                        flow.insert(*param, Vec::new());
                        grew = true;
                    }
                }
            }
        }
        if !grew {
            break;
        }
    }

    // Step 3: check uses. Any flow Value used unsafely → mark the
    // whole "flow group" as escaped. A flow group is the transitive
    // closure linked by shared block params.
    //
    // For simplicity: if ANY flow Value escapes, demote ALL flow
    // Values to non-promotable. This is conservative but correct.
    // (A precise impl would do connected components.)
    let mut escaped = false;
    let in_flow = |v: &Value| shape.contains_key(v);
    for block in func.blocks.values() {
        for inst in &block.insts {
            match inst {
                Inst::Alloc(..) | Inst::AllocDyn(..) => {}
                Inst::Store(_, _, val) => {
                    // Storing a flow Value as the *val* into another
                    // object means it escapes onto the heap.
                    if in_flow(val) {
                        escaped = true;
                    }
                }
                Inst::StoreDyn(p, idx, val) => {
                    if in_flow(p) || in_flow(idx) || in_flow(val) {
                        escaped = true;
                    }
                }
                Inst::Load(_, _, _) => {
                    // Loads on a flow Value are fine — will become
                    // Extract. (And we already know the load's source
                    // type is an alloc.)
                }
                Inst::LoadDyn(_, p, idx) => {
                    if in_flow(p) || in_flow(idx) {
                        escaped = true;
                    }
                }
                Inst::RcInc(_) | Inst::RcDec(_) => {
                    // OK on flow Values.
                }
                Inst::Call(_, callee_name, args) => {
                    // A flow Value passed as Call arg escapes —
                    // unless the callee has that arg position
                    // promoted to a matching Agg shape (cross-fn
                    // arg SROA), in which case the call site will
                    // pass the Pack value instead of an alloc.
                    for (i, arg) in args.iter().enumerate() {
                        if !in_flow(arg) {
                            continue;
                        }
                        let accepted = callees
                            .get(callee_name)
                            .and_then(|a| a.new_params.get(&i))
                            .map(|tys| tys.len())
                            == shape.get(arg).copied();
                        if !accepted {
                            escaped = true;
                            break;
                        }
                    }
                }
                Inst::CowStore(_, ptr, _, val) => {
                    if in_flow(ptr) || in_flow(val) {
                        escaped = true;
                    }
                }
                Inst::CowStoreDyn(_, ptr, idx, val) => {
                    if in_flow(ptr) || in_flow(idx) || in_flow(val) {
                        escaped = true;
                    }
                }
                Inst::CowMoveOut(_, ptr, _) => {
                    if in_flow(ptr) {
                        escaped = true;
                    }
                }
                Inst::CowResizeDyn(_, ptr, size) => {
                    if in_flow(ptr) || in_flow(size) {
                        escaped = true;
                    }
                }
                Inst::BinOp(_, _, l, r) => {
                    if in_flow(l) || in_flow(r) {
                        escaped = true;
                    }
                }
                Inst::Cast(_, src) | Inst::BitCast(_, src) => {
                    if in_flow(src) {
                        escaped = true;
                    }
                }
                Inst::Pack(_, fields) => {
                    if fields.iter().any(in_flow) {
                        escaped = true;
                    }
                }
                Inst::Extract(_, agg, _) => {
                    if in_flow(agg) {
                        // Extract on an alloc-derived flow Value is
                        // weird — it'd already be an Agg. Treat as
                        // escape to be safe.
                        escaped = true;
                    }
                }
                Inst::Const(..) | Inst::StaticRef(..) => {}
            }
        }
        if escaped { break; }
        // Terminator: Returns are fine (we'll promote return type).
        // For Jump/Branch/SwitchInt edge args, the destination block
        // param at the matching position must also be in flow — if a
        // promoted Value lands on an RcPtr-typed param, there's a
        // type mismatch and we have to back out.
        for edge in block.terminator.successors() {
            let dest = &func.blocks[&edge.target];
            for (pi, arg) in edge.args.iter().enumerate() {
                if in_flow(arg) {
                    let Some(dest_param) = dest.params.get(pi) else {
                        escaped = true;
                        continue;
                    };
                    if !in_flow(dest_param) {
                        escaped = true;
                    }
                }
            }
        }
    }

    if escaped {
        return FuncAnalysis {
            promotable: HashMap::new(),
            alloc_layouts: HashMap::new(),
            new_return: None,
            new_params: HashMap::new(),
        };
    }

    // Determine the new return type: if any Return value is in flow,
    // the function returns Agg. (All return values must agree on
    // shape — already enforced by shape propagation.)
    let mut new_return: Option<Vec<ScalarType>> = None;
    for block in func.blocks.values() {
        if let Terminator::Return(v) = &block.terminator {
            if let Some(&n) = shape.get(v) {
                // Derive field scalar types from the canonical layout.
                // We don't always have alloc_layouts for block params
                // / call results, so fall back to the alloc's stores
                // by walking back. For simplicity: if v is an Alloc,
                // use alloc_layouts; else, we infer from any reachable
                // alloc's stored value types.
                let tys = field_types_for(*v, &alloc_layouts, &flow, n);
                new_return = Some(tys);
            }
        }
    }

    // For each function param that survived the escape check, infer
    // its new Agg layout from the types of the Loads on it.
    let mut new_params: HashMap<usize, Vec<ScalarType>> = HashMap::new();
    for (i, p) in func.params.iter().enumerate() {
        let Some(&n) = shape.get(p) else { continue; };
        // Only count params seeded from offsets (not ones that happen
        // to share a shape map with an alloc — which can't happen for
        // function params, but stay defensive).
        if p.ty != ScalarType::RcPtr {
            continue;
        }
        let tys = field_types_from_loads(func, *p, n);
        new_params.insert(i, tys);
    }

    FuncAnalysis {
        promotable: shape,
        alloc_layouts,
        new_return,
        new_params,
    }
}

/// Verify every call site to `callee_name` uses the call result in
/// ways compatible with the result being `Agg(expected_shape)`-typed.
/// Direct safe uses: `Load` (becomes `Extract`), `RcInc`/`RcDec`
/// (dropped). Cross-block: the call result threading into a block
/// param is fine as long as the destination param is already in the
/// caller's promotable set with matching shape (cross-fn return SROA
/// then chains into the caller's intra-fn block-param SROA). Likewise
/// for Return when the caller itself has a matching `new_return`.
fn call_sites_safe(
    module: &Module,
    per_func: &HashMap<String, FuncAnalysis>,
    callee_name: &str,
    expected_shape: usize,
) -> bool {
    for (caller_name, caller_func) in &module.functions {
        let caller_a = &per_func[caller_name];
        // Collect call-result Values for this callee.
        let mut call_results: HashSet<Value> = HashSet::new();
        for block in caller_func.blocks.values() {
            for inst in &block.insts {
                if let Inst::Call(d, n, _) = inst {
                    if n == callee_name {
                        call_results.insert(*d);
                    }
                }
            }
        }
        if call_results.is_empty() {
            continue;
        }
        for block in caller_func.blocks.values() {
            for inst in &block.insts {
                match inst {
                    Inst::Load(_, p, _) if call_results.contains(p) => {} // ok
                    Inst::RcInc(v) | Inst::RcDec(v) if call_results.contains(v) => {} // ok
                    Inst::Call(_, _, args) => {
                        if args.iter().any(|a| call_results.contains(a)) {
                            return false;
                        }
                    }
                    Inst::Store(_, _, val) | Inst::StoreDyn(_, _, val) => {
                        if call_results.contains(val) {
                            return false;
                        }
                    }
                    Inst::CowStore(_, ptr, _, val) | Inst::CowStoreDyn(_, ptr, _, val) => {
                        if call_results.contains(ptr) || call_results.contains(val) {
                            return false;
                        }
                    }
                    Inst::CowMoveOut(_, ptr, _) => {
                        if call_results.contains(ptr) {
                            return false;
                        }
                    }
                    Inst::CowResizeDyn(_, ptr, size) => {
                        if call_results.contains(ptr) || call_results.contains(size) {
                            return false;
                        }
                    }
                    Inst::BinOp(_, _, l, r) => {
                        if call_results.contains(l) || call_results.contains(r) {
                            return false;
                        }
                    }
                    Inst::Cast(_, src) | Inst::BitCast(_, src) => {
                        if call_results.contains(src) {
                            return false;
                        }
                    }
                    Inst::LoadDyn(_, p, _) => {
                        if call_results.contains(p) {
                            return false;
                        }
                    }
                    Inst::Pack(_, fields) => {
                        if fields.iter().any(|f| call_results.contains(f)) {
                            return false;
                        }
                    }
                    Inst::Extract(_, agg, _) => {
                        if call_results.contains(agg) {
                            return false;
                        }
                    }
                    _ => {}
                }
            }
            // Edge args: OK if the destination block param is itself
            // promoted to a matching shape in the caller's analysis —
            // the rewrite will retype the param and the threading
            // chain together. Otherwise (param not promoted) the
            // rewrite would feed an Agg into an RcPtr param.
            for edge in block.terminator.successors() {
                let dest_block = &caller_func.blocks[&edge.target];
                for (pi, arg) in edge.args.iter().enumerate() {
                    if !call_results.contains(arg) {
                        continue;
                    }
                    let Some(dest_param) = dest_block.params.get(pi) else {
                        return false;
                    };
                    let Some(&n) = caller_a.promotable.get(dest_param) else {
                        return false;
                    };
                    if n != expected_shape {
                        return false;
                    }
                }
            }
            // Return: OK only if caller's own return is also being
            // promoted to a matching shape.
            if let Terminator::Return(v) = &block.terminator {
                if call_results.contains(v) {
                    let Some(tys) = &caller_a.new_return else {
                        return false;
                    };
                    if tys.len() != expected_shape {
                        return false;
                    }
                }
            }
        }
    }
    true
}

/// Verify that every call site to `callee_name` can supply an Agg
/// value at each newly-promoted arg position: the arg-feeding Value
/// must be in the caller's own promotable set with the expected
/// shape. If any call site can't, we'd be passing an RcPtr alloc
/// where the callee now expects an Agg — so reject the promotion.
fn arg_promotion_call_sites_safe(
    module: &Module,
    per_func: &HashMap<String, FuncAnalysis>,
    callee_name: &str,
    new_params: &HashMap<usize, Vec<ScalarType>>,
) -> bool {
    for (caller_name, caller_func) in &module.functions {
        let caller_a = &per_func[caller_name];
        for block in caller_func.blocks.values() {
            for inst in &block.insts {
                let Inst::Call(_, n, args) = inst else { continue; };
                if n != callee_name {
                    continue;
                }
                for (i, expected_tys) in new_params {
                    let Some(arg) = args.get(*i) else { return false; };
                    let Some(&shape_n) = caller_a.promotable.get(arg) else {
                        return false;
                    };
                    if shape_n != expected_tys.len() {
                        return false;
                    }
                }
            }
        }
    }
    true
}

/// For each rcptr-typed function param, collect the byte offsets at
/// which it's `Load`ed inside the function body. Other uses (rc
/// traffic, edge args, etc.) are ignored here — they're checked by
/// the escape pass later.
fn collect_param_load_offsets(func: &crate::ssa::Function) -> HashMap<Value, Vec<usize>> {
    let params: HashSet<Value> = func.params.iter().copied().collect();
    let mut offsets: HashMap<Value, Vec<usize>> = HashMap::new();
    for block in func.blocks.values() {
        for inst in &block.insts {
            if let Inst::Load(_, p, off) = inst {
                if params.contains(p) {
                    offsets.entry(*p).or_default().push(*off);
                }
            }
        }
    }
    offsets
}

/// Given a multiset of byte offsets, return `Some(n)` if they form a
/// dense run `{0, 8, …, (n-1)*8}` (each offset appearing at least
/// once), else `None`. Sparse / non-stride-8 layouts can't be packed
/// into an Agg.
fn dense_shape(offsets: &[usize]) -> Option<usize> {
    if offsets.is_empty() {
        return None;
    }
    let max = *offsets.iter().max().unwrap();
    if max % 8 != 0 {
        return None;
    }
    let n = max / 8 + 1;
    let seen: HashSet<usize> = offsets.iter().copied().collect();
    for i in 0..n {
        if !seen.contains(&(i * 8)) {
            return None;
        }
    }
    Some(n)
}

/// Field types for a promoted function param: for each slot index,
/// the scalar type of any `Load` on that param at offset `slot*8`.
/// All loads at the same offset agree on type by SSA construction.
fn field_types_from_loads(func: &crate::ssa::Function, p: Value, n: usize) -> Vec<ScalarType> {
    let mut tys: Vec<Option<ScalarType>> = vec![None; n];
    for block in func.blocks.values() {
        for inst in &block.insts {
            if let Inst::Load(d, ptr, off) = inst {
                if *ptr == p {
                    let slot = off / 8;
                    if slot < n {
                        tys[slot] = Some(d.ty);
                    }
                }
            }
        }
    }
    tys.into_iter()
        .map(|t| t.unwrap_or(ScalarType::I64))
        .collect()
}

fn field_types_for(
    v: Value,
    layouts: &HashMap<Value, Vec<Value>>,
    _flow: &HashMap<Value, Vec<Value>>,
    n: usize,
) -> Vec<ScalarType> {
    // If we have the direct alloc layout, use it.
    if let Some(fields) = layouts.get(&v) {
        return fields.iter().map(|f| f.ty).collect();
    }
    // Otherwise (block param / call result), pick any alloc with
    // matching field count and use its types. Conservative — assumes
    // all flow paths have compatible field types (which is required
    // for SROA to be sound anyway).
    for fields in layouts.values() {
        if fields.len() == n {
            return fields.iter().map(|f| f.ty).collect();
        }
    }
    // No alloc layout available (pure call-result flow). Default to
    // i64 per field; the caller-side rewrites will redo this from
    // the callee's actual sig.
    vec![ScalarType::I64; n]
}

fn build_predecessors(func: &crate::ssa::Function) -> HashMap<BlockId, Vec<BlockId>> {
    let mut preds: HashMap<BlockId, Vec<BlockId>> = HashMap::new();
    for (&bid, block) in &func.blocks {
        for edge in block.terminator.successors() {
            preds.entry(edge.target).or_default().push(bid);
        }
    }
    preds
}

fn edges_to(block: &crate::ssa::Block, target: BlockId) -> Vec<Vec<Value>> {
    block
        .terminator
        .successors()
        .into_iter()
        .filter(|e| e.target == target)
        .map(|e| e.args.clone())
        .collect()
}

fn rewrite(
    func: &mut crate::ssa::Function,
    a: &FuncAnalysis,
    sig_changes: &HashMap<String, Vec<ScalarType>>,
) {
    // Short-circuit if there's nothing to do: no own promotable
    // values and no calls to sig-changed callees.
    let calls_sig_changed_callee = func.blocks.values().any(|b| {
        b.insts.iter().any(|i| matches!(i, Inst::Call(_, n, _) if sig_changes.contains_key(n)))
    });
    if a.promotable.is_empty() && !calls_sig_changed_callee {
        return;
    }

    // Rewrite block params' types.
    for block in func.blocks.values_mut() {
        for p in block.params.iter_mut() {
            if let Some(&n) = a.promotable.get(p) {
                p.ty = ScalarType::Agg(n);
            }
        }
    }

    // Build the "new type" map: every promoted Value gets type
    // `Agg(n)`. Every Value at a call site to a sig-changed callee
    // also gets retyped. Track call-result Values explicitly so the
    // per-inst rewrite can convert their Loads/rc traffic even when
    // the caller's overall analysis escaped (sig changes are
    // committed module-wide; call sites must follow regardless).
    let mut new_ty: HashMap<usize, ScalarType> = a
        .promotable
        .iter()
        .map(|(v, &n)| (v.id, ScalarType::Agg(n)))
        .collect();
    let mut call_result_agg: HashMap<Value, usize> = HashMap::new();
    for block in func.blocks.values() {
        for inst in &block.insts {
            if let Inst::Call(d, callee, _) = inst {
                if let Some(tys) = sig_changes.get(callee) {
                    new_ty.insert(d.id, ScalarType::Agg(tys.len()));
                    call_result_agg.insert(*d, tys.len());
                }
            }
        }
    }

    // Retype every operand Value in every instruction and terminator
    // whose id appears in new_ty.
    let retype = |v: &mut Value| {
        if let Some(&ty) = new_ty.get(&v.id) {
            v.ty = ty;
        }
    };
    for block in func.blocks.values_mut() {
        for p in block.params.iter_mut() {
            retype(p);
        }
        for inst in block.insts.iter_mut() {
            if let Some(d) = inst.dest_mut() {
                retype(d);
            }
            inst.map_operands_mut(&retype);
        }
        block.terminator.map_operands_mut(&retype);
    }

    // Rewrite instructions.
    for block in func.blocks.values_mut() {
        let mut new_insts: Vec<Inst> = Vec::with_capacity(block.insts.len());
        // Track last store position for each promotable alloc — Pack
        // emits at the last-store position.
        let mut last_store_idx: HashMap<Value, usize> = HashMap::new();
        for (i, inst) in block.insts.iter().enumerate() {
            if let Inst::Store(p, _, _) = inst {
                if a.alloc_layouts.contains_key(p) {
                    last_store_idx.insert(*p, i);
                }
            }
        }
        for (i, inst) in block.insts.iter().enumerate() {
            match inst {
                Inst::Alloc(v, _) if a.alloc_layouts.contains_key(v) => {
                    // Drop the alloc — Pack will come at last_store_idx.
                }
                Inst::Store(p, _, _) if a.alloc_layouts.contains_key(p) => {
                    if last_store_idx.get(p) == Some(&i) {
                        let fields = &a.alloc_layouts[p];
                        let mut packed = *p;
                        packed.ty = ScalarType::Agg(fields.len());
                        new_insts.push(Inst::Pack(packed, fields.clone()));
                    }
                    // Earlier stores into the alloc: drop.
                }
                Inst::Load(d, p, off) if a.promotable.contains_key(p) || call_result_agg.contains_key(p) => {
                    let idx = off / 8;
                    let n = a.promotable.get(p).copied()
                        .or_else(|| call_result_agg.get(p).copied())
                        .unwrap();
                    let mut agg = *p;
                    agg.ty = ScalarType::Agg(n);
                    new_insts.push(Inst::Extract(*d, agg, idx));
                }
                Inst::RcInc(v) | Inst::RcDec(v) if a.promotable.contains_key(v) || call_result_agg.contains_key(v) => {
                    // Drop rc traffic on promoted aggs and call
                    // results whose callee was sig-changed.
                }
                Inst::Call(d, callee, args) => {
                    // If the callee's return type changed, the call
                    // result is now Agg-typed.
                    let mut new_inst = inst.clone();
                    if let Some(tys) = sig_changes.get(callee) {
                        if let Inst::Call(d_mut, _, _) = &mut new_inst {
                            d_mut.ty = ScalarType::Agg(tys.len());
                        }
                    }
                    let _ = (d, args);
                    new_insts.push(new_inst);
                }
                other => new_insts.push(other.clone()),
            }
        }
        block.insts = new_insts;
    }
}
