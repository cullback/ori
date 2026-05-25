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

    // Phase B.5: verify each candidate sig change is safe and demote
    // rejections. Verification is iterative — rejecting one callee's
    // sig invalidates callers' analyses (their flow set assumed the
    // callee accepted Agg args). We maintain monotonic `denied` sets:
    // once a function's return/param promotion is rejected, force it
    // empty for the rest of the run so the fixpoint can't restore it.
    // Each round only adds to denied, bounded by function count.
    let mut denied_r: HashSet<String> = HashSet::new();
    let mut denied_p: HashSet<String> = HashSet::new();
    // `_param_sigs` is computed for the verification loop's
    // termination check (no new denials) but the actual rewrite uses
    // `promotable` and the per-function `new_params` recorded in
    // `per_func` after the fixpoint converges.
    let (return_sigs, _param_sigs) = loop {
        // Re-run the Phase B fixpoint with denied sigs zeroed out.
        loop {
            let mut changed = false;
            for (name, func) in &module.functions {
                let mut a = analyze_with_callee_sigs(func, &per_func);
                if denied_r.contains(name) {
                    a.new_return = None;
                }
                if denied_p.contains(name) {
                    a.new_params.clear();
                }
                if a != per_func[name] {
                    per_func.insert(name.clone(), a);
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }

        let return_sigs: HashMap<String, Vec<ScalarType>> = per_func
            .iter()
            .filter_map(|(n, a)| a.new_return.as_ref().map(|tys| (n.clone(), tys.clone())))
            // __main is the program entry — its return type is the ABI
            // to the Rust-side eval driver, which expects an RcPtr
            // Result. Keep that signature stable even when the Result
            // alloc is otherwise promotable.
            .filter(|(name, _)| name != "__main")
            .filter(|(name, tys)| call_sites_safe(module, &per_func, name, tys.len()))
            .collect();
        let param_sigs: HashMap<String, HashMap<usize, Vec<ScalarType>>> = per_func
            .iter()
            .filter(|(_, a)| !a.new_params.is_empty())
            .map(|(n, a)| (n.clone(), a.new_params.clone()))
            .filter(|(name, _)| name != "__main")
            .filter(|(name, params)| {
                arg_promotion_call_sites_safe(module, &per_func, name, params)
            })
            .collect();

        // Any candidate we just rejected gets added to denied; force
        // the next round of fixpoint to keep it empty.
        let mut grew = false;
        let mut new_denied_r: Vec<String> = Vec::new();
        let mut new_denied_p: Vec<String> = Vec::new();
        for (name, a) in per_func.iter() {
            if a.new_return.is_some()
                && !return_sigs.contains_key(name)
                && !denied_r.contains(name)
            {
                new_denied_r.push(name.clone());
                grew = true;
            }
            if !a.new_params.is_empty()
                && !param_sigs.contains_key(name)
                && !denied_p.contains(name)
            {
                new_denied_p.push(name.clone());
                grew = true;
            }
        }
        denied_r.extend(new_denied_r);
        denied_p.extend(new_denied_p);
        if !grew {
            // Final pass: a rejected function's body still has stale
            // promotable / alloc_layouts entries from its own analysis
            // — clear them so the body isn't rewritten.
            for (name, a) in per_func.iter_mut() {
                if denied_r.contains(name) || denied_p.contains(name) {
                    a.promotable.clear();
                    a.alloc_layouts.clear();
                    a.new_return = None;
                    a.new_params.clear();
                }
            }
            break (return_sigs, param_sigs);
        }
    };
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
    // For allocs whose fields include any RcPtr, we need to emit
    // per-field `rc_dec` at the position where the original alloc's
    // rc_dec would have cascade-freed its children. When the alloc's
    // Pack value flows only within its defining block, that rc_dec
    // is on the alloc Value itself and the rewrite can look up the
    // field Values from `alloc_layouts`. But when the Pack value
    // crosses a block boundary (becoming a new block-param Value),
    // the rc_dec lands on the block param — for which we have only a
    // shape and not the original field Values. Synthesizing Extracts
    // there to dec each field would work but needs fresh-Value
    // plumbing we don't have today. Conservative: skip the promotion
    // in that case.
    let alloc_crosses_block: HashSet<Value> = {
        let mut crossing: HashSet<Value> = HashSet::new();
        for block in func.blocks.values() {
            for op in block.terminator.operands() {
                if alloc_layouts.contains_key(&op) {
                    crossing.insert(op);
                }
            }
        }
        crossing
    };
    alloc_layouts.retain(|alloc, fields| {
        let has_rcptr = fields.iter().any(|f| f.ty == ScalarType::RcPtr);
        !has_rcptr || !alloc_crosses_block.contains(alloc)
    });

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

    // Step 3: connected-component escape analysis.
    //
    // Group flow values into components that must succeed-or-fail
    // together: when a block param P is in flow, it's the *same*
    // component as every pred-edge-arg flowing into P, because at
    // rewrite time they all need to agree on the new Agg type. Then
    // any unsafe use of a value escapes its whole component, but
    // leaves other components untouched. This lets us promote `v_a`
    // even when an unrelated `v_b` in the same function is stranded
    // — without it, the analysis was whole-function: one bad alloc
    // (e.g. a buffer threaded through the outer walk loop) would
    // poison every other promotable alloc in that function.
    let mut uf = UnionFind::new();
    for v in shape.keys() {
        uf.add(*v);
    }
    for (&bid, block) in &func.blocks {
        for (pi, param) in block.params.iter().enumerate() {
            if !shape.contains_key(param) {
                continue;
            }
            let Some(preds) = predecessors.get(&bid) else { continue };
            for pred_bid in preds {
                let pred_block = &func.blocks[pred_bid];
                for edge_args in edges_to(pred_block, bid) {
                    let Some(arg) = edge_args.get(pi) else { continue };
                    if shape.contains_key(arg) {
                        uf.union(*param, *arg);
                    }
                }
            }
        }
    }

    let in_flow = |v: &Value| shape.contains_key(v);
    let mut escaped: HashSet<Value> = HashSet::new();
    let escape = |v: &Value, uf: &mut UnionFind, set: &mut HashSet<Value>| {
        if in_flow(v) {
            set.insert(uf.find(*v));
        }
    };
    for block in func.blocks.values() {
        for inst in &block.insts {
            match inst {
                Inst::Alloc(..) | Inst::AllocDyn(..) => {}
                Inst::Store(_, _, val) => {
                    // Storing a flow Value as the *val* into another
                    // object means it escapes onto the heap.
                    escape(val, &mut uf, &mut escaped);
                }
                Inst::StoreDyn(p, idx, val) => {
                    escape(p, &mut uf, &mut escaped);
                    escape(idx, &mut uf, &mut escaped);
                    escape(val, &mut uf, &mut escaped);
                }
                Inst::Load(_, _, _) => {
                    // Loads on a flow Value are fine — will become
                    // Extract.
                }
                Inst::LoadDyn(_, p, idx) => {
                    escape(p, &mut uf, &mut escaped);
                    escape(idx, &mut uf, &mut escaped);
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
                            escape(arg, &mut uf, &mut escaped);
                        }
                    }
                }
                Inst::CowStore(_, ptr, _, val) => {
                    escape(ptr, &mut uf, &mut escaped);
                    escape(val, &mut uf, &mut escaped);
                }
                Inst::CowStoreDyn(_, ptr, idx, val) => {
                    escape(ptr, &mut uf, &mut escaped);
                    escape(idx, &mut uf, &mut escaped);
                    escape(val, &mut uf, &mut escaped);
                }
                Inst::CowMoveOut(_, ptr, _) => {
                    escape(ptr, &mut uf, &mut escaped);
                }
                Inst::CowResizeDyn(_, ptr, size) => {
                    escape(ptr, &mut uf, &mut escaped);
                    escape(size, &mut uf, &mut escaped);
                }
                Inst::BinOp(_, _, l, r) => {
                    escape(l, &mut uf, &mut escaped);
                    escape(r, &mut uf, &mut escaped);
                }
                Inst::Cast(_, src) | Inst::BitCast(_, src) => {
                    escape(src, &mut uf, &mut escaped);
                }
                Inst::Pack(_, fields) => {
                    for f in fields {
                        escape(f, &mut uf, &mut escaped);
                    }
                }
                Inst::Extract(_, agg, _) => {
                    // Extract on an alloc-derived flow Value is
                    // weird — it'd already be an Agg. Treat as
                    // escape to be safe.
                    escape(agg, &mut uf, &mut escaped);
                }
                Inst::Const(..) | Inst::StaticRef(..) => {}
            }
        }
        // Terminator edge args: if the arg is in flow but the dest
        // block param isn't, there's no way to align types — at
        // rewrite the arg becomes Agg while the param stays RcPtr.
        // Escape the arg's component. (Returns are handled below
        // when we build new_return.)
        for edge in block.terminator.successors() {
            let dest = &func.blocks[&edge.target];
            for (pi, arg) in edge.args.iter().enumerate() {
                if !in_flow(arg) {
                    continue;
                }
                let dest_param_in_flow = dest
                    .params
                    .get(pi)
                    .map(|p| in_flow(p))
                    .unwrap_or(false);
                if !dest_param_in_flow {
                    escape(arg, &mut uf, &mut escaped);
                }
            }
        }
        // __main is the program entry — its return type is part of
        // the ABI to the Rust eval driver, which expects RcPtr. We
        // can't change that signature, so escape any Return value's
        // component to prevent the body from rewriting the Return to
        // produce an Agg (which would mismatch the unchanged sig).
        if func.name == "__main" {
            if let Terminator::Return(v) = &block.terminator {
                escape(v, &mut uf, &mut escaped);
            }
        }
    }

    // Drop every value whose component escaped.
    let in_escaped_component =
        |v: &Value, uf: &mut UnionFind| escaped.contains(&uf.find(*v));
    shape.retain(|v, _| !in_escaped_component(v, &mut uf));
    alloc_layouts.retain(|v, _| !in_escaped_component(v, &mut uf));

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

/// Plain disjoint-set with path compression. Used to group flow
/// values that share an SROA promotion fate: when a block param ends
/// up in flow, it's the same component as every pred-edge-arg that
/// brought a flow value to it. An unsafe use then escapes the whole
/// component, but other components survive.
struct UnionFind {
    parent: HashMap<Value, Value>,
}

impl UnionFind {
    fn new() -> Self {
        Self { parent: HashMap::new() }
    }
    fn add(&mut self, v: Value) {
        self.parent.entry(v).or_insert(v);
    }
    fn find(&mut self, v: Value) -> Value {
        let p = self.parent[&v];
        if p == v {
            return v;
        }
        let root = self.find(p);
        self.parent.insert(v, root);
        root
    }
    fn union(&mut self, a: Value, b: Value) {
        let ra = self.find(a);
        let rb = self.find(b);
        if ra != rb {
            self.parent.insert(ra, rb);
        }
    }
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
        // RC traffic for promoted Aggs with RcPtr fields.
        //
        // The lower stage emits `Store(alloc, off, ptr_val)` with an
        // implicit `rc_inc(ptr_val)` (target gains a claim); the
        // alloc's eventual `rc_dec` cascades to dec the held ptrs.
        // After SROA folds alloc+Stores into Pack, none of that
        // happens automatically. We re-emit it explicitly:
        //
        //   Pack with RcPtr field      → emit `rc_inc(field)`
        //   Extract producing RcPtr    → emit `rc_inc(dest)`
        //   rc_dec on promoted value   → emit `rc_dec(field)` per
        //                                RcPtr field of the layout
        //   rc_inc on promoted value   → emit `rc_inc(field)` per
        //                                RcPtr field of the layout
        //
        // The Pack rc_inc balances the local's rc_dec on the stored
        // value; the Extract rc_inc balances the consumer's rc_dec
        // on the loaded value; the per-field decs at the promoted
        // value's death replace the cascade-free.
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
                        // Pack-owns claim on each RcPtr field —
                        // emit the rc_inc the original Store did.
                        for field in fields {
                            if field.ty == ScalarType::RcPtr {
                                new_insts.push(Inst::RcInc(*field));
                            }
                        }
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
                    // Mirror Load's auto-rc-inc on RcPtr extractions.
                    if d.ty == ScalarType::RcPtr {
                        new_insts.push(Inst::RcInc(*d));
                    }
                }
                Inst::RcInc(v) if a.promotable.contains_key(v) || call_result_agg.contains_key(v) => {
                    // The promoted Agg held N field claims via its
                    // Pack/Extract rc_incs. An rc_inc on the Agg
                    // means "I'm sharing this Agg" — equivalent to
                    // rc_inc'ing each RcPtr field. (Non-RcPtr fields
                    // don't carry rc, so nothing to do for them.)
                    if let Some(fields) = a.alloc_layouts.get(v) {
                        for field in fields {
                            if field.ty == ScalarType::RcPtr {
                                new_insts.push(Inst::RcInc(*field));
                            }
                        }
                    }
                    // For call_result_agg without local layout info,
                    // we'd need to Extract each field first. Skip
                    // for now — callees returning Aggs with RcPtr
                    // fields are excluded by the param/return
                    // promotion verifier in practice.
                }
                Inst::RcDec(v) if a.promotable.contains_key(v) || call_result_agg.contains_key(v) => {
                    // Symmetric to RcInc above: cascade-dec the
                    // RcPtr fields.
                    if let Some(fields) = a.alloc_layouts.get(v) {
                        for field in fields {
                            if field.ty == ScalarType::RcPtr {
                                new_insts.push(Inst::RcDec(*field));
                            }
                        }
                    }
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

