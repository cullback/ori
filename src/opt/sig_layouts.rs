//! Whole-program layout inference.
//!
//! Computes per-Value slot-type layouts that span function boundaries.
//! Where the local `compute_slot_types` only sees `Alloc`+`Store` and
//! propagation across block-param edges, this pass *also* propagates
//! layouts through:
//! - Function entry parameters (callers' arg layouts join → param layout)
//! - `Call` results (callee's return layout flows to the result)
//!
//! Without these, `emit_drops` falls back to runtime cascade via the
//! heap's stored `ptr_offsets`, which prevents:
//! - Cross-block move-out (parent's Drop has to mask moved-out slots,
//!   and that mask only works when slot_types are known statically)
//! - Cross-function Reuse pairing
//! - Static rc inc/dec elimination at call boundaries
//!
//! ## Representation
//!
//! `Layout` is `Vec<ScalarType>` — flat list of slot types. A `Ptr`
//! slot means "pointer to *some* heap object" but does not carry the
//! pointee's layout (no nested layout yet). For dropping the *parent*
//! that's sufficient: we only need to know which slots are Ptr so the
//! cascade decisions are correct.
//!
//! ## Fixpoint
//!
//! The per-value map and per-function signatures are recomputed in a
//! round-robin until nothing changes. Each round:
//! 1. For each function, run intra-procedural slot_type inference
//!    seeded with the current cross-function knowledge.
//! 2. Derive each function's `return_layout` from the Return value.
//! 3. Derive each function's `param_layouts` by joining caller arg
//!    layouts across all call sites (agree → set; disagree → None).
//!
//! Layouts can only become *more specific* over iterations (None ->
//! Some, never the other way). Termination follows from the lattice
//! height = number of (Function, ParamIndex) plus number of Functions.

use std::collections::HashMap;

use crate::ssa::Module;
use crate::ssa::instruction::{Inst, ScalarType, Terminator, Value};

/// Per-slot type vector. `slot_types[i]` is the type of the i-th
/// 8-byte slot in the heap object.
pub type Layout = Vec<ScalarType>;

/// Cross-function layout signatures: what each function's parameters
/// and return value look like.
#[derive(Default, Debug, Clone)]
pub struct FuncSignature {
    pub params: Vec<Option<Layout>>,
    pub ret: Option<Layout>,
}

/// Per-module collection of function signatures plus per-function
/// per-value layout maps. The per-value maps cover everything the
/// `emit_drops` Phase B needs.
#[derive(Default, Debug, Clone)]
pub struct ModuleLayouts {
    /// Per-function signature.
    pub signatures: HashMap<String, FuncSignature>,
    /// Per-function: layout per Ptr-typed Value (params + insts +
    /// block params).
    pub values: HashMap<String, HashMap<Value, Layout>>,
}

/// Analyze layouts for every function in `module`. Returns a
/// `ModuleLayouts` ready to be consumed by `emit_drops`.
pub fn analyze(module: &Module) -> ModuleLayouts {
    let mut layouts = ModuleLayouts::default();

    // Seed: empty signatures (one entry per function) so the lookup
    // in `infer_function` never panics.
    for (name, func) in &module.functions {
        layouts.signatures.insert(
            name.clone(),
            FuncSignature { params: vec![None; func.params.len()], ret: None },
        );
    }

    // Fixpoint: iterate until nothing changes.
    for _ in 0..32 {
        let mut changed = false;

        // Phase 1: per-function value layouts.
        let mut new_values: HashMap<String, HashMap<Value, Layout>> = HashMap::new();
        for (name, func) in &module.functions {
            let signatures = &layouts.signatures;
            let map = infer_function(func, signatures);
            new_values.insert(name.clone(), map);
        }
        if new_values != layouts.values {
            layouts.values = new_values;
            changed = true;
        }

        // Phase 2: return layouts. Join across *every* Return in the
        // function: all returned values must share the same slot
        // layout, otherwise the callee's return shape isn't statically
        // determined and `ret` stays `None`. Result-like sum types
        // with heterogeneous variants land here.
        for (name, func) in &module.functions {
            let values = &layouts.values[name];
            let mut joined: Option<Layout> = None;
            let mut conflict = false;
            let mut saw_ptr_return = false;
            for block in func.blocks.values() {
                let Terminator::Return(v) = &block.terminator else { continue };
                if v.ty != ScalarType::Ptr {
                    continue;
                }
                saw_ptr_return = true;
                let Some(layout) = values.get(v).cloned() else {
                    // One return path has unknown layout — the whole
                    // signature is unknown.
                    conflict = true;
                    break;
                };
                match &joined {
                    None => joined = Some(layout),
                    Some(existing) if existing == &layout => {}
                    Some(_) => {
                        conflict = true;
                        break;
                    }
                }
            }
            let new_ret = if conflict || !saw_ptr_return { None } else { joined };
            let sig = layouts.signatures.get_mut(name).unwrap();
            if sig.ret != new_ret {
                sig.ret = new_ret;
                changed = true;
            }
        }

        // Phase 3: param layouts (join across all call sites).
        let mut callers: HashMap<String, Vec<Vec<Option<Layout>>>> = HashMap::new();
        for caller_name in module.functions.keys() {
            let caller_values = &layouts.values[caller_name];
            let caller_func = &module.functions[caller_name];
            for block in caller_func.blocks.values() {
                for inst in &block.insts {
                    if let Inst::Call(_, callee, args) = inst {
                        if !module.functions.contains_key(callee) {
                            continue;
                        }
                        let arg_layouts: Vec<Option<Layout>> = args
                            .iter()
                            .map(|a| {
                                if a.ty == ScalarType::Ptr {
                                    caller_values.get(a).cloned()
                                } else {
                                    None
                                }
                            })
                            .collect();
                        callers.entry(callee.clone()).or_default().push(arg_layouts);
                    }
                }
            }
        }
        for (name, func) in &module.functions {
            let sites = callers.get(name).cloned().unwrap_or_default();
            let mut new_params: Vec<Option<Layout>> = vec![None; func.params.len()];
            if !sites.is_empty() {
                for i in 0..func.params.len() {
                    let mut joined: Option<Layout> = None;
                    let mut conflict = false;
                    for site in &sites {
                        let Some(arg_layout) = site.get(i).and_then(|x| x.as_ref()) else {
                            continue;
                        };
                        match &joined {
                            None => joined = Some(arg_layout.clone()),
                            Some(existing) if existing == arg_layout => {}
                            Some(_) => {
                                conflict = true;
                                break;
                            }
                        }
                    }
                    if !conflict {
                        new_params[i] = joined;
                    }
                }
            }
            let sig = layouts.signatures.get_mut(name).unwrap();
            if sig.params != new_params {
                sig.params = new_params;
                changed = true;
            }
        }

        if !changed {
            break;
        }
    }

    layouts
}

/// Intra-procedural per-Value slot_type inference, seeded with cross-
/// function signatures. Returns a map from Ptr-typed Value to its slot
/// layout.
///
/// Sources of layout:
/// - `Alloc(v, size)` → `[Ptr; size/8]`, refined by subsequent `Store`s.
/// - Function entry params → from `signatures[func].params[i]`.
/// - `Call(_, name, _)` result → from `signatures[name].ret`.
/// - Block params → join of layouts on each incoming edge (must all
///   agree; if any predecessor has a known layout that disagrees with
///   another, the param is dropped from the map).
fn infer_function(
    func: &crate::ssa::Function,
    signatures: &HashMap<String, FuncSignature>,
) -> HashMap<Value, Layout> {
    let mut map: HashMap<Value, Layout> = HashMap::new();

    // Seed: function parameters.
    if let Some(sig) = signatures.get(&func.name) {
        for (i, p) in func.params.iter().enumerate() {
            if p.ty != ScalarType::Ptr {
                continue;
            }
            if let Some(layout) = sig.params.get(i).and_then(|x| x.clone()) {
                map.insert(*p, layout);
            }
        }
    }

    // Seed: Alloc-defined values + Call results.
    for block in func.blocks.values() {
        for inst in &block.insts {
            match inst {
                Inst::Alloc(dest, size) => {
                    let num_slots = size / 8;
                    map.insert(*dest, vec![ScalarType::Ptr; num_slots]);
                }
                Inst::Call(dest, callee, _) if dest.ty == ScalarType::Ptr => {
                    if let Some(sig) = signatures.get(callee) {
                        if let Some(ret) = &sig.ret {
                            map.insert(*dest, ret.clone());
                        }
                    }
                }
                _ => {}
            }
        }
    }

    // Refine Alloc layouts by following Stores. Order matters: a
    // later Store of slot i overrides earlier slot-i Stores; we walk
    // forward so the final type sticks.
    for block in func.blocks.values() {
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

    // Propagate layouts across block-param edges (the SSA join points).
    // Iterate until fixpoint.
    let mut conflict: std::collections::HashSet<Value> = std::collections::HashSet::new();
    loop {
        let mut changed = false;
        for block in func.blocks.values() {
            for edge in block.terminator.successors() {
                let succ_params = &func.blocks[&edge.target].params;
                for (param, arg) in succ_params.iter().zip(edge.args.iter()) {
                    if param.ty != ScalarType::Ptr {
                        continue;
                    }
                    if conflict.contains(param) {
                        continue;
                    }
                    let Some(arg_slots) = map.get(arg).cloned() else {
                        continue;
                    };
                    match map.get(param) {
                        None => {
                            map.insert(*param, arg_slots);
                            changed = true;
                        }
                        Some(existing) if existing != &arg_slots => {
                            map.remove(param);
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

    map
}
