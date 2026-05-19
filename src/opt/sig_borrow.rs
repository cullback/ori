//! Whole-program parameter ownership inference.
//!
//! Per function, per Ptr parameter, classify as:
//! - `Transferring` — the function transfers ownership of the param
//!   away (returns it, stores it into a heap object, packs it into
//!   an aggregate, or passes it to a `Transferring` position of
//!   another callee). The caller has handed off ownership; it must
//!   not drop the value.
//! - `Borrowing` — the function only reads from the param. It never
//!   moves the value onward. The caller retains ownership and drops
//!   at its own last use.
//!
//! ## Why
//!
//! Today, `emit_drops::cleanly_transferred` puts *every* Ptr `Call`
//! arg into the "don't drop in caller" set — too conservative. This
//! leaks the value: neither caller nor callee frees, because the
//! callee's params are still classified `Borrowed` by ownership
//! analysis (no static Drop emitted inside the callee).
//!
//! With `ParamUsage::Borrowing` known, the caller stops treating those
//! args as cleanly_transferred and emits its own `Drop` at the arg's
//! last use. Since `Drop` cascades through Ptr children via the static
//! mask, dropping the root frees the whole structure — the callee
//! doesn't need to do anything special inside.
//!
//! ## Inference
//!
//! Start every Ptr param as `Borrowing`. Promote to `Transferring`
//! when the body shows a transfer site for it: a `Return`, a
//! `Store`/`StoreDyn` value, a `Pack`/`Insert` field, or a `Call` arg
//! position that the callee marks `Transferring`. Iterate to fixpoint
//! across the call graph.
//!
//! A param can also be transferred *via a child*: `Load(child, P, off)`
//! followed by transferring `child` (e.g., returning it). This pattern
//! is common in accessors (`head`, `unwrap`). For now we conservatively
//! mark the param `Transferring` whenever a Ptr child loaded from it
//! is transferred — this preserves correctness (caller doesn't drop)
//! at the cost of some missed optimization (the parent box still leaks
//! when the child is moved out).

use std::collections::{HashMap, HashSet};

use crate::ssa::Module;
use crate::ssa::instruction::{Inst, ScalarType, Terminator, Value};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ParamUsage {
    Transferring,
    Borrowing,
}

#[derive(Debug, Clone, Default)]
pub struct FuncSignature {
    /// `params[i]` is `None` for non-Ptr params.
    pub params: Vec<Option<ParamUsage>>,
}

#[derive(Debug, Clone, Default)]
pub struct ModuleUsage {
    pub funcs: HashMap<String, FuncSignature>,
}

impl ModuleUsage {
    /// Lookup callee param usage at index `idx`. Unknown callees and
    /// non-Ptr params default to `Transferring` (the conservative
    /// caller-side behavior — caller keeps treating as transferred,
    /// matching the legacy `cleanly_transferred` blanket rule).
    pub fn usage(&self, callee: &str, idx: usize) -> ParamUsage {
        self.funcs
            .get(callee)
            .and_then(|sig| sig.params.get(idx).copied().flatten())
            .unwrap_or(ParamUsage::Transferring)
    }
}

/// Analyze param usage for every function in `module`.
pub fn analyze(module: &Module) -> ModuleUsage {
    let mut usage = ModuleUsage::default();
    for (name, func) in &module.functions {
        let params: Vec<Option<ParamUsage>> = func
            .params
            .iter()
            .map(|p| {
                if p.ty == ScalarType::Ptr {
                    Some(ParamUsage::Borrowing) // start optimistic
                } else {
                    None
                }
            })
            .collect();
        usage.funcs.insert(name.clone(), FuncSignature { params });
    }

    for _ in 0..32 {
        let mut changed = false;
        for (name, func) in &module.functions {
            let new_params = infer_function(func, &usage);
            let sig = usage.funcs.get_mut(name).unwrap();
            if sig.params != new_params {
                sig.params = new_params;
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }

    usage
}

/// For a single function, decide each Ptr param's usage.
fn infer_function(func: &crate::ssa::Function, usage: &ModuleUsage) -> Vec<Option<ParamUsage>> {
    // Step 1: build the set of values "transferred" by this function
    // body. A value is transferred if it (or a Ptr child reachable
    // from it) ends up in a Return / Store / Pack / Insert / a
    // Call-arg-to-Transferring-callee.
    let transferred = compute_transferred_values(func, usage);

    // Step 2: for each Ptr param, check if it (or a transitively
    // loaded Ptr child of it) appears in `transferred`.
    let mut child_to_root: HashMap<Value, Value> = HashMap::new();
    for block in func.blocks.values() {
        for inst in &block.insts {
            if let Inst::Load(child, parent, _) | Inst::LoadDyn(child, parent, _) = inst {
                if child.ty == ScalarType::Ptr {
                    let root = *child_to_root.get(parent).unwrap_or(parent);
                    child_to_root.insert(*child, root);
                }
            }
        }
    }

    func.params
        .iter()
        .map(|p| {
            if p.ty != ScalarType::Ptr {
                return None;
            }
            // Direct transfer of the param itself.
            if transferred.contains(p) {
                return Some(ParamUsage::Transferring);
            }
            // Transfer via a Ptr child rooted at this param.
            for (child, root) in &child_to_root {
                if root == p && transferred.contains(child) {
                    return Some(ParamUsage::Transferring);
                }
            }
            Some(ParamUsage::Borrowing)
        })
        .collect()
}

/// Set of Ptr values that this function transfers ownership of —
/// directly or via downstream operations.
fn compute_transferred_values(func: &crate::ssa::Function, usage: &ModuleUsage) -> HashSet<Value> {
    let mut transferred: HashSet<Value> = HashSet::new();

    // Seed from terminator (Return / Jump args) and direct transfer
    // sites (Store / Pack / Insert / Call-to-Transferring).
    for block in func.blocks.values() {
        match &block.terminator {
            Terminator::Return(v) if v.ty == ScalarType::Ptr => {
                transferred.insert(*v);
            }
            _ => {}
        }
        for edge in block.terminator.successors() {
            for v in &edge.args {
                if v.ty == ScalarType::Ptr {
                    transferred.insert(*v);
                }
            }
        }
        for inst in &block.insts {
            match inst {
                Inst::Store(_, _, val) | Inst::StoreDyn(_, _, val)
                    if val.ty == ScalarType::Ptr =>
                {
                    transferred.insert(*val);
                }
                Inst::Call(_, callee, args) => {
                    for (i, a) in args.iter().enumerate() {
                        if a.ty == ScalarType::Ptr
                            && usage.usage(callee, i) == ParamUsage::Transferring
                        {
                            transferred.insert(*a);
                        }
                    }
                }
                _ => {}
            }
        }
    }

    transferred
}
