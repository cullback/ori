//! Retype static-derived Values from `RcPtr` to `Ptr`.
//!
//! `static_promote` produces `StaticRef` instructions whose dest type
//! is inherited from the original `Alloc` (always `RcPtr`). Statics
//! don't participate in refcounting — their runtime rc is the sentinel
//! `u32::MAX`, and rc ops on them are no-ops. Typing them as `Ptr`
//! expresses this intent at the SSA layer, lets `rc_emit` skip them
//! entirely, and aligns the IR with what a future codegen will want.
//!
//! The retype is a per-function fixpoint:
//!
//! 1. Seed: every `StaticRef` dest is static.
//! 2. Propagate: a block param is static if every incoming edge puts a
//!    static value at that position. Iterate to fixpoint.
//! 3. Retype: every Value with id in the static set gets `ty = Ptr`.
//!
//! Boundaries where a static-typed Value meets an RcPtr-typed position
//! (Call args, Return, edge args into non-static block params) stay as
//! `Ptr` — the validator's `types_compatible` treats `Ptr` and `RcPtr`
//! as interchangeable because both are 8-byte heap pointers and the
//! sentinel-rc runtime semantics make rc on `Ptr`-typed statics a
//! no-op. No bitcasts needed.
//!
//! Cross-function: if a function's `Return` carries a static, the
//! function's `return_type` is updated to `Ptr`. Callers' `Call` dests
//! pick this up via a second pass that walks every Call site and
//! retypes the result to the callee's (possibly-updated) return type.

use std::collections::{HashMap, HashSet};

use crate::ssa::Module;
use crate::ssa::instruction::{Inst, ScalarType, Terminator, Value};

pub fn run(module: &mut Module) {
    // Per-function retype, collecting functions whose return type
    // changed so we can propagate to callers in a second pass.
    let mut return_types: HashMap<String, Vec<ScalarType>> = HashMap::new();
    for (name, func) in module.functions.iter_mut() {
        retype_function(func);
        return_types.insert(name.clone(), func.return_type.clone());
    }
    // Cross-function: retype Call dests targeting functions whose
    // returns are now Ptr. Single pass — Call dests aren't transitively
    // retyped (they're already RcPtr-typed and stay so unless this pass
    // explicitly changes them; retyping to Ptr here would require
    // another local fixpoint per function, which we defer).
    for func in module.functions.values_mut() {
        for block in func.blocks.values_mut() {
            for inst in block.insts.iter_mut() {
                if let Inst::Call { results, target, .. } = inst {
                    let Some(callee_ret) = return_types.get(target) else {
                        continue;
                    };
                    for (i, r) in results.iter_mut().enumerate() {
                        if let Some(&ret_ty) = callee_ret.get(i) {
                            if ret_ty == ScalarType::Ptr {
                                r.ty = ScalarType::Ptr;
                            }
                        }
                    }
                }
            }
        }
    }
}

fn retype_function(func: &mut crate::ssa::Function) {
    // Seed: StaticRef defs.
    let mut static_set: HashSet<usize> = HashSet::new();
    for block in func.blocks.values() {
        for inst in &block.insts {
            if let Inst::StaticRef(dest, _) = inst {
                static_set.insert(dest.id);
            }
        }
    }
    if static_set.is_empty() {
        return;
    }

    // Predecessors: for each target block, the (predecessor_id,
    // edge_args) of every incoming edge. Block params join over all
    // incoming edges, so a param is static iff every incoming edge
    // puts a static value there.
    let mut predecessors: HashMap<crate::ssa::instruction::BlockId, Vec<Vec<Value>>> =
        HashMap::new();
    for block in func.blocks.values() {
        for edge in block.terminator.successors() {
            predecessors
                .entry(edge.target)
                .or_default()
                .push(edge.args.clone());
        }
    }

    // Fixpoint: extend the static set through block params.
    loop {
        let mut changed = false;
        for (bid, block) in func.blocks.iter() {
            for (pi, param) in block.params.iter().enumerate() {
                if static_set.contains(&param.id) {
                    continue;
                }
                let Some(preds) = predecessors.get(bid) else {
                    continue;
                };
                if preds.is_empty() {
                    continue;
                }
                let all_static = preds.iter().all(|args| {
                    args.get(pi)
                        .is_some_and(|v| static_set.contains(&v.id))
                });
                if all_static {
                    static_set.insert(param.id);
                    changed = true;
                }
            }
        }
        if !changed {
            break;
        }
    }

    // Retype every Value with id in the set to Ptr.
    let retype = |v: &mut Value| {
        if static_set.contains(&v.id) {
            v.ty = ScalarType::Ptr;
        }
    };

    for p in func.params.iter_mut() {
        retype(p);
    }
    for block in func.blocks.values_mut() {
        for p in block.params.iter_mut() {
            retype(p);
        }
        for inst in block.insts.iter_mut() {
            for d in inst.dests_mut() {
                retype(d);
            }
            inst.map_operands_mut(retype);
        }
        match &mut block.terminator {
            Terminator::Return(rets) => {
                for v in rets.iter_mut() {
                    retype(v);
                }
            }
            Terminator::Jump(edge) => {
                for v in edge.args.iter_mut() {
                    retype(v);
                }
            }
            Terminator::Branch {
                cond,
                then_edge,
                else_edge,
            } => {
                retype(cond);
                for v in then_edge.args.iter_mut() {
                    retype(v);
                }
                for v in else_edge.args.iter_mut() {
                    retype(v);
                }
            }
            Terminator::SwitchInt {
                scrutinee,
                arms,
                default,
            } => {
                retype(scrutinee);
                for (_, edge) in arms.iter_mut() {
                    for v in edge.args.iter_mut() {
                        retype(v);
                    }
                }
                if let Some(edge) = default {
                    for v in edge.args.iter_mut() {
                        retype(v);
                    }
                }
            }
        }
    }

    // Update the function's declared return type if any returned value
    // is now static. Validator's types_compatible accepts both shapes,
    // but propagating the Ptr typing lets callers see it too.
    for block in func.blocks.values() {
        if let Terminator::Return(rets) = &block.terminator {
            for (i, v) in rets.iter().enumerate() {
                if static_set.contains(&v.id)
                    && func
                        .return_type
                        .get(i)
                        .copied()
                        != Some(ScalarType::Ptr)
                {
                    if let Some(ty) = func.return_type.get_mut(i) {
                        *ty = ScalarType::Ptr;
                    }
                }
            }
        }
    }
}
