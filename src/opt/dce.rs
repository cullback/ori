//! Dead-code elimination.
//!
//! - **block-level**: remove blocks unreachable from entry.
//! - **inst-level**: remove instructions whose destination is never
//!   used, unless they have a side effect.
//! - **function-level**: remove functions never called from any
//!   reachable function.

use std::collections::HashSet;

use crate::ssa::instruction::{BlockId, Inst, Value};
use crate::ssa::{Function, Module};

pub fn run(func: &mut Function) -> bool {
    let mut changed = false;

    // 1. Remove unreachable blocks by marking reachable ones from entry.
    let mut reachable = HashSet::new();
    let mut worklist = vec![func.entry];
    while let Some(bid) = worklist.pop() {
        if !reachable.insert(bid) {
            continue;
        }
        for edge in func.blocks[&bid].terminator.successors() {
            worklist.push(edge.target);
        }
    }
    if reachable.len() < func.blocks.len() {
        let dead: Vec<BlockId> = func
            .blocks
            .keys()
            .copied()
            .filter(|bid| !reachable.contains(bid))
            .collect();
        for bid in dead {
            func.blocks.remove(&bid).unwrap();
            changed = true;
        }
    }

    // 2. Remove instructions whose destination value is never used.
    let mut used: HashSet<Value> = HashSet::new();
    for block in func.blocks.values() {
        for inst in &block.insts {
            for v in inst.operands() {
                used.insert(v);
            }
        }
        for v in block.terminator.operands() {
            used.insert(v);
        }
    }

    for block in func.blocks.values_mut() {
        let before = block.insts.len();
        block.insts.retain(|inst| {
            if let Some(dest) = inst.dest() {
                if is_side_effect(inst) {
                    return true;
                }
                if used.contains(&dest) {
                    return true;
                }
                return false;
            }
            true
        });
        if block.insts.len() != before {
            changed = true;
        }
    }
    changed
}

/// Remove functions that are never called from any other function.
pub fn dead_functions(module: &mut Module) {
    let mut called: HashSet<String> = HashSet::new();
    called.insert(module.entry.clone());
    for func in module.functions.values() {
        for block in func.blocks.values() {
            for inst in &block.insts {
                if let Inst::Call { target, .. } = inst {
                    called.insert(target.clone());
                }
            }
        }
    }
    module.functions.retain(|name, _| called.contains(name));
}

/// True if removing this instruction would change observable program
/// behavior. New instruction variants that allocate, store, or alter
/// reference counts MUST be added here.
pub fn is_side_effect(inst: &Inst) -> bool {
    matches!(
        inst,
        Inst::Call { .. }
            | Inst::Alloc(..)
            | Inst::AllocDyn(..)
            | Inst::Store(..)
            | Inst::StoreDyn(..)
            | Inst::RcInc(..)
            | Inst::RcDec(..)
            | Inst::CowStore(..)
            | Inst::CowStoreDyn(..)
            | Inst::CowMoveOut(..)
            | Inst::CowResizeDyn(..)
    )
}
