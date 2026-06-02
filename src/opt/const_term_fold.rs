//! Fold terminators whose decision-input is a known constant.
//!
//! Two rewrites:
//!
//! - `Branch { cond, then_edge, else_edge }` where `cond` resolves to
//!   a `Const(c)` → `Jump(if c != 0 { then_edge } else { else_edge })`.
//! - `SwitchInt { scrutinee, arms, default }` where `scrutinee`
//!   resolves to `Const(c)` → `Jump(matching_arm | default)`.
//!
//! Both rewrites unblock downstream `dce` / `merge_blocks` to collapse
//! the now-dead arms. Each terminator handled independently — single
//! pass over the function, no iteration to fixpoint needed (the
//! rewrite doesn't expose new const-cond branches).
//!
//! Pre-conditions: Const insts define each constant value; const
//! values aren't rewritten by this pass (`const_fold` handles that).
//! Post-conditions: no `Branch`/`SwitchInt` whose decision-input is
//! a Value defined by `Inst::Const(_, _)`.

use std::collections::HashMap;

use crate::ssa::instruction::{Inst, Terminator, Value};
use crate::ssa::Function;

pub fn run(func: &mut Function) -> bool {
    // Collect every `Const` definition in the function. Const insts
    // are SSA-defs, so each Value has at most one entry.
    let mut consts: HashMap<Value, u64> = HashMap::new();
    for block in func.blocks.values() {
        for inst in &block.insts {
            if let Inst::Const(dest, bits) = inst {
                consts.insert(*dest, *bits);
            }
        }
    }

    let mut changed = false;
    for block in func.blocks.values_mut() {
        match &block.terminator {
            Terminator::Branch { cond, then_edge, else_edge } => {
                let Some(&c) = consts.get(cond) else { continue };
                let edge = if c != 0 { then_edge } else { else_edge };
                block.terminator = Terminator::Jump(edge.clone());
                changed = true;
            }
            Terminator::SwitchInt { scrutinee, arms, default } => {
                let Some(&c) = consts.get(scrutinee) else { continue };
                let taken = arms
                    .iter()
                    .find(|(v, _)| *v == c)
                    .map(|(_, e)| e)
                    .or(default.as_ref());
                if let Some(edge) = taken {
                    block.terminator = Terminator::Jump(edge.clone());
                    changed = true;
                }
                // No matching arm + no default: leave alone (the
                // SSA's exhaustiveness should make this unreachable;
                // we'd rather hit the validator than silently corrupt).
            }
            _ => {}
        }
    }
    changed
}
