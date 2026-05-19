//! Fold branch-to-switch patterns.
//!
//! When a Branch goes to two blocks that each just jump (with constant
//! args) to the same merge block, and that merge block starts with a
//! SwitchInt on the merged param, replace the Branch with a direct
//! branch to the resolved switch targets.
//!
//! Before:
//!   branch cond ? bT : bF
//!   bT: jump merge(1_u8)
//!   bF: jump merge(0_u8)
//!   merge(tag): switch tag { 1 -> X, 0 -> Y }
//!
//! After:
//!   branch cond ? X : Y

use std::collections::HashMap;

use crate::ssa::instruction::{BlockEdge, BlockId, Inst, Terminator, Value};
use crate::ssa::Function;

pub fn run(func: &mut Function) {
    // Collect const values defined in each block for resolving jump args.
    let mut block_consts: HashMap<BlockId, HashMap<Value, u64>> = HashMap::new();
    for (&bid, block) in &func.blocks {
        let mut consts = HashMap::new();
        for inst in &block.insts {
            if let Inst::Const(d, bits) = inst {
                consts.insert(*d, *bits);
            }
        }
        block_consts.insert(bid, consts);
    }

    let block_ids: Vec<BlockId> = func.blocks.keys().copied().collect();
    for bid in block_ids {
        let block = &func.blocks[&bid];
        let Terminator::Branch { cond, then_edge, else_edge, .. } = &block.terminator else {
            continue;
        };

        let then_b = &func.blocks[&then_edge.target];
        let else_b = &func.blocks[&else_edge.target];
        let (Terminator::Jump(then_jedge), Terminator::Jump(else_jedge)) =
            (&then_b.terminator, &else_b.terminator)
        else {
            continue;
        };
        if then_jedge.target != else_jedge.target {
            continue;
        }
        let merge_id = then_jedge.target;

        if then_jedge.args.len() != 1 || else_jedge.args.len() != 1 {
            continue;
        }

        let then_consts = &block_consts[&then_edge.target];
        let else_consts = &block_consts[&else_edge.target];
        let Some(&then_val) = then_jedge.args.first().and_then(|v| then_consts.get(v)) else {
            continue;
        };
        let Some(&else_val) = else_jedge.args.first().and_then(|v| else_consts.get(v)) else {
            continue;
        };

        let merge_block = &func.blocks[&merge_id];
        if merge_block.params.len() != 1 {
            continue;
        }
        let Terminator::SwitchInt { scrutinee, arms, default } = &merge_block.terminator else {
            continue;
        };
        if *scrutinee != merge_block.params[0] {
            continue;
        }
        if !merge_block.insts.is_empty() {
            continue;
        }

        let resolve = |val: u64| -> Option<BlockEdge> {
            for (arm_val, edge) in arms {
                if *arm_val == val {
                    return Some(edge.clone());
                }
            }
            default.clone()
        };
        let Some(true_edge) = resolve(then_val) else { continue };
        let Some(false_edge) = resolve(else_val) else { continue };

        // The arm edges live in the merge block; their args may
        // reference the merge block's param (the switch scrutinee).
        // We can't carry such references back to `bid` without
        // substituting the constant value, so bail in that case.
        let merge_param = merge_block.params[0];
        if true_edge.args.iter().any(|a| *a == merge_param)
            || false_edge.args.iter().any(|a| *a == merge_param)
        {
            continue;
        }

        let cond = *cond;
        let new_then_args = [then_edge.args.clone(), true_edge.args].concat();
        let new_else_args = [else_edge.args.clone(), false_edge.args].concat();

        func.blocks.get_mut(&bid).unwrap().terminator = Terminator::Branch {
            cond,
            then_edge: BlockEdge { target: true_edge.target, args: new_then_args },
            else_edge: BlockEdge { target: false_edge.target, args: new_else_args },
        };
    }
}
