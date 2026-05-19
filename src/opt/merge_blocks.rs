//! Merge a block into its sole predecessor when the predecessor's
//! terminator is an unconditional Jump.

use std::collections::{HashMap, HashSet};

use crate::ssa::instruction::{BlockId, Terminator, Value};
use crate::ssa::Function;

use super::operands::{rewrite_operands, rewrite_terminator_operands};

pub fn run(func: &mut Function) {
    // Count how many incoming edges each block has, and from where.
    // Only track blocks reached by exactly one Jump (not Branch/SwitchInt).
    let mut jump_preds: HashMap<BlockId, BlockId> = HashMap::new();
    let mut multi_pred: HashSet<BlockId> = HashSet::new();

    for (&src, block) in &func.blocks {
        match &block.terminator {
            Terminator::Jump(edge) => {
                if multi_pred.contains(&edge.target) {
                    // already has multiple predecessors
                } else if jump_preds.contains_key(&edge.target) {
                    // second predecessor — no longer mergeable
                    jump_preds.remove(&edge.target);
                    multi_pred.insert(edge.target);
                } else {
                    jump_preds.insert(edge.target, src);
                }
            }
            term => {
                // Branch/SwitchInt — all successors get marked multi-pred.
                for edge in term.successors() {
                    jump_preds.remove(&edge.target);
                    multi_pred.insert(edge.target);
                }
            }
        }
    }

    // Don't merge the entry block into anything.
    jump_preds.remove(&func.entry);

    for (target, pred) in &jump_preds {
        let Some(target_block) = func.blocks.remove(target) else { continue };
        let Some(pred_block) = func.blocks.get_mut(pred) else {
            // Predecessor was already merged away. Restore the target.
            func.blocks.insert(*target, target_block);
            continue;
        };

        let Terminator::Jump(ref edge) = pred_block.terminator else { continue };
        let args = &edge.args;
        let arg_map: HashMap<Value, Value> = target_block
            .params
            .iter()
            .zip(args.iter())
            .map(|(&p, &a)| (p, a))
            .collect();

        for mut inst in target_block.insts {
            rewrite_operands(&mut inst, &arg_map);
            pred_block.insts.push(inst);
        }

        let mut new_term = target_block.terminator;
        rewrite_terminator_operands(&mut new_term, &arg_map);
        pred_block.terminator = new_term;
    }
}
