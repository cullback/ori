//! Jump threading.
//!
//! Eliminates blocks that contain no instructions and end in an
//! unconditional Jump. Predecessors are redirected to the final
//! target with arguments composed through the chain. Also merges
//! trivial entry-block forwards.

use std::collections::HashMap;

use crate::ssa::instruction::{BlockEdge, BlockId, Terminator, Value};
use crate::ssa::Function;

use super::operands::{rewrite_operands, rewrite_terminator_operands};

pub fn run(func: &mut Function) -> bool {
    // Two kinds of redirectable blocks (no instructions, terminates with Jump):
    //
    // 1. Param-forwarding: all jump args are block params. Predecessors
    //    remap their args through the index mapping.
    // 2. Fixed-arg: block has no params. Predecessors replace their
    //    edge with the block's fixed jump target and args.
    #[derive(Clone)]
    enum Redirect {
        ParamForward(BlockId, Vec<usize>),
        FixedArgs(BlockId, Vec<Value>),
    }

    let mut redirects: HashMap<BlockId, Redirect> = HashMap::new();
    for (&bid, block) in &func.blocks {
        if !block.insts.is_empty() {
            continue;
        }
        let Terminator::Jump(ref edge) = block.terminator else {
            continue;
        };
        if block.params.is_empty() {
            redirects.insert(bid, Redirect::FixedArgs(edge.target, edge.args.clone()));
        } else {
            let param_indices: Option<Vec<usize>> = edge
                .args
                .iter()
                .map(|arg| block.params.iter().position(|p| p == arg))
                .collect();
            if let Some(indices) = param_indices {
                redirects.insert(bid, Redirect::ParamForward(edge.target, indices));
            }
        }
    }

    if redirects.is_empty() {
        return false;
    }

    // Resolve chains.
    let resolved: HashMap<BlockId, Redirect> = redirects
        .keys()
        .map(|&bid| {
            let mut current = redirects[&bid].clone();
            loop {
                let next_target = match &current {
                    Redirect::ParamForward(t, _) | Redirect::FixedArgs(t, _) => *t,
                };
                let Some(next) = redirects.get(&next_target) else {
                    break;
                };
                current = match (&current, next) {
                    (Redirect::ParamForward(_, indices), Redirect::ParamForward(t2, indices2)) => {
                        Redirect::ParamForward(*t2, indices.iter().map(|&i| indices2[i]).collect())
                    }
                    (Redirect::ParamForward(_, indices), Redirect::FixedArgs(t2, args2)) => {
                        Redirect::FixedArgs(*t2, indices.iter().map(|&i| args2[i]).collect())
                    }
                    (Redirect::FixedArgs(_, args), Redirect::ParamForward(t2, indices2)) => {
                        Redirect::FixedArgs(*t2, indices2.iter().map(|&i| args[i]).collect())
                    }
                    (Redirect::FixedArgs(_, args), Redirect::FixedArgs(t2, _)) => {
                        Redirect::FixedArgs(*t2, args.clone())
                    }
                };
            }
            (bid, current)
        })
        .collect();

    // Rewrite all terminators that reference redirected blocks.
    let mut changed = false;
    let remap = |edge: &BlockEdge| -> Option<BlockEdge> {
        resolved.get(&edge.target).map(|redirect| match redirect {
            Redirect::ParamForward(target, indices) => {
                BlockEdge { target: *target, args: indices.iter().map(|&i| edge.args[i]).collect() }
            }
            Redirect::FixedArgs(target, fixed_args) => {
                BlockEdge { target: *target, args: fixed_args.clone() }
            }
        })
    };

    for block in func.blocks.values_mut() {
        match &mut block.terminator {
            Terminator::Jump(edge) => {
                if let Some(ne) = remap(edge) {
                    *edge = ne;
                    changed = true;
                }
            }
            Terminator::Branch { then_edge, else_edge, .. } => {
                if let Some(ne) = remap(then_edge) {
                    *then_edge = ne;
                    changed = true;
                }
                if let Some(ne) = remap(else_edge) {
                    *else_edge = ne;
                    changed = true;
                }
            }
            Terminator::SwitchInt { arms, default, .. } => {
                for (_, edge) in arms.iter_mut() {
                    if let Some(ne) = remap(edge) {
                        *edge = ne;
                        changed = true;
                    }
                }
                if let Some(edge) = default {
                    if let Some(ne) = remap(edge) {
                        *edge = ne;
                        changed = true;
                    }
                }
            }
            _ => {}
        }
    }

    // Merge trivial entry block: if the entry block has no instructions
    // and jumps to a target, and the target has no OTHER predecessors,
    // splice the target's content into the entry block and drop the
    // now-redundant target block.
    if func.blocks[&func.entry].insts.is_empty() {
        if let Terminator::Jump(ref edge) = func.blocks[&func.entry].terminator {
            let target = edge.target;
            if target != func.entry && func.blocks.contains_key(&target) {
                let other_preds = func
                    .blocks
                    .iter()
                    .filter(|(bid, _)| **bid != func.entry)
                    .any(|(_, b)| b.terminator.successors().into_iter().any(|e| e.target == target));
                if !other_preds {
                    let args = edge.args.clone();
                    let target_block = func.blocks.remove(&target).unwrap();
                    let arg_map: HashMap<Value, Value> = target_block
                        .params
                        .iter()
                        .zip(args.iter())
                        .map(|(&p, &a)| (p, a))
                        .collect();
                    let entry = func.entry;
                    let entry_block = func.blocks.get_mut(&entry).unwrap();
                    entry_block.insts = target_block.insts;
                    entry_block.terminator = target_block.terminator;
                    for inst in &mut entry_block.insts {
                        rewrite_operands(inst, &arg_map);
                    }
                    rewrite_terminator_operands(&mut entry_block.terminator, &arg_map);
                    changed = true;
                }
            }
        }
    }

    changed
}
