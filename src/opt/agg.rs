//! Aggregate-related peephole opts.
//!
//! - `load_of_agg` — convert `Load(d, v, off)` to `Extract` when `v`
//!   is Agg-typed (post-inline cleanup that enables `extract_of_pack`).
//! - `extract_of_pack` — fold `Extract(Pack(a,b,c), i)` → the i-th
//!   field.
//! - `split_agg_params` — split N-wide `Agg(n)` block params into N
//!   scalar params, expanding each predecessor's `Pack` arg into its
//!   field values. After DCE the Pack/Extract instructions vanish.

use std::collections::HashMap;

use crate::ssa::instruction::{BlockEdge, BlockId, Inst, ScalarType, Terminator, Value};
use crate::ssa::Function;

use super::operands::{rewrite_operands, rewrite_terminator_operands};

pub fn load_of_agg(func: &mut Function) {
    for block in func.blocks.values_mut() {
        for inst in &mut block.insts {
            if let Inst::Load(dest, ptr, offset) = inst {
                if matches!(ptr.ty, ScalarType::Agg(_)) {
                    *inst = Inst::Extract(*dest, *ptr, *offset);
                }
            }
        }
    }
}

pub fn extract_of_pack(func: &mut Function) -> bool {
    let mut packs: HashMap<Value, Vec<Value>> = HashMap::new();
    for block in func.blocks.values() {
        for inst in &block.insts {
            if let Inst::Pack(dest, fields) = inst {
                packs.insert(*dest, fields.clone());
            }
        }
    }
    if packs.is_empty() {
        return false;
    }

    let mut replacements: HashMap<Value, Value> = HashMap::new();
    for block in func.blocks.values() {
        for inst in &block.insts {
            if let Inst::Extract(dest, agg, idx) = inst {
                if let Some(sources) = packs.get(agg) {
                    if let Some(&src) = sources.get(*idx) {
                        replacements.insert(*dest, src);
                    }
                }
            }
        }
    }

    if replacements.is_empty() {
        return false;
    }

    for block in func.blocks.values_mut() {
        for inst in &mut block.insts {
            rewrite_operands(inst, &replacements);
        }
        rewrite_terminator_operands(&mut block.terminator, &replacements);
    }
    true
}

pub fn split_agg_params(func: &mut Function) {
    // Build a map: Value → Pack fields, so we can look through Packs
    // when expanding terminator args.
    let mut packs: HashMap<Value, Vec<Value>> = HashMap::new();
    for block in func.blocks.values() {
        for inst in &block.insts {
            if let Inst::Pack(dest, fields) = inst {
                packs.insert(*dest, fields.clone());
            }
        }
    }

    // Collect all args flowing to each (block, param_index).
    let mut pred_args: HashMap<(BlockId, usize), Vec<Value>> = HashMap::new();
    for block in func.blocks.values() {
        for edge in block.terminator.successors() {
            for (i, &v) in edge.args.iter().enumerate() {
                pred_args.entry((edge.target, i)).or_default().push(v);
            }
        }
    }

    let mut next_val = func
        .params
        .iter()
        .map(|v| v.id + 1)
        .chain(func.blocks.values().flat_map(|b| {
            b.params
                .iter()
                .map(|v| v.id + 1)
                .chain(b.insts.iter().filter_map(|i| i.dest().map(|d| d.id + 1)))
        }))
        .max()
        .unwrap_or(0);
    let block_ids: Vec<BlockId> = func.blocks.keys().copied().collect();

    for bid in &block_ids {
        if *bid == func.entry {
            continue;
        }
        let params: Vec<Value> = func.blocks[bid].params.clone();
        let mut splits: Vec<Option<Vec<Value>>> = Vec::new();
        let mut any_split = false;

        for (pi, &p) in params.iter().enumerate() {
            if let ScalarType::Agg(n) = p.ty {
                let pred_vals = pred_args.get(&(*bid, pi));
                let all_packs = pred_vals
                    .map(|args| args.iter().all(|v| packs.contains_key(v)))
                    .unwrap_or(false);
                if all_packs {
                    let only_extract_uses = func.blocks.values().all(|b| {
                        let inst_ok = b.insts.iter().all(|inst| {
                            if let Inst::Extract(_, _agg, _) = inst {
                                return true;
                            }
                            !inst.operands().contains(&p)
                        });
                        let term_ok = !b.terminator.operands().contains(&p);
                        inst_ok && term_ok
                    });
                    if !only_extract_uses {
                        splits.push(None);
                        continue;
                    }
                    let all_pred_packs: Vec<&Vec<Value>> = pred_vals
                        .unwrap()
                        .iter()
                        .filter_map(|v| packs.get(v))
                        .collect();
                    let mut field_types: Vec<ScalarType> = Vec::with_capacity(n);
                    let mut types_agree = true;
                    for i in 0..n {
                        let first_ty = all_pred_packs
                            .first()
                            .and_then(|fs| fs.get(i))
                            .map(|fv| fv.ty)
                            .unwrap_or(ScalarType::U64);
                        if all_pred_packs.iter().all(|fs| {
                            fs.get(i).map(|fv| fv.ty).unwrap_or(ScalarType::U64) == first_ty
                        }) {
                            field_types.push(first_ty);
                        } else {
                            types_agree = false;
                            break;
                        }
                    }
                    if !types_agree {
                        splits.push(None);
                        continue;
                    }
                    let new_ps: Vec<Value> = field_types
                        .iter()
                        .map(|&ty| {
                            let v = Value { id: next_val, ty };
                            next_val += 1;
                            v
                        })
                        .collect();
                    splits.push(Some(new_ps));
                    any_split = true;
                } else {
                    splits.push(None);
                }
            } else {
                splits.push(None);
            }
        }
        if !any_split {
            continue;
        }

        // Replace Extract(param, i) → new_params[i].
        let mut replacements: HashMap<Value, Value> = HashMap::new();
        for block in func.blocks.values() {
            for inst in &block.insts {
                if let Inst::Extract(dest, agg, idx) = inst {
                    for (pi, &p) in params.iter().enumerate() {
                        if *agg == p {
                            if let Some(Some(new_ps)) = splits.get(pi) {
                                if let Some(&nv) = new_ps.get(*idx) {
                                    replacements.insert(*dest, nv);
                                }
                            }
                        }
                    }
                }
            }
        }

        // Rebuild block params.
        let mut new_params = Vec::new();
        for (pi, &p) in params.iter().enumerate() {
            match &splits[pi] {
                Some(new_ps) => new_params.extend_from_slice(new_ps),
                None => new_params.push(p),
            }
        }
        func.blocks.get_mut(bid).unwrap().params = new_params;

        // Expand args in all terminators targeting this block.
        for src_bid in &block_ids {
            let term = &func.blocks[src_bid].terminator;
            if let Some(t) = expand_term_args(term, *bid, &splits, &packs) {
                func.blocks.get_mut(src_bid).unwrap().terminator = t;
            }
        }

        if !replacements.is_empty() {
            for block in func.blocks.values_mut() {
                for inst in &mut block.insts {
                    rewrite_operands(inst, &replacements);
                }
                rewrite_terminator_operands(&mut block.terminator, &replacements);
            }
        }
    }
}

/// Expand Pack arguments in a terminator edge targeting `target`.
fn expand_term_args(
    term: &Terminator,
    target: BlockId,
    splits: &[Option<Vec<Value>>],
    packs: &HashMap<Value, Vec<Value>>,
) -> Option<Terminator> {
    fn expand(
        args: &[Value],
        bid: BlockId,
        target: BlockId,
        splits: &[Option<Vec<Value>>],
        packs: &HashMap<Value, Vec<Value>>,
    ) -> Option<Vec<Value>> {
        if bid != target {
            return None;
        }
        let mut out = Vec::new();
        let mut changed = false;
        for (i, &v) in args.iter().enumerate() {
            match splits.get(i) {
                Some(Some(new_ps)) => {
                    if let Some(fields) = packs.get(&v) {
                        out.extend_from_slice(fields);
                    } else {
                        for _ in 0..new_ps.len() {
                            out.push(v);
                        }
                    }
                    changed = true;
                }
                _ => out.push(v),
            }
        }
        if changed { Some(out) } else { None }
    }

    match term {
        Terminator::Jump(edge) => expand(&edge.args, edge.target, target, splits, packs)
            .map(|a| Terminator::Jump(BlockEdge { target: edge.target, args: a })),
        Terminator::Branch { cond, then_edge, else_edge } => {
            let t = expand(&then_edge.args, then_edge.target, target, splits, packs);
            let e = expand(&else_edge.args, else_edge.target, target, splits, packs);
            if t.is_some() || e.is_some() {
                Some(Terminator::Branch {
                    cond: *cond,
                    then_edge: BlockEdge {
                        target: then_edge.target,
                        args: t.unwrap_or_else(|| then_edge.args.clone()),
                    },
                    else_edge: BlockEdge {
                        target: else_edge.target,
                        args: e.unwrap_or_else(|| else_edge.args.clone()),
                    },
                })
            } else {
                None
            }
        }
        Terminator::SwitchInt { scrutinee, arms, default } => {
            let mut changed = false;
            let new_arms: Vec<_> = arms
                .iter()
                .map(|(tag, edge)| {
                    if let Some(a) = expand(&edge.args, edge.target, target, splits, packs) {
                        changed = true;
                        (*tag, BlockEdge { target: edge.target, args: a })
                    } else {
                        (*tag, edge.clone())
                    }
                })
                .collect();
            let new_def = default.as_ref().and_then(|edge| {
                expand(&edge.args, edge.target, target, splits, packs).map(|a| {
                    changed = true;
                    BlockEdge { target: edge.target, args: a }
                })
            });
            if changed {
                Some(Terminator::SwitchInt {
                    scrutinee: *scrutinee,
                    arms: new_arms,
                    default: new_def.or_else(|| default.clone()),
                })
            } else {
                None
            }
        }
        Terminator::Return(_) => None,
    }
}
