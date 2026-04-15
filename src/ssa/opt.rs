//! Simple SSA optimization passes: dead code elimination, constant
//! folding, and no-op elimination.

use std::collections::{HashMap, HashSet};

use super::instruction::{BinaryOp, BlockId, Inst, ScalarType, Terminator, Value};
use super::{Function, Module};

/// Run optimization passes in a single deliberate sequence.
/// Each pass is self-sufficient — no fixpoint looping needed.
pub fn optimize(module: &mut Module) {
    for func in module.functions.values_mut() {
        const_fold(func);
        nop_elim(func);
        jump_threading(func);
        branch_switch_fold(func);
        jump_threading(func);
        branch_switch_fold(func);
        // merge_blocks(func); // TODO: fix value scoping bug on 201503
        dce(func);
    }
}

/// Dead code elimination: remove instructions whose destination
/// value is never used by any other instruction or terminator.
/// Returns true if any instructions were removed.
fn dce(func: &mut Function) -> bool {
    let mut changed = false;

    // 1. Remove unreachable blocks by marking reachable ones from entry.
    let mut reachable = HashSet::new();
    let mut worklist = vec![func.entry];
    while let Some(bid) = worklist.pop() {
        if !reachable.insert(bid) {
            continue;
        }
        for (succ, _) in func.blocks[&bid].terminator.successors() {
            worklist.push(succ);
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
            func.blocks.remove(&bid);
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
                used.contains(&dest)
            } else {
                true
            }
        });
        if block.insts.len() != before {
            changed = true;
        }
    }
    changed
}

/// Constant folding: evaluate operations on constant operands at
/// compile time. Replaces `BinOp(dest, op, const_a, const_b)` with
/// `Const(dest, ty, result)`.
/// Returns true if any instructions were folded.
fn const_fold(func: &mut Function) -> bool {
    use std::collections::HashMap;

    // Map from Value → (ScalarType, bits) for known constants.
    let mut consts: HashMap<Value, (ScalarType, u64)> = HashMap::new();
    for block in func.blocks.values() {
        for inst in &block.insts {
            if let Inst::Const(dest, ty, bits) = inst {
                consts.insert(*dest, (*ty, *bits));
            }
        }
    }

    let mut changed = false;
    for block in func.blocks.values_mut() {
        for inst in &mut block.insts {
            if let Inst::BinOp(dest, op, lhs, rhs) = inst {
                let lc = consts.get(lhs).copied();
                let rc = consts.get(rhs).copied();
                if let (Some((lty, lbits)), Some((_, rbits))) = (lc, rc) {
                    if let Some(result) = fold_binop(*op, lty, lbits, rbits) {
                        consts.insert(*dest, (result.0, result.1));
                        *inst = Inst::Const(*dest, result.0, result.1);
                        changed = true;
                    }
                }
            }
        }
    }
    changed
}

/// No-op elimination: remove identity operations where the result
/// equals one of the operands. Replaces the instruction by
/// rewriting all uses of dest to the identity operand.
/// Returns true if any instructions were eliminated.
fn nop_elim(func: &mut Function) -> bool {
    use std::collections::HashMap;

    // Map from Value → (ScalarType, bits) for known constants.
    let mut consts: HashMap<Value, (ScalarType, u64)> = HashMap::new();
    // Map from dest → replacement value (the identity operand).
    let mut replacements: HashMap<Value, Value> = HashMap::new();

    for block in func.blocks.values() {
        for inst in &block.insts {
            if let Inst::Const(dest, ty, bits) = inst {
                consts.insert(*dest, (*ty, *bits));
            }
            if let Inst::BinOp(dest, op, lhs, rhs) = inst {
                if let Some(replacement) = detect_nop(*op, *lhs, *rhs, &consts) {
                    replacements.insert(*dest, replacement);
                }
            }
        }
    }

    if replacements.is_empty() {
        return false;
    }

    // Resolve chains: if a→b and b→c, then a→c.
    let mut resolved: HashMap<Value, Value> = HashMap::new();
    for (&from, &to) in &replacements {
        let mut target = to;
        while let Some(&next) = replacements.get(&target) {
            target = next;
        }
        resolved.insert(from, target);
    }

    // Rewrite all operand references and remove the now-dead no-op instructions.
    for block in func.blocks.values_mut() {
        for inst in &mut block.insts {
            rewrite_operands(inst, &resolved);
        }
        rewrite_terminator_operands(&mut block.terminator, &resolved);
        block.insts.retain(|inst| {
            inst.dest().map_or(true, |d| !resolved.contains_key(&d))
        });
    }

    true
}

/// Jump threading: eliminate blocks that contain no instructions and
/// just unconditionally jump to another block. Predecessors are
/// redirected to the final target with arguments composed through
/// the chain. Also merges trivial entry-block forwards.
fn jump_threading(func: &mut Function) -> bool {
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
        let Terminator::Jump(target, ref args) = block.terminator else {
            continue;
        };
        if block.params.is_empty() {
            // Fixed-arg: no params, just forwards constant args.
            redirects.insert(bid, Redirect::FixedArgs(target, args.clone()));
        } else {
            // Param-forwarding: each arg must be a block param.
            let param_indices: Option<Vec<usize>> = args
                .iter()
                .map(|arg| block.params.iter().position(|p| p == arg))
                .collect();
            if let Some(indices) = param_indices {
                redirects.insert(bid, Redirect::ParamForward(target, indices));
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
                        // Fixed→Fixed: second block has no params, so first block's
                        // args are irrelevant — just use the second block's fixed args.
                        Redirect::FixedArgs(*t2, args.clone())
                    }
                };
            }
            (bid, current)
        })
        .collect();

    // Rewrite all terminators that reference redirected blocks.
    let mut changed = false;
    let remap = |bid: BlockId, args: &[Value]| -> Option<(BlockId, Vec<Value>)> {
        resolved.get(&bid).map(|redirect| match redirect {
            Redirect::ParamForward(target, indices) => {
                (*target, indices.iter().map(|&i| args[i]).collect())
            }
            Redirect::FixedArgs(target, fixed_args) => (*target, fixed_args.clone()),
        })
    };

    for block in func.blocks.values_mut() {
        match &mut block.terminator {
            Terminator::Jump(target, args) => {
                if let Some((nt, na)) = remap(*target, args) {
                    *target = nt;
                    *args = na;
                    changed = true;
                }
            }
            Terminator::Branch {
                then_block,
                then_args,
                else_block,
                else_args,
                ..
            } => {
                if let Some((nt, na)) = remap(*then_block, then_args) {
                    *then_block = nt;
                    *then_args = na;
                    changed = true;
                }
                if let Some((ne, na)) = remap(*else_block, else_args) {
                    *else_block = ne;
                    *else_args = na;
                    changed = true;
                }
            }
            Terminator::SwitchInt { arms, default, .. } => {
                for (_, bid, args) in arms.iter_mut() {
                    if let Some((nt, na)) = remap(*bid, args) {
                        *bid = nt;
                        *args = na;
                        changed = true;
                    }
                }
                if let Some((bid, args)) = default {
                    if let Some((nt, na)) = remap(*bid, args) {
                        *bid = nt;
                        *args = na;
                        changed = true;
                    }
                }
            }
            _ => {}
        }
    }

    // Merge trivial entry block: if the entry block has no instructions
    // and jumps to a target, substitute jump args for the target's block
    // params and splice the target's content into the entry block.
    if func.blocks[&func.entry].insts.is_empty() {
        if let Terminator::Jump(target, ref args) = func.blocks[&func.entry].terminator {
            if target != func.entry && func.blocks.contains_key(&target) {
                let target_block = func.blocks[&target].clone();
                let arg_map: HashMap<Value, Value> = target_block
                    .params
                    .iter()
                    .zip(args.iter())
                    .map(|(&p, &a)| (p, a))
                    .collect();
                let entry = func.entry;
                func.blocks.get_mut(&entry).unwrap().insts = target_block.insts;
                func.blocks.get_mut(&entry).unwrap().terminator = target_block.terminator;
                // Rewrite entry block's new content to use the jump args.
                let entry_block = func.blocks.get_mut(&entry).unwrap();
                for inst in &mut entry_block.insts {
                    rewrite_operands(inst, &arg_map);
                }
                rewrite_terminator_operands(&mut entry_block.terminator, &arg_map);
                changed = true;
            }
        }
    }

    changed
}

/// Fold branch-to-switch patterns: when a Branch goes to two blocks
/// that each just jump (with constant args) to the same merge block,
/// and that merge block starts with a SwitchInt on the merged param,
/// replace the Branch with a direct branch to the switch targets.
///
/// Before:
///   branch cond ? bT : bF
///   bT: jump merge(1_u8)
///   bF: jump merge(0_u8)
///   merge(tag): switch tag { 1 -> X, 0 -> Y }
///
/// After:
///   branch cond ? X : Y
fn branch_switch_fold(func: &mut Function) {
    // Collect const values defined in each block for resolving jump args.
    let mut block_consts: HashMap<BlockId, HashMap<Value, u64>> = HashMap::new();
    for (&bid, block) in &func.blocks {
        let mut consts = HashMap::new();
        for inst in &block.insts {
            if let Inst::Const(d, _, bits) = inst {
                consts.insert(*d, *bits);
            }
        }
        block_consts.insert(bid, consts);
    }

    let block_ids: Vec<BlockId> = func.blocks.keys().copied().collect();
    for bid in block_ids {
        let block = &func.blocks[&bid];
        let Terminator::Branch {
            cond,
            then_block,
            then_args,
            else_block,
            else_args,
            ..
        } = &block.terminator
        else {
            continue;
        };

        // Both targets must be blocks that just jump to the same merge.
        let then_b = &func.blocks[then_block];
        let else_b = &func.blocks[else_block];
        let (Terminator::Jump(then_target, then_jargs), Terminator::Jump(else_target, else_jargs)) =
            (&then_b.terminator, &else_b.terminator)
        else {
            continue;
        };
        if then_target != else_target {
            continue;
        }
        let merge_id = *then_target;

        // Both must pass exactly one arg.
        if then_jargs.len() != 1 || else_jargs.len() != 1 {
            continue;
        }

        // Resolve the constant values of the jump args.
        let then_consts = &block_consts[then_block];
        let else_consts = &block_consts[else_block];
        let Some(&then_val) = then_jargs.first().and_then(|v| then_consts.get(v)) else {
            continue;
        };
        let Some(&else_val) = else_jargs.first().and_then(|v| else_consts.get(v)) else {
            continue;
        };

        // The merge block must start with SwitchInt on its first param.
        let merge_block = &func.blocks[&merge_id];
        if merge_block.params.len() != 1 {
            continue;
        }
        let Terminator::SwitchInt {
            scrutinee,
            arms,
            default,
        } = &merge_block.terminator
        else {
            continue;
        };
        if *scrutinee != merge_block.params[0] {
            continue;
        }
        if !merge_block.insts.is_empty() {
            continue;
        }

        // Find where each constant goes in the switch.
        let resolve = |val: u64| -> Option<(BlockId, Vec<Value>)> {
            for (arm_val, target, args) in arms {
                if *arm_val == val {
                    return Some((*target, args.clone()));
                }
            }
            default.clone()
        };
        let Some((true_target, true_args)) = resolve(then_val) else {
            continue;
        };
        let Some((false_target, false_args)) = resolve(else_val) else {
            continue;
        };

        let cond = *cond;
        let new_then_args = [then_args.clone(), true_args].concat();
        let new_else_args = [else_args.clone(), false_args].concat();

        func.blocks.get_mut(&bid).unwrap().terminator = Terminator::Branch {
            cond,
            then_block: true_target,
            then_args: new_then_args,
            else_block: false_target,
            else_args: new_else_args,
        };
    }
}

/// Merge single-predecessor blocks: if block B has exactly one
/// predecessor A, and A unconditionally jumps to B, append B's
/// content into A and remove B.
fn merge_blocks(func: &mut Function) {
    // Count how many incoming edges each block has, and from where.
    // Only track blocks reached by exactly one Jump (not Branch/SwitchInt).
    let mut jump_preds: HashMap<BlockId, BlockId> = HashMap::new();
    let mut multi_pred: HashSet<BlockId> = HashSet::new();

    for (&src, block) in &func.blocks {
        match &block.terminator {
            Terminator::Jump(target, _) => {
                if multi_pred.contains(target) {
                    // already has multiple predecessors
                } else if jump_preds.contains_key(target) {
                    // second predecessor — no longer mergeable
                    jump_preds.remove(target);
                    multi_pred.insert(*target);
                } else {
                    jump_preds.insert(*target, src);
                }
            }
            term => {
                // Branch/SwitchInt — all successors get marked as multi-pred
                // (the predecessor has multiple outgoing edges, so the
                // successor can't be merged back into it).
                for (succ, _) in term.successors() {
                    jump_preds.remove(&succ);
                    multi_pred.insert(succ);
                }
            }
        }
    }

    // Don't merge the entry block into anything.
    jump_preds.remove(&func.entry);

    // Merge each eligible block into its sole predecessor.
    for (target, pred) in &jump_preds {
        let Some(target_block) = func.blocks.remove(target) else {
            continue;
        };
        let Some(pred_block) = func.blocks.get_mut(pred) else {
            // Predecessor was already merged away. Restore the target.
            func.blocks.insert(*target, target_block);
            continue;
        };

        // Build param→arg substitution from the Jump.
        let Terminator::Jump(_, ref args) = pred_block.terminator else {
            continue;
        };
        let arg_map: HashMap<Value, Value> = target_block
            .params
            .iter()
            .zip(args.iter())
            .map(|(&p, &a)| (p, a))
            .collect();

        // Append target's instructions (with params substituted) to predecessor.
        for mut inst in target_block.insts {
            rewrite_operands(&mut inst, &arg_map);
            pred_block.insts.push(inst);
        }

        // Replace predecessor's terminator with target's terminator.
        let mut new_term = target_block.terminator;
        rewrite_terminator_operands(&mut new_term, &arg_map);
        pred_block.terminator = new_term;
    }
}

// ---- Helpers ----

fn is_side_effect(inst: &Inst) -> bool {
    matches!(
        inst,
        Inst::Call(..)
            | Inst::Alloc(..)
            | Inst::Store(..)
            | Inst::StoreDyn(..)
            | Inst::RcInc(..)
            | Inst::RcDec(..)
            | Inst::Reset(..)
            | Inst::Reuse(..)
    )
}

#[expect(clippy::cast_possible_wrap, reason = "integer arithmetic folding")]
fn fold_binop(op: BinaryOp, ty: ScalarType, lbits: u64, rbits: u64) -> Option<(ScalarType, u64)> {
    match ty {
        ScalarType::I64 => {
            let l = lbits as i64;
            let r = rbits as i64;
            let result = match op {
                BinaryOp::Add => l.checked_add(r)?,
                BinaryOp::Sub => l.checked_sub(r)?,
                BinaryOp::Mul => l.checked_mul(r)?,
                BinaryOp::Div if r != 0 => l.checked_div(r)?,
                BinaryOp::Rem if r != 0 => l.checked_rem(r)?,
                BinaryOp::Xor => l ^ r,
                BinaryOp::Eq => return Some((ScalarType::U8, u64::from(l == r))),
                BinaryOp::Neq => return Some((ScalarType::U8, u64::from(l != r))),
                BinaryOp::Lt => return Some((ScalarType::U8, u64::from(l < r))),
                BinaryOp::Le => return Some((ScalarType::U8, u64::from(l <= r))),
                BinaryOp::Gt => return Some((ScalarType::U8, u64::from(l > r))),
                BinaryOp::Ge => return Some((ScalarType::U8, u64::from(l >= r))),
                BinaryOp::Max => l.max(r),
                _ => return None,
            };
            Some((ScalarType::I64, result as u64))
        }
        ScalarType::U64 => {
            let result = match op {
                BinaryOp::Add => lbits.checked_add(rbits)?,
                BinaryOp::Sub => lbits.checked_sub(rbits)?,
                BinaryOp::Mul => lbits.checked_mul(rbits)?,
                BinaryOp::Div if rbits != 0 => lbits.checked_div(rbits)?,
                BinaryOp::Rem if rbits != 0 => lbits.checked_rem(rbits)?,
                BinaryOp::Xor => lbits ^ rbits,
                BinaryOp::Eq => return Some((ScalarType::U8, u64::from(lbits == rbits))),
                BinaryOp::Neq => return Some((ScalarType::U8, u64::from(lbits != rbits))),
                BinaryOp::Lt => return Some((ScalarType::U8, u64::from(lbits < rbits))),
                BinaryOp::Le => return Some((ScalarType::U8, u64::from(lbits <= rbits))),
                BinaryOp::Gt => return Some((ScalarType::U8, u64::from(lbits > rbits))),
                BinaryOp::Ge => return Some((ScalarType::U8, u64::from(lbits >= rbits))),
                BinaryOp::Max => lbits.max(rbits),
                _ => return None,
            };
            Some((ScalarType::U64, result))
        }
        _ => None,
    }
}

fn detect_nop(
    op: BinaryOp,
    lhs: Value,
    rhs: Value,
    consts: &std::collections::HashMap<Value, (ScalarType, u64)>,
) -> Option<Value> {
    let lc = consts.get(&lhs).map(|(_, b)| *b);
    let rc = consts.get(&rhs).map(|(_, b)| *b);
    match op {
        BinaryOp::Add if rc == Some(0) => Some(lhs),
        BinaryOp::Add if lc == Some(0) => Some(rhs),
        BinaryOp::Sub if rc == Some(0) => Some(lhs),
        BinaryOp::Mul if rc == Some(1) => Some(lhs),
        BinaryOp::Mul if lc == Some(1) => Some(rhs),
        BinaryOp::Div if rc == Some(1) => Some(lhs),
        _ => None,
    }
}

pub fn rewrite_operands(inst: &mut Inst, map: &std::collections::HashMap<Value, Value>) {
    match inst {
        Inst::BinOp(_, _, lhs, rhs) => {
            if let Some(&r) = map.get(lhs) { *lhs = r; }
            if let Some(&r) = map.get(rhs) { *rhs = r; }
        }
        Inst::Call(_, _, args) => {
            for a in args { if let Some(&r) = map.get(a) { *a = r; } }
        }
        Inst::Load(_, ptr, _) => {
            if let Some(&r) = map.get(ptr) { *ptr = r; }
        }
        Inst::Store(ptr, _, val) => {
            if let Some(&r) = map.get(ptr) { *ptr = r; }
            if let Some(&r) = map.get(val) { *val = r; }
        }
        Inst::LoadDyn(_, ptr, idx) => {
            if let Some(&r) = map.get(ptr) { *ptr = r; }
            if let Some(&r) = map.get(idx) { *idx = r; }
        }
        Inst::StoreDyn(ptr, idx, val) => {
            if let Some(&r) = map.get(ptr) { *ptr = r; }
            if let Some(&r) = map.get(idx) { *idx = r; }
            if let Some(&r) = map.get(val) { *val = r; }
        }
        Inst::RcInc(v) | Inst::RcDec(v) => {
            if let Some(&r) = map.get(v) { *v = r; }
        }
        Inst::Reset(_, ptr, _) => {
            if let Some(&r) = map.get(ptr) { *ptr = r; }
        }
        Inst::Reuse(_, tok, _) => {
            if let Some(&r) = map.get(tok) { *tok = r; }
        }
        Inst::Const(..) | Inst::Alloc(..) | Inst::StaticRef(..) => {}
    }
}

pub fn rewrite_terminator_operands(
    term: &mut super::instruction::Terminator,
    map: &std::collections::HashMap<Value, Value>,
) {
    use super::instruction::Terminator;
    match term {
        Terminator::Return(v) => {
            if let Some(&r) = map.get(v) { *v = r; }
        }
        Terminator::Jump(_, args) => {
            for a in args { if let Some(&r) = map.get(a) { *a = r; } }
        }
        Terminator::Branch { cond, then_args, else_args, .. } => {
            if let Some(&r) = map.get(cond) { *cond = r; }
            for a in then_args { if let Some(&r) = map.get(a) { *a = r; } }
            for a in else_args { if let Some(&r) = map.get(a) { *a = r; } }
        }
        Terminator::SwitchInt { scrutinee, arms, default, .. } => {
            if let Some(&r) = map.get(scrutinee) { *scrutinee = r; }
            for (_, _, args) in arms { for a in args { if let Some(&r) = map.get(a) { *a = r; } } }
            if let Some((_, args)) = default { for a in args { if let Some(&r) = map.get(a) { *a = r; } } }
        }
    }
}
