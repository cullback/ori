//! Identity-operation removal: `x + 0`, `x * 1`, `x / 1`, etc.
//!
//! Detects BinOps whose result equals one of the operands and rewrites
//! all uses of the result to that operand. The now-dead BinOp gets
//! removed; downstream DCE will sweep the rest.

use std::collections::HashMap;

use crate::ssa::instruction::{BinaryOp, Inst, ScalarType, Value};
use crate::ssa::Function;

use super::operands::{rewrite_operands, rewrite_terminator_operands};

pub fn run(func: &mut Function) -> bool {
    // Map from Value → (ScalarType, bits) for known constants.
    let mut consts: HashMap<Value, (ScalarType, u64)> = HashMap::new();
    // Map from dest → replacement value (the identity operand).
    let mut replacements: HashMap<Value, Value> = HashMap::new();

    for block in func.blocks.values() {
        for inst in &block.insts {
            if let Inst::Const(dest, bits) = inst {
                consts.insert(*dest, (dest.ty, *bits));
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

fn detect_nop(
    op: BinaryOp,
    lhs: Value,
    rhs: Value,
    consts: &HashMap<Value, (ScalarType, u64)>,
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
