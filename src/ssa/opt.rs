//! Simple SSA optimization passes: dead code elimination, constant
//! folding, and no-op elimination.

use std::collections::HashSet;

use super::instruction::{BinaryOp, Inst, ScalarType, Value};
use super::{Function, Module};

/// Run all optimization passes until no further progress is made.
pub fn optimize(module: &mut Module) {
    for func in module.functions.values_mut() {
        loop {
            let a = dce(func);
            let b = const_fold(func);
            let c = nop_elim(func);
            if !(a || b || c) {
                break;
            }
        }
    }
}

/// Dead code elimination: remove instructions whose destination
/// value is never used by any other instruction or terminator.
/// Returns true if any instructions were removed.
fn dce(func: &mut Function) -> bool {
    // Collect all values that are used as operands.
    let mut used: HashSet<Value> = HashSet::new();
    for block in &func.blocks {
        for inst in &block.insts {
            for v in inst.operands() {
                used.insert(v);
            }
        }
        for v in block.terminator.operands() {
            used.insert(v);
        }
    }

    let mut changed = false;
    for block in &mut func.blocks {
        let before = block.insts.len();
        block.insts.retain(|inst| {
            if let Some(dest) = inst.dest() {
                // Keep side-effecting instructions even if unused.
                if is_side_effect(inst) {
                    return true;
                }
                // Keep if the result is used somewhere.
                used.contains(&dest)
            } else {
                // No destination (Store, RcInc, RcDec) — always keep.
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
    for block in &func.blocks {
        for inst in &block.insts {
            if let Inst::Const(dest, ty, bits) = inst {
                consts.insert(*dest, (*ty, *bits));
            }
        }
    }

    let mut changed = false;
    for block in &mut func.blocks {
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

    for block in &func.blocks {
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

    // Rewrite all operand references.
    for block in &mut func.blocks {
        for inst in &mut block.insts {
            rewrite_operands(inst, &resolved);
        }
        rewrite_terminator_operands(&mut block.terminator, &resolved);
    }

    // Remove the no-op instructions (they're now unused after rewriting).
    true // DCE will clean them up on the next iteration.
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
            | Inst::StaticRef(..)
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
                BinaryOp::Eq => return Some((ScalarType::Bool, u64::from(l == r))),
                BinaryOp::Neq => return Some((ScalarType::Bool, u64::from(l != r))),
                BinaryOp::Lt => return Some((ScalarType::Bool, u64::from(l < r))),
                BinaryOp::Le => return Some((ScalarType::Bool, u64::from(l <= r))),
                BinaryOp::Gt => return Some((ScalarType::Bool, u64::from(l > r))),
                BinaryOp::Ge => return Some((ScalarType::Bool, u64::from(l >= r))),
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
                BinaryOp::Eq => return Some((ScalarType::Bool, u64::from(lbits == rbits))),
                BinaryOp::Neq => return Some((ScalarType::Bool, u64::from(lbits != rbits))),
                BinaryOp::Lt => return Some((ScalarType::Bool, u64::from(lbits < rbits))),
                BinaryOp::Le => return Some((ScalarType::Bool, u64::from(lbits <= rbits))),
                BinaryOp::Gt => return Some((ScalarType::Bool, u64::from(lbits > rbits))),
                BinaryOp::Ge => return Some((ScalarType::Bool, u64::from(lbits >= rbits))),
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

fn rewrite_operands(inst: &mut Inst, map: &std::collections::HashMap<Value, Value>) {
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

fn rewrite_terminator_operands(
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
        Terminator::None => {}
    }
}
