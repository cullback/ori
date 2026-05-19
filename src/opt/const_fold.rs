//! Constant folding for `BinOp(Const, Const)` → `Const`.
//!
//! Walks every block once, replacing any BinOp whose operands resolve
//! to known constants with a Const carrying the folded result.

use std::collections::HashMap;

use crate::ssa::instruction::{BinaryOp, Inst, ScalarType, Value};
use crate::ssa::Function;

pub fn run(func: &mut Function) -> bool {
    // Map from Value → (ScalarType, bits) for known constants.
    let mut consts: HashMap<Value, (ScalarType, u64)> = HashMap::new();
    for block in func.blocks.values() {
        for inst in &block.insts {
            if let Inst::Const(dest, bits) = inst {
                consts.insert(*dest, (dest.ty, *bits));
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
                        *inst = Inst::Const(*dest, result.1);
                        changed = true;
                    }
                }
            }
        }
    }
    changed
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
                BinaryOp::And => l & r,
                BinaryOp::Or => l | r,
                BinaryOp::Xor => l ^ r,
                BinaryOp::Shl => l.wrapping_shl(r as u32),
                BinaryOp::Shr => l.wrapping_shr(r as u32),
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
                BinaryOp::And => lbits & rbits,
                BinaryOp::Or => lbits | rbits,
                BinaryOp::Xor => lbits ^ rbits,
                BinaryOp::Shl => lbits.wrapping_shl(rbits as u32),
                BinaryOp::Shr => lbits.wrapping_shr(rbits as u32),
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
        ScalarType::I32 => {
            let l = lbits as i32;
            let r = rbits as i32;
            let result = match op {
                BinaryOp::Add => l.checked_add(r)? as u64,
                BinaryOp::Sub => l.checked_sub(r)? as u64,
                BinaryOp::Mul => l.checked_mul(r)? as u64,
                BinaryOp::Div if r != 0 => l.checked_div(r)? as u64,
                BinaryOp::Rem if r != 0 => l.checked_rem(r)? as u64,
                BinaryOp::And => (l & r) as u64,
                BinaryOp::Or => (l | r) as u64,
                BinaryOp::Xor => (l ^ r) as u64,
                BinaryOp::Shl => l.wrapping_shl(r as u32) as u64,
                BinaryOp::Shr => l.wrapping_shr(r as u32) as u64,
                BinaryOp::Eq => return Some((ScalarType::U8, u64::from(l == r))),
                BinaryOp::Neq => return Some((ScalarType::U8, u64::from(l != r))),
                BinaryOp::Lt => return Some((ScalarType::U8, u64::from(l < r))),
                BinaryOp::Le => return Some((ScalarType::U8, u64::from(l <= r))),
                BinaryOp::Gt => return Some((ScalarType::U8, u64::from(l > r))),
                BinaryOp::Ge => return Some((ScalarType::U8, u64::from(l >= r))),
                _ => return None,
            };
            Some((ScalarType::I32, result))
        }
        ScalarType::U8 => {
            let l = lbits as u8;
            let r = rbits as u8;
            let result = match op {
                BinaryOp::Add => u64::from(l.wrapping_add(r)),
                BinaryOp::Sub => u64::from(l.wrapping_sub(r)),
                BinaryOp::And => u64::from(l & r),
                BinaryOp::Or => u64::from(l | r),
                BinaryOp::Xor => u64::from(l ^ r),
                BinaryOp::Shl => u64::from(l.wrapping_shl(u32::from(r))),
                BinaryOp::Shr => u64::from(l.wrapping_shr(u32::from(r))),
                BinaryOp::Eq => return Some((ScalarType::U8, u64::from(l == r))),
                BinaryOp::Neq => return Some((ScalarType::U8, u64::from(l != r))),
                _ => return None,
            };
            Some((ScalarType::U8, result))
        }
        ScalarType::U32 => {
            let l = lbits as u32;
            let r = rbits as u32;
            let result = match op {
                BinaryOp::Add => u64::from(l.wrapping_add(r)),
                BinaryOp::Sub => u64::from(l.wrapping_sub(r)),
                BinaryOp::Mul => u64::from(l.wrapping_mul(r)),
                BinaryOp::Div if r != 0 => u64::from(l / r),
                BinaryOp::Rem if r != 0 => u64::from(l % r),
                BinaryOp::And => u64::from(l & r),
                BinaryOp::Or => u64::from(l | r),
                BinaryOp::Xor => u64::from(l ^ r),
                BinaryOp::Shl => u64::from(l.wrapping_shl(r)),
                BinaryOp::Shr => u64::from(l.wrapping_shr(r)),
                BinaryOp::Eq => return Some((ScalarType::U8, u64::from(l == r))),
                BinaryOp::Neq => return Some((ScalarType::U8, u64::from(l != r))),
                BinaryOp::Lt => return Some((ScalarType::U8, u64::from(l < r))),
                BinaryOp::Le => return Some((ScalarType::U8, u64::from(l <= r))),
                BinaryOp::Gt => return Some((ScalarType::U8, u64::from(l > r))),
                BinaryOp::Ge => return Some((ScalarType::U8, u64::from(l >= r))),
                _ => return None,
            };
            Some((ScalarType::U32, result))
        }
        _ => None,
    }
}
