//! Fuse adjacent `RcInc(v)` / `RcDec(v)` pairs within a block.
//!
//! The bracket around a use of `v` exists to keep `v` alive even if
//! a parent object gets decremented in between (Perceus-style "keep
//! loaded child alive across parent's death"). Removing the bracket
//! is only safe if nothing between them can drop `v`'s refcount —
//! specifically, no `Reset` or `RcDec` of *any* value (either could
//! cascade-free `v` via a child slot), and no matching op on `v`
//! itself (another observation).

use crate::ssa::Module;
use crate::ssa::instruction::Inst;

pub fn run(module: &mut Module) {
    for func in module.functions.values_mut() {
        for (_, block) in &mut func.blocks {
            loop {
                if !fuse_one_pair(&mut block.insts) {
                    break;
                }
            }
        }
    }
}

/// Find and remove one rc_inc/rc_dec pair. Returns true if a pair
/// was removed.
fn fuse_one_pair(insts: &mut Vec<Inst>) -> bool {
    for i in 0..insts.len() {
        let (is_inc, v) = match &insts[i] {
            Inst::RcInc(v) => (true, *v),
            Inst::RcDec(v) => (false, *v),
            _ => continue,
        };
        let target = if is_inc { Inst::RcDec(v) } else { Inst::RcInc(v) };
        for j in (i + 1)..insts.len() {
            let is_match = match (&insts[j], &target) {
                (Inst::RcInc(a), Inst::RcInc(b)) | (Inst::RcDec(a), Inst::RcDec(b)) => a == b,
                _ => false,
            };
            if is_match {
                insts.remove(j);
                insts.remove(i);
                return true;
            }
            // Any op that can lower v's refcount (directly or via a
            // parent's child-slot cascade) invalidates the bracket.
            // Another inc/dec on v also counts as an observation.
            match &insts[j] {
                Inst::Reset(..) | Inst::RcDec(_) => break,
                Inst::RcInc(w) if *w == v => break,
                _ => {}
            }
        }
    }
    false
}
