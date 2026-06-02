//! Forward dataflow over SSA Values, computing what we statically
//! know about each Value at codegen time.
//!
//! The lattice is intentionally small (4 elements) so this file can
//! grow without re-architecting. Each element subsumes an existing
//! pattern or unblocks an upcoming feature; consumers in `lower_main`
//! consult facts at emit-time rather than re-deriving knowledge from
//! the SSA structure.
//!
//!   `Bottom`          - unreachable (meet identity).
//!   `Const(bits)`     - subsumes parts of `const_fold` at emit time.
//!   `StaticRef(idx)`  - unblocks rc-skip for the upcoming RC runtime;
//!                       lets us drop the sentinel-rc convention.
//!   `Top`             - unknown.
//!
//! Stage 1 does not propagate facts through `Call`, `Load`, or
//! `LoadDyn` (all yield `Top`); those need either summaries or richer
//! lattice elements (`HeapAlloc(site)`, `KnownZeroHigh`, etc.) which
//! land in later stages as use cases appear.

#![allow(
    clippy::cast_possible_truncation,
    clippy::cast_possible_wrap,
    clippy::cast_sign_loss,
    clippy::match_same_arms,
    clippy::missing_const_for_fn,
    clippy::missing_assert_message,
    clippy::pub_with_shorthand,
    dead_code
)]

use std::collections::HashMap;

use crate::ssa::{BinaryOp, Function, Inst, Terminator, Value};

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Facts {
    Bottom,
    Const(u64),
    StaticRef(usize),
    Top,
}

impl Facts {
    /// Lattice meet (greatest lower bound). Used at block joins to
    /// combine facts from multiple incoming edges. Conservative: if
    /// inputs disagree, the result is `Top`.
    #[must_use]
    pub fn meet(self, other: Self) -> Self {
        use Facts::{Bottom, Const, StaticRef, Top};
        match (self, other) {
            (Bottom, x) | (x, Bottom) => x,
            (Top, _) | (_, Top) => Top,
            (Const(a), Const(b)) if a == b => Const(a),
            (StaticRef(a), StaticRef(b)) if a == b => StaticRef(a),
            _ => Top,
        }
    }

    #[must_use]
    pub fn as_const(self) -> Option<u64> {
        if let Self::Const(v) = self { Some(v) } else { None }
    }

    #[must_use]
    pub fn as_static_ref(self) -> Option<usize> {
        if let Self::StaticRef(idx) = self { Some(idx) } else { None }
    }
}

/// Evaluate a `BinOp` over `Const` operands, returning `Top` for ops
/// that don't fold (comparisons returning a boolean still fold —
/// they're representable as `Const(0)` / `Const(1)`).
#[must_use]
fn eval_binop(op: BinaryOp, a: u64, b: u64) -> Facts {
    let r = match op {
        BinaryOp::Add => a.wrapping_add(b),
        BinaryOp::Sub => a.wrapping_sub(b),
        BinaryOp::Mul => a.wrapping_mul(b),
        BinaryOp::And => a & b,
        BinaryOp::Or => a | b,
        BinaryOp::Xor => a ^ b,
        BinaryOp::Shl => a.wrapping_shl(b as u32),
        BinaryOp::Shr => a.wrapping_shr(b as u32),
        BinaryOp::Eq => u64::from(a == b),
        BinaryOp::Neq => u64::from(a != b),
        BinaryOp::Lt => u64::from((a as i64) < (b as i64)),
        BinaryOp::Le => u64::from((a as i64) <= (b as i64)),
        BinaryOp::Gt => u64::from((a as i64) > (b as i64)),
        BinaryOp::Ge => u64::from((a as i64) >= (b as i64)),
        // Div/Rem need divisor != 0 check; conservative for now.
        BinaryOp::Div | BinaryOp::Rem if b == 0 => return Facts::Top,
        BinaryOp::Div => a.wrapping_div(b),
        BinaryOp::Rem => a.wrapping_rem(b),
        BinaryOp::Max => a.max(b),
    };
    Facts::Const(r)
}

/// Compute facts for every Value in `func`. Iterates a forward
/// dataflow worklist to fixpoint. For our SSA shapes (lambda-lifted,
/// no general recursion) this typically converges in 1–2 passes.
#[must_use]
pub fn analyze(func: &Function) -> HashMap<usize, Facts> {
    let mut facts: HashMap<usize, Facts> = HashMap::new();

    // Conservative initial state: every Value is `Bottom` (unreachable)
    // until we see its definition. Function params start at `Top` —
    // we don't know what callers will pass.
    for p in &func.params {
        facts.insert(p.id, Facts::Top);
    }
    for block in func.blocks.values() {
        for p in &block.params {
            facts.insert(p.id, Facts::Bottom);
        }
        for inst in &block.insts {
            for d in inst.dests() {
                facts.insert(d.id, Facts::Bottom);
            }
        }
    }

    let lookup = |v: Value, f: &HashMap<usize, Facts>| -> Facts {
        f.get(&v.id).copied().unwrap_or(Facts::Top)
    };

    // Worklist fixpoint. Simple driver — re-scan all blocks until no
    // facts change. For the SSA sizes we see (≤ a few hundred values
    // per function) this is fine; later stages can switch to a proper
    // worklist if it shows up in profiles.
    let mut changed = true;
    while changed {
        changed = false;
        for block in func.blocks.values() {
            for inst in &block.insts {
                let new_fact = transfer(inst, &facts, &lookup);
                for (d, fact) in inst.dests().iter().zip(new_fact.iter()) {
                    let prev = facts.get(&d.id).copied().unwrap_or(Facts::Bottom);
                    if prev != *fact {
                        facts.insert(d.id, *fact);
                        changed = true;
                    }
                }
            }
        }
        // Propagate edge arguments into block-param facts (meet over
        // all incoming edges).
        for src_block in func.blocks.values() {
            for edge in src_block.terminator.successors() {
                let dest_block = &func.blocks[&edge.target];
                for (arg, param) in edge.args.iter().zip(&dest_block.params) {
                    let arg_fact = lookup(*arg, &facts);
                    let prev = facts.get(&param.id).copied().unwrap_or(Facts::Bottom);
                    let merged = prev.meet(arg_fact);
                    if prev != merged {
                        facts.insert(param.id, merged);
                        changed = true;
                    }
                }
            }
        }
    }

    facts
}

/// Per-instruction transfer function. Returns one `Facts` per dest.
fn transfer(
    inst: &Inst,
    facts: &HashMap<usize, Facts>,
    lookup: &impl Fn(Value, &HashMap<usize, Facts>) -> Facts,
) -> Vec<Facts> {
    match inst {
        Inst::Const(_, bits) => vec![Facts::Const(*bits)],
        Inst::StaticRef(_, idx) => vec![Facts::StaticRef(*idx)],
        Inst::BinOp(_, op, l, r) => {
            let lf = lookup(*l, facts);
            let rf = lookup(*r, facts);
            match (lf, rf) {
                (Facts::Const(a), Facts::Const(b)) => vec![eval_binop(*op, a, b)],
                _ => vec![Facts::Top],
            }
        }
        Inst::Cast(_, src) | Inst::BitCast(_, src) => {
            // Bit-preserving for our 64-bit register model — if source
            // is a known const, the cast doesn't change its low bits.
            // (Narrowing semantics are enforced by emit_store's mask;
            // a Const that was wider than dest.ty would already have
            // been folded with the appropriate width.)
            vec![lookup(*src, facts)]
        }
        // Producers we can't (yet) summarize.
        Inst::Alloc(..) | Inst::AllocDyn(..) | Inst::Load(..) | Inst::LoadDyn(..)
        | Inst::Call { .. } | Inst::CowStore(..) | Inst::CowStoreDyn(..)
        | Inst::CowResizeDyn(..) | Inst::CowMoveOut { .. } => {
            inst.dests().iter().map(|_| Facts::Top).collect()
        }
        // No-result.
        Inst::Store(..) | Inst::StoreDyn(..) | Inst::RcInc(_) | Inst::RcDec(_) => vec![],
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ssa::{Block, BlockId, ScalarType};
    use std::collections::BTreeMap;

    fn val(id: usize, ty: ScalarType) -> Value {
        Value { id, ty }
    }

    /// Lattice meet behaves like a lattice: `Bottom` is identity,
    /// `Top` absorbs, equal elements collapse, unequal ⟶ `Top`.
    #[test]
    fn meet_lattice_laws() {
        assert_eq!(Facts::Bottom.meet(Facts::Const(3)), Facts::Const(3));
        assert_eq!(Facts::Const(3).meet(Facts::Bottom), Facts::Const(3));
        assert_eq!(Facts::Top.meet(Facts::Const(3)), Facts::Top);
        assert_eq!(Facts::Const(3).meet(Facts::Const(3)), Facts::Const(3));
        assert_eq!(Facts::Const(3).meet(Facts::Const(4)), Facts::Top);
        assert_eq!(Facts::StaticRef(0).meet(Facts::StaticRef(0)), Facts::StaticRef(0));
        assert_eq!(Facts::StaticRef(0).meet(Facts::StaticRef(1)), Facts::Top);
        assert_eq!(Facts::Const(3).meet(Facts::StaticRef(0)), Facts::Top);
    }

    /// `Const(2) + Const(3)` folds to `Const(5)`.
    #[test]
    fn binop_const_const_folds() {
        let v_a = val(0, ScalarType::U64);
        let v_b = val(1, ScalarType::U64);
        let v_sum = val(2, ScalarType::U64);

        let block = Block {
            params: vec![],
            insts: vec![
                Inst::Const(v_a, 2),
                Inst::Const(v_b, 3),
                Inst::BinOp(v_sum, BinaryOp::Add, v_a, v_b),
            ],
            terminator: Terminator::Return(vec![v_sum]),
        };
        let mut blocks = BTreeMap::new();
        blocks.insert(BlockId(0), block);

        let func = Function {
            name: "test".to_string(),
            params: vec![],
            blocks,
            return_type: vec![ScalarType::U64],
            entry: BlockId(0),
            next_block: 1,
        };

        let f = analyze(&func);
        assert_eq!(f[&v_a.id], Facts::Const(2));
        assert_eq!(f[&v_b.id], Facts::Const(3));
        assert_eq!(f[&v_sum.id], Facts::Const(5));
    }

    /// `static_ref @7` is tracked as `StaticRef(7)`.
    #[test]
    fn static_ref_tracked() {
        let v = val(0, ScalarType::Ptr);
        let block = Block {
            params: vec![],
            insts: vec![Inst::StaticRef(v, 7)],
            terminator: Terminator::Return(vec![v]),
        };
        let mut blocks = BTreeMap::new();
        blocks.insert(BlockId(0), block);
        let func = Function {
            name: "test".to_string(),
            params: vec![],
            blocks,
            return_type: vec![ScalarType::Ptr],
            entry: BlockId(0),
            next_block: 1,
        };

        let f = analyze(&func);
        assert_eq!(f[&v.id], Facts::StaticRef(7));
    }

    /// A `BinOp` with one `Top` operand stays `Top` — facts are
    /// conservative across unknown inputs.
    #[test]
    fn binop_with_unknown_is_top() {
        let v_param = val(0, ScalarType::U64);
        let v_k = val(1, ScalarType::U64);
        let v_r = val(2, ScalarType::U64);

        let block = Block {
            params: vec![],
            insts: vec![
                Inst::Const(v_k, 5),
                Inst::BinOp(v_r, BinaryOp::Add, v_param, v_k),
            ],
            terminator: Terminator::Return(vec![v_r]),
        };
        let mut blocks = BTreeMap::new();
        blocks.insert(BlockId(0), block);
        let func = Function {
            name: "test".to_string(),
            params: vec![v_param],
            blocks,
            return_type: vec![ScalarType::U64],
            entry: BlockId(0),
            next_block: 1,
        };

        let f = analyze(&func);
        assert_eq!(f[&v_param.id], Facts::Top); // function params start as Top
        assert_eq!(f[&v_k.id], Facts::Const(5));
        assert_eq!(f[&v_r.id], Facts::Top);
    }
}
