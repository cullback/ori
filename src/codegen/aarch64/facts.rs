//! Forward dataflow over SSA Values, computing what we statically
//! know about each Value **at codegen time** — i.e. facts that aren't
//! representable at the SSA layer because they're about machine-model
//! artifacts (64-bit register bit patterns, future allocation-site
//! dispatch for free-helper emission).
//!
//! The lattice deliberately does NOT carry facts that the SSA can
//! already reason about (constant propagation, static-ref provenance):
//! those are SSA-to-SSA equivalence rewrites and live in `src/opt/`
//! where every downstream consumer benefits. See CLAUDE.md's
//! "Where optimizations go" rule.
//!
//!   `Bottom`            - unreachable (meet identity).
//!   `KnownZeroHigh(N)`  - the value's top N MSBs are proven zero.
//!                         Lets `emit_store` skip the narrow op when
//!                         the source already fits.
//!   `Const(bits)`       - kept ONLY as a derivation source for
//!                         `KnownZeroHigh` (small consts have leading
//!                         zeros). NOT consumed for const-prop — that
//!                         already happened in `opt/const_fold`.
//!   `Top`               - unknown.

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
    /// Known bit pattern. Carried because `Const(c)` implies
    /// `c.leading_zeros()` zero high bits — used as a derivation
    /// source for `KnownZeroHigh`. NOT consumed for const-folding;
    /// that's done at the SSA layer by `opt/const_fold`.
    Const(u64),
    /// The value's top `bits` MSBs are proven zero.
    KnownZeroHigh(u8),
    Top,
}

impl Facts {
    /// Lattice meet (greatest lower bound). Used at block joins to
    /// combine facts from multiple incoming edges.
    #[must_use]
    pub fn meet(self, other: Self) -> Self {
        use Facts::{Bottom, Const, KnownZeroHigh, Top};
        match (self, other) {
            (Bottom, x) | (x, Bottom) => x,
            (Top, _) | (_, Top) => Top,
            (Const(a), Const(b)) if a == b => Const(a),
            (KnownZeroHigh(a), KnownZeroHigh(b)) => KnownZeroHigh(a.min(b)),
            (Const(c), KnownZeroHigh(k)) | (KnownZeroHigh(k), Const(c)) => {
                let cz = c.leading_zeros() as u8;
                KnownZeroHigh(cz.min(k))
            }
            (Const(a), Const(b)) => {
                // Different consts degrade to the weaker
                // KnownZeroHigh bound that subsumes both.
                let za = a.leading_zeros() as u8;
                let zb = b.leading_zeros() as u8;
                KnownZeroHigh(za.min(zb))
            }
        }
    }

    /// How many top bits are proven zero. Used by emit-time consumers
    /// to decide whether the per-type narrowing op is necessary.
    #[must_use]
    pub fn known_zero_high_bits(self) -> u8 {
        match self {
            Self::Bottom => 64, // unreachable — any narrowing trivially holds
            Self::Const(c) => c.leading_zeros() as u8,
            Self::KnownZeroHigh(n) => n,
            Self::Top => 0,
        }
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

/// Width-implied `KnownZeroHigh` for a scalar type. After a load /
/// cast / narrow store, the high bits are zero per the SSA's
/// 8-byte-slot zero-pad invariant.
fn known_zero_high_for_type(ty: crate::ssa::ScalarType) -> u8 {
    use crate::ssa::ScalarType;
    match ty {
        ScalarType::U8 | ScalarType::I8 => 56,
        ScalarType::U16 | ScalarType::I16 => 48,
        ScalarType::U32 | ScalarType::I32 => 32,
        _ => 0,
    }
}

/// Per-instruction transfer function. Returns one `Facts` per dest.
fn transfer(
    inst: &Inst,
    facts: &HashMap<usize, Facts>,
    lookup: &impl Fn(Value, &HashMap<usize, Facts>) -> Facts,
) -> Vec<Facts> {
    use crate::ssa::ScalarType;
    match inst {
        Inst::Const(_, bits) => vec![Facts::Const(*bits)],
        Inst::StaticRef(_, _) => vec![Facts::Top], // tracked at SSA layer (Ptr type + retype_statics)
        Inst::BinOp(_, op, l, r) => {
            let lf = lookup(*l, facts);
            let rf = lookup(*r, facts);
            match (lf, rf) {
                (Facts::Const(a), Facts::Const(b)) => vec![eval_binop(*op, a, b)],
                // Comparisons always produce 0 or 1 regardless of
                // operand facts (cset writes the full reg to 0/1).
                _ if matches!(
                    op,
                    BinaryOp::Eq | BinaryOp::Neq | BinaryOp::Lt | BinaryOp::Le
                        | BinaryOp::Gt | BinaryOp::Ge
                ) => vec![Facts::KnownZeroHigh(63)],
                // Arithmetic on narrow types in our 64-bit register
                // model CAN overflow into the upper 32 bits. Don't
                // claim KZH from declared type — that would let
                // emit_store skip a needed narrowing.
                _ => vec![Facts::Top],
            }
        }
        Inst::Cast(_, src) | Inst::BitCast(_, src) => {
            // Bit-preserving copy in our register model — fact flows
            // through unchanged. The dest type's narrowness is
            // enforced at emit_store time when needed.
            vec![lookup(*src, facts)]
        }
        Inst::Load(dest, _, _) | Inst::LoadDyn(dest, _, _) => {
            // Loads from 8-byte slots return the slot's stored value.
            // emit_store always narrows on the *previous* write, so
            // the slot's high bits are guaranteed zero for narrow
            // dest types — the loaded value carries that KZH.
            let zh = known_zero_high_for_type(dest.ty);
            if zh > 0 {
                vec![Facts::KnownZeroHigh(zh)]
            } else {
                vec![Facts::Top]
            }
        }
        // Producers we can't (yet) summarize. Their results go to
        // Top — emit_store will narrow if needed.
        Inst::Alloc(..) | Inst::AllocDyn(..)
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

    /// Lattice meet: `Bottom` is identity, `Top` absorbs, equal
    /// elements collapse, unequal-but-comparable degrades to the
    /// weakest fact that subsumes both (`KnownZeroHigh` when both
    /// arms are scalar).
    #[test]
    fn meet_lattice_laws() {
        // Bottom = identity.
        assert_eq!(Facts::Bottom.meet(Facts::Const(3)), Facts::Const(3));
        assert_eq!(Facts::Const(3).meet(Facts::Bottom), Facts::Const(3));
        // Top absorbs.
        assert_eq!(Facts::Top.meet(Facts::Const(3)), Facts::Top);
        // Equal elements collapse.
        assert_eq!(Facts::Const(3).meet(Facts::Const(3)), Facts::Const(3));
        // Different consts: degrade to KnownZeroHigh of the lower
        // bound (3 has 62 leading zeros, 4 has 61 → meet is 61).
        assert_eq!(Facts::Const(3).meet(Facts::Const(4)), Facts::KnownZeroHigh(61));
        // Const + KnownZeroHigh: take the looser.
        assert_eq!(
            Facts::Const(3).meet(Facts::KnownZeroHigh(56)),
            Facts::KnownZeroHigh(56),
        );
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

    /// `Load(U8)` carries `KnownZeroHigh(56)` — the slot was narrowed
    /// when stored, so loads inherit the narrow property.
    #[test]
    fn load_u8_known_zero_high() {
        let v_ptr = val(0, ScalarType::RcPtr);
        let v_byte = val(1, ScalarType::U8);
        let block = Block {
            params: vec![],
            insts: vec![Inst::Load(v_byte, v_ptr, 0)],
            terminator: Terminator::Return(vec![v_byte]),
        };
        let mut blocks = BTreeMap::new();
        blocks.insert(BlockId(0), block);
        let func = Function {
            name: "test".to_string(),
            params: vec![v_ptr],
            blocks,
            return_type: vec![ScalarType::U8],
            entry: BlockId(0),
            next_block: 1,
        };

        let f = analyze(&func);
        assert_eq!(f[&v_byte.id], Facts::KnownZeroHigh(56));
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
