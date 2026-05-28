//! `LoweredValue` — what a lowered expression produces.
//!
//! Source-level scalar types lower to `Single(v)` — one SSA Value.
//! Tuple and record types lower to `Multi(vs)` — N parallel SSA
//! Values, one per slot in the tuple's / record's decomposed shape.
//! No heap object exists for the aggregate; the slots are register-
//! resident.
//!
//! Consumers that only handle scalars (BinOp, scalar Call args, ...)
//! call `into_single`, which materializes any in-flight Multi to a
//! heap pointer by emitting `Alloc + Store + Store + ...`. Most
//! call sites land here today.
//!
//! Consumers that understand decomposed shapes (field access,
//! destructure, multi-value Return, multi-slot Call args) inspect
//! `Multi` directly and consume the slot Values without going through
//! a heap round-trip.

use crate::ssa::Value;

#[derive(Debug, Clone)]
pub(super) enum LoweredValue {
    /// A single SSA Value. Scalars and (legacy) heap-pointers to
    /// aggregates land here.
    Single(Value),
    /// N parallel SSA Values, one per decomposed slot. Tuple and
    /// record literals produce this when their use context can
    /// consume the slots directly.
    Multi(Vec<Value>),
}

impl LoweredValue {
    /// Wrap a single Value.
    pub(super) fn single(v: Value) -> Self {
        Self::Single(v)
    }
}
