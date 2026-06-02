//! Core IR — algebraic-rewriting layer between the typed AST and SSA.
//!
//! See `notes/core-ir.md` for the design rationale, what the language
//! properties unlock, and the empirical gate that justifies adding
//! rules incrementally.
//!
//! ## Primitives
//!
//! Post-lambda-lift, post-mono, typed, direct-style. Seven
//! **structural** primitives — each carries an algebraic rewrite
//! home:
//!
//! - `Var` — variable reference (single slot)
//! - `Lit` — scalar literal
//! - `App` — first-order call to a known top-level function
//! - `Let` — `let x = e1 in e2`
//! - `Match` — non-recursive case analysis on tag unions
//! - `Cata` — structural recursion (the **only** iteration primitive)
//! - `Con` — tag-union constructor
//!
//! Plus one **scalar** primitive, `BinOp`, for arithmetic / comparison
//! / bitwise / boolean operators.
//!
//! **No `Record`, `Tuple`, or `FieldAccess` in the IR.** Aggregates
//! are SROA'd at AST→Core: an N-field record/tuple becomes N parallel
//! Core expressions in a slot list. Field access becomes slot picking.
//! See `notes/core-ir.md` for the rationale (algebraic-purity, no-
//! aggregate-identity language property).
//!
//! ## Status
//!
//! Skeleton — types and module wiring only. AST→Core lowering and
//! Core→SSA lowering follow in subsequent commits, alongside the
//! first fusion rule (`Cata(f, z, Map(g, xs)) → Cata(λacc x. f acc (g x), z, xs)`)
//! and a benchmark that measures the optimization ceiling on a real
//! program.

pub mod expr;
pub mod lower;
pub mod to_ssa;
