//! Core IR — algebraic-rewriting layer between the typed AST and SSA.
//!
//! See `notes/core-ir.md` for the design rationale, what the language
//! properties unlock, and the empirical gate that justifies adding
//! rules incrementally.
//!
//! ## Primitives
//!
//! Post-lambda-lift, post-mono, typed, direct-style. Eight
//! **structural** primitives — each carries an algebraic rewrite
//! home, the test for whether the IR earns its shape:
//!
//! - `Var` — variable reference
//! - `Lit` — scalar literal
//! - `App` — first-order call to a known top-level function
//! - `Let` — `let x = e1 in e2`
//! - `Match` — non-recursive case analysis on tag unions
//! - `Cata` — structural recursion (the **only** iteration primitive)
//! - `Con` — tag-union constructor
//! - `Record` — non-tagged aggregate
//!
//! Plus one **scalar** primitive, `BinOp`, for arithmetic / comparison
//! / bitwise / boolean operators. Scalar ops sit outside the
//! algebraic rewrite system (fusion never touches them); they could
//! be modeled as `App` to intrinsic symbols, but that adds plumbing
//! for no payoff. Treating them as a dedicated node keeps `App` to
//! mean "call a user or library function," which is more honest.
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
