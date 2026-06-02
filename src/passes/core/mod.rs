//! Core IR — algebraic-rewriting layer between the typed AST and SSA.
//!
//! See `notes/core-ir.md` for the design rationale, what the language
//! properties unlock, and the empirical gate that justifies adding
//! rules incrementally.
//!
//! ## Eight primitives
//!
//! Post-lambda-lift, post-mono, typed, direct-style. Every primitive
//! has a corresponding algebraic-rewrite home — that's the test for
//! whether the IR is "right" vs carrying dead structure.
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
//! ## Status
//!
//! Skeleton — types and module wiring only. AST→Core lowering and
//! Core→SSA lowering follow in subsequent commits, alongside the
//! first fusion rule (`Cata(f, z, Map(g, xs)) → Cata(λacc x. f acc (g x), z, xs)`)
//! and a benchmark that measures the optimization ceiling on a real
//! program.

pub mod expr;
pub mod lower;
