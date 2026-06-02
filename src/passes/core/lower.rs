//! AST → Core lowering.
//!
//! Translates the post-mono, post-lambda-lift, post-pattern-flattened
//! AST into the Core IR. Each `ExprKind` maps to a Core primitive or
//! to a small Core expression tree:
//!
//! | AST | Core |
//! |---|---|
//! | `IntLit/FloatLit/StrLit` | `Lit` |
//! | `Name` | `Var` (locals) or `App` with 0 args (top-level value refs) |
//! | `Call`, `QualifiedCall`, `MethodCall` | `App` |
//! | `BinOp` | `App` to a builtin (`+`, `-`, ..., are functions in Core) |
//! | `Block(stmts, last)` | nested `Let`s ending in `last` |
//! | `If` | `Match` with bool patterns |
//! | `Fold` | `Cata` |
//! | `Record` | `Record` |
//! | `RecordUpdate` | sequence of `Let` + `Record` with updated fields |
//! | `FieldAccess` | `App` to a field projector |
//! | `Tuple` | `Record` with positional field names |
//! | `ListLit` | nested `Con(Cons, ...)` ending in `Con(Nil)` |
//! | `Is` | `Match` |
//! | `Lambda`, `Closure` | should not appear here (eliminated by lambda passes) |
//!
//! ## Status
//!
//! Skeleton — the type signature is in place; implementation lands
//! incrementally as we need it for the first end-to-end fusion
//! demonstration. We start with a minimal subset (literals,
//! variables, calls, blocks, binops) sufficient to round-trip a
//! tiny test program. Other ExprKinds error out until they're
//! implemented.

use super::expr::Expr;

/// Lower an AST module into Core.
///
/// **Not yet implemented.** Returns an error string for now — the
/// real signature will mirror `lower::lower` once we know what
/// supporting context the Core pass needs.
pub fn lower() -> Result<Vec<Expr>, String> {
    Err("AST→Core lowering not yet implemented".into())
}
