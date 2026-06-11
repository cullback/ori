//! Core IR expressions — thirteen variants.
//!
//! Direct-style, single-valued throughout, typed at every node,
//! post-monomorphization. See `notes/core-ir.md` for the full
//! spec.

use crate::literal::{Literal, StrLit};
use crate::pattern::Pattern;
use crate::sym::{FnId, LocalId, TagId};
use crate::ty::CoreType;

#[derive(Debug, Clone)]
pub enum Expr {
    // ---- Universal ----
    Var {
        sym: LocalId,
        ty: CoreType,
    },
    Lit {
        value: Literal,
        ty: CoreType,
    },
    /// First-order call to a known top-level target. Builtins
    /// (arithmetic, cast, range) are `App` with builtin `FnId`s
    /// that the lowering layer dispatches inline.
    App {
        target: FnId,
        args: Vec<Expr>,
        ty: CoreType,
    },
    /// Single-binder bind-and-go. Multi-result was always an SSA
    /// ABI concern; with values nesting, the multi-slot machinery
    /// evaporates.
    Let {
        binder: LocalId,
        value: Box<Expr>,
        body: Box<Expr>,
        ty: CoreType,
    },

    // ---- Algebraic structure ----
    /// Non-recursive case analysis. Scrutinee is a single value;
    /// case-of-case and case-of-known-constructor are syntactic.
    Match {
        scrutinee: Box<Expr>,
        arms: Vec<MatchArm>,
        ty: CoreType,
    },
    /// Tag-union constructor. Records and tuples are single-variant
    /// `Con`s; closures are `Con`s with `TagId::Closure(_)`.
    Con {
        tag: TagId,
        args: Vec<Expr>,
        ty: CoreType,
    },
    /// Catamorphism. The only iteration primitive (along with `Gen`).
    Fold {
        kind: FoldKind,
        fold_fn: FnId,
        target: Box<Expr>,
        init: Vec<Expr>,
        captures: Vec<Expr>,
        /// `Some(shape)` when AST→Core verified the body matches
        /// a recognized algebra template; `None` for opaque folds.
        shape: Option<FoldShape>,
        ty: CoreType,
    },
    /// Anamorphism — bounded unfold. `bound` is computed before
    /// the loop; this is what keeps `Gen` total.
    Gen {
        bound: Box<Expr>,
        step_fn: FnId,
        init: Vec<Expr>,
        captures: Vec<Expr>,
        elem_ty: CoreType,
        ty: CoreType,
    },

    // ---- Divergence ----
    /// Explicit crash. The one partial construct in any Ori
    /// program; rewrites treat it as a syntactic barrier.
    Crash {
        msg: StrLit,
        ty: CoreType,
    },

    // ---- Buffer trio (single-valued at Core) ----
    BufLit {
        elements: Vec<Expr>,
        elem_ty: CoreType,
        ty: CoreType,
    },
    /// Bounds-checked load returning `Result<T, OutOfBounds>`-shaped
    /// value. The check is visible to rewrites.
    BufLoad {
        buf: Box<Expr>,
        idx: Box<Expr>,
        ty: CoreType,
    },
    /// Unchecked load — produced by bounds-elimination rewrites
    /// that proved `idx < len`. **Never emitted by AST→Core.**
    BufLoadUnchecked {
        buf: Box<Expr>,
        idx: Box<Expr>,
        ty: CoreType,
    },
    /// `xs.append(y)`. Lowers to `cow_resize_dyn`. FBIP intent at
    /// the variant level.
    BufAppend {
        buf: Box<Expr>,
        val: Box<Expr>,
        ty: CoreType,
    },
    /// `xs.set(i, y)`. Lowers to `cow_store_dyn`. FBIP intent.
    BufSet {
        buf: Box<Expr>,
        idx: Box<Expr>,
        val: Box<Expr>,
        ty: CoreType,
    },
}

#[derive(Debug, Clone)]
pub struct MatchArm {
    pub pattern: Pattern,
    pub guards: Vec<Expr>,
    pub body: Box<Expr>,
    pub is_return: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FoldKind {
    /// `fold_fn` returns `b` directly.
    Total,
    /// `fold_fn` returns `Step(b) = Continue(b) | Break(b)`.
    /// Distinct fusion laws apply.
    EarlyExit,
}

/// Recognized algebra shapes for `Fold`. Closed enum — adding a
/// shape is the same commitment as adding the fusion rules that
/// match on it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FoldShape {
    Map,
    Filter,
    Scan,
    Zip,
    Take,
    Drop,
}

impl Expr {
    /// The result type of this expression.
    #[must_use]
    pub fn ty(&self) -> &CoreType {
        match self {
            Self::Var { ty, .. }
            | Self::Lit { ty, .. }
            | Self::App { ty, .. }
            | Self::Let { ty, .. }
            | Self::Match { ty, .. }
            | Self::Con { ty, .. }
            | Self::Fold { ty, .. }
            | Self::Gen { ty, .. }
            | Self::Crash { ty, .. }
            | Self::BufLit { ty, .. }
            | Self::BufLoad { ty, .. }
            | Self::BufLoadUnchecked { ty, .. }
            | Self::BufAppend { ty, .. }
            | Self::BufSet { ty, .. } => ty,
        }
    }
}
