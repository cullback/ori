//! Core IR expression type and supporting structures.
//!
//! ## Identifiers
//!
//! Core reuses the AST's `SymbolId` for both variables (locals,
//! parameters) and function references. After mono + lambda-lift +
//! reachable-prune, every `SymbolId` resolves to a known top-level
//! definition or a local binding. We don't introduce a separate
//! `VarId`/`FuncId` split — the symbol table already does that work.
//!
//! ## Types
//!
//! Every Core node carries its result type. We use the same `Type`
//! the inference engine produces; by the time we build Core, mono
//! has erased polymorphism, so types are concrete.
//!
//! ## Why direct-style, not ANF
//!
//! ANF (every subexpression named via a `Let`) is cleaner for
//! dataflow but buries the algebraic structure under naming noise.
//! `Map(f, Map(g, xs))` becomes `Let(t, App(map, [g, xs]), App(map, [f, t]))`
//! which obscures the pattern fusion wants to recognize. We keep
//! Core direct-style; ANF normalization happens between Core and
//! SSA if needed.

use crate::ssa::BinaryOp;
use crate::symbol::SymbolId;
use crate::types::engine::Type;

/// Constructor tag — the source name of the variant (`"Cons"`,
/// `"Nil"`, `"Ok"`, `"Err"`, `"True"`, ...). Tag unions are
/// structural in Ori (the tag name identifies the variant within
/// its union), and the inference/lower layers already key on
/// strings, so Core does too. Could be interned later if profile
/// shows it matters.
pub type TagId = String;

/// A scalar literal value. Matches what `ExprKind::IntLit` /
/// `FloatLit` / `StrLit` produce in the AST, but we keep the variant
/// distinction explicit so the Core stays self-describing.
#[derive(Debug, Clone)]
pub enum Literal {
    Int(i64),
    Float(f64),
    Str(Vec<u8>),
}

/// A pattern in a `Match` arm. Restricted to **shallow** patterns —
/// `flatten_patterns` runs before Core, so nested constructor /
/// record / list / tuple patterns have already been desugared into
/// chains of shallow matches.
#[derive(Debug, Clone)]
pub enum Pattern {
    /// `Cons(x, xs)` — a tag-union constructor with field binders.
    /// Each outer entry corresponds to one source-level binder; the
    /// inner Vec holds the slot symbols for that binder. Single-slot
    /// binders (a binder of scalar type, or of an aggregate that
    /// stays heap-resident) have a 1-element inner vec carrying the
    /// AST binder sym directly. Multi-slot binders (e.g. binding
    /// `rest: Lnk` where Lnk decomposes to (tag, payload)) have an
    /// N-element inner vec of minted slot syms — those are what
    /// `ctx.locals` maps the source binder to in `Name` expansion.
    /// A wildcard binder has its `SymbolId` set to `u32::MAX`.
    Constructor { tag: TagId, binders: Vec<Vec<SymbolId>> },
    /// `42` — match a specific integer literal. The scrutinee's
    /// equality with the literal gates the arm.
    IntLit(i64),
    /// `"foo"` — match a specific string literal.
    StrLit(Vec<u8>),
    /// `_` — match anything, bind nothing.
    Wildcard,
    /// `x` (bare name) — match anything, bind to `x`.
    Binding(SymbolId),
}

/// One arm of a `Match` expression.
///
/// `guards` are predicate expressions that must all evaluate to
/// `True` after the pattern matches; an arm with an unsatisfied
/// guard falls through to the next arm. `is_return` flips the arm
/// from "produce a value for the match" to "return this value from
/// the enclosing function" — the `?` operator desugars to a return
/// arm in the `Err` branch.
#[derive(Debug, Clone)]
pub struct MatchArm {
    pub pattern: Pattern,
    pub guards: Vec<Expr>,
    pub body: Expr,
    pub is_return: bool,
}

impl MatchArm {
    /// Bare-arm constructor: pattern + body, no guards, no return.
    /// Most call sites synthesizing arms (And/Or desugar, Is sugar,
    /// the multi-arm Match in If/Match) build this shape; the
    /// guarded / return variants are added by `lower_match_arm`
    /// when reading guards / is_return off the AST arm.
    pub fn plain(pattern: Pattern, body: Expr) -> Self {
        Self { pattern, guards: vec![], body, is_return: false }
    }
}

/// The Core IR expression. Eight primitives — see module docs for
/// the rationale.
#[derive(Debug, Clone)]
pub enum Expr {
    /// `Var(sym, type)` — reference to a binding (local, param, or
    /// top-level value).
    Var {
        sym: SymbolId,
        ty: Type,
    },

    /// `Lit(value, type)` — scalar literal.
    Lit {
        value: Literal,
        ty: Type,
    },

    /// `App(target, args, return_type)` — first-order call to a known
    /// top-level function. After lambda-lift + defunctionalization,
    /// `target` always resolves to a top-level definition; we use the
    /// **mangled display name** (a `String`) rather than `SymbolId`
    /// because the rest of the type system + SSA `Call.target` work
    /// in strings, and several callers (resolved `MethodCall` /
    /// `QualifiedCall`) deliver names directly without a `SymbolId`.
    App {
        target: String,
        args: Vec<Expr>,
        ty: Type,
    },

    /// `Let(binders, value, body)` — bind `value`'s N slots to N
    /// `binders` for the scope of `body`. Single-slot bindings have
    /// `binders.len() == 1`; multi-slot (when `value` is a multi-
    /// result call, payload constructor, etc.) has `binders.len() ==
    /// expand_slots(value.ty).len()`.
    Let {
        binders: Vec<SymbolId>,
        value: Box<Expr>,
        body: Box<Expr>,
        ty: Type,
    },

    /// `Match(scrutinee_slots, scrutinee_ty, arms, type)` — non-
    /// recursive case analysis on a tag union. Distinct from `Cata`
    /// because not every case-of is a fold (`Maybe`, `Result`,
    /// single-variant unions are non-recursive). Every arm has the
    /// same `ty`.
    ///
    /// `scrutinee_slots` is a parallel slot list (length matches
    /// `expand_slots` of the scrutinee's source type): single-slot
    /// scrutinees use a 1-element vec; multi-slot scrutinees (e.g.
    /// matching on a `Maybe` parameter that decomposed to (tag,
    /// payload)) carry both slots. to_ssa flattens this into the
    /// `Value` list it uses to derive `tag_val` / `payload_val`.
    ///
    /// `scrutinee_ty` is the **source-level** type of the scrutinee,
    /// preserved here because the individual slot exprs may carry
    /// per-slot scalar placeholder types (`Con("U64")`,
    /// `Con("__RcPtr")`) that lose the union shape needed for
    /// structural-constructor layout.
    Match {
        scrutinee_slots: Vec<Expr>,
        scrutinee_ty: Type,
        arms: Vec<MatchArm>,
        ty: Type,
    },

    /// `Cata(fold_fn, target, extra_args)` — structural recursion
    /// over an inductive value. The **only iteration primitive in
    /// Core**.
    ///
    /// Represents a call to a fold-shaped recursive function: one
    /// that pattern-matches `target` against the inductive type's
    /// variants and recurses into the recursive fields. After
    /// `fold_lift` runs, every `fold` expression in source has been
    /// rewritten to this shape; AST→Core promotes calls to those
    /// `__fold_N` helpers into `Cata` so that algebraic rewrites
    /// can pattern-match on them.
    ///
    /// `fold_fn` is the mangled function name (matches an SSA
    /// `Call.target`). `target` is the inductive value being
    /// consumed. `extra_args` are the trailing parameters of the
    /// fold function — captured free variables from the original
    /// `fold` expression, plus any accumulator passed alongside the
    /// inductive value.
    ///
    /// At Core→SSA the lowering is identical to an `App` call;
    /// `Cata`'s value lives at the rewrite layer (rules.rs), where
    /// `Cata ∘ Cata` fusion, `Cata ∘ Map → Cata`, `Cata` of a
    /// literal list constant-folding, etc. become syntactic
    /// rewrites instead of SCEV-style reconstruction.
    Cata {
        fold_fn: String,
        /// Parallel slot list for the inductive value. Multi-slot
        /// inductives (Lnk, Tree, Nat — multi-variant payload
        /// unions) decompose to (tag, payload) at the SSA layer
        /// and arrive here as a 2-element vec; single-slot
        /// inductives (Phase E singleton closures with one
        /// capture, or `:=` aliases that scalar_type collapses)
        /// use a 1-element vec.
        target_slots: Vec<Expr>,
        extra_args: Vec<Expr>,
        ty: Type,
    },

    /// `Con(tag, args, type)` — tag-union constructor. Explicit, not
    /// folded into `App` — keeps `Match(Con(t, args), arms)` as a
    /// syntactic rewrite (`case-of-known-constructor`).
    ///
    /// **Records and tuples don't have a Core node.** They're SROA'd
    /// at AST→Core into slot lists (see `lower::lower_expr_slots`).
    /// `Con` stays because it carries a tag — the dispatch needs to
    /// be visible to `Match`.
    Con {
        tag: TagId,
        args: Vec<Expr>,
        ty: Type,
    },

    /// `BinOp(op, lhs, rhs, type)` — scalar arithmetic / comparison /
    /// bitwise / shift / boolean operator. **Not** modeled as `App`
    /// to an intrinsic symbol — scalar primitives sit outside the
    /// algebraic rewrite system (fusion laws don't touch them) and
    /// `App` should mean "call a user or library function."
    ///
    /// Uses the SSA-level `BinaryOp` directly rather than the AST's
    /// narrower `BinOp` so Core can carry bitwise-and / shl / shr —
    /// ops the surface syntax exposes only through `__builtin.*`
    /// intrinsic methods (no infix form).
    BinOp {
        op: BinaryOp,
        lhs: Box<Expr>,
        rhs: Box<Expr>,
        ty: Type,
    },

    /// `ListLit(elements, elem_ty, ty)` — list literal `[a, b, c]`.
    /// Lowers to alloc + N stores + header alloc, matching existing-
    /// lower's convention. Doesn't decompose at SROA (lists are
    /// heap-resident; only their `(len, cap, data)` header decomposes
    /// at function-boundary use, which Core handles via expand_slots).
    /// Each element must be single-slot for now; multi-slot elements
    /// (List of records, etc.) need inlined-element layout support.
    ListLit {
        elements: Vec<Expr>,
        elem_ty: Type,
        ty: Type,
    },

    /// `ProjSlot(source_slots, slot_idx, ty)` — pick one slot out of
    /// a multi-slot value's decomposition. The first leaf primitive
    /// in the List-as-buffer family: `List.len(xs)` lowers to
    /// `ProjSlot(xs.slots, 0, U64)` — the (len, cap, data) trio's
    /// first element. Doesn't participate in algebraic rewrites
    /// (no fusion law touches a header projection); lowers 1:1 to
    /// the SSA `Value` already produced by `source_slots`'s
    /// per-slot lowering.
    ProjSlot {
        source_slots: Vec<Expr>,
        slot_idx: usize,
        ty: Type,
    },
}

impl Expr {
    /// The result type of this expression. Stamped on every node so
    /// type-preserving rewrites are trivial to verify.
    pub fn ty(&self) -> &Type {
        match self {
            Self::Var { ty, .. }
            | Self::Lit { ty, .. }
            | Self::App { ty, .. }
            | Self::Let { ty, .. }
            | Self::Match { ty, .. }
            | Self::Cata { ty, .. }
            | Self::Con { ty, .. }
            | Self::BinOp { ty, .. }
            | Self::ListLit { ty, .. }
            | Self::ProjSlot { ty, .. } => ty,
        }
    }
}
