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

use crate::ast::BinOp as AstBinOp;
use crate::symbol::SymbolId;
use crate::types::engine::Type;

/// Field identifier within a record. Reuses the AST representation;
/// fields are interned strings during inference.
pub type FieldId = String;

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
    /// Each binder is either a fresh symbol (introducing a binding
    /// for the arm body) or — represented by an unused symbol — a
    /// wildcard. After flatten, all fields are at this binding level.
    Constructor { tag: TagId, binders: Vec<SymbolId> },
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
#[derive(Debug, Clone)]
pub struct MatchArm {
    pub pattern: Pattern,
    pub body: Expr,
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
    /// `target` always resolves to a top-level `SymbolId`; there's no
    /// `Lam` node and no indirect call.
    App {
        target: SymbolId,
        args: Vec<Expr>,
        ty: Type,
    },

    /// `Let(binder, value, body)` — bind `value` to `binder` for the
    /// scope of `body`. The bound variable's type is on the binder's
    /// `Var` references; the `Let` itself takes the body's type.
    Let {
        binder: SymbolId,
        value: Box<Expr>,
        body: Box<Expr>,
        ty: Type,
    },

    /// `Match(scrutinee, arms, type)` — non-recursive case analysis
    /// on a tag union. Distinct from `Cata` because not every case-of
    /// is a fold (`Maybe`, `Result`, single-variant unions are
    /// non-recursive). Every arm has the same `ty`.
    Match {
        scrutinee: Box<Expr>,
        arms: Vec<MatchArm>,
        ty: Type,
    },

    /// `Cata(alg, init, target)` — structural recursion over an
    /// inductive value. **The only iteration primitive in Core.**
    /// `alg` is the step function (a `SymbolId` of a lifted top-level
    /// after lambda-lift); `init` is the initial accumulator; `target`
    /// is the inductive value being consumed. Type is `init`'s type
    /// (folds always produce the accumulator's type).
    ///
    /// Generic over the inductive type. Lists, trees, user-defined
    /// inductives all use the same node — the `target`'s type tells
    /// us which inductive we're folding over.
    Cata {
        alg: SymbolId,
        init: Box<Expr>,
        target: Box<Expr>,
        ty: Type,
    },

    /// `Con(tag, args, type)` — tag-union constructor. Explicit, not
    /// folded into `App` — keeps `Match(Con(t, args), arms)` as a
    /// syntactic rewrite (`case-of-known-constructor`).
    Con {
        tag: TagId,
        args: Vec<Expr>,
        ty: Type,
    },

    /// `Record(fields, type)` — non-tagged aggregate. Distinct from
    /// `Con` because there's no alternative branch — records aren't
    /// pattern-matched against multiple constructors.
    Record {
        fields: Vec<(FieldId, Expr)>,
        ty: Type,
    },

    /// `BinOp(op, lhs, rhs, type)` — scalar arithmetic / comparison /
    /// bitwise / boolean operator. **Not** modeled as `App` to an
    /// intrinsic symbol — scalar primitives sit outside the algebraic
    /// rewrite system (fusion laws don't touch them) and `App` should
    /// mean "call a user or library function." Treating binops as App
    /// would force an intrinsic-symbol registry for no payoff.
    BinOp {
        op: AstBinOp,
        lhs: Box<Expr>,
        rhs: Box<Expr>,
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
            | Self::Record { ty, .. }
            | Self::BinOp { ty, .. } => ty,
        }
    }
}
