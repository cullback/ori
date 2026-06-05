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
    /// The arm's body as a slot list — one Core `Expr` per slot of
    /// the Match's result type. Multi-slot results (Result, Maybe,
    /// records, Str, List) get N entries; scalar results get 1.
    /// At `to_ssa`, the entries lower to N parallel `Value`s
    /// jumped to the merge block's N block params.
    pub body: Vec<Expr>,
    pub is_return: bool,
}

impl MatchArm {
    /// Bare-arm constructor: single-Expr body (the common case for
    /// arms whose result is single-slot — booleans, scalars,
    /// closure-tag fanouts). Wraps the body in a 1-entry slot list.
    pub fn plain(pattern: Pattern, body: Expr) -> Self {
        Self { pattern, guards: vec![], body: vec![body], is_return: false }
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
        /// Per source-level field, the number of Core args (each
        /// corresponding to one SSA slot) it occupies after the
        /// `Name`-multi-slot flattening that `lower_expr_slots`
        /// performs upstream. `field_slot_counts.iter().sum() ==
        /// args.len()`. `to_ssa` uses this to re-group the flat
        /// args list when materializing a wrapper per source field
        /// in the Con's payload.
        field_slot_counts: Vec<usize>,
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

    /// `BufLoad(buf, idx, ty)` — unchecked indexed load from a
    /// buffer pointer. The leaf primitive backing `List.get`'s
    /// success branch and the only memory-read op Core emits for
    /// the buffer family. Combined with a bounds-check `Match`,
    /// `List.get(xs, i)` desugars to:
    ///
    /// ```text
    /// if i < xs_slots[0]
    ///   then Ok(BufLoad(xs_slots[2], i, T))
    ///   else Err(OutOfBounds)
    /// ```
    ///
    /// Slot picks on a list trio (e.g. `.len`, `.data`) are done by
    /// direct slot-list indexing in `lower_expr_slots` — no Core
    /// node needed since lists are 3-slot SROA'd everywhere internal
    /// to the IR.
    ///
    /// `BufLoad` itself doesn't fuse — it lowers 1:1 to SSA
    /// `load_dyn`.
    BufLoad {
        buf: Box<Expr>,
        idx: Box<Expr>,
        ty: Type,
    },

    /// `ListRange(start, end, ty)` — produces a `(len, cap, data)`
    /// trio whose buffer holds `start, start+1, …, end-1` (or an
    /// empty list when `end <= start`). The leaf primitive backing
    /// `List.range(start, end)`. At `to_ssa` it expands into a
    /// counter-driven fill loop; at the Core layer it stays opaque
    /// so future Ana ∘ Cata → Hylo deforestation can recognize it
    /// as an unfold.
    ///
    /// `ty` is the result `List(U64)` type.
    ListRange {
        start: Box<Expr>,
        end: Box<Expr>,
        ty: Type,
    },

    /// `ListWalk(list_slots, init, target, captures, elem_ty, ty)`
    /// — folds the list under a step function, threading the
    /// accumulator. Currently restricted to the **singleton**
    /// closure case: `target` is the lifted apply function name
    /// resolved at AST→Core time via `mono.singletons` /
    /// `mono.tag_targets`. Non-singleton closures still bail to
    /// existing-lower.
    ///
    /// At `to_ssa` this expands to a counted loop with explicit
    /// block params for the i-counter, accumulator slots, the
    /// (len, data) header, and the captures.
    ///
    /// - `list_slots`: the source list's `(len, cap, data)` trio
    ///   exprs.
    /// - `init`: the initial accumulator value (multi-slot).
    /// - `target`: the direct-call function name (e.g.
    ///   `lifted_0`).
    /// - `captures`: closure-environment values passed to
    ///   `target` alongside `acc` and `elem`.
    /// - `elem_ty`: element type of `list`.
    /// - `ty`: result type (the accumulator's type after the
    ///   fold).
    ListWalk {
        list_slots: Vec<Expr>,
        init: Vec<Expr>,
        target: String,
        captures: Vec<Expr>,
        elem_ty: Type,
        ty: Type,
    },

    /// Same as `ListWalk`, except `target`'s return is a `Step(b)`
    /// tag union (`[Continue(b), Break(b)]`). After each step call,
    /// the loop dispatches on the tag: `Continue` → next iteration
    /// with payload as new acc; `Break` → jump to `done` with
    /// payload as result.
    ListWalkUntil {
        list_slots: Vec<Expr>,
        init: Vec<Expr>,
        target: String,
        captures: Vec<Expr>,
        elem_ty: Type,
        ty: Type,
    },

    /// `ListAppend(list_slots, val_slots, elem_ty, ty)` — produces
    /// a new `(len, cap, data)` trio with `val_slots` written at
    /// index `len`. For multi-slot elements (records, Str, nested
    /// List), the buffer stride is `val_slots.len() * 8` and each
    /// slot lands at consecutive 8-byte offsets within the
    /// element's stride bucket. Implemented via `cow_resize_dyn` +
    /// per-slot stores; FBIP reuses the buffer in place when
    /// refcount is 1.
    ListAppend {
        list_slots: Vec<Expr>,
        val_slots: Vec<Expr>,
        elem_ty: Type,
        ty: Type,
    },

    /// `ListSet(list_slots, idx, val_slots, elem_ty, ty)` —
    /// produces a new `(len, cap, data)` trio with `val_slots`
    /// written at element index `idx`. Buffer is `cow_store_dyn`'d
    /// in place when refcount is 1; otherwise it clones. Stride
    /// handling matches `ListAppend`.
    ListSet {
        list_slots: Vec<Expr>,
        idx: Box<Expr>,
        val_slots: Vec<Expr>,
        elem_ty: Type,
        ty: Type,
    },

    /// `Cast { src, dest_ty, bitcast, ty }` — a scalar conversion
    /// (e.g. `U8 → U32` zero-extend, `F64 → U64` bitcast). Lowers
    /// directly to SSA's `Cast` or `BitCast` instruction. `bitcast =
    /// true` preserves the bit pattern (used for `to_bits` /
    /// `from_bits`); `false` does a typed cast (zero/sign-extend,
    /// truncate).
    Cast {
        src: Box<Expr>,
        dest_ty: crate::ssa::ScalarType,
        bitcast: bool,
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
            | Self::BufLoad { ty, .. }
            | Self::ListRange { ty, .. }
            | Self::ListWalk { ty, .. }
            | Self::ListWalkUntil { ty, .. }
            | Self::ListAppend { ty, .. }
            | Self::ListSet { ty, .. }
            | Self::Cast { ty, .. } => ty,
        }
    }

    /// Overwrite the result type. Used at HO call sites to retype an
    /// arg's closure-valued expression from the source-level Arrow
    /// to the post-specialize closure tag-union so downstream
    /// slot-count computations (Match merge params, Let binders)
    /// match what the callee expects.
    pub fn set_ty(&mut self, new_ty: Type) {
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
            | Self::BufLoad { ty, .. }
            | Self::ListRange { ty, .. }
            | Self::ListWalk { ty, .. }
            | Self::ListWalkUntil { ty, .. }
            | Self::ListAppend { ty, .. }
            | Self::ListSet { ty, .. }
            | Self::Cast { ty, .. } => *ty = new_ty,
        }
    }
}
