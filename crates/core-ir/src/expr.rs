//! Core IR expressions — the eleven variants.
//!
//! Direct-style (not ANF), typed at every node, post-monomorphization.
//! See `notes/core-ir.md` for the spec and the rationale behind each
//! variant. **Open design questions** for v1 are flagged inline.

use crate::literal::Literal;
use crate::pattern::Pattern;
use crate::sym::{SymbolId, TagId};
use crate::ty::Type;

/// The Core IR expression.
#[derive(Debug, Clone)]
pub enum Expr {
    // ---- Universal ----
    /// Reference to a binding (local, parameter, or top-level value).
    ///
    /// **Open question:** spec says single-slot. Multi-slot bindings
    /// are accessed via `lower_expr_slots` which expands to N
    /// parallel slot-Vars. The IR variant itself is slot-agnostic —
    /// it carries one `SymbolId`. The N-slot expansion is a runtime
    /// thing tracked in lowering context. Is that the right shape,
    /// or should multi-slot Vars be syntactically distinct?
    Var { sym: SymbolId, ty: Type },

    /// Scalar literal.
    Lit { value: Literal, ty: Type },

    /// First-order call to a known top-level function.
    ///
    /// After mono, `target` is a monomorphic function. After defunc,
    /// every call edge is known statically. Builtin targets
    /// (arithmetic, cast, range) dispatch inline at lowering instead
    /// of going through `Inst::Call`.
    App {
        target: SymbolId,
        args: Vec<Expr>,
        ty: Type,
    },

    /// `Let(binders, value, body)` — bind `value`'s N slots to N
    /// `binders` for the scope of `body`.
    ///
    /// Single-slot bindings have `binders.len() == 1`; multi-slot
    /// (record, tuple, trio, multi-variant payload) has
    /// `binders.len() == expand_slots(value.ty()).len()`.
    Let {
        binders: Vec<SymbolId>,
        value: Box<Expr>,
        body: Box<Expr>,
        ty: Type,
    },

    // ---- Algebraic ----
    /// Non-recursive case analysis on a tag union.
    ///
    /// **Open question (major):** `scrutinee_slots: Vec<Expr>` and
    /// `body: Vec<Expr>` (in `MatchArm`) are pre-decomposed parallel
    /// slot lists. The lowering layer could do this expansion itself
    /// via `lower_expr_slots`. Storing it pre-decomposed makes
    /// algebraic rewrites awkward (every walker iterates over Vec).
    /// Cleaner shape: `scrutinee: Box<Expr>`, `body: Box<Expr>`,
    /// let lowering expand. Cost: lowering grows complexity; some
    /// rewrites that match on per-slot scrutinees need rework.
    Match {
        scrutinee_slots: Vec<Expr>,
        scrutinee_ty: Type,
        arms: Vec<MatchArm>,
        ty: Type,
    },

    /// Structural recursion / catamorphism — the only iteration
    /// primitive at Core. See `notes/core-ir.md`'s "`Cata` in
    /// detail" for the full field-by-field semantics.
    ///
    /// **Open question (major):** `early_exit: bool` is a flag
    /// distinguishing the `walk_until` shape. An enum
    /// `CataKind { Plain, Step }` (or similar) is more honest and
    /// makes the two SSA lowerings syntactically distinct. Trivial
    /// to do; just unclear if there are future shapes (`Anamorphism`,
    /// `Paramorphism`) that would push toward a richer enum.
    Cata {
        fold_fn: SymbolId,
        target_slots: Vec<Expr>,
        target_ty: Type,
        init: Vec<Expr>,
        captures: Vec<Expr>,
        elem_ty: Type,
        early_exit: bool,
        ty: Type,
    },

    /// Tag-union constructor.
    ///
    /// **Open question (major):** `field_slot_counts` is stored
    /// derived data. The existing implementation tried to derive
    /// it at lowering from the constructor's scheme; failed because
    /// `ty` for declared constructors is *polymorphic* (`Result(Var,
    /// Var)`), and subst against polymorphic ty is identity. See the
    /// "Types in Core" section of the spec.
    ///
    /// V1 design choice: do we (a) accept the same workaround and
    /// store the slot counts, or (b) make `Con.ty` monomorphic by
    /// distinguishing closure tags from declared tags upstream and
    /// stamping the monomorphic `ast.ty` for declared? Option (b)
    /// removes this field entirely. Worth trying in v1.
    ///
    /// For now (until we decide): kept, with the same shape as the
    /// existing implementation.
    Con {
        tag: TagId,
        args: Vec<Expr>,
        field_slot_counts: Vec<usize>,
        ty: Type,
    },

    // ---- Buffer trio ----
    /// Buffer literal: `[1, 2, 3]`, `"abc"`. Elements are already
    /// flat per-slot — for `List(Record)` with N-slot elements,
    /// `elements.len() == n * N`.
    BufLit {
        elements: Vec<Expr>,
        elem_ty: Type,
        ty: Type,
    },

    /// `xs.get(idx)` — bounds-checked index returning the element
    /// type's value (the bounds check + Result wrapping happens at
    /// AST→Core via Match around this primitive).
    ///
    /// **Open question:** existing implementation wraps `BufLoad`
    /// in a `Match { bounds_check, Ok(BufLoad(...)), Err(OOB) }`
    /// at AST→Core. Should `BufLoad` carry its own
    /// `Result<T, OutOfBounds>`-shaped return, with the bounds
    /// check internal? Cleaner ergonomics; lowering grows a small
    /// branch. The current externalize-the-check approach lets
    /// algebraic rewrites elide the check when the index is
    /// provably in range.
    BufLoad {
        buf: Box<Expr>,
        idx: Box<Expr>,
        ty: Type,
    },

    /// `xs.append(y)` — produces a new trio. Lowers to
    /// `cow_resize_dyn` (FBIP: mutate in place when `rc == 1`,
    /// clone when `rc > 1`).
    ///
    /// **Open question:** `buf_slots: Vec<Expr>` and
    /// `val_slots: Vec<Expr>` are pre-decomposed parallel slot
    /// lists for the same reason as Match. Same trade-off as
    /// scrutinee_slots above — should they be single Exprs that
    /// lowering expands?
    BufAppend {
        buf_slots: Vec<Expr>,
        val_slots: Vec<Expr>,
        elem_ty: Type,
        ty: Type,
    },

    /// `xs.set(i, y)` — produces a new trio. Lowers to
    /// `cow_store_dyn`. Same FBIP rationale as `BufAppend`.
    BufSet {
        buf_slots: Vec<Expr>,
        idx: Box<Expr>,
        val_slots: Vec<Expr>,
        elem_ty: Type,
        ty: Type,
    },
}

/// One arm of a `Match` expression.
///
/// `guards` are predicate expressions that must all evaluate to
/// `True` for the arm to fire; an arm with an unsatisfied guard
/// falls through to the next arm.
///
/// `is_return` flips the arm from "produce a value for the match"
/// to "return this value from the enclosing function" — the `?`
/// operator desugars to a match with `Err` as a return arm.
#[derive(Debug, Clone)]
pub struct MatchArm {
    pub pattern: Pattern,
    pub guards: Vec<Expr>,
    /// The arm's body as a slot list — one Core `Expr` per slot
    /// of the Match's result type.
    pub body: Vec<Expr>,
    pub is_return: bool,
}
