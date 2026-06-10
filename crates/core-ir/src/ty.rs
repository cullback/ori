//! Types in Core IR.
//!
//! Every Core node carries `ty: Type`. The variants mirror what
//! `notes/core-ir.md`'s "Types in Core" section describes, but the
//! v1 prototype gets to make different choices than the existing
//! implementation. **Open questions** are flagged inline.

use crate::sym::TagId;

/// Source-level type carried on every Core node.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
    /// Primitive scalar (`I64`, `U8`, `Bool`, `F64`) or a named
    /// user type (`MyUnion`, `Box`). Post-mono, named user types
    /// are concrete.
    Con(String),

    /// Applied type constructor: `Result(I64, Str)`, `List(I64)`,
    /// `Maybe(T)`.
    App(String, Vec<Type>),

    /// Function type. After mono + lambda-lift + defunc, this
    /// only appears for top-level function references; user-level
    /// HOFs flow through closure tag unions.
    ///
    /// **Open question:** the existing `Type::Arrow` carries an
    /// optional `lambda_set`. Do we need it at Core? After
    /// `lambda::specialize` + `lambda::narrow`, every Arrow's
    /// lambda set is closed and either singleton (direct call) or
    /// multi (dispatched via `__apply_K`). The set is upstream
    /// information; Core probably doesn't need to look at it
    /// again. Dropping it would simplify this variant.
    Arrow {
        params: Vec<Type>,
        ret: Box<Type>,
    },

    /// Discriminated union — `[Ok(T), Err(E)]`, `[True, False]`,
    /// or a synthesized `__Closure_X`.
    TagUnion {
        tags: Vec<(TagId, Vec<Type>)>,
    },

    /// Type variable. **Should not appear in Core post-mono.**
    ///
    /// The existing implementation has one exception: declared-
    /// constructor `Con.ty` carries the polymorphic scheme return
    /// type (`Result(Var(a), Var(e))`) rather than the monomorphic
    /// instantiation, because closure constructors need a union-
    /// shaped type at construction time and the surrounding AST's
    /// `ty` is just the closure's return type.
    ///
    /// **Design question for v1**: do we accept this exception, or
    /// do we make `Con.ty` always monomorphic and handle closures
    /// differently (e.g., distinguish closure tags from declared
    /// tags at construction)?
    ///
    /// If we accept: keep this variant, document the exception,
    /// move on.
    ///
    /// If we fix: this variant could be removed entirely from Core's
    /// `Type` (Core's type representation would be a "monomorphic
    /// type" subset of the inference engine's `Type`). Stronger
    /// type-level invariant; nicer for analyses; requires more work
    /// at AST → Core.
    Var(u32),
}
