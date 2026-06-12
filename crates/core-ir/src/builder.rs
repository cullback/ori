//! Builder API for constructing Core programs in tests.
//!
//! The builder tracks types for bindings (`LocalVar`) so that
//! using a binding doesn't require re-stating its type at each
//! reference site. Conversions via `Into<Expr>` let local
//! variables flow into argument positions naturally.

use crate::expr::{Expr, FoldKind, FoldShape, MatchArm};
use crate::literal::{Literal, StrLit};
use crate::pattern::{Binder, Pattern};
use crate::sym::{ClosureTagId, DeclTagId, FnId, LocalId, TagId, TypeId};
use crate::ty::{CoreType, Scalar};

/// A locally-bound variable with its type attached.
///
/// `LocalVar` is the unit of binding in builder code. Use it as
/// the `binder` in `Let` / pattern positions; pass it (by value
/// or by reference) wherever an `Expr` is expected.
#[derive(Debug, Clone)]
pub struct LocalVar {
    pub id: LocalId,
    pub ty: CoreType,
}

impl LocalVar {
    /// Build an `Expr::Var` referencing this binding.
    #[must_use]
    pub fn expr(&self) -> Expr {
        Expr::Var { sym: self.id, ty: self.ty.clone() }
    }

    /// Build a `Pattern::Binding` for use in a `Match` arm.
    #[must_use]
    pub fn pat(&self) -> Pattern {
        Pattern::Binding(self.id)
    }

    /// Build a `Binder::Sym` for use inside a `Constructor` pattern.
    #[must_use]
    pub fn as_binder(&self) -> Binder {
        Binder::Sym(self.id)
    }
}

impl From<LocalVar> for Expr {
    fn from(v: LocalVar) -> Self { v.expr() }
}

impl From<&LocalVar> for Expr {
    fn from(v: &LocalVar) -> Self { v.expr() }
}

/// Builder for Core IR programs. Allocates fresh identifiers and
/// provides ergonomic constructors.
#[derive(Default)]
pub struct Builder {
    next_local: u32,
    next_fn: u32,
    next_decl_tag: u32,
    next_closure_tag: u32,
    next_type: u32,
}

impl Builder {
    #[must_use]
    pub fn new() -> Self { Self::default() }

    // ---------------- Fresh identifiers ----------------

    /// A fresh local binding with a known type. Use it directly
    /// in `let`, `match`, and argument positions.
    pub fn local(&mut self, ty: impl Into<CoreType>) -> LocalVar {
        let id = LocalId(self.next_local);
        self.next_local += 1;
        LocalVar { id, ty: ty.into() }
    }

    /// A fresh top-level callable identifier.
    pub fn func(&mut self) -> FnId {
        let id = FnId(self.next_fn);
        self.next_fn += 1;
        id
    }

    pub fn decl_tag(&mut self) -> DeclTagId {
        let id = DeclTagId(self.next_decl_tag);
        self.next_decl_tag += 1;
        id
    }

    pub fn closure_tag(&mut self) -> ClosureTagId {
        let id = ClosureTagId(self.next_closure_tag);
        self.next_closure_tag += 1;
        id
    }

    pub fn type_id(&mut self) -> TypeId {
        let id = TypeId(self.next_type);
        self.next_type += 1;
        id
    }

    // ---------------- Type constructors ----------------
    //
    // Primitive types come from `Scalar` directly — write
    // `Scalar::I64` (or `I64` with `use Scalar::*`) anywhere a
    // type is expected; conversions via `Into<CoreType>` handle
    // it. These ADT-shape helpers stay on the builder because
    // they mint fresh `TypeId`s.

    /// `List(T)`. Mints a fresh `TypeId` for the `List` head;
    /// tests that care about head identity should mint and reuse
    /// one explicitly.
    pub fn list_of(&mut self, elem: impl Into<CoreType>) -> CoreType {
        let head = self.type_id();
        CoreType::Adt(head, vec![elem.into()])
    }

    /// `Result(T, E)`.
    pub fn result_of(
        &mut self,
        ok: impl Into<CoreType>,
        err: impl Into<CoreType>,
    ) -> CoreType {
        let head = self.type_id();
        CoreType::Adt(head, vec![ok.into(), err.into()])
    }

    /// `Maybe(T)`.
    pub fn maybe_of(&mut self, t: impl Into<CoreType>) -> CoreType {
        let head = self.type_id();
        CoreType::Adt(head, vec![t.into()])
    }

    /// `Str` (`List(U8)` under the spec).
    pub fn str_ty(&mut self) -> CoreType { self.list_of(Scalar::U8) }

    // ---------------- Literal shortcuts (return Expr) ----------------

    /// `42_i64` — emits `Expr::Lit` of `I64` type directly.
    #[must_use]
    pub fn int(&self, n: i64) -> Expr {
        Expr::Lit { value: Literal::Int(n), ty: Scalar::I64.into() }
    }

    /// `5_u8`.
    #[must_use]
    pub fn byte(&self, n: u8) -> Expr {
        Expr::Lit { value: Literal::Int(i64::from(n)), ty: Scalar::U8.into() }
    }

    /// `true` / `false` literal.
    #[must_use]
    pub fn bool_(&self, v: bool) -> Expr {
        Expr::Lit { value: Literal::Int(i64::from(v)), ty: Scalar::Bool.into() }
    }

    /// `3.14_f64`.
    #[must_use]
    pub fn float(&self, x: f64) -> Expr {
        Expr::Lit { value: Literal::Float(x), ty: Scalar::F64.into() }
    }

    /// `crash("msg")` of the given result type.
    pub fn crash(&self, msg: impl Into<String>, ty: impl Into<CoreType>) -> Expr {
        Expr::Crash { msg: StrLit::new(msg), ty: ty.into() }
    }

    // ---------------- Composite constructors ----------------

    /// `f(args...)` returning `ret_ty`.
    #[must_use]
    pub fn call(
        &self,
        target: FnId,
        args: impl IntoIterator<Item = Expr>,
        ret_ty: impl Into<CoreType>,
    ) -> Expr {
        Expr::App {
            target,
            args: args.into_iter().collect(),
            ty: ret_ty.into(),
        }
    }

    /// `let x = value in body`. The result type is taken from
    /// `body`.
    pub fn bind(
        &self,
        x: &LocalVar,
        value: impl Into<Expr>,
        body: impl Into<Expr>,
    ) -> Expr {
        let body_expr: Expr = body.into();
        let ty = body_expr.ty().clone();
        Expr::Let {
            binder: x.id,
            value: Box::new(value.into()),
            body: Box::new(body_expr),
            ty: ty.into(),
        }
    }

    /// `match scrutinee of arms...` returning `ty`.
    pub fn match_(
        &self,
        scrutinee: impl Into<Expr>,
        arms: impl IntoIterator<Item = MatchArm>,
        ty: impl Into<CoreType>,
    ) -> Expr {
        Expr::Match {
            scrutinee: Box::new(scrutinee.into()),
            arms: arms.into_iter().collect(),
            ty: ty.into(),
        }
    }

    /// `Tag(args...)` — tag-union constructor.
    pub fn con(
        &self,
        tag: TagId,
        args: impl IntoIterator<Item = Expr>,
        ty: impl Into<CoreType>,
    ) -> Expr {
        Expr::Con {
            tag,
            args: args.into_iter().collect(),
            ty: ty.into(),
        }
    }

    // ---------------- Fold / Gen ----------------

    /// Total catamorphism — `fold_fn` returns `b` directly.
    pub fn fold(
        &self,
        fold_fn: FnId,
        target: impl Into<Expr>,
        init: impl IntoIterator<Item = Expr>,
        captures: impl IntoIterator<Item = Expr>,
        ty: impl Into<CoreType>,
    ) -> Expr {
        Expr::Fold {
            kind: FoldKind::Total,
            fold_fn,
            target: Box::new(target.into()),
            init: init.into_iter().collect(),
            captures: captures.into_iter().collect(),
            shape: None,
            ty: ty.into(),
        }
    }

    /// Early-exit catamorphism — `fold_fn` returns `Step(b)`.
    pub fn fold_until(
        &self,
        fold_fn: FnId,
        target: impl Into<Expr>,
        init: impl IntoIterator<Item = Expr>,
        captures: impl IntoIterator<Item = Expr>,
        ty: impl Into<CoreType>,
    ) -> Expr {
        Expr::Fold {
            kind: FoldKind::EarlyExit,
            fold_fn,
            target: Box::new(target.into()),
            init: init.into_iter().collect(),
            captures: captures.into_iter().collect(),
            shape: None,
            ty: ty.into(),
        }
    }

    /// Attach a verified shape to an existing `Fold`. Panics if
    /// applied to a non-`Fold`.
    #[must_use]
    pub fn with_shape(&self, mut expr: Expr, shape: FoldShape) -> Expr {
        if let Expr::Fold { shape: s, .. } = &mut expr {
            *s = Some(shape);
        } else {
            panic!("with_shape applied to non-Fold");
        }
        expr
    }

    /// Bounded anamorphism.
    pub fn gen_(
        &self,
        bound: impl Into<Expr>,
        step_fn: FnId,
        init: impl IntoIterator<Item = Expr>,
        captures: impl IntoIterator<Item = Expr>,
        elem_ty: impl Into<CoreType>,
        ty: impl Into<CoreType>,
    ) -> Expr {
        Expr::Gen {
            bound: Box::new(bound.into()),
            step_fn,
            init: init.into_iter().collect(),
            captures: captures.into_iter().collect(),
            elem_ty: elem_ty.into(),
            ty: ty.into(),
        }
    }

    // ---------------- Buffer primitives ----------------

    pub fn buf_lit(
        &self,
        elements: impl IntoIterator<Item = Expr>,
        elem_ty: impl Into<CoreType>,
        ty: impl Into<CoreType>,
    ) -> Expr {
        Expr::BufLit {
            elements: elements.into_iter().collect(),
            elem_ty: elem_ty.into(),
            ty: ty.into(),
        }
    }

    pub fn buf_load(&self, buf: impl Into<Expr>, idx: impl Into<Expr>, ty: impl Into<CoreType>) -> Expr {
        Expr::BufLoad {
            buf: Box::new(buf.into()),
            idx: Box::new(idx.into()),
            ty: ty.into(),
        }
    }

    pub fn buf_load_unchecked(
        &self,
        buf: impl Into<Expr>,
        idx: impl Into<Expr>,
        ty: impl Into<CoreType>,
    ) -> Expr {
        Expr::BufLoadUnchecked {
            buf: Box::new(buf.into()),
            idx: Box::new(idx.into()),
            ty: ty.into(),
        }
    }

    pub fn buf_append(&self, buf: impl Into<Expr>, val: impl Into<Expr>, ty: impl Into<CoreType>) -> Expr {
        Expr::BufAppend {
            buf: Box::new(buf.into()),
            val: Box::new(val.into()),
            ty: ty.into(),
        }
    }

    pub fn buf_set(
        &self,
        buf: impl Into<Expr>,
        idx: impl Into<Expr>,
        val: impl Into<Expr>,
        ty: impl Into<CoreType>,
    ) -> Expr {
        Expr::BufSet {
            buf: Box::new(buf.into()),
            idx: Box::new(idx.into()),
            val: Box::new(val.into()),
            ty: ty.into(),
        }
    }

    // ---------------- Patterns + arms ----------------

    #[must_use]
    pub fn pat_con(&self, tag: TagId, binders: impl IntoIterator<Item = Binder>) -> Pattern {
        Pattern::Constructor {
            tag,
            binders: binders.into_iter().collect(),
        }
    }

    #[must_use]
    pub const fn pat_wild(&self) -> Pattern { Pattern::Wildcard }

    /// One arm with no guards.
    pub fn arm(&self, pattern: Pattern, body: impl Into<Expr>) -> MatchArm {
        MatchArm {
            pattern,
            guards: vec![],
            body: Box::new(body.into()),
            is_return: false,
        }
    }

    /// Arm with guards.
    pub fn arm_guarded(
        &self,
        pattern: Pattern,
        guards: impl IntoIterator<Item = Expr>,
        body: impl Into<Expr>,
    ) -> MatchArm {
        MatchArm {
            pattern,
            guards: guards.into_iter().collect(),
            body: Box::new(body.into()),
            is_return: false,
        }
    }

    /// `: pat return body` arm — short-circuits the enclosing
    /// function.
    pub fn arm_return(&self, pattern: Pattern, body: impl Into<Expr>) -> MatchArm {
        MatchArm {
            pattern,
            guards: vec![],
            body: Box::new(body.into()),
            is_return: true,
        }
    }

    // ---------------- Tag constructors ----------------

    #[must_use]
    pub fn declared(&self, tag: DeclTagId) -> TagId { TagId::Declared(tag) }

    #[must_use]
    pub fn closure(&self, tag: ClosureTagId) -> TagId { TagId::Closure(tag) }
}
