//! Builder API for constructing Core programs in tests.
//!
//! Analogous to `ssa::Builder` but tree-shaped (Core isn't
//! imperative). The builder manages identifier minting and
//! provides ergonomic constructors so test programs don't
//! drown in struct literals.

use crate::expr::{Expr, FoldKind, FoldShape, MatchArm};
use crate::literal::{Literal, StrLit};
use crate::pattern::{Binder, Pattern};
use crate::sym::{ClosureTagId, DeclTagId, FnId, LocalId, TagId, TypeId};
use crate::ty::{CoreType, Scalar};

/// Allocates fresh identifiers and provides ergonomic constructors.
///
/// Identifiers are sequentially allocated u32s; tests can build
/// many independent programs by using separate `Builder`
/// instances.
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
    pub fn new() -> Self {
        Self::default()
    }

    // ---- Fresh identifiers ----

    pub fn fresh_local(&mut self) -> LocalId {
        let id = LocalId(self.next_local);
        self.next_local += 1;
        id
    }

    pub fn fresh_fn(&mut self) -> FnId {
        let id = FnId(self.next_fn);
        self.next_fn += 1;
        id
    }

    pub fn fresh_decl_tag(&mut self) -> DeclTagId {
        let id = DeclTagId(self.next_decl_tag);
        self.next_decl_tag += 1;
        id
    }

    pub fn fresh_closure_tag(&mut self) -> ClosureTagId {
        let id = ClosureTagId(self.next_closure_tag);
        self.next_closure_tag += 1;
        id
    }

    pub fn fresh_type(&mut self) -> TypeId {
        let id = TypeId(self.next_type);
        self.next_type += 1;
        id
    }

    // ---- Type shorthands ----

    #[must_use]
    pub fn i64(&self) -> CoreType { CoreType::Prim(Scalar::I64) }
    #[must_use]
    pub fn u8(&self) -> CoreType { CoreType::Prim(Scalar::U8) }
    #[must_use]
    pub fn u64(&self) -> CoreType { CoreType::Prim(Scalar::U64) }
    #[must_use]
    pub fn bool(&self) -> CoreType { CoreType::Prim(Scalar::Bool) }
    #[must_use]
    pub fn f64(&self) -> CoreType { CoreType::Prim(Scalar::F64) }

    #[must_use]
    pub fn adt(&self, head: TypeId, args: Vec<CoreType>) -> CoreType {
        CoreType::Adt(head, args)
    }

    // ---- Leaf constructors ----

    #[must_use]
    pub fn var(&self, sym: LocalId, ty: CoreType) -> Expr {
        Expr::Var { sym, ty }
    }

    #[must_use]
    pub fn lit_i64(&self, n: i64) -> Expr {
        Expr::Lit { value: Literal::Int(n), ty: self.i64() }
    }

    #[must_use]
    pub fn lit_u8(&self, n: u8) -> Expr {
        Expr::Lit { value: Literal::Int(i64::from(n)), ty: self.u8() }
    }

    #[must_use]
    pub fn lit_bool(&self, b: bool) -> Expr {
        Expr::Lit { value: Literal::Int(i64::from(b)), ty: self.bool() }
    }

    #[must_use]
    pub fn lit_f64(&self, f: f64) -> Expr {
        Expr::Lit { value: Literal::Float(f), ty: self.f64() }
    }

    #[must_use]
    pub fn crash(&self, msg: impl Into<String>, ty: CoreType) -> Expr {
        Expr::Crash { msg: StrLit::new(msg), ty }
    }

    // ---- Composite constructors ----

    #[must_use]
    pub fn call(&self, target: FnId, args: Vec<Expr>, ret_ty: CoreType) -> Expr {
        Expr::App { target, args, ty: ret_ty }
    }

    #[must_use]
    pub fn let_(&self, binder: LocalId, value: Expr, body: Expr) -> Expr {
        let ty = body.ty().clone();
        Expr::Let { binder, value: Box::new(value), body: Box::new(body), ty }
    }

    #[must_use]
    pub fn match_(&self, scrutinee: Expr, arms: Vec<MatchArm>, ty: CoreType) -> Expr {
        Expr::Match { scrutinee: Box::new(scrutinee), arms, ty }
    }

    #[must_use]
    pub fn con(&self, tag: TagId, args: Vec<Expr>, ty: CoreType) -> Expr {
        Expr::Con { tag, args, ty }
    }

    // ---- Fold/Gen ----

    /// Total catamorphism. `fold_fn` returns `b` directly.
    #[must_use]
    pub fn fold(
        &self,
        fold_fn: FnId,
        target: Expr,
        init: Vec<Expr>,
        captures: Vec<Expr>,
        ty: CoreType,
    ) -> Expr {
        Expr::Fold {
            kind: FoldKind::Total,
            fold_fn,
            target: Box::new(target),
            init,
            captures,
            shape: None,
            ty,
        }
    }

    /// Early-exit catamorphism (`walk_until` shape). `fold_fn`
    /// returns `Step(b)`.
    #[must_use]
    pub fn fold_until(
        &self,
        fold_fn: FnId,
        target: Expr,
        init: Vec<Expr>,
        captures: Vec<Expr>,
        ty: CoreType,
    ) -> Expr {
        Expr::Fold {
            kind: FoldKind::EarlyExit,
            fold_fn,
            target: Box::new(target),
            init,
            captures,
            shape: None,
            ty,
        }
    }

    /// Attach a verified shape annotation to an existing `Fold`.
    /// Panics if applied to a non-`Fold`.
    #[must_use]
    pub fn with_shape(&self, mut expr: Expr, shape: FoldShape) -> Expr {
        if let Expr::Fold { shape: s, .. } = &mut expr {
            *s = Some(shape);
        } else {
            panic!("with_shape applied to non-Fold");
        }
        expr
    }

    #[must_use]
    pub fn gen_(
        &self,
        bound: Expr,
        step_fn: FnId,
        init: Vec<Expr>,
        captures: Vec<Expr>,
        elem_ty: CoreType,
        ty: CoreType,
    ) -> Expr {
        Expr::Gen {
            bound: Box::new(bound),
            step_fn,
            init,
            captures,
            elem_ty,
            ty,
        }
    }

    // ---- Buffer primitives ----

    #[must_use]
    pub fn buf_lit(&self, elements: Vec<Expr>, elem_ty: CoreType, ty: CoreType) -> Expr {
        Expr::BufLit { elements, elem_ty, ty }
    }

    #[must_use]
    pub fn buf_load(&self, buf: Expr, idx: Expr, ty: CoreType) -> Expr {
        Expr::BufLoad { buf: Box::new(buf), idx: Box::new(idx), ty }
    }

    #[must_use]
    pub fn buf_load_unchecked(&self, buf: Expr, idx: Expr, ty: CoreType) -> Expr {
        Expr::BufLoadUnchecked { buf: Box::new(buf), idx: Box::new(idx), ty }
    }

    #[must_use]
    pub fn buf_append(&self, buf: Expr, val: Expr, ty: CoreType) -> Expr {
        Expr::BufAppend { buf: Box::new(buf), val: Box::new(val), ty }
    }

    #[must_use]
    pub fn buf_set(&self, buf: Expr, idx: Expr, val: Expr, ty: CoreType) -> Expr {
        Expr::BufSet { buf: Box::new(buf), idx: Box::new(idx), val: Box::new(val), ty }
    }

    // ---- Patterns + arms ----

    #[must_use]
    pub fn pat_con(&self, tag: TagId, binders: Vec<Binder>) -> Pattern {
        Pattern::Constructor { tag, binders }
    }

    #[must_use]
    pub fn pat_wild(&self) -> Pattern { Pattern::Wildcard }

    #[must_use]
    pub fn pat_bind(&self, sym: LocalId) -> Pattern { Pattern::Binding(sym) }

    #[must_use]
    pub fn arm(&self, pattern: Pattern, body: Expr) -> MatchArm {
        MatchArm { pattern, guards: vec![], body: Box::new(body), is_return: false }
    }

    #[must_use]
    pub fn arm_with_guards(
        &self,
        pattern: Pattern,
        guards: Vec<Expr>,
        body: Expr,
    ) -> MatchArm {
        MatchArm { pattern, guards, body: Box::new(body), is_return: false }
    }

    #[must_use]
    pub fn arm_return(&self, pattern: Pattern, body: Expr) -> MatchArm {
        MatchArm { pattern, guards: vec![], body: Box::new(body), is_return: true }
    }

    // ---- Tag constructors ----

    #[must_use]
    pub fn declared_tag(&self, tag: DeclTagId) -> TagId { TagId::Declared(tag) }

    #[must_use]
    pub fn closure_tag(&self, tag: ClosureTagId) -> TagId { TagId::Closure(tag) }
}
