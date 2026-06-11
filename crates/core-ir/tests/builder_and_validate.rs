//! Hand-built Core programs running through the validator.
//!
//! Each test constructs an isolated Core fragment via the builder
//! and checks the validator's response. These are sanity tests —
//! they prove the IR types compose, the builder is ergonomic
//! enough to be usable, and the validator catches the failures
//! it claims to.

use std::collections::HashMap;

use core_ir::{
    validate_call_graph, validate_scope, Binder, Builder, Expr, FoldShape,
    ValidationError,
};

#[test]
fn lit_passes_scope() {
    let b = Builder::new();
    let prog = b.lit_i64(42);
    validate_scope(&[], &prog).expect("literal is closed");
}

#[test]
fn unbound_var_fails_scope() {
    let mut b = Builder::new();
    let x = b.fresh_local();
    let prog = b.var(x, b.i64());
    let err = validate_scope(&[], &prog).unwrap_err();
    assert!(
        matches!(err, ValidationError::UnboundVar(s) if s == x),
        "expected UnboundVar({x:?}), got {err:?}",
    );
}

#[test]
fn parameter_in_scope_passes() {
    let mut b = Builder::new();
    let x = b.fresh_local();
    let prog = b.var(x, b.i64());
    validate_scope(&[x], &prog).expect("x is a parameter");
}

#[test]
fn let_binds_in_body() {
    // let x = 1 in x
    let mut b = Builder::new();
    let x = b.fresh_local();
    let prog = b.let_(x, b.lit_i64(1), b.var(x, b.i64()));
    validate_scope(&[], &prog).expect("x is bound by Let");
}

#[test]
fn let_does_not_leak_outside_body() {
    // (let x = 1 in 2) + x — the outer x is unbound.
    // We model "+" as a builtin App.
    let mut b = Builder::new();
    let plus = b.fresh_fn();
    let x = b.fresh_local();
    let let_part = b.let_(x, b.lit_i64(1), b.lit_i64(2));
    let prog = b.call(plus, vec![let_part, b.var(x, b.i64())], b.i64());
    let err = validate_scope(&[], &prog).unwrap_err();
    assert!(matches!(err, ValidationError::UnboundVar(_)));
}

#[test]
fn pattern_binder_in_scope_for_arm_body() {
    // match xs with Cons(h, t) -> h
    //              | Nil       -> 0
    let mut b = Builder::new();
    let cons = b.fresh_decl_tag();
    let nil = b.fresh_decl_tag();
    let xs = b.fresh_local();
    let h = b.fresh_local();
    let t = b.fresh_local();
    let cons_arm = b.arm(
        b.pat_con(b.declared_tag(cons), vec![Binder::Sym(h), Binder::Sym(t)]),
        b.var(h, b.i64()),
    );
    let nil_arm = b.arm(b.pat_con(b.declared_tag(nil), vec![]), b.lit_i64(0));
    let list_head = b.fresh_type(); let list_ty = b.adt(list_head, vec![b.i64()]);
    let prog = b.match_(b.var(xs, list_ty.clone()), vec![cons_arm, nil_arm], b.i64());
    validate_scope(&[xs], &prog).expect("h, t are bound by Cons pattern");
}

#[test]
fn wildcard_does_not_bind() {
    // match xs with Cons(_, t) -> t-which-is-unbound-outside
    // Actually the wildcard is fine; the test is that body
    // referencing t in the wildcard position would fail.
    let mut b = Builder::new();
    let cons = b.fresh_decl_tag();
    let xs = b.fresh_local();
    let leak = b.fresh_local(); // never bound
    let arm = b.arm(
        b.pat_con(b.declared_tag(cons), vec![Binder::Wildcard, Binder::Wildcard]),
        b.var(leak, b.i64()),
    );
    let list_head = b.fresh_type(); let list_ty = b.adt(list_head, vec![b.i64()]);
    let prog = b.match_(b.var(xs, list_ty.clone()), vec![arm], b.i64());
    let err = validate_scope(&[xs], &prog).unwrap_err();
    assert!(matches!(err, ValidationError::UnboundVar(s) if s == leak));
}

#[test]
fn fold_targets_a_value() {
    // fold(sum_step, 0, [], xs) where xs is a parameter.
    let mut b = Builder::new();
    let xs = b.fresh_local();
    let sum_step = b.fresh_fn();
    let list_head = b.fresh_type(); let list_ty = b.adt(list_head, vec![b.i64()]);
    let prog = b.fold(
        sum_step,
        b.var(xs, list_ty),
        vec![b.lit_i64(0)],
        vec![],
        b.i64(),
    );
    validate_scope(&[xs], &prog).expect("xs is in scope");
}

#[test]
fn nested_fold_is_just_nested_value() {
    // The flagship-fusion shape: Fold(walk, init, [g], Fold(map, [], [f], xs))
    // The test isn't fusion — it's that nesting *just works*: no
    // slot Vec, no Let-rebinding, no environment analysis.
    let mut b = Builder::new();
    let xs = b.fresh_local();
    let walk = b.fresh_fn();
    let map = b.fresh_fn();
    let f = b.fresh_local();
    let g = b.fresh_local();
    let list_head = b.fresh_type(); let list_i64 = b.adt(list_head, vec![b.i64()]);
    let inner = b.fold(
        map,
        b.var(xs, list_i64.clone()),
        vec![],
        vec![b.var(f, b.i64())], // closure-as-captured-value
        list_i64,
    );
    let outer = b.fold(
        walk,
        inner,
        vec![b.lit_i64(0)],
        vec![b.var(g, b.i64())],
        b.i64(),
    );
    validate_scope(&[xs, f, g], &outer).expect("nesting is syntactic");
}

#[test]
fn fold_shape_annotation_attaches() {
    let mut b = Builder::new();
    let xs = b.fresh_local();
    let map_fn = b.fresh_fn();
    let f = b.fresh_local();
    let list_head = b.fresh_type(); let list_i64 = b.adt(list_head, vec![b.i64()]);
    let prog = b.with_shape(
        b.fold(
            map_fn,
            b.var(xs, list_i64.clone()),
            vec![],
            vec![b.var(f, b.i64())],
            list_i64,
        ),
        FoldShape::Map,
    );
    let Expr::Fold { shape, .. } = &prog else {
        panic!("expected Fold");
    };
    assert_eq!(*shape, Some(FoldShape::Map));
}

#[test]
fn gen_makes_anamorphism_first_class() {
    // List.range(0, 10) — bounded Gen producing List(I64).
    let mut b = Builder::new();
    let range_step = b.fresh_fn();
    let list_head = b.fresh_type(); let list_i64 = b.adt(list_head, vec![b.i64()]);
    let prog = b.gen_(
        b.lit_i64(10),
        range_step,
        vec![b.lit_i64(0)],
        vec![],
        b.i64(),
        list_i64,
    );
    validate_scope(&[], &prog).expect("closed");
}

#[test]
fn crash_is_a_leaf() {
    let b = Builder::new();
    let prog = b.crash("kaboom", b.i64());
    validate_scope(&[], &prog).expect("Crash carries no Var refs");
}

#[test]
fn buffer_primitives_compose() {
    // xs.set(2, 99).append(100) — chain mutations on a binding.
    let mut b = Builder::new();
    let xs = b.fresh_local();
    let list_head = b.fresh_type(); let list_i64 = b.adt(list_head, vec![b.i64()]);
    let set = b.buf_set(
        b.var(xs, list_i64.clone()),
        b.lit_i64(2),
        b.lit_i64(99),
        list_i64.clone(),
    );
    let prog = b.buf_append(set, b.lit_i64(100), list_i64);
    validate_scope(&[xs], &prog).expect("buffer chain is well-scoped");
}

#[test]
fn dag_check_passes_with_no_calls() {
    let functions: HashMap<core_ir::FnId, Expr> = HashMap::new();
    validate_call_graph(&functions).expect("empty graph is acyclic");
}

#[test]
fn dag_check_allows_self_recursion() {
    // f calls f — the structural-fold pattern.
    let mut b = Builder::new();
    let f = b.fresh_fn();
    let body = b.call(f, vec![b.lit_i64(0)], b.i64());
    let functions: HashMap<_, _> = std::iter::once((f, body)).collect();
    validate_call_graph(&functions).expect("self-recursion allowed");
}

#[test]
fn dag_check_catches_mutual_recursion() {
    // f calls g, g calls f — mutual cycle, rejected.
    let mut b = Builder::new();
    let f = b.fresh_fn();
    let g = b.fresh_fn();
    let f_body = b.call(g, vec![], b.i64());
    let g_body = b.call(f, vec![], b.i64());
    let functions: HashMap<_, _> = [(f, f_body), (g, g_body)].into_iter().collect();
    let err = validate_call_graph(&functions).unwrap_err();
    assert!(matches!(err, ValidationError::CallGraphCycle(_)));
}
