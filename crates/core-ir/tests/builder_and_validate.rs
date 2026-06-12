//! Hand-built Core programs running through the validator.
//!
//! These exercise the builder's ergonomics — every test reads
//! like a recipe for the program it builds. If a test reads as
//! struct-literal noise, the builder needs another pass.

use std::collections::HashMap;

use core_ir::{validate_call_graph, validate_scope, Binder, Builder, Expr, FoldShape, ValidationError};

#[test]
fn lit_passes_scope() {
    let b = Builder::new();
    validate_scope(&[], &b.int(42)).expect("literal is closed");
}

#[test]
fn unbound_var_fails_scope() {
    let mut b = Builder::new();
    let x = b.local(b.i64());
    let err = validate_scope(&[], &x.expr()).unwrap_err();
    assert!(matches!(err, ValidationError::UnboundVar(s) if s == x.id));
}

#[test]
fn parameter_in_scope_passes() {
    let mut b = Builder::new();
    let x = b.local(b.i64());
    validate_scope(&[x.id], &x.expr()).expect("x is a parameter");
}

#[test]
fn let_binds_in_body() {
    // let x = 1 in x
    let mut b = Builder::new();
    let x = b.local(b.i64());
    let prog = b.bind(&x, b.int(1), &x);
    validate_scope(&[], &prog).expect("x is bound by Let");
}

#[test]
fn let_does_not_leak_outside_body() {
    // plus((let x = 1 in 2), x) — outer x is unbound
    let mut b = Builder::new();
    let plus = b.func();
    let x = b.local(b.i64());
    let inner_let = b.bind(&x, b.int(1), b.int(2));
    let prog = b.call(plus, [inner_let, x.expr()], b.i64());
    let err = validate_scope(&[], &prog).unwrap_err();
    assert!(matches!(err, ValidationError::UnboundVar(_)));
}

#[test]
fn pattern_binder_in_scope_for_arm_body() {
    // match xs with
    //   | Cons(h, t) -> h
    //   | Nil        -> 0
    let mut b = Builder::new();
    let list_i64 = b.list_of(b.i64());
    let xs = b.local(list_i64);
    let cons = b.decl_tag();
    let nil = b.decl_tag();
    let h = b.local(b.i64());
    let t = b.local(b.i64());

    let prog = b.match_(
        &xs,
        [
            b.arm(
                b.pat_con(b.declared(cons), [h.as_binder(), t.as_binder()]),
                &h,
            ),
            b.arm(b.pat_con(b.declared(nil), []), b.int(0)),
        ],
        b.i64(),
    );

    validate_scope(&[xs.id], &prog).expect("h, t bound by Cons");
}

#[test]
fn wildcard_does_not_bind() {
    let mut b = Builder::new();
    let list_i64 = b.list_of(b.i64());
    let xs = b.local(list_i64);
    let cons = b.decl_tag();
    let leak = b.local(b.i64()); // never bound

    let prog = b.match_(
        &xs,
        [b.arm(
            b.pat_con(b.declared(cons), [Binder::Wildcard, Binder::Wildcard]),
            &leak,
        )],
        b.i64(),
    );

    let err = validate_scope(&[xs.id], &prog).unwrap_err();
    assert!(matches!(err, ValidationError::UnboundVar(s) if s == leak.id));
}

#[test]
fn fold_targets_a_value() {
    // fold(sum_step, 0, [], xs)
    let mut b = Builder::new();
    let list_i64 = b.list_of(b.i64());
    let xs = b.local(list_i64);
    let sum_step = b.func();
    let prog = b.fold(sum_step, &xs, [b.int(0)], [], b.i64());
    validate_scope(&[xs.id], &prog).expect("xs in scope");
}

#[test]
fn nested_fold_is_just_nested_value() {
    // The flagship: Fold(walk, Fold(map, xs, [], [f]), [0], [g])
    // No slot Vec, no Let-rebinding, no environment analysis —
    // just nested values.
    let mut b = Builder::new();
    let list_i64 = b.list_of(b.i64());
    let xs = b.local(list_i64.clone());
    let f = b.local(b.i64());
    let g = b.local(b.i64());
    let map = b.func();
    let walk = b.func();

    let inner = b.fold(map, &xs, [], [f.expr()], list_i64);
    let outer = b.fold(walk, inner, [b.int(0)], [g.expr()], b.i64());

    validate_scope(&[xs.id, f.id, g.id], &outer).expect("nesting is syntactic");
}

#[test]
fn fold_shape_annotation_attaches() {
    let mut b = Builder::new();
    let list_i64 = b.list_of(b.i64());
    let xs = b.local(list_i64.clone());
    let f = b.local(b.i64());
    let map_fn = b.func();

    let prog = b.with_shape(
        b.fold(map_fn, &xs, [], [f.expr()], list_i64),
        FoldShape::Map,
    );

    let Expr::Fold { shape, .. } = &prog else { panic!("expected Fold"); };
    assert_eq!(*shape, Some(FoldShape::Map));
}

#[test]
fn gen_makes_anamorphism_first_class() {
    // List.range(0, 10) — bounded Gen producing List(I64).
    let mut b = Builder::new();
    let list_i64 = b.list_of(b.i64());
    let range_step = b.func();
    let prog = b.gen_(b.int(10), range_step, [b.int(0)], [], b.i64(), list_i64);
    validate_scope(&[], &prog).expect("closed");
}

#[test]
fn crash_is_a_leaf() {
    let b = Builder::new();
    validate_scope(&[], &b.crash("kaboom", b.i64())).expect("Crash carries no Var refs");
}

#[test]
fn buffer_primitives_compose() {
    // xs.set(2, 99).append(100)
    let mut b = Builder::new();
    let list_i64 = b.list_of(b.i64());
    let xs = b.local(list_i64.clone());
    let set = b.buf_set(&xs, b.int(2), b.int(99), list_i64.clone());
    let prog = b.buf_append(set, b.int(100), list_i64);
    validate_scope(&[xs.id], &prog).expect("buffer chain well-scoped");
}

#[test]
fn dag_check_passes_with_no_calls() {
    let functions: HashMap<core_ir::FnId, Expr> = HashMap::new();
    validate_call_graph(&functions).expect("empty graph is acyclic");
}

#[test]
fn dag_check_allows_self_recursion() {
    let mut b = Builder::new();
    let f = b.func();
    let body = b.call(f, [b.int(0)], b.i64());
    let functions: HashMap<_, _> = std::iter::once((f, body)).collect();
    validate_call_graph(&functions).expect("self-recursion allowed");
}

#[test]
fn dag_check_catches_mutual_recursion() {
    let mut b = Builder::new();
    let f = b.func();
    let g = b.func();
    let f_body = b.call(g, [], b.i64());
    let g_body = b.call(f, [], b.i64());
    let functions: HashMap<_, _> = [(f, f_body), (g, g_body)].into_iter().collect();
    let err = validate_call_graph(&functions).unwrap_err();
    assert!(matches!(err, ValidationError::CallGraphCycle(_)));
}
