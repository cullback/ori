//! Rewrite rule tests — exercises `simplify` end-to-end.

use std::collections::HashSet;

use core_ir::{free_vars, simplify, validate_scope, Binder, Builder, Expr, FnTotality};

#[test]
fn free_vars_of_literal_is_empty() {
    let b = Builder::new();
    assert!(free_vars(&b.int(1)).is_empty());
}

#[test]
fn free_vars_of_var_is_singleton() {
    let mut b = Builder::new();
    let x = b.local(b.i64());
    let fv = free_vars(&x.expr());
    assert_eq!(fv, std::iter::once(x.id).collect::<HashSet<_>>());
}

#[test]
fn free_vars_of_let_excludes_bound_var() {
    // let x = 1 in plus(x, y) — y is free, x is bound
    let mut b = Builder::new();
    let plus = b.func();
    let x = b.local(b.i64());
    let y = b.local(b.i64());
    let prog = b.bind(&x, b.int(1), b.call(plus, [x.expr(), y.expr()], b.i64()));
    assert_eq!(free_vars(&prog), std::iter::once(y.id).collect());
}

#[test]
fn dead_let_eliminated_when_value_total() {
    // let x = 42 in 99 — x unused; value is a total literal.
    let mut b = Builder::new();
    let x = b.local(b.i64());
    let prog = b.bind(&x, b.int(42), b.int(99));
    let after = simplify(prog, &FnTotality::new());
    assert!(matches!(&after, Expr::Lit { .. }), "expected Lit, got {after}");
    validate_scope(&[], &after).expect("rewrite preserved scope");
}

#[test]
fn dead_let_preserved_when_value_crashes() {
    // let x = crash("boom") in 99 — eliding would skip the crash.
    let mut b = Builder::new();
    let x = b.local(b.i64());
    let prog = b.bind(&x, b.crash("boom", b.i64()), b.int(99));
    let after = simplify(prog, &FnTotality::new());
    assert!(matches!(&after, Expr::Let { .. }), "Let preserved: got {after}");
}

#[test]
fn live_let_preserved() {
    let mut b = Builder::new();
    let x = b.local(b.i64());
    let prog = b.bind(&x, b.int(7), &x);
    let after = simplify(prog, &FnTotality::new());
    assert!(matches!(&after, Expr::Let { .. }));
}

#[test]
fn nested_dead_let_eliminates() {
    // let x = 1 in (let y = 2 in x) — y dead, x live → let x = 1 in x
    let mut b = Builder::new();
    let x = b.local(b.i64());
    let y = b.local(b.i64());
    let prog = b.bind(&x, b.int(1), b.bind(&y, b.int(2), &x));
    let after = simplify(prog, &FnTotality::new());
    let Expr::Let { binder, body, .. } = &after else { panic!("expected outer Let") };
    assert_eq!(*binder, x.id);
    assert!(matches!(body.as_ref(), Expr::Var { sym, .. } if *sym == x.id));
}

#[test]
fn dead_let_with_total_app_eliminates() {
    // let x = pure_fn(1) in 99; pure_fn marked total → eliminates.
    let mut b = Builder::new();
    let pure_fn = b.func();
    let x = b.local(b.i64());
    let prog = b.bind(&x, b.call(pure_fn, [b.int(1)], b.i64()), b.int(99));
    let mut fns = FnTotality::new();
    fns.insert(pure_fn, true);
    let after = simplify(prog, &fns);
    assert!(matches!(&after, Expr::Lit { .. }));
}

#[test]
fn dead_let_with_unknown_callee_preserved() {
    // let x = unknown(1) in 99 — unknown is opaque → preserve.
    let mut b = Builder::new();
    let unknown = b.func();
    let x = b.local(b.i64());
    let prog = b.bind(&x, b.call(unknown, [b.int(1)], b.i64()), b.int(99));
    let after = simplify(prog, &FnTotality::new());
    assert!(matches!(&after, Expr::Let { .. }));
}

#[test]
fn simplify_descends_into_match_arms() {
    // match xs with
    //   | Cons(_, _) -> (let dead = 1 in 5)
    //   | Nil        -> 0
    // Cons arm's dead-let should fire, leaving body as `5`.
    let mut b = Builder::new();
    let list_i64 = b.list_of(b.i64());
    let xs = b.local(list_i64);
    let dead = b.local(b.i64());
    let cons = b.decl_tag();
    let nil = b.decl_tag();

    let prog = b.match_(
        &xs,
        [
            b.arm(
                b.pat_con(b.declared(cons), [Binder::Wildcard, Binder::Wildcard]),
                b.bind(&dead, b.int(1), b.int(5)),
            ),
            b.arm(b.pat_con(b.declared(nil), []), b.int(0)),
        ],
        b.i64(),
    );

    let after = simplify(prog, &FnTotality::new());
    let Expr::Match { arms, .. } = &after else { panic!("expected Match") };
    assert!(matches!(arms[0].body.as_ref(), Expr::Lit { .. }), "dead-let in Cons arm gone");
}
