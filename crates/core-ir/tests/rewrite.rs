//! Rewrite rule tests.
//!
//! Exercises the rewrite layer end-to-end: build a program, run
//! `simplify` against a totality table, verify the result matches
//! the expected shape, and check the rewrite preserved scope
//! correctness.

use std::collections::HashSet;

use core_ir::{
    free_vars, simplify, validate_scope, Builder, Expr, FnTotality,
};

#[test]
fn free_vars_of_literal_is_empty() {
    let b = Builder::new();
    assert!(free_vars(&b.lit_i64(1)).is_empty());
}

#[test]
fn free_vars_of_var_is_singleton() {
    let mut b = Builder::new();
    let x = b.fresh_local();
    let prog = b.var(x, b.i64());
    let fv = free_vars(&prog);
    assert_eq!(fv, std::iter::once(x).collect::<HashSet<_>>());
}

#[test]
fn free_vars_of_let_excludes_bound_var() {
    // let x = 1 in (x + y) — y is free, x is bound
    let mut b = Builder::new();
    let plus = b.fresh_fn();
    let x = b.fresh_local();
    let y = b.fresh_local();
    let prog = b.let_(
        x,
        b.lit_i64(1),
        b.call(plus, vec![b.var(x, b.i64()), b.var(y, b.i64())], b.i64()),
    );
    let fv = free_vars(&prog);
    assert_eq!(fv, std::iter::once(y).collect::<HashSet<_>>());
}

#[test]
fn dead_let_eliminated_when_value_total() {
    // let x = 42 in 99 — x is unused; the literal value is total.
    let mut b = Builder::new();
    let x = b.fresh_local();
    let prog = b.let_(x, b.lit_i64(42), b.lit_i64(99));
    let fns = FnTotality::new();
    let after = simplify(prog, &fns);
    assert!(matches!(&after, Expr::Lit { .. }), "expected Lit, got {after}");
    validate_scope(&[], &after).expect("rewrite preserved scope");
}

#[test]
fn dead_let_preserved_when_value_crashes() {
    // let x = crash("boom") in 99 — x is unused but the value
    // crashes; eliminating would skip the crash, which is unsound.
    // The totality calculator returns false for Crash; the
    // rewrite should *not* fire.
    let mut b = Builder::new();
    let x = b.fresh_local();
    let prog = b.let_(x, b.crash("boom", b.i64()), b.lit_i64(99));
    let fns = FnTotality::new();
    let after = simplify(prog, &fns);
    assert!(
        matches!(&after, Expr::Let { .. }),
        "Let preserved because value crashes: got {after}",
    );
}

#[test]
fn live_let_preserved() {
    // let x = 7 in x — x is used; binding must stay.
    let mut b = Builder::new();
    let x = b.fresh_local();
    let prog = b.let_(x, b.lit_i64(7), b.var(x, b.i64()));
    let fns = FnTotality::new();
    let after = simplify(prog, &fns);
    assert!(matches!(&after, Expr::Let { .. }), "live binding stays: {after}");
}

#[test]
fn nested_dead_let_eliminates() {
    // let x = 1 in (let y = 2 in x)
    //   — y is dead, x is live.
    // Expected after simplify: let x = 1 in x  (inner Let gone)
    let mut b = Builder::new();
    let x = b.fresh_local();
    let y = b.fresh_local();
    let prog = b.let_(
        x,
        b.lit_i64(1),
        b.let_(y, b.lit_i64(2), b.var(x, b.i64())),
    );
    let fns = FnTotality::new();
    let after = simplify(prog, &fns);
    let Expr::Let { binder, body, .. } = &after else {
        panic!("expected outer Let, got {after}");
    };
    assert_eq!(*binder, x, "outer Let preserved with x");
    assert!(matches!(body.as_ref(), Expr::Var { sym, .. } if *sym == x));
}

#[test]
fn dead_let_with_total_app_eliminates() {
    // let x = pure_fn(1) in 99
    //   pure_fn is marked total in the FnTotality table.
    // Expected: 99 (the Let is eliminated because pure_fn is total).
    let mut b = Builder::new();
    let pure_fn = b.fresh_fn();
    let x = b.fresh_local();
    let prog = b.let_(
        x,
        b.call(pure_fn, vec![b.lit_i64(1)], b.i64()),
        b.lit_i64(99),
    );
    let mut fns = FnTotality::new();
    fns.insert(pure_fn, true);
    let after = simplify(prog, &fns);
    assert!(matches!(&after, Expr::Lit { .. }), "expected Lit: {after}");
}

#[test]
fn dead_let_with_unknown_callee_preserved() {
    // let x = unknown_fn(1) in 99
    //   unknown_fn isn't in the FnTotality table; conservatively
    //   treat as non-total. The Let stays.
    let mut b = Builder::new();
    let unknown_fn = b.fresh_fn();
    let x = b.fresh_local();
    let prog = b.let_(
        x,
        b.call(unknown_fn, vec![b.lit_i64(1)], b.i64()),
        b.lit_i64(99),
    );
    let fns = FnTotality::new(); // empty — unknown_fn is opaque
    let after = simplify(prog, &fns);
    assert!(matches!(&after, Expr::Let { .. }), "Let preserved: {after}");
}

#[test]
fn simplify_descends_into_match_arms() {
    // match x with
    //   | Cons(_, _) -> (let dead = 1 in 5)
    //   | Nil        -> 0
    //
    // The inner dead-let in the Cons arm should eliminate, leaving
    // the arm body as just `5`. This proves the recursive walk
    // descends into Match arms.
    let mut b = Builder::new();
    let xs = b.fresh_local();
    let dead = b.fresh_local();
    let cons = b.fresh_decl_tag();
    let nil = b.fresh_decl_tag();
    let list_head = b.fresh_type();
    let list_ty = b.adt(list_head, vec![b.i64()]);

    let cons_arm_body = b.let_(dead, b.lit_i64(1), b.lit_i64(5));
    let cons_arm = b.arm(
        b.pat_con(
            b.declared_tag(cons),
            vec![core_ir::Binder::Wildcard, core_ir::Binder::Wildcard],
        ),
        cons_arm_body,
    );
    let nil_arm = b.arm(b.pat_con(b.declared_tag(nil), vec![]), b.lit_i64(0));

    let prog = b.match_(b.var(xs, list_ty), vec![cons_arm, nil_arm], b.i64());
    let fns = FnTotality::new();
    let after = simplify(prog, &fns);

    let Expr::Match { arms, .. } = &after else {
        panic!("expected Match, got {after}");
    };
    let Expr::Lit { .. } = arms[0].body.as_ref() else {
        panic!("expected Cons arm body to be Lit (dead-let eliminated)");
    };
}
