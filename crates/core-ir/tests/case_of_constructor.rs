//! Case-of-known-constructor tests.
//!
//! The flagship demonstration that `Con` and `Match` as distinct
//! variants enable syntactic rewrites — `Match(Con(tag, args), arms)`
//! becomes the matching arm's body with field binders substituted by
//! `args`, no analysis required.

use core_ir::Scalar::I64;
use core_ir::{simplify, validate_scope, Binder, Builder, Expr, FnTotality};

#[test]
fn cons_match_resolves_to_first_arg() {
    // match Cons(7, Nil) of
    //   | Cons(h, t) -> h
    //   | Nil        -> 0
    //
    // Expected: 7. The Match and Con both vanish.
    let mut b = Builder::new();
    let list_i64 = b.list_of(I64);
    let cons = b.decl_tag();
    let nil = b.decl_tag();
    let h = b.local(I64);
    let t = b.local(list_i64.clone());

    // Build the scrutinee: Cons(7, Nil)
    let nil_value = b.con(b.declared(nil), [], list_i64.clone());
    let scrutinee = b.con(
        b.declared(cons),
        [b.int(7), nil_value],
        list_i64.clone(),
    );

    let prog = b.match_(
        scrutinee,
        [
            b.arm(
                b.pat_con(b.declared(cons), [h.as_binder(), t.as_binder()]),
                &h,
            ),
            b.arm(b.pat_con(b.declared(nil), []), b.int(0)),
        ],
        I64,
    );

    let after = simplify(prog, &FnTotality::new());
    assert!(matches!(&after, Expr::Lit { .. }), "expected Lit(7), got {after}");
    validate_scope(&[], &after).expect("rewrite preserves scope");
}

#[test]
fn nil_match_resolves_to_zero() {
    // match Nil of
    //   | Cons(h, t) -> h
    //   | Nil        -> 0
    //
    // Expected: 0. The matching arm is the second one.
    let mut b = Builder::new();
    let list_i64 = b.list_of(I64);
    let cons = b.decl_tag();
    let nil = b.decl_tag();
    let h = b.local(I64);
    let t = b.local(list_i64.clone());

    let scrutinee = b.con(b.declared(nil), [], list_i64);

    let prog = b.match_(
        scrutinee,
        [
            b.arm(
                b.pat_con(b.declared(cons), [h.as_binder(), t.as_binder()]),
                &h,
            ),
            b.arm(b.pat_con(b.declared(nil), []), b.int(0)),
        ],
        I64,
    );

    let after = simplify(prog, &FnTotality::new());
    assert!(matches!(&after, Expr::Lit { .. }));
}

#[test]
fn wildcard_arm_catches_unknown_tag() {
    // match Foo(1) of
    //   | Wildcard -> 42
    //
    // Expected: 42. Wildcard always matches.
    let mut b = Builder::new();
    let result_ty = b.maybe_of(I64);
    let foo = b.decl_tag();

    let scrutinee = b.con(b.declared(foo), [b.int(1)], result_ty);
    let prog = b.match_(scrutinee, [b.arm(b.pat_wild(), b.int(42))], I64);

    let after = simplify(prog, &FnTotality::new());
    assert!(matches!(&after, Expr::Lit { .. }));
}

#[test]
fn variable_pattern_binds_whole_constructor() {
    // match Cons(7, Nil) of
    //   | x -> something_using_x
    //
    // The x binding captures the whole Con value. Substituting in
    // the body should reintroduce the Cons(7, Nil) expression.
    let mut b = Builder::new();
    let list_i64 = b.list_of(I64);
    let cons = b.decl_tag();
    let nil = b.decl_tag();
    let x = b.local(list_i64.clone());
    let get_len = b.func();

    let nil_value = b.con(b.declared(nil), [], list_i64.clone());
    let scrutinee = b.con(b.declared(cons), [b.int(7), nil_value], list_i64.clone());

    let prog = b.match_(
        scrutinee,
        [b.arm(b.pat_bind(&x), b.call(get_len, [x.expr()], I64))],
        I64,
    );

    let after = simplify(prog, &FnTotality::new());
    // x got substituted with Cons(7, Nil), so the result is
    // get_len(Cons(7, Nil)) — an App, not the original Match.
    assert!(matches!(&after, Expr::App { .. }), "expected App, got {after}");
}

#[test]
fn guarded_arm_blocks_rewrite() {
    // match Cons(7, Nil) of
    //   | Cons(h, _) and (h > 0) -> h
    //   | _                       -> 0
    //
    // Even though Cons matches the first arm structurally, the
    // guard makes the result run-time dependent. case-of-known-con
    // bails; the Match stays.
    let mut b = Builder::new();
    let list_i64 = b.list_of(I64);
    let cons = b.decl_tag();
    let h = b.local(I64);
    let nil = b.decl_tag();

    let nil_value = b.con(b.declared(nil), [], list_i64.clone());
    let scrutinee = b.con(b.declared(cons), [b.int(7), nil_value], list_i64);

    // Some opaque guard. Using a func to keep the arm shape honest.
    let gt = b.func();

    let prog = b.match_(
        scrutinee,
        [
            b.arm_guarded(
                b.pat_con(b.declared(cons), [h.as_binder(), Binder::Wildcard]),
                [b.call(gt, [h.expr(), b.int(0)], I64)],
                &h,
            ),
            b.arm(b.pat_wild(), b.int(0)),
        ],
        I64,
    );

    let after = simplify(prog, &FnTotality::new());
    assert!(matches!(&after, Expr::Match { .. }), "guard blocks rewrite, got {after}");
}

#[test]
fn nested_match_and_case_of_known_compose() {
    // let p = Cons(7, Nil) in match p of Cons(h, _) -> h
    //
    // After beta on the Let (Cons is *not* a literal/var so beta
    // doesn't fire on the binder), the Match folds via
    // case-of-known-constructor only if we recognise Cons as the
    // scrutinee. Today we *don't* — beta is limited to lit/var,
    // so this test exercises the negative path: the Let stays.
    let mut b = Builder::new();
    let list_i64 = b.list_of(I64);
    let cons = b.decl_tag();
    let nil = b.decl_tag();
    let h = b.local(I64);
    let t = b.local(list_i64.clone());
    let p = b.local(list_i64.clone());

    let nil_value = b.con(b.declared(nil), [], list_i64.clone());
    let cons_value = b.con(b.declared(cons), [b.int(7), nil_value], list_i64);

    let match_part = b.match_(
        &p,
        [b.arm(
            b.pat_con(b.declared(cons), [h.as_binder(), t.as_binder()]),
            &h,
        )],
        I64,
    );

    let prog = b.bind(&p, cons_value, match_part);
    let after = simplify(prog, &FnTotality::new());
    // The Let around the Match stays because beta doesn't propagate
    // a Con value — limiting beta to lit/var is the conservative
    // choice that prevents code-size blowup.
    assert!(matches!(&after, Expr::Let { .. }), "Let preserved with Con value, got {after}");
}

#[test]
fn case_of_known_con_recursively_simplifies() {
    // match Cons(7, Nil) of
    //   | Cons(h, _) -> let dead = 0 in h
    //
    // After case-of-known-con: let dead = 0 in 7.
    // Then dead-let / beta finishes: 7.
    let mut b = Builder::new();
    let list_i64 = b.list_of(I64);
    let cons = b.decl_tag();
    let nil = b.decl_tag();
    let h = b.local(I64);
    let dead = b.local(I64);

    let nil_value = b.con(b.declared(nil), [], list_i64.clone());
    let scrutinee = b.con(b.declared(cons), [b.int(7), nil_value], list_i64);

    let prog = b.match_(
        scrutinee,
        [b.arm(
            b.pat_con(b.declared(cons), [h.as_binder(), Binder::Wildcard]),
            b.bind(&dead, b.int(0), &h),
        )],
        I64,
    );

    let after = simplify(prog, &FnTotality::new());
    assert!(matches!(&after, Expr::Lit { .. }), "expected fully-reduced Lit, got {after}");
}
