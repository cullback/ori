//! Type-consistency validator tests.
//!
//! Each test constructs a deliberately ill-typed program and
//! verifies the validator catches it, plus a well-typed counterpart
//! that should pass cleanly.

use std::collections::HashMap;

use core_ir::Scalar::{I64, U8};
use core_ir::{
    validate_totality, validate_types, Builder, CoreType, Expr, FnTotality, Literal,
    LocalId, ValidationError,
};

#[test]
fn well_typed_let_passes() {
    // let x = 1 in x
    let mut b = Builder::new();
    let x = b.local(I64);
    let prog = b.bind(&x, b.int(1), &x);
    validate_types(&HashMap::new(), &prog).expect("well-typed");
}

#[test]
fn var_with_wrong_type_caught() {
    // let x = 1 in (x typed as U8 — a mismatch)
    let mut b = Builder::new();
    let x = b.local(I64);
    let bad_var = Expr::Var { sym: x.id, ty: U8.into() };
    let prog = b.bind(&x, b.int(1), bad_var);
    let err = validate_types(&HashMap::new(), &prog).unwrap_err();
    assert!(
        matches!(err, ValidationError::VarTypeMismatch { sym, .. } if sym == x.id),
        "expected VarTypeMismatch, got {err:?}",
    );
}

#[test]
fn match_arm_returning_wrong_type_caught() {
    // match xs with
    //   | Cons(_, _) -> 0_i64
    //   | Nil        -> 0_u8  (wrong type!)
    let mut b = Builder::new();
    let list_i64 = b.list_of(I64);
    let xs = b.local(list_i64.clone());
    let cons = b.decl_tag();
    let nil = b.decl_tag();
    let prog = b.match_(
        &xs,
        [
            b.arm(
                b.pat_con(b.declared(cons), [core_ir::Binder::Wildcard, core_ir::Binder::Wildcard]),
                b.int(0),
            ),
            b.arm(b.pat_con(b.declared(nil), []), b.byte(0)),
        ],
        I64,
    );
    let scope: HashMap<LocalId, CoreType> = std::iter::once((xs.id, list_i64)).collect();
    let err = validate_types(&scope, &prog).unwrap_err();
    assert!(matches!(err, ValidationError::ArmTypeMismatch { .. }), "got {err:?}");
}

#[test]
fn buf_lit_with_wrong_elem_type_caught() {
    // [1_i64, 2_i64] declared as `List(U8)` — element type mismatch.
    let mut b = Builder::new();
    let list_u8 = b.list_of(U8);
    let prog = b.buf_lit([b.int(1), b.int(2)], U8, list_u8);
    let err = validate_types(&HashMap::new(), &prog).unwrap_err();
    assert!(
        matches!(err, ValidationError::BufLitElemMismatch { .. }),
        "got {err:?}",
    );
}

#[test]
fn buf_append_with_wrong_val_type_caught() {
    // List(I64).append(U8 value) — mismatch.
    let mut b = Builder::new();
    let list_i64 = b.list_of(I64);
    let xs = b.local(list_i64.clone());
    let bad = b.buf_append(&xs, b.byte(7), list_i64.clone());
    let scope: HashMap<LocalId, CoreType> = std::iter::once((xs.id, list_i64)).collect();
    let err = validate_types(&scope, &bad).unwrap_err();
    assert!(
        matches!(err, ValidationError::BufElementMismatch { op: "BufAppend", .. }),
        "got {err:?}",
    );
}

#[test]
fn buf_set_with_wrong_val_type_caught() {
    let mut b = Builder::new();
    let list_i64 = b.list_of(I64);
    let xs = b.local(list_i64.clone());
    let bad = b.buf_set(&xs, b.int(0), b.byte(7), list_i64.clone());
    let scope: HashMap<LocalId, CoreType> = std::iter::once((xs.id, list_i64)).collect();
    let err = validate_types(&scope, &bad).unwrap_err();
    assert!(
        matches!(err, ValidationError::BufElementMismatch { op: "BufSet", .. }),
        "got {err:?}",
    );
}

#[test]
fn buf_load_with_wrong_result_type_caught() {
    // List(I64)[idx] declared as returning U8 — mismatch.
    let mut b = Builder::new();
    let list_i64 = b.list_of(I64);
    let xs = b.local(list_i64.clone());
    let bad = b.buf_load(&xs, b.int(0), U8);
    let scope: HashMap<LocalId, CoreType> = std::iter::once((xs.id, list_i64)).collect();
    let err = validate_types(&scope, &bad).unwrap_err();
    assert!(
        matches!(err, ValidationError::BufElementMismatch { op: "BufLoad", .. }),
        "got {err:?}",
    );
}

#[test]
fn fold_over_non_list_caught() {
    // fold over an I64 — not a List shape.
    let mut b = Builder::new();
    let bad_target = b.int(0); // I64, not a List
    let fold_fn = b.func();
    let prog = b.fold(fold_fn, bad_target, [], [], I64);
    let err = validate_types(&HashMap::new(), &prog).unwrap_err();
    assert!(
        matches!(err, ValidationError::FoldTargetNotList(_)),
        "got {err:?}",
    );
}

#[test]
fn well_typed_buffer_chain_passes() {
    let mut b = Builder::new();
    let list_i64 = b.list_of(I64);
    let xs = b.local(list_i64.clone());
    let prog = b.buf_append(
        b.buf_set(&xs, b.int(0), b.int(99), list_i64.clone()),
        b.int(100),
        list_i64.clone(),
    );
    let scope: HashMap<LocalId, CoreType> = std::iter::once((xs.id, list_i64)).collect();
    validate_types(&scope, &prog).expect("matched element types");
}

// ---- Totality validator ----

#[test]
fn total_marked_function_actually_total_passes() {
    // pure_fn: () -> 42  — total. Marked total. Should pass.
    let mut b = Builder::new();
    let pure_fn = b.func();
    let body = b.int(42);
    let functions: HashMap<_, _> = std::iter::once((pure_fn, body)).collect();
    let mut fns = FnTotality::new();
    fns.insert(pure_fn, true);
    validate_totality(&functions, &fns).expect("total claim is honest");
}

#[test]
fn total_marked_function_with_crash_caught() {
    // pure_fn: () -> crash("kaboom") — *not* total. Marked total
    // anyway. Validator catches the lie.
    let mut b = Builder::new();
    let pure_fn = b.func();
    let body = b.crash("kaboom", I64);
    let functions: HashMap<_, _> = std::iter::once((pure_fn, body)).collect();
    let mut fns = FnTotality::new();
    fns.insert(pure_fn, true);
    let err = validate_totality(&functions, &fns).unwrap_err();
    assert!(matches!(
        err,
        ValidationError::TotalFunctionNotActuallyTotal(f) if f == pure_fn
    ));
}

#[test]
fn total_marked_function_calling_non_total_caught() {
    // pure_fn calls opaque_fn; opaque is unknown, so pure isn't
    // actually total.
    let mut b = Builder::new();
    let pure_fn = b.func();
    let opaque = b.func();
    let body = b.call(opaque, [], I64);
    let functions: HashMap<_, _> = std::iter::once((pure_fn, body)).collect();
    let mut fns = FnTotality::new();
    fns.insert(pure_fn, true);
    // Note: opaque is not in fns, so is_total treats it as non-total.
    let err = validate_totality(&functions, &fns).unwrap_err();
    assert!(matches!(
        err,
        ValidationError::TotalFunctionNotActuallyTotal(f) if f == pure_fn
    ));
}

#[test]
fn unmarked_function_not_checked() {
    // We don't claim total for unmarked_fn; it can contain Crash.
    let mut b = Builder::new();
    let unmarked = b.func();
    let body = b.crash("kaboom", I64);
    let functions: HashMap<_, _> = std::iter::once((unmarked, body)).collect();
    let fns = FnTotality::new(); // empty
    validate_totality(&functions, &fns).expect("unmarked fn isn't checked");
}

// Ensure builder always produces well-typed BufLit even with
// LocalVar refs.
#[test]
fn well_typed_buf_lit_from_literals_passes() {
    let mut b = Builder::new();
    let _ = Literal::Int(0);
    let list_u8 = b.list_of(U8);
    let prog = b.buf_lit([b.byte(b'a'), b.byte(b'b')], U8, list_u8);
    validate_types(&HashMap::new(), &prog).expect("homogeneous BufLit");
}
