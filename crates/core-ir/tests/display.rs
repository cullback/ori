//! Pretty-printer smoke tests.

use core_ir::Scalar::{I64, U8};
use core_ir::{Builder, FoldShape};

#[test]
fn lit_renders_with_type() {
    let b = Builder::new();
    assert_eq!(format!("{}", b.int(42)), "42:I64");
}

#[test]
fn var_renders_with_sym_and_type() {
    let mut b = Builder::new();
    let x = b.local(I64);
    assert_eq!(format!("{}", x.expr()), "%0:I64");
}

#[test]
fn app_renders_call_shape() {
    let mut b = Builder::new();
    let plus = b.func();
    assert_eq!(
        format!("{}", b.call(plus, [b.int(1), b.int(2)], I64)),
        "@0(1:I64, 2:I64):I64",
    );
}

#[test]
fn crash_renders_with_msg() {
    let b = Builder::new();
    assert_eq!(format!("{}", b.crash("kaboom", I64)), "Crash(\"kaboom\"):I64");
}

#[test]
fn let_renders_multiline() {
    let mut b = Builder::new();
    let x = b.local(I64);
    let prog = b.bind(&x, b.int(1), &x);
    let rendered = format!("{prog}");
    assert!(rendered.contains("let %0 ="));
    assert!(rendered.contains("1:I64"));
    assert!(rendered.contains("in"));
    assert!(rendered.contains("%0:I64"));
}

#[test]
fn match_renders_arms() {
    let mut b = Builder::new();
    let list_i64 = b.list_of(I64);
    let xs = b.local(list_i64);
    let cons = b.decl_tag();
    let nil = b.decl_tag();
    let h = b.local(I64);
    let t = b.local(I64);

    let prog = b.match_(
        &xs,
        [
            b.arm(b.pat_con(b.declared(cons), [h.as_binder(), t.as_binder()]), &h),
            b.arm(b.pat_con(b.declared(nil), []), b.int(0)),
        ],
        I64,
    );

    let rendered = format!("{prog}");
    assert!(rendered.contains("match %0"));
    assert!(rendered.contains("| D0(%1, %2) -> %1:I64"));
    assert!(rendered.contains("| D1 -> 0:I64"));
}

#[test]
fn fold_renders_kind_and_shape() {
    let mut b = Builder::new();
    let list_i64 = b.list_of(I64);
    let xs = b.local(list_i64.clone());
    let f = b.local(I64);
    let map_fn = b.func();

    let prog = b.with_shape(
        b.fold(map_fn, &xs, [], [f.expr()], list_i64),
        FoldShape::Map,
    );

    let rendered = format!("{prog}");
    assert!(rendered.contains("Fold[Total, Map] @0"));
    assert!(rendered.contains("target = %0"));
    assert!(rendered.contains("captures = [%1:I64]"));
}

#[test]
fn buf_lit_renders_compact() {
    let mut b = Builder::new();
    let list_u8 = b.list_of(U8);
    let prog = b.buf_lit([b.byte(b'h'), b.byte(b'i')], U8, list_u8);
    let rendered = format!("{prog}");
    assert!(rendered.starts_with("["));
    assert!(rendered.contains("104:U8"));
    assert!(rendered.contains("(U8)"));
}
