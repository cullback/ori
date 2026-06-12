//! Pretty-printer tests.
//!
//! Snapshot-style: build a program, render it, compare against
//! the expected string. The output format is for human readers
//! debugging the IR; small format tweaks here are expected.

use core_ir::{Binder, Builder, FoldShape};

#[test]
fn lit_renders_with_type() {
    let b = Builder::new();
    let prog = b.lit_i64(42);
    assert_eq!(format!("{prog}"), "42:I64");
}

#[test]
fn var_renders_with_sym_and_type() {
    let mut b = Builder::new();
    let x = b.fresh_local();
    let prog = b.var(x, b.i64());
    assert_eq!(format!("{prog}"), "%0:I64");
}

#[test]
fn app_renders_call_shape() {
    let mut b = Builder::new();
    let plus = b.fresh_fn();
    let prog = b.call(plus, vec![b.lit_i64(1), b.lit_i64(2)], b.i64());
    assert_eq!(format!("{prog}"), "@0(1:I64, 2:I64):I64");
}

#[test]
fn crash_renders_with_msg() {
    let b = Builder::new();
    let prog = b.crash("kaboom", b.i64());
    assert_eq!(format!("{prog}"), "Crash(\"kaboom\"):I64");
}

#[test]
fn let_renders_multiline() {
    let mut b = Builder::new();
    let x = b.fresh_local();
    let prog = b.let_(x, b.lit_i64(1), b.var(x, b.i64()));
    let rendered = format!("{prog}");
    assert!(rendered.contains("let %0 ="));
    assert!(rendered.contains("1:I64"));
    assert!(rendered.contains("in"));
    assert!(rendered.contains("%0:I64"));
}

#[test]
fn match_renders_arms() {
    let mut b = Builder::new();
    let xs = b.fresh_local();
    let cons = b.fresh_decl_tag();
    let nil = b.fresh_decl_tag();
    let h = b.fresh_local();
    let t = b.fresh_local();
    let list_head = b.fresh_type();
    let list_ty = b.adt(list_head, vec![b.i64()]);
    let prog = b.match_(
        b.var(xs, list_ty.clone()),
        vec![
            b.arm(
                b.pat_con(b.declared_tag(cons), vec![Binder::Sym(h), Binder::Sym(t)]),
                b.var(h, b.i64()),
            ),
            b.arm(b.pat_con(b.declared_tag(nil), vec![]), b.lit_i64(0)),
        ],
        b.i64(),
    );
    let rendered = format!("{prog}");
    assert!(rendered.contains("match %0:T0(I64)"));
    assert!(rendered.contains("| D0(%1, %2) -> %1:I64"));
    assert!(rendered.contains("| D1 -> 0:I64"));
}

#[test]
fn fold_renders_kind_and_shape() {
    let mut b = Builder::new();
    let xs = b.fresh_local();
    let map_fn = b.fresh_fn();
    let f = b.fresh_local();
    let list_head = b.fresh_type();
    let list_i64 = b.adt(list_head, vec![b.i64()]);
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
    let rendered = format!("{prog}");
    assert!(rendered.contains("Fold[Total, Map] @0"));
    assert!(rendered.contains("target = %0"));
    assert!(rendered.contains("captures = [%1:I64]"));
}

#[test]
fn buf_lit_renders_compact() {
    let b = Builder::new();
    let list_head = core_ir::TypeId(99);
    let list_u8 = b.adt(list_head, vec![b.u8()]);
    let prog = b.buf_lit(
        vec![b.lit_u8(b'h'), b.lit_u8(b'i')],
        b.u8(),
        list_u8.clone(),
    );
    let rendered = format!("{prog}");
    assert!(rendered.starts_with("["));
    assert!(rendered.contains("104:U8")); // 'h'
    assert!(rendered.contains(":T99(U8)(U8)")); // result-type then elem-type
}
