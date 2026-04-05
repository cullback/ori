use std::collections::HashMap;

use crate::ir::{NumVal, Value};

/// Compile and run an Ori program with the given I64 input.
fn run(source: &str, input: i64) -> Value {
    let tokens = crate::token::tokenize(source);
    let module = crate::parse::parse(tokens);
    let (program, input_var) = crate::lower::lower(module);
    let mut env = HashMap::new();
    env.insert(input_var, Value::VNum(NumVal::I64(input)));
    crate::eval::eval(&env, &program, &program.main)
}

fn run_i64(source: &str, input: i64) -> i64 {
    match run(source, input) {
        Value::VNum(NumVal::I64(n)) => n,
        other => panic!("expected I64 result, got {other:?}"),
    }
}

// ============================================================
// Arithmetic
// ============================================================

#[test]
fn identity() {
    let result = run_i64("main : I64\nmain = |x| x", 42);
    assert_eq!(result, 42);
}

#[test]
fn double() {
    let result = run_i64("main : I64\nmain = |arg| (\n  c = 2 * arg\n  c\n)", 21);
    assert_eq!(result, 42);
}

#[test]
fn arithmetic_precedence() {
    // 2 + 3 * 4 = 14 (not 20)
    let result = run_i64("main : I64\nmain = |x| 2 + 3 * 4", 0);
    assert_eq!(result, 14);
}

#[test]
fn nested_arithmetic() {
    let result = run_i64(
        "main : I64\nmain = |x| (\n  a = x + 1\n  b = a * 2\n  b + 3\n)",
        10,
    );
    assert_eq!(result, 25);
}

// ============================================================
// Tag unions and pattern matching
// ============================================================

#[test]
fn bool_not() {
    let source = "\
Bool : [True, False]

not : Bool -> Bool
not = |b| if b
    : True then False
    : False then True

bool_to_i64 : Bool -> I64
bool_to_i64 = |b| if b
    : True then 1
    : False then 0

main : I64
main = |arg| bool_to_i64(not(True))";

    assert_eq!(run_i64(source, 0), 0);
}

#[test]
fn bool_and() {
    let source = "\
Bool : [True, False]

and : Bool, Bool -> Bool
and = |a, b| if a
    : True then b
    : False then False

bool_to_i64 : Bool -> I64
bool_to_i64 = |b| if b
    : True then 1
    : False then 0

main : I64
main = |arg| bool_to_i64(and(True, True))";

    assert_eq!(run_i64(source, 0), 1);
}

#[test]
fn tag_with_payload() {
    let source = "\
Maybe : [Just(I64), Nothing]

unwrap_or : Maybe, I64 -> I64
unwrap_or = |m, default| if m
    : Just(val) then val
    : Nothing then default

main : I64
main = |arg| unwrap_or(Just(42), 0)";

    assert_eq!(run_i64(source, 0), 42);
}

#[test]
fn tag_with_payload_nothing() {
    let source = "\
Maybe : [Just(I64), Nothing]

unwrap_or : Maybe, I64 -> I64
unwrap_or = |m, default| if m
    : Just(val) then val
    : Nothing then default

main : I64
main = |arg| unwrap_or(Nothing, 99)";

    assert_eq!(run_i64(source, 0), 99);
}

// ============================================================
// Boolean if-then-else (desugars to match on Bool)
// ============================================================

#[test]
fn if_then_else_true_branch() {
    let source = "main : I64\nmain = |x| if x == 0 then 99 else x * 2";
    assert_eq!(run_i64(source, 0), 99);
}

#[test]
fn if_then_else_false_branch() {
    let source = "main : I64\nmain = |x| if x == 0 then 99 else x * 2";
    assert_eq!(run_i64(source, 5), 10);
}

#[test]
fn if_then_else_nested() {
    let source = "\
main : I64
main = |x| (
    a = if x == 0 then 1 else 0
    b = if a == 1 then 100 else 200
    b
)";
    assert_eq!(run_i64(source, 0), 100);
    assert_eq!(run_i64(source, 5), 200);
}

#[test]
fn not_equal() {
    let source = "main : I64\nmain = |x| if x != 0 then 1 else 0";
    assert_eq!(run_i64(source, 0), 0);
    assert_eq!(run_i64(source, 7), 1);
}

// ============================================================
// Prelude (Bool available without declaration)
// ============================================================

#[test]
fn prelude_bool_available() {
    // Use True/False without declaring Bool
    let source = "\
to_i64 : Bool -> I64
to_i64 = |b| if b
    : True then 1
    : False then 0

main : I64
main = |arg| to_i64(True)";

    assert_eq!(run_i64(source, 0), 1);
}

// ============================================================
// Multiple functions
// ============================================================

#[test]
fn multi_function_calls() {
    let source = "\
add1 : I64 -> I64
add1 = |x| x + 1

double : I64 -> I64
double = |x| x * 2

main : I64
main = |arg| double(add1(arg))";

    assert_eq!(run_i64(source, 10), 22);
}

#[test]
fn function_with_block() {
    let source = "\
compute : I64, I64 -> I64
compute = |a, b| (
    sum = a + b
    product = a * b
    sum + product
)

main : I64
main = |arg| compute(3, 4)";

    assert_eq!(run_i64(source, 0), 19);
}

// ============================================================
// File-based tests (programs/ directory)
// ============================================================

#[test]
fn program_double_ori() {
    let source = std::fs::read_to_string("programs/double.ori").unwrap();
    assert_eq!(run_i64(&source, 21), 42);
}

#[test]
fn program_bool_ori() {
    let source = std::fs::read_to_string("programs/bool.ori").unwrap();
    assert_eq!(run_i64(&source, 0), 0);
}

#[test]
fn program_conditional_ori() {
    let source = std::fs::read_to_string("programs/conditional.ori").unwrap();
    assert_eq!(run_i64(&source, 0), 99);
    assert_eq!(run_i64(&source, 5), 10);
}
