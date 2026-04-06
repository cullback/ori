use std::collections::HashMap;

use crate::ir::{NumVal, Value};

/// Compile and run an Ori program with the given I64 input.
fn run(source: &str, input: i64) -> Value {
    let parsed = crate::parse::parse(source);
    let (module, scope) = crate::resolve::resolve_imports(parsed);
    crate::infer::check(source, &module, &scope);
    let (program, input_var) = crate::lower::lower(&module, &scope);
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

fn run_u64(source: &str, input: i64) -> u64 {
    match run(source, input) {
        Value::VNum(NumVal::U64(n)) => n,
        other => panic!("expected U64 result, got {other:?}"),
    }
}

// ============================================================
// Tuples
// ============================================================

#[test]
fn tuple_basic() {
    let source = "\
main : I64 -> I64
main = |arg| (
    pair = (1, 2)
    (a, b) = pair
    a + b
)";
    assert_eq!(run_i64(source, 0), 3);
}

#[test]
fn tuple_from_function() {
    let source = "\
swap = |a, b| (b, a)

main : I64 -> I64
main = |arg| (
    (x, y) = swap(3, 7)
    x * 10 + y
)";
    assert_eq!(run_i64(source, 0), 73);
}

#[test]
fn tuple_nested() {
    let source = "\
main : I64 -> I64
main = |arg| (
    t = ((1, 2), (3, 4))
    ((a, b), (c, d)) = t
    a + b + c + d
)";
    assert_eq!(run_i64(source, 0), 10);
}

// ============================================================
// Arithmetic
// ============================================================

#[test]
fn identity() {
    let result = run_i64("main : I64 -> I64\nmain = |x| x", 42);
    assert_eq!(result, 42);
}

#[test]
fn double() {
    let result = run_i64(
        "main : I64 -> I64\nmain = |arg| (\n  c = 2 * arg\n  c\n)",
        21,
    );
    assert_eq!(result, 42);
}

#[test]
fn arithmetic_precedence() {
    // 2 + 3 * 4 = 14 (not 20)
    let result = run_i64("main : I64 -> I64\nmain = |x| 2 + 3 * 4", 0);
    assert_eq!(result, 14);
}

#[test]
fn nested_arithmetic() {
    let result = run_i64(
        "main : I64 -> I64\nmain = |x| (\n  a = x + 1\n  b = a * 2\n  b + 3\n)",
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

main : I64 -> I64
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

main : I64 -> I64
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

main : I64 -> I64
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

main : I64 -> I64
main = |arg| unwrap_or(Nothing, 99)";

    assert_eq!(run_i64(source, 0), 99);
}

// ============================================================
// Boolean if-then-else (desugars to match on Bool)
// ============================================================

#[test]
fn if_then_else_true_branch() {
    let source = "main : I64 -> I64\nmain = |x| if x == 0 then 99 else x * 2";
    assert_eq!(run_i64(source, 0), 99);
}

#[test]
fn if_then_else_false_branch() {
    let source = "main : I64 -> I64\nmain = |x| if x == 0 then 99 else x * 2";
    assert_eq!(run_i64(source, 5), 10);
}

#[test]
fn if_then_else_nested() {
    let source = "\
main : I64 -> I64
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
    let source = "main : I64 -> I64\nmain = |x| if x != 0 then 1 else 0";
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

main : I64 -> I64
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

main : I64 -> I64
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

main : I64 -> I64
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

// ============================================================
// Fold (structural recursion)
// ============================================================

#[test]
fn fold_nat_to_i64() {
    let source = "\
Nat : [Zero, Succ(Nat)]

to_i64 : Nat -> I64
to_i64 = |n| fold n
    : Zero then 0
    : Succ(prev) then prev + 1

main : I64 -> I64
main = |arg| to_i64(Succ(Succ(Succ(Zero))))";

    assert_eq!(run_i64(source, 0), 3);
}

#[test]
fn fold_list_sum() {
    let source = "\
Lnk : [Nil, Cons(I64, Lnk)]

list_sum : Lnk -> I64
list_sum = |xs| fold xs
    : Nil then 0
    : Cons(hd, rest) then hd + rest

main : I64 -> I64
main = |arg| list_sum(Cons(1, Cons(2, Cons(3, Nil))))";

    assert_eq!(run_i64(source, 0), 6);
}

#[test]
fn fold_list_length() {
    let source = "\
Lnk : [Nil, Cons(I64, Lnk)]

list_length : Lnk -> I64
list_length = |xs| fold xs
    : Nil then 0
    : Cons(_, rest) then rest + 1

main : I64 -> I64
main = |arg| list_length(Cons(10, Cons(20, Cons(30, Cons(40, Cons(50, Nil))))))";

    assert_eq!(run_i64(source, 0), 5);
}

#[test]
fn fold_tree_sum() {
    let source = "\
Tree : [Leaf(I64), Branch(Tree, Tree)]

tree_sum : Tree -> I64
tree_sum = |t| fold t
    : Leaf(val) then val
    : Branch(left, right) then left + right

main : I64 -> I64
main = |arg| tree_sum(Branch(Branch(Leaf(1), Leaf(2)), Leaf(3)))";

    assert_eq!(run_i64(source, 0), 6);
}

#[test]
fn fold_tree_depth() {
    let source = "\
Tree : [Leaf(I64), Branch(Tree, Tree)]

max : I64, I64 -> I64
max = |a, b| if a != b then (if b != a then a else b) else a

tree_depth : Tree -> I64
tree_depth = |t| fold t
    : Leaf(_) then 1
    : Branch(left, right) then (
        m = max(left, right)
        m + 1
    )

main : I64 -> I64
main = |arg| tree_depth(Branch(Branch(Leaf(1), Leaf(2)), Leaf(3)))";

    assert_eq!(run_i64(source, 0), 3);
}

#[test]
fn fold_list_map_inc() {
    let source = "\
Lnk : [Nil, Cons(I64, Lnk)]

map_inc : Lnk -> Lnk
map_inc = |xs| fold xs
    : Nil then Nil
    : Cons(hd, rest) then Cons(hd + 1, rest)

list_sum : Lnk -> I64
list_sum = |xs| fold xs
    : Nil then 0
    : Cons(hd, rest) then hd + rest

main : I64 -> I64
main = |arg| list_sum(map_inc(Cons(1, Cons(2, Cons(3, Nil)))))";

    // (1+1) + (2+1) + (3+1) = 9
    assert_eq!(run_i64(source, 0), 9);
}

#[test]
fn fold_factorial() {
    let source = "\
Nat : [Zero, Succ(Nat)]
Pair : [MkPair(I64, I64)]

factorial : Nat -> I64
factorial = |n| (
    result = fold n
        : Zero then MkPair(0, 1)
        : Succ(rec) then
            if rec
                : MkPair(idx, f) then (
                    next = idx + 1
                    MkPair(next, next * f)
                )
    if result
        : MkPair(_, f) then f
)

main : I64 -> I64
main = |arg| factorial(Succ(Succ(Succ(Succ(Succ(Zero))))))";

    assert_eq!(run_i64(source, 0), 120);
}

#[test]
fn fold_fibonacci() {
    let source = "\
Nat : [Zero, Succ(Nat)]
Pair : [MkPair(I64, I64)]

fibonacci : Nat -> I64
fibonacci = |n| (
    result = fold n
        : Zero then MkPair(0, 1)
        : Succ(rec) then
            if rec
                : MkPair(a, b) then MkPair(b, a + b)
    if result
        : MkPair(a, _) then a
)

main : I64 -> I64
main = |arg| fibonacci(Succ(Succ(Succ(Succ(Succ(Succ(Succ(Succ(Succ(Succ(Zero)))))))))))";

    assert_eq!(run_i64(source, 0), 55);
}

// ============================================================
// File-based fold tests
// ============================================================

#[test]
fn program_nat_to_i64_ori() {
    let source = std::fs::read_to_string("programs/nat_to_i64.ori").unwrap();
    assert_eq!(run_i64(&source, 0), 3);
}

#[test]
fn program_list_sum_ori() {
    let source = std::fs::read_to_string("programs/list_sum.ori").unwrap();
    assert_eq!(run_i64(&source, 0), 42);
}

#[test]
fn program_tree_sum_ori() {
    let source = std::fs::read_to_string("programs/tree_sum.ori").unwrap();
    assert_eq!(run_i64(&source, 0), 6);
}

// ============================================================
// Higher-order functions (defunctionalization)
// ============================================================

#[test]
fn lambda_no_capture() {
    let source = "\
Lnk : [Nil, Cons(I64, Lnk)]

map : Lnk, (I64 -> I64) -> Lnk
map = |xs, f| fold xs
    : Nil then Nil
    : Cons(hd, rest) then Cons(f(hd), rest)

list_sum : Lnk -> I64
list_sum = |xs| fold xs
    : Nil then 0
    : Cons(hd, rest) then hd + rest

main : I64 -> I64
main = |arg| list_sum(map(Cons(1, Cons(2, Cons(3, Nil))), |x| x + 1))";

    assert_eq!(run_i64(source, 0), 9);
}

#[test]
fn lambda_with_capture() {
    let source = "\
Lnk : [Nil, Cons(I64, Lnk)]

map : Lnk, (I64 -> I64) -> Lnk
map = |xs, f| fold xs
    : Nil then Nil
    : Cons(hd, rest) then Cons(f(hd), rest)

list_sum : Lnk -> I64
list_sum = |xs| fold xs
    : Nil then 0
    : Cons(hd, rest) then hd + rest

main : I64 -> I64
main = |n| list_sum(map(Cons(1, Cons(2, Cons(3, Nil))), |x| x + n))";

    assert_eq!(run_i64(source, 10), 36);
}

#[test]
fn func_ref_as_arg() {
    let source = "\
Lnk : [Nil, Cons(I64, Lnk)]

map : Lnk, (I64 -> I64) -> Lnk
map = |xs, f| fold xs
    : Nil then Nil
    : Cons(hd, rest) then Cons(f(hd), rest)

add1 : I64 -> I64
add1 = |x| x + 1

list_sum : Lnk -> I64
list_sum = |xs| fold xs
    : Nil then 0
    : Cons(hd, rest) then hd + rest

main : I64 -> I64
main = |arg| list_sum(map(Cons(1, Cons(2, Cons(3, Nil))), add1))";

    assert_eq!(run_i64(source, 0), 9);
}

#[test]
fn multiple_lambdas_same_set() {
    let source = "\
apply_to : I64, (I64 -> I64) -> I64
apply_to = |x, f| f(x)

main : I64 -> I64
main = |x| (
    a = apply_to(x, |y| y + 1)
    b = apply_to(x, |y| y * 2)
    a + b
)";

    // x=5: a = 6, b = 10, result = 16
    assert_eq!(run_i64(source, 5), 16);
}

#[test]
fn lambda_and_func_ref_same_set() {
    let source = "\
double : I64 -> I64
double = |x| x * 2

apply_to : I64, (I64 -> I64) -> I64
apply_to = |x, f| f(x)

main : I64 -> I64
main = |x| (
    a = apply_to(x, double)
    b = apply_to(x, |y| y + 10)
    a + b
)";

    // x=3: a = 6, b = 13, result = 19
    assert_eq!(run_i64(source, 3), 19);
}

#[test]
fn walk_via_fold_with_lambda() {
    // walk implemented as a user function using fold + lambda
    let source = "\
Lnk : [Nil, Cons(I64, Lnk)]

walk : Lnk, I64, (I64, I64 -> I64) -> I64
walk = |xs, init, f| fold xs
    : Nil then init
    : Cons(hd, acc) then f(acc, hd)

main : I64 -> I64
main = |arg| walk(Cons(1, Cons(2, Cons(3, Nil))), 0, |acc, x| acc + x)";

    assert_eq!(run_i64(source, 0), 6);
}

// ============================================================
// Associated functions on types
// ============================================================

#[test]
fn associated_fn_basic() {
    let source = "\
Lnk : [Nil, Cons(I64, Lnk)].(
    sum : Lnk -> I64
    sum = |xs| fold xs
        : Nil then 0
        : Cons(hd, rest) then hd + rest
)

main : I64 -> I64
main = |arg| Lnk.sum(Cons(1, Cons(2, Cons(3, Nil))))";

    assert_eq!(run_i64(source, 0), 6);
}

#[test]
fn associated_fn_with_lambda() {
    let source = "\
Lnk : [Nil, Cons(I64, Lnk)].(
    map : Lnk, (I64 -> I64) -> Lnk
    map = |xs, f| fold xs
        : Nil then Nil
        : Cons(hd, rest) then Cons(f(hd), rest)

    sum : Lnk -> I64
    sum = |xs| fold xs
        : Nil then 0
        : Cons(hd, rest) then hd + rest
)

main : I64 -> I64
main = |n| Lnk.sum(Lnk.map(Cons(1, Cons(2, Cons(3, Nil))), |x| x + n))";

    assert_eq!(run_i64(source, 10), 36);
}

#[test]
fn associated_fn_walk() {
    let source = "\
Lnk : [Nil, Cons(I64, Lnk)].(
    walk : Lnk, I64, (I64, I64 -> I64) -> I64
    walk = |xs, init, f| fold xs
        : Nil then init
        : Cons(hd, acc) then f(acc, hd)
)

main : I64 -> I64
main = |arg| Lnk.walk(Cons(1, Cons(2, Cons(3, Nil))), 0, |acc, x| acc + x)";

    assert_eq!(run_i64(source, 0), 6);
}

#[test]
fn associated_fn_calling_another() {
    let source = "\
Lnk : [Nil, Cons(I64, Lnk)].(
    map : Lnk, (I64 -> I64) -> Lnk
    map = |xs, f| fold xs
        : Nil then Nil
        : Cons(hd, rest) then Cons(f(hd), rest)

    sum : Lnk -> I64
    sum = |xs| fold xs
        : Nil then 0
        : Cons(hd, rest) then hd + rest

    sum_doubled : Lnk -> I64
    sum_doubled = |xs| Lnk.sum(Lnk.map(xs, |x| x * 2))
)

main : I64 -> I64
main = |arg| Lnk.sum_doubled(Cons(1, Cons(2, Cons(3, Nil))))";

    assert_eq!(run_i64(source, 0), 12);
}

// ============================================================
// Records and row polymorphism
// ============================================================

#[test]
fn record_literal_and_field_access() {
    let source = "\
main : I64 -> I64
main = |arg| (
    point = { x: 1, y: 2 }
    point.x + point.y
)";
    assert_eq!(run_i64(source, 0), 3);
}

#[test]
fn record_as_function_arg() {
    let source = "\
get_x = |r| r.x

main : I64 -> I64
main = |arg| get_x({ x: 42, y: 0 })";
    assert_eq!(run_i64(source, 0), 42);
}

#[test]
fn record_row_polymorphism() {
    let source = "\
get_x = |r| r.x

main : I64 -> I64
main = |arg| (
    a = get_x({ x: 10, y: 20 })
    b = get_x({ x: 30, z: 40 })
    a + b
)";
    assert_eq!(run_i64(source, 0), 40);
}

#[test]
fn nested_record_field_access() {
    let source = "\
main : I64 -> I64
main = |arg| (
    r = { inner: { val: 42 } }
    r.inner.val
)";
    assert_eq!(run_i64(source, 0), 42);
}

#[test]
fn record_returned_from_function() {
    let source = "\
make_point = |x, y| { x: x, y: y }

main : I64 -> I64
main = |arg| (
    p = make_point(3, 4)
    p.x + p.y
)";
    assert_eq!(run_i64(source, 0), 7);
}

#[test]
#[should_panic(expected = "type error")]
fn record_type_error_missing_field() {
    run_i64(
        "\
get_x = |r| r.x
main : I64 -> I64
main = |arg| get_x({ y: 1 })",
        0,
    );
}

// ============================================================
// Record destructuring
// ============================================================

#[test]
fn record_destructure_basic() {
    let source = "\
main : I64 -> I64
main = |arg| (
    point = { x: 10, y: 20 }
    { x, y } = point
    x + y
)";
    assert_eq!(run_i64(source, 0), 30);
}

#[test]
fn record_destructure_rename() {
    let source = "\
main : I64 -> I64
main = |arg| (
    point = { x: 3, y: 4 }
    { x: a, y: b } = point
    a * b
)";
    assert_eq!(run_i64(source, 0), 12);
}

#[test]
fn record_destructure_nested() {
    let source = "\
main : I64 -> I64
main = |arg| (
    r = { inner: { val: 42 } }
    { inner } = r
    { val } = inner
    val
)";
    assert_eq!(run_i64(source, 0), 42);
}

// ============================================================
// Type aliases
// ============================================================

#[test]
fn type_alias_record() {
    let source = "\
Point : { x: I64, y: I64 }

make_point : I64, I64 -> Point
make_point = |x, y| { x: x, y: y }

main : I64 -> I64
main = |arg| (
    p = make_point(3, 4)
    p.x + p.y
)";
    assert_eq!(run_i64(source, 0), 7);
}

#[test]
fn type_alias_in_function_annotation() {
    let source = "\
Point : { x: I64, y: I64 }

get_x : Point -> I64
get_x = |p| p.x

main : I64 -> I64
main = |arg| get_x({ x: 42, y: 0 })";
    assert_eq!(run_i64(source, 0), 42);
}

// ============================================================
// Type inference — error detection
// ============================================================

#[test]
#[should_panic(expected = "type error")]
fn type_error_add_bool() {
    run_i64("main : I64 -> I64\nmain = |x| x + True", 0);
}

#[test]
#[should_panic(expected = "type error")]
fn type_error_if_branch_mismatch() {
    run_i64(
        "main : I64 -> I64\nmain = |x| if x == 0 then 1 else True",
        0,
    );
}

// ============================================================
// Type inference — parametric polymorphism
// ============================================================

#[test]
fn generic_maybe_type() {
    let source = "\
Maybe(a) : [Just(a), Nothing]

unwrap_or : Maybe(I64), I64 -> I64
unwrap_or = |m, default| if m
    : Just(val) then val
    : Nothing then default

main : I64 -> I64
main = |arg| unwrap_or(Just(42), 0)";

    assert_eq!(run_i64(source, 0), 42);
}

#[test]
fn generic_list_type() {
    let source = "\
Lnk(a) : [Nil, Cons(a, Lnk(a))].(
    sum : Lnk(I64) -> I64
    sum = |xs| fold xs
        : Nil then 0
        : Cons(hd, rest) then hd + rest
)

main : I64 -> I64
main = |arg| Lnk.sum(Cons(1, Cons(2, Cons(3, Nil))))";

    assert_eq!(run_i64(source, 0), 6);
}

// ============================================================
// Built-in List type
// ============================================================

#[test]
fn builtin_list_literal() {
    let source = "\
main : I64 -> I64
main = |arg| List.len([1, 2, 3])";

    assert_eq!(run_i64(source, 0), 3);
}

#[test]
fn builtin_list_get() {
    let source = "\
main : I64 -> I64
main = |arg| List.get([10, 20, 30], 1)";

    assert_eq!(run_i64(source, 0), 20);
}

#[test]
fn builtin_list_append() {
    let source = "\
main : I64 -> I64
main = |arg| List.len(List.append([1, 2], 3))";

    assert_eq!(run_i64(source, 0), 3);
}

#[test]
fn builtin_list_walk_sum() {
    let source = "\
main : I64 -> I64
main = |arg| List.walk([1, 2, 3, 4, 5], 0, |acc, x| acc + x)";

    assert_eq!(run_i64(source, 0), 15);
}

#[test]
fn builtin_list_reverse() {
    let source = "\
main : I64 -> I64
main = |arg| List.get(List.reverse([10, 20, 30]), 0)";

    // reversed = [30, 20, 10], first element is 30
    assert_eq!(run_i64(source, 0), 30);
}

#[test]
fn builtin_list_map() {
    let source = "\
main : I64 -> I64
main = |arg| List.sum(List.map([1, 2, 3], |x| x * 2))";

    assert_eq!(run_i64(source, 0), 12);
}

#[test]
fn builtin_list_sum() {
    let source = "\
main : I64 -> I64
main = |arg| List.sum([1, 2, 3, 4, 5])";

    assert_eq!(run_i64(source, 0), 15);
}

#[test]
fn builtin_list_empty() {
    let source = "\
main : I64 -> I64
main = |arg| List.len([])";

    assert_eq!(run_i64(source, 0), 0);
}
