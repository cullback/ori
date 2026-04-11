use crate::source::SourceArena;
use crate::ssa::eval::Scalar;

/// Compile and run an Ori program via SSA with the given I64 input.
fn run(source: &str, input: i64) -> Scalar {
    let mut arena = SourceArena::new();
    let file_id = arena.add("<test>".to_owned(), source.to_owned());
    let parsed = crate::syntax::parse::parse(arena.content(file_id), file_id).unwrap();
    let mut resolved = crate::resolve::resolve_imports(parsed, &mut arena, None).unwrap();
    resolved.module = crate::fold_lift::lift(resolved.module, &mut resolved.symbols);
    resolved.module = crate::flatten_patterns::flatten(resolved.module, &mut resolved.symbols);
    crate::topo::compute(&mut resolved.module, &resolved.symbols).unwrap();
    let infer_result = crate::types::infer::check(
        &arena,
        &mut resolved.module,
        &resolved.scope,
        &resolved.symbols,
        &resolved.fields,
    )
    .unwrap();
    let (mono_module, mono_infer) =
        crate::mono::specialize(resolved.module, infer_result, &mut resolved.symbols);
    let defunc_module = crate::defunc::rewrite(
        mono_module,
        &arena,
        &resolved.scope,
        &mono_infer,
        &mut resolved.symbols,
    );
    let pre_prune_decls = crate::decl_info::build(
        &arena,
        &defunc_module,
        &resolved.scope,
        &mono_infer,
        &resolved.symbols,
    );
    resolved.module = crate::reachable::prune(defunc_module, &pre_prune_decls, &resolved.symbols);
    let (ssa_module, input_vals) = crate::ssa::lower::lower(
        &arena,
        &resolved.module,
        &resolved.scope,
        &mono_infer,
        &resolved.symbols,
        &resolved.fields,
    )
    .unwrap();

    let mut heap = crate::ssa::eval::new_heap();
    let ssa_args: Vec<Scalar> = input_vals
        .iter()
        .enumerate()
        .map(|(i, _)| {
            if i == 0 {
                Scalar::I64(input)
            } else {
                // Empty list: 3-slot header (len=0, cap=0, data_ptr)
                let data = heap.alloc(0);
                let header = heap.alloc(3);
                heap.store(header, 0, Scalar::U64(0));
                heap.store(header, 1, Scalar::U64(0));
                heap.store(header, 2, Scalar::Ptr(data));
                Scalar::Ptr(header)
            }
        })
        .collect();
    crate::ssa::eval::eval(&ssa_module, &mut heap, &ssa_args)
}

fn run_i64(source: &str, input: i64) -> i64 {
    match run(source, input) {
        Scalar::I64(n) => n,
        other => panic!("expected I64 result, got {other:?}"),
    }
}

/// Run parse → resolve → fold_lift → flatten_patterns → topo → infer
/// and return the inferred function scheme for the given function
/// name as a rendered string. Used by tests that want to assert on
/// inferred types without needing the full SSA pipeline — e.g. tests
/// for structural tag unions where lowering support isn't landed yet.
#[allow(dead_code, reason = "used by structural-tag inference tests")]
fn infer_func_type(source: &str, func: &str) -> String {
    let mut arena = SourceArena::new();
    let file_id = arena.add("<test>".to_owned(), source.to_owned());
    let parsed = crate::syntax::parse::parse(arena.content(file_id), file_id).unwrap();
    let mut resolved = crate::resolve::resolve_imports(parsed, &mut arena, None).unwrap();
    resolved.module = crate::fold_lift::lift(resolved.module, &mut resolved.symbols);
    resolved.module = crate::flatten_patterns::flatten(resolved.module, &mut resolved.symbols);
    crate::topo::compute(&mut resolved.module, &resolved.symbols).unwrap();
    let infer_result = crate::types::infer::check(
        &arena,
        &mut resolved.module,
        &resolved.scope,
        &resolved.symbols,
        &resolved.fields,
    )
    .unwrap_or_else(|e| panic!("infer failed: {}", e.format(&arena)));
    let scheme = infer_result
        .func_schemes
        .get(func)
        .unwrap_or_else(|| panic!("no scheme for function '{func}'"));
    render_scheme(&scheme.ty)
}

#[allow(dead_code, reason = "used by structural-tag inference tests")]
fn render_scheme(ty: &crate::types::engine::Type) -> String {
    use crate::types::engine::Type;
    match ty {
        Type::Var(_) => "'_".to_owned(),
        Type::Con(name) => name.clone(),
        Type::App(name, args) => {
            let arg_strs: Vec<String> = args.iter().map(render_scheme).collect();
            format!("{name}({})", arg_strs.join(", "))
        }
        Type::Arrow(params, ret) => {
            let param_strs: Vec<String> = params.iter().map(render_scheme).collect();
            format!("{} -> {}", param_strs.join(", "), render_scheme(ret))
        }
        Type::Record { fields, rest } => {
            let mut field_strs: Vec<String> = fields
                .iter()
                .map(|(n, t)| format!("{n}: {}", render_scheme(t)))
                .collect();
            if rest.is_some() {
                field_strs.push("..".to_owned());
            }
            format!("{{ {} }}", field_strs.join(", "))
        }
        Type::TagUnion { tags, rest } => {
            let mut tag_strs: Vec<String> = tags
                .iter()
                .map(|(n, payloads)| {
                    if payloads.is_empty() {
                        n.clone()
                    } else {
                        let ps: Vec<String> = payloads.iter().map(render_scheme).collect();
                        format!("{n}({})", ps.join(", "))
                    }
                })
                .collect();
            if rest.is_some() {
                tag_strs.push("..".to_owned());
            }
            format!("[{}]", tag_strs.join(", "))
        }
        Type::Tuple(elems) => {
            let elem_strs: Vec<String> = elems.iter().map(render_scheme).collect();
            format!("({})", elem_strs.join(", "))
        }
    }
}

fn run_u64(source: &str, input: i64) -> u64 {
    match run(source, input) {
        Scalar::U64(n) => n,
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

both : Bool, Bool -> Bool
both = |a, b| if a
    : True then b
    : False then False

bool_to_i64 : Bool -> I64
bool_to_i64 = |b| if b
    : True then 1
    : False then 0

main : I64 -> I64
main = |arg| bool_to_i64(both(True, True))";

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
// Stdlib import (Bool available via import)
// ============================================================

#[test]
fn prelude_bool_available() {
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
// Type inference -- error detection
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
// Type inference -- parametric polymorphism
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
main : I64 -> U64
main = |arg| List.len([1, 2, 3])";

    assert_eq!(run_u64(source, 0), 3);
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
main : I64 -> U64
main = |arg| List.len(List.append([1, 2], 3))";

    assert_eq!(run_u64(source, 0), 3);
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
fn builtin_list_set() {
    let source = "\
main : I64 -> I64
main = |arg| List.get(List.set([10, 20, 30], 1, 99), 1)";

    assert_eq!(run_i64(source, 0), 99);
}

#[test]
fn builtin_list_reverse_then_walk() {
    // Right-to-left iteration is expressed as `reverse().walk(...)`.
    // reversed = [3, 2, 1]; 0 * 10 + 3 = 3; 3 * 10 + 2 = 32; 32 * 10 + 1 = 321.
    let source = "\
main : I64 -> I64
main = |arg| List.walk(List.reverse([1, 2, 3]), 0, |acc, x| acc * 10 + x)";

    assert_eq!(run_i64(source, 0), 321);
}

#[test]
fn builtin_list_reverse_standalone() {
    // `reverse` as a standalone operation — verify the list contents
    // are actually reordered (by indexing into the reversed list).
    let source = "\
main : I64 -> I64
main = |arg| List.get(List.reverse([10, 20, 30]), 0)";

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
fn walk_until_break_early() {
    // Sum elements until we hit a value > 3, then break
    let source = "\
main : I64 -> I64
main = |arg| List.walk_until([1, 2, 3, 4, 5], 0, |acc, x|
    if x == 4 then Break(acc)
    else Continue(acc + x)
)";
    // 1 + 2 + 3 = 6 (stops before 4)
    assert_eq!(run_i64(source, 0), 6);
}

#[test]
fn walk_until_no_break() {
    // No break — processes all elements
    let source = "\
main : I64 -> I64
main = |arg| List.walk_until([1, 2, 3], 0, |acc, x| Continue(acc + x))";
    assert_eq!(run_i64(source, 0), 6);
}

#[test]
fn reverse_then_walk_until_break_early() {
    // Right-to-left walk-until via reverse().walk_until(...). Walk
    // the reversed list [5, 4, 3, 2, 1] and break when we hit 2.
    let source = "\
main : I64 -> I64
main = |arg| List.walk_until(List.reverse([1, 2, 3, 4, 5]), 0, |acc, x|
    if x == 2 then Break(acc)
    else Continue(acc + x)
)";
    // 5 + 4 + 3 = 12 (stops before 2)
    assert_eq!(run_i64(source, 0), 12);
}

#[test]
fn builtin_list_empty() {
    let source = "\
main : I64 -> U64
main = |arg| List.len([])";

    assert_eq!(run_u64(source, 0), 0);
}

// ============================================================
// Str type
// ============================================================

#[test]
fn dot_method_call() {
    let source = "\
main : I64 -> U64
main = |arg| \"hello\".count_bytes()";

    assert_eq!(run_u64(source, 0), 5);
}

#[test]
fn dot_method_chain() {
    let source = "\
main : I64 -> U64
main = |arg| \"hi\".concat(\"!\").count_bytes()";

    assert_eq!(run_u64(source, 0), 3);
}

#[test]
fn dot_method_on_list() {
    let source = "\
main : I64 -> I64
main = |arg| [10, 20, 30].get(1)";

    assert_eq!(run_i64(source, 0), 20);
}

#[test]
fn str_count_bytes() {
    let source = "\
main : I64 -> U64
main = |arg| Str.count_bytes(\"hello\")";

    assert_eq!(run_u64(source, 0), 5);
}

#[test]
fn str_append() {
    let source = "\
main : I64 -> U64
main = |arg| Str.count_bytes(Str.concat(\"hi\", \"!\"))";

    assert_eq!(run_u64(source, 0), 3);
}

#[test]
fn str_get_byte() {
    // 'H' = 72 in ASCII/UTF-8
    let source = "\
main : I64 -> U8
main = |arg| Str.get(\"Hello\", 0)";

    match run(source, 0) {
        Scalar::U8(n) => assert_eq!(n, 72),
        other => panic!("expected U8, got {other:?}"),
    }
}

#[test]
fn str_literal_escape() {
    let source = "\
main : I64 -> U64
main = |arg| Str.count_bytes(\"line1\\nline2\")";

    // "line1\nline2" = 11 bytes
    assert_eq!(run_u64(source, 0), 11);
}

// ============================================================
// Character literals
// ============================================================

#[test]
fn char_literal_ascii() {
    let source = "\
main : I64 -> I64
main = |arg| 'A'";
    assert_eq!(run_i64(source, 0), 65);
}

#[test]
fn char_literal_paren() {
    let source = "\
main : I64 -> I64
main = |arg| '('";
    assert_eq!(run_i64(source, 0), 40);
}

#[test]
fn char_literal_escape_newline() {
    let source = "\
main : I64 -> I64
main = |arg| '\\n'";
    assert_eq!(run_i64(source, 0), 10);
}

#[test]
fn char_literal_emoji() {
    let source = "\
main : I64 -> I64
main = |arg| '\u{1F469}'";
    // U+1F469 = 128105
    assert_eq!(run_i64(source, 0), 128105);
}

#[test]
fn char_literal_in_arithmetic() {
    let source = "\
main : I64 -> I64
main = |arg| 'A' + 1";
    assert_eq!(run_i64(source, 0), 66);
}

// ============================================================
// String interpolation
// ============================================================

#[test]
fn string_interpolation_basic() {
    let source = "\
main : I64 -> U64
main = |arg| (
    name = \"world\"
    \"hello ${name}\".count_bytes()
)";
    // "hello world" = 11 bytes
    assert_eq!(run_u64(source, 0), 11);
}

#[test]
fn string_interpolation_multiple() {
    let source = "\
main : I64 -> U64
main = |arg| (
    a = \"foo\"
    b = \"bar\"
    \"${a}${b}\".count_bytes()
)";
    // "foobar" = 6 bytes
    assert_eq!(run_u64(source, 0), 6);
}

#[test]
fn string_interpolation_only() {
    let source = "\
main : I64 -> U64
main = |arg| (
    x = \"abc\"
    \"${x}\".count_bytes()
)";
    assert_eq!(run_u64(source, 0), 3);
}

#[test]
fn string_dollar_without_brace() {
    // $ without { is a literal dollar sign
    let source = "\
main : I64 -> U64
main = |arg| \"price $5\".count_bytes()";
    // "price $5" = 8 bytes
    assert_eq!(run_u64(source, 0), 8);
}

#[test]
fn string_escaped_interpolation() {
    // \${ produces literal ${
    let source = "\
main : I64 -> U64
main = |arg| \"use \\${x}\".count_bytes()";
    // "use ${x}" = 8 bytes
    assert_eq!(run_u64(source, 0), 8);
}

#[test]
fn string_interpolation_auto_to_str() {
    // Interpolated I64 is auto-converted via .to_str()
    let source = "\
main : I64 -> U64
main = |arg| (
    n : I64
    n = 42
    \"n=${n}\".count_bytes()
)";
    // "n=42" = 4 bytes
    assert_eq!(run_u64(source, 0), 4);
}

// ============================================================
// Triple-quoted strings
// ============================================================

#[test]
fn triple_string_basic() {
    let source = "\
main : I64 -> U64
main = |arg| \"\"\"\n    hello\n    world\n    \"\"\".count_bytes()";
    // "hello\nworld" = 11 bytes
    assert_eq!(run_u64(source, 0), 11);
}

#[test]
fn triple_string_preserves_relative_indent() {
    let source = "\
main : I64 -> U64
main = |arg| \"\"\"\n    line1\n        indented\n    \"\"\".count_bytes()";
    // "line1\n    indented" = 18 bytes
    assert_eq!(run_u64(source, 0), 18);
}

#[test]
fn triple_string_with_interpolation() {
    let source = "\
main : I64 -> U64
main = |arg| (
    name = \"Alice\"
    \"\"\"\n    hello ${name}\n    \"\"\".count_bytes()
)";
    // "hello Alice" = 11 bytes
    assert_eq!(run_u64(source, 0), 11);
}

// ============================================================
// Float literals and polymorphic numbers
// ============================================================

#[test]
fn float_literal_arithmetic() {
    let source = "\
main : I64 -> F64
main = |arg| 3.14 * 2.0";

    match run(source, 0) {
        Scalar::F64(n) => {
            assert!((n - 6.28).abs() < 0.001);
        }
        other => panic!("expected F64, got {other:?}"),
    }
}

#[test]
fn int_literal_defaults_to_i64() {
    let source = "\
main : I64 -> I64
main = |arg| 1 + 2 + 3";

    assert_eq!(run_i64(source, 0), 6);
}

#[test]
fn int_division() {
    let source = "\
main : I64 -> I64
main = |arg| 10 / 3";

    assert_eq!(run_i64(source, 0), 3);
}

// ============================================================
// Constraints (structural method dispatch)
// ============================================================

#[test]
fn constraint_inferred_from_addition() {
    // add_twice is polymorphic with an inferred `add` constraint
    // When called with I64 args, constraint is satisfied
    let source = "\
add_twice = |x, y| x + y + y

main : I64 -> I64
main = |arg| add_twice(10, 3)";

    assert_eq!(run_i64(source, 0), 16);
}

#[test]
fn constraint_where_clause_parses() {
    // Explicit where clause -- just verifies it parses and checks
    let source = "\
add_twice : a, a -> a where [a.add]
add_twice = |x, y| x + y + y

main : I64 -> I64
main = |arg| add_twice(10, 3)";

    assert_eq!(run_i64(source, 0), 16);
}

#[test]
fn constraint_method_on_concrete_type() {
    // x.not() where x is Bool -- resolves to Bool.not
    let source = "\
main : I64 -> I64
main = |arg| (
    b = True
    result = b.not()
    if result
        : True then 1
        : False then 0
)";

    assert_eq!(run_i64(source, 0), 0);
}

// ============================================================
// Type declaration kinds (alias, transparent, opaque)
// ============================================================

#[test]
fn transparent_nominal_visible_outside() {
    // :=  transparent — internals visible everywhere
    // A function outside the .() block can accept/return the underlying type
    let source = "\
Foo := I64.(
    new : I64 -> Foo
    new = |x| x
)

unwrap : Foo -> I64
unwrap = |f| f

main : I64 -> I64
main = |arg| unwrap(Foo.new(42))";

    assert_eq!(run_i64(source, 0), 42);
}

#[test]
#[should_panic(expected = "unify")]
fn opaque_hidden_outside() {
    // :: opaque — internals hidden outside .() block
    // A function outside the block cannot treat Foo as I64
    let source = "\
Foo :: I64.(
    new : I64 -> Foo
    new = |x| x
)

unwrap : Foo -> I64
unwrap = |f| f

main : I64 -> I64
main = |arg| unwrap(Foo.new(42))";

    run_i64(source, 0);
}

// ============================================================
// Doc comments
// ============================================================

#[test]
fn doc_comment_attached_to_decl() {
    let source = "\
# Doubles a number.
double : I64 -> I64
double = |x| x + x

main : I64 -> I64
main = |arg| double(arg)";

    // Verify it parses and runs correctly with # comments
    assert_eq!(run_i64(source, 5), 10);

    // Verify the doc comment is attached to the type annotation
    let mut arena = crate::source::SourceArena::new();
    let file_id = arena.add("<test>".to_owned(), source.to_owned());
    let parsed = crate::syntax::parse::parse(arena.content(file_id), file_id).unwrap();
    let first_decl = &parsed.decls[0];
    match first_decl {
        crate::syntax::raw::Decl::TypeAnno { doc, .. } => {
            assert_eq!(doc.as_deref(), Some("Doubles a number."));
        }
        _ => panic!("expected TypeAnno"),
    }
}

#[test]
fn doc_comment_multiline() {
    let source = "\
# First line.
# Second line.
double : I64 -> I64
double = |x| x + x

main : I64 -> I64
main = |arg| double(arg)";

    let mut arena = crate::source::SourceArena::new();
    let file_id = arena.add("<test>".to_owned(), source.to_owned());
    let parsed = crate::syntax::parse::parse(arena.content(file_id), file_id).unwrap();
    match &parsed.decls[0] {
        crate::syntax::raw::Decl::TypeAnno { doc, .. } => {
            assert_eq!(doc.as_deref(), Some("First line.\nSecond line."));
        }
        _ => panic!("expected TypeAnno"),
    }
}

#[test]
fn blank_line_breaks_doc_comment() {
    let source = "\
# This is NOT a doc comment because of the blank line.

double : I64 -> I64
double = |x| x + x

main : I64 -> I64
main = |arg| double(arg)";

    let mut arena = crate::source::SourceArena::new();
    let file_id = arena.add("<test>".to_owned(), source.to_owned());
    let parsed = crate::syntax::parse::parse(arena.content(file_id), file_id).unwrap();
    match &parsed.decls[0] {
        crate::syntax::raw::Decl::TypeAnno { doc, .. } => {
            assert!(doc.is_none());
        }
        _ => panic!("expected TypeAnno"),
    }
}

// ============================================================
// Monomorphization tests removed: Core IR no longer exists.
// The above behavioral tests cover all the same scenarios.
// ============================================================

// ============================================================
// Or-patterns
// ============================================================

#[test]
fn or_pattern_basic() {
    let source = "\
Shape : [Circle(I64), Sphere(I64), Rect(I64, I64)]
area : Shape -> I64
area = |s| if s
    : Circle(r) or Sphere(r) then r * r
    : Rect(w, h) then w * h
main : I64 -> I64
main = |arg| area(Circle(5))";
    assert_eq!(run_i64(source, 0), 25);
}

#[test]
fn or_pattern_second_alternative() {
    let source = "\
Shape : [Circle(I64), Sphere(I64), Rect(I64, I64)]
area : Shape -> I64
area = |s| if s
    : Circle(r) or Sphere(r) then r * r
    : Rect(w, h) then w * h
main : I64 -> I64
main = |arg| area(Sphere(3))";
    assert_eq!(run_i64(source, 0), 9);
}

// ============================================================
// Nested patterns (flatten_patterns pass)
// ============================================================

// ============================================================
// Structural tag unions
// ============================================================

#[test]
fn structural_tag_runtime_nullary() {
    // End-to-end: compile and run a program that uses structural
    // constructors and a match to dispatch on them. Exercises the
    // SSA lowering path (steps 7-9).
    let source = "\
pick : I64 -> [Blue, Green, Red]
pick = |n| if n == 0 then Red
    else if n == 1 then Green
    else Blue

main : I64 -> I64
main = |arg| (
    r = pick(arg)
    if r
        : Red then 100
        : Green then 200
        : Blue then 300
)";
    assert_eq!(run_i64(source, 0), 100);
    assert_eq!(run_i64(source, 1), 200);
    assert_eq!(run_i64(source, 2), 300);
}

#[test]
fn structural_tag_runtime_with_payload() {
    // Structural constructors carrying I64 payloads, matched with
    // field bindings.
    let source = "\
wrap : I64 -> [Neg(I64), Pos(I64), Zero]
wrap = |n| if n == 0 then Zero
    else if n == 1 then Pos(n)
    else Neg(n)

main : I64 -> I64
main = |arg| (
    r = wrap(arg)
    if r
        : Pos(x) then x * 10
        : Neg(x) then x * -1
        : Zero then 999
)";
    assert_eq!(run_i64(source, 0), 999);
    assert_eq!(run_i64(source, 1), 10);
    assert_eq!(run_i64(source, 5), -5);
}

#[test]
fn structural_tag_runtime_open_row_annotation() {
    // Open-row annotation on a function return type. The body
    // produces a narrower union; the caller uses a wider (closed)
    // annotation to pin it. Verifies grammar support for `..` and
    // that inference/mono/lowering all cooperate.
    let source = "\
pick : I64 -> [Red, Green, ..]
pick = |n| if n == 0 then Red else Green

describe : [Blue, Green, Red] -> I64
describe = |c| if c
    : Red then 10
    : Green then 20
    : Blue then 30

main : I64 -> I64
main = |arg| describe(pick(arg))";
    assert_eq!(run_i64(source, 0), 10);
    assert_eq!(run_i64(source, 1), 20);
}

#[test]
fn structural_tag_runtime_is_expression() {
    // Standalone `is` expression on a structural tag value.
    let source = "\
check : I64 -> [No, Yes]
check = |n| if n == 0 then Yes else No

main : I64 -> I64
main = |arg| (
    r = check(arg)
    if r is Yes then 1 else 0
)";
    assert_eq!(run_i64(source, 0), 1);
    assert_eq!(run_i64(source, 7), 0);
}

#[test]
fn structural_tag_widening_to_annotated_type() {
    // An annotation closes the row. Here the body produces a union
    // containing just Red and Green, which widens to match the
    // annotated closed union of three tags. Open-row syntax `..`
    // in annotations isn't supported by the grammar yet, so we use
    // a closed annotation for now.
    let source = "\
parse : I64 -> [Red, Green, Blue]
parse = |n| if n == 0 then Red else Green";
    let ty = infer_func_type(source, "parse");
    // After widening, the inferred type should be the annotated
    // closed union — exactly three tags, no open row.
    assert!(
        ty.contains("Red") && ty.contains("Green") && ty.contains("Blue"),
        "expected closed union of three tags, got: {ty}"
    );
    assert!(
        !ty.contains(".."),
        "annotation should close the row, got: {ty}"
    );
}

#[test]
fn structural_tag_with_payload_annotation() {
    // Structural constructor with a payload: `Wrapped(n)` produces
    // a tag union where Wrapped carries an I64, closed to the
    // annotated return type.
    let source = "\
wrap : I64 -> [Wrapped(I64)]
wrap = |n| Wrapped(n)";
    let ty = infer_func_type(source, "wrap");
    assert!(
        ty.contains("Wrapped(I64)"),
        "expected Wrapped carrying I64, got: {ty}"
    );
}

#[test]
fn structural_tag_multiple_with_payloads() {
    // Three constructors with different payload shapes. The
    // annotation closes the row; inference unifies the payloads to
    // the annotated types.
    let source = "\
classify : I64 -> [Pos(I64), Neg(I64), Zero]
classify = |n| if n == 0 then Zero
    else if n == 1 then Pos(n)
    else Neg(n)";
    let ty = infer_func_type(source, "classify");
    assert!(
        ty.contains("Pos(I64)") && ty.contains("Neg(I64)") && ty.contains("Zero"),
        "expected closed union, got: {ty}"
    );
}

#[test]
fn structural_tag_match_closes_row() {
    // An exhaustive match on a parameter with no annotation should
    // close the scrutinee's row to exactly the tags covered. Here
    // `c`'s inferred type starts open (from the match arms) and
    // closes to `[Red, Green, Blue]` because all three branches
    // are covered and there's no else.
    let source = "\
describe = |c| if c
    : Red then 1
    : Green then 2
    : Blue then 3";
    let ty = infer_func_type(source, "describe");
    assert!(
        ty.contains("Red") && ty.contains("Green") && ty.contains("Blue"),
        "expected all three tags in closed union, got: {ty}"
    );
    assert!(
        !ty.contains(".."),
        "exhaustive match should close the row, got: {ty}"
    );
}

#[test]
fn structural_tag_match_with_else_stays_open() {
    // A match with an `else` branch leaves the row open — the else
    // handles anything else that could flow in. The scrutinee's
    // type should still contain `..`.
    let source = "\
describe = |c| if c
    : Red then 1
    : Green then 2
    else 0";
    let ty = infer_func_type(source, "describe");
    assert!(
        ty.contains("Red") && ty.contains("Green"),
        "expected Red and Green in union, got: {ty}"
    );
    assert!(
        ty.contains(".."),
        "else branch should leave row open, got: {ty}"
    );
}

#[test]
fn structural_tag_open_row_without_annotation() {
    // Without a closing annotation, the inferred body type keeps
    // its open row. The two branches contribute `Red` and `Green`,
    // and the inferred type contains both plus an open rest (`..`).
    let source = "\
parse = |n| if n == 0 then Red else Green";
    let ty = infer_func_type(source, "parse");
    assert!(
        ty.contains("Red") && ty.contains("Green"),
        "expected union containing both tags, got: {ty}"
    );
    assert!(
        ty.contains(".."),
        "expected open row without annotation, got: {ty}"
    );
}

#[test]
fn nested_pattern_ok_branch() {
    // Constructor-in-constructor pattern; taken via the Ok branch.
    let source = "\
Pair : [Pair(Result(I64, I64), I64)]
compute : Pair -> I64
compute = |p| if p
    : Pair(Ok(x), y) then x + y
    : Pair(Err(x), y) then x - y
main : I64 -> I64
main = |arg| compute(Pair(Ok(42), 7))";
    assert_eq!(run_i64(source, 0), 49);
}

#[test]
fn nested_pattern_err_branch() {
    // Same shape, but the inner match falls through from Ok to Err.
    let source = "\
Pair : [Pair(Result(I64, I64), I64)]
compute : Pair -> I64
compute = |p| if p
    : Pair(Ok(x), y) then x + y
    : Pair(Err(x), y) then x - y
main : I64 -> I64
main = |arg| compute(Pair(Err(100), 7))";
    assert_eq!(run_i64(source, 0), 93);
}

#[test]
fn nested_pattern_double_nesting() {
    // Constructor nested inside constructor nested inside constructor.
    // Each arm exercises a different fallthrough path.
    let source = "\
Box : [Box(Result(Result(I64, I64), I64))]
compute : Box -> I64
compute = |b| if b
    : Box(Ok(Ok(x))) then x * 10
    : Box(Ok(Err(x))) then x + 1
    : Box(Err(x)) then x - 1
main : I64 -> I64
main = |arg| compute(Box(Ok(Ok(5))))";
    assert_eq!(run_i64(source, 0), 50);
}

#[test]
fn nested_pattern_double_nesting_middle() {
    let source = "\
Box : [Box(Result(Result(I64, I64), I64))]
compute : Box -> I64
compute = |b| if b
    : Box(Ok(Ok(x))) then x * 10
    : Box(Ok(Err(x))) then x + 1
    : Box(Err(x)) then x - 1
main : I64 -> I64
main = |arg| compute(Box(Ok(Err(5))))";
    assert_eq!(run_i64(source, 0), 6);
}

#[test]
fn nested_pattern_double_nesting_outer() {
    let source = "\
Box : [Box(Result(Result(I64, I64), I64))]
compute : Box -> I64
compute = |b| if b
    : Box(Ok(Ok(x))) then x * 10
    : Box(Ok(Err(x))) then x + 1
    : Box(Err(x)) then x - 1
main : I64 -> I64
main = |arg| compute(Box(Err(5)))";
    assert_eq!(run_i64(source, 0), 4);
}

#[test]
fn nested_pattern_is_expr() {
    // Nested Constructor pattern inside a standalone `is` expression,
    // not a match arm — exercises the `flatten_is_expr` path. Uses a
    // user-defined type so the test is self-contained.
    let source = "\
Boxed : [Boxed(Result(I64, I64))]
main : I64 -> I64
main = |arg| (
    b = Boxed(Ok(77))
    if b is Boxed(Ok(x)) then x else 0
)";
    assert_eq!(run_i64(source, 0), 77);
}

#[test]
fn nested_pattern_is_expr_no_match() {
    // Same shape, but the inner pattern doesn't match — exercises the
    // false fallthrough of the synthesized is-chain.
    let source = "\
Boxed : [Boxed(Result(I64, I64))]
main : I64 -> I64
main = |arg| (
    b = Boxed(Err(77))
    if b is Boxed(Ok(x)) then x else 0
)";
    assert_eq!(run_i64(source, 0), 0);
}

// ============================================================
// Guards (and condition)
// ============================================================

#[test]
fn guard_basic() {
    let source = "\
Cmd : [Move(I64), Stop]
handle : Cmd -> I64
handle = |c| if c
    : Move(dist) and dist == 0 then 99
    : Move(dist) then dist
    : Stop then 0
main : I64 -> I64
main = |arg| handle(Move(42))";
    assert_eq!(run_i64(source, 0), 42);
}

#[test]
fn guard_fallthrough() {
    let source = "\
Cmd : [Move(I64), Stop]
handle : Cmd -> I64
handle = |c| if c
    : Move(dist) and dist == 0 then 99
    : Move(dist) then dist
    : Stop then 0
main : I64 -> I64
main = |arg| handle(Move(0))";
    assert_eq!(run_i64(source, 0), 99);
}

#[test]
fn guard_chain() {
    // Two guards chained with and
    let source = "\
Val : [Pair(I64, I64)]
check : Val -> I64
check = |v| if v
    : Pair(a, b) and a == 1 and b == 2 then 100
    : Pair(a, b) then a + b
main : I64 -> I64
main = |arg| check(Pair(1, 2))";
    assert_eq!(run_i64(source, 0), 100);
}

// ============================================================
// Return in match arms
// ============================================================

#[test]
fn return_in_arm() {
    let source = "\
Val : [A(I64), B(I64)]
extract : Val -> I64
extract = |v| if v
    : A(x) return x
    : B(x) then x * 2
main : I64 -> I64
main = |arg| extract(A(7))";
    assert_eq!(run_i64(source, 0), 7);
}

#[test]
fn return_in_arm_b_branch() {
    let source = "\
Val : [A(I64), B(I64)]
extract : Val -> I64
extract = |v| if v
    : A(x) return x
    : B(x) then x * 2
main : I64 -> I64
main = |arg| extract(B(5))";
    assert_eq!(run_i64(source, 0), 10);
}

// ============================================================
// Guard clause: if condition return val
// ============================================================

#[test]
fn guard_clause_if_return() {
    let source = "\
main : I64 -> I64
main = |arg| (
    if arg == 0 return 99
    arg * 2
)";
    assert_eq!(run_i64(source, 0), 99);
}

#[test]
fn guard_clause_fallthrough() {
    let source = "\
main : I64 -> I64
main = |arg| (
    if arg == 0 return 99
    arg * 2
)";
    assert_eq!(run_i64(source, 5), 10);
}

// ============================================================
// Is pattern-test operator
// ============================================================

#[test]
fn is_basic() {
    let source = "\
Val : [A(I64), B(I64)]
main : I64 -> I64
main = |arg| (
    v = A(42)
    if v is A(_) then 1 else 0
)";
    assert_eq!(run_i64(source, 0), 1);
}

#[test]
fn is_no_match() {
    let source = "\
Val : [A(I64), B(I64)]
main : I64 -> I64
main = |arg| (
    v = B(42)
    if v is A(_) then 1 else 0
)";
    assert_eq!(run_i64(source, 0), 0);
}

#[test]
fn is_binding_flow() {
    // Bindings from is flow through and into then
    let source = "\
Val : [A(I64), B(I64)]
main : I64 -> I64
main = |arg| (
    v = A(42)
    if v is A(x) and x == 42 then x else 0
)";
    assert_eq!(run_i64(source, 0), 42);
}

#[test]
fn is_chain() {
    // Multiple is in and chain
    let source = "\
Inner : [Val(I64)]
Outer : [Wrap(Inner)]
main : I64 -> I64
main = |arg| (
    o = Wrap(Val(99))
    if o is Wrap(inner) and inner is Val(n) then n else 0
)";
    assert_eq!(run_i64(source, 0), 99);
}

#[test]
fn is_guard_clause() {
    // is with return for guard clause
    let source = "\
Val : [A(I64), B(I64)]
unwrap_a : Val -> I64
unwrap_a = |v| (
    if v is A(x) return x
    0
)
main : I64 -> I64
main = |arg| unwrap_a(A(7))";
    assert_eq!(run_i64(source, 0), 7);
}

#[test]
fn is_or_expression() {
    let source = "\
Val : [A(I64), B(I64), C]
main : I64 -> I64
main = |arg| (
    v = B(1)
    if v is A(_) or v is B(_) then 1 else 0
)";
    assert_eq!(run_i64(source, 0), 1);
}

#[test]
fn and_or_precedence() {
    // and binds tighter than or
    // True or (False and False) -> True
    let source = "\
main : I64 -> I64
main = |arg| if True or False and False then 1 else 0";
    assert_eq!(run_i64(source, 0), 1);
}

// ============================================================
// Top-level let-polymorphism (Step 5: inference rework)
//
// Pre-Step-5, Pass 1 forward-declared every free function with a
// monomorphic fresh arrow. That meant if you used `id` in two call
// sites with different argument types, the first use would lock
// `id`'s parameter to that type and the second would fail. After
// Step 5, functions are inferred in topological order and generalized
// immediately, so each caller instantiates a fresh copy.
// ============================================================

#[test]
fn let_poly_same_type_twice() {
    let source = "\
id = |x| x

main : I64 -> I64
main = |arg| id(1) + id(2)";
    assert_eq!(run_i64(source, 0), 3);
}

#[test]
fn let_poly_different_types() {
    // `id` used at I64 and a tag-union constructor in the same body.
    // Pre-Step-5 this would fail because `id` was forward-declared as
    // monomorphic and its tvar would be fixed at the first call site.
    let source = "\
Pair : [MkPair(I64, I64)]

id = |x| x

main : I64 -> I64
main = |arg| (
    a : I64
    a = id(5)
    p : Pair
    p = id(MkPair(1, 2))
    if p
        : MkPair(x, y) then a + x + y
)";
    assert_eq!(run_i64(source, 0), 8);
}

// ============================================================
// Topological sort — System T cycle detection
// ============================================================

#[test]
fn topo_cycle_errors() {
    // Mutual recursion: `f` and `g` call each other. System T forbids
    // this, so `topo::compute` should produce an error. We run the
    // frontend up through topo and assert it fails with a message that
    // mentions the cycle.
    let source = "\
f : I64 -> I64
f = |x| g(x)

g : I64 -> I64
g = |x| f(x)

main : I64 -> I64
main = |arg| f(arg)";
    let mut arena = crate::source::SourceArena::new();
    let file_id = arena.add("<test>".to_owned(), source.to_owned());
    let parsed = crate::syntax::parse::parse(arena.content(file_id), file_id).unwrap();
    let mut resolved = crate::resolve::resolve_imports(parsed, &mut arena, None).unwrap();
    resolved.module = crate::fold_lift::lift(resolved.module, &mut resolved.symbols);
    let err = crate::topo::compute(&mut resolved.module, &resolved.symbols)
        .expect_err("expected cycle detection error");
    let msg = err.format(&arena);
    assert!(
        msg.contains("System T violation"),
        "expected 'System T violation' in error, got: {msg}"
    );
    assert!(
        msg.contains('f') && msg.contains('g'),
        "expected both cycle members in error, got: {msg}"
    );
}

// ============================================================
// Name resolver — shadowing and is-binding flow
//
// These tests exercise the scope-tracking resolver built into
// `ast::from_raw`, added in Step 6b. Each tests a specific scoping
// rule that's easy to get wrong.
// ============================================================

#[test]
fn shadowing_let_with_self_reference() {
    // `let x = x + 1`: the RHS `x` refers to the OUTER x, not the new
    // one. The resolver is required to resolve `val` before binding
    // the new `name`.
    let source = "\
main : I64 -> I64
main = |arg| (
    x = 10
    x = x + 5
    x
)";
    assert_eq!(run_i64(source, 0), 15);
}

#[test]
fn shadowing_param_then_let() {
    // Block-local `let` shadows a function parameter.
    let source = "\
main : I64 -> I64
main = |x| (
    x = x * 2
    x + 1
)";
    assert_eq!(run_i64(source, 4), 9);
}

#[test]
fn lambda_captures_outer_let_inline() {
    // A lambda inlined at a call site captures a name bound in the
    // enclosing block. The resolver must look the captured name up
    // through the scope stack and use the outer binding's `SymbolId`.
    let source = "\
apply : (I64 -> I64), I64 -> I64
apply = |f, n| f(n)

main : I64 -> I64
main = |arg| (
    x = 10
    apply(|y| y + x, 5)
)";
    assert_eq!(run_i64(source, 0), 15);
}

// ============================================================
// Monomorphization (Step 7)
//
// Checks that polymorphic functions get specialized per call-site
// instantiation and that the SSA output contains the specialized
// names (not the originals).
// ============================================================

/// Compile the source through the frontend + mono and return the
/// SSA module. Use this helper to assert specific specialization
/// names appear in the output.
fn compile_to_ssa(source: &str) -> crate::ssa::Module {
    let mut arena = SourceArena::new();
    let file_id = arena.add("<test>".to_owned(), source.to_owned());
    let parsed = crate::syntax::parse::parse(arena.content(file_id), file_id).unwrap();
    let mut resolved = crate::resolve::resolve_imports(parsed, &mut arena, None).unwrap();
    resolved.module = crate::fold_lift::lift(resolved.module, &mut resolved.symbols);
    resolved.module = crate::flatten_patterns::flatten(resolved.module, &mut resolved.symbols);
    crate::topo::compute(&mut resolved.module, &resolved.symbols).unwrap();
    let infer_result = crate::types::infer::check(
        &arena,
        &mut resolved.module,
        &resolved.scope,
        &resolved.symbols,
        &resolved.fields,
    )
    .unwrap();
    let (mono_module, mono_infer) =
        crate::mono::specialize(resolved.module, infer_result, &mut resolved.symbols);
    let defunc_module = crate::defunc::rewrite(
        mono_module,
        &arena,
        &resolved.scope,
        &mono_infer,
        &mut resolved.symbols,
    );
    let pre_prune_decls = crate::decl_info::build(
        &arena,
        &defunc_module,
        &resolved.scope,
        &mono_infer,
        &resolved.symbols,
    );
    resolved.module = crate::reachable::prune(defunc_module, &pre_prune_decls, &resolved.symbols);
    let (ssa, _) = crate::ssa::lower::lower(
        &arena,
        &resolved.module,
        &resolved.scope,
        &mono_infer,
        &resolved.symbols,
        &resolved.fields,
    )
    .unwrap();
    ssa
}

fn ssa_has_function(ssa: &crate::ssa::Module, name: &str) -> bool {
    format!("{ssa}").lines().any(|line| {
        line.starts_with(&format!("fn {name}(")) || line.starts_with(&format!("fn {name}:"))
    })
}

#[test]
fn mono_list_sum_single_instantiation() {
    // `List.sum` is polymorphic (`forall a [a.add]. List(a) -> a`).
    // A call with `List(I64)` should produce exactly one
    // `List.sum__I64` specialization, no polymorphic original.
    let source = "\
main : I64 -> I64
main = |arg| List.sum([1, 2, 3, 4, 5])";
    let ssa = compile_to_ssa(source);
    assert!(
        ssa_has_function(&ssa, "List.sum__I64"),
        "expected List.sum__I64 in SSA, got:\n{ssa}"
    );
    assert!(
        !ssa_has_function(&ssa, "List.sum"),
        "unspecialized List.sum should be dropped"
    );
}

#[test]
fn mono_get_age_two_row_specializations() {
    // `get_age` is polymorphic on record row. Called with two
    // differently-shaped records, it should produce two distinct
    // specializations.
    let source = "\
Person : { name: I64, age: I64 }

get_age = |person| person.age

main : I64 -> I64
main = |arg| (
    alice : Person
    alice = { name: 1, age: 30 }
    bob = { age: 25, location: 2 }
    get_age(alice) + get_age(bob)
)";
    let ssa = compile_to_ssa(source);
    let out = format!("{ssa}");
    let spec_count = out.lines().filter(|l| l.contains("fn get_age__")).count();
    assert_eq!(
        spec_count, 2,
        "expected 2 get_age specializations, got {spec_count}\n{out}"
    );
    assert!(!ssa_has_function(&ssa, "get_age"), "polymorphic original should be dropped");
}

#[test]
fn mono_identity_function_two_types() {
    // The classic let-polymorphism case: `id` used at two different
    // types. Mono should produce two specializations.
    let source = "\
Pair : [MkPair(I64, I64)]

id = |x| x

main : I64 -> I64
main = |arg| (
    a = id(5)
    p = id(MkPair(1, 2))
    if p
        : MkPair(x, y) then a + x + y
)";
    let ssa = compile_to_ssa(source);
    let out = format!("{ssa}");
    let id_specs: Vec<&str> = out
        .lines()
        .filter(|l| l.starts_with("fn id__"))
        .collect();
    assert!(
        id_specs.len() >= 2,
        "expected at least 2 id specializations, got {}\nfull SSA:\n{out}",
        id_specs.len()
    );
}

// ============================================================
// Defunctionalization (Step 8)
//
// Checks that `defunc::rewrite` produces a module with no
// `ExprKind::Lambda` anywhere, synthesizes the expected
// `__apply_K` and `__lambda_K` decls, and preserves runtime
// semantics across every flavor of higher-order call.
// ============================================================

/// Returns true if any `ExprKind::Lambda` survives in the defunc
/// output. Used by `mono_no_lambdas_after_defunc` to assert the
/// rewrite is complete.
fn any_lambda_in_module(module: &crate::ast::Module<'_>) -> bool {
    fn in_expr(expr: &crate::ast::Expr<'_>) -> bool {
        use crate::ast::{ExprKind, Stmt};
        match &expr.kind {
            ExprKind::Lambda { .. } => true,
            ExprKind::BinOp { lhs, rhs, .. } => in_expr(lhs) || in_expr(rhs),
            ExprKind::Call { args, .. } => args.iter().any(in_expr),
            ExprKind::QualifiedCall { args, .. } => args.iter().any(in_expr),
            ExprKind::MethodCall { receiver, args, .. } => {
                in_expr(receiver) || args.iter().any(in_expr)
            }
            ExprKind::Block(stmts, result) => {
                stmts.iter().any(|s| match s {
                    Stmt::Let { val, .. } | Stmt::Destructure { val, .. } => in_expr(val),
                    Stmt::Guard { condition, return_val } => in_expr(condition) || in_expr(return_val),
                    Stmt::TypeHint { .. } => false,
                }) || in_expr(result)
            }
            ExprKind::If { expr, arms, else_body } => {
                in_expr(expr)
                    || arms
                        .iter()
                        .any(|a| a.guards.iter().any(in_expr) || in_expr(&a.body))
                    || else_body.as_deref().is_some_and(in_expr)
            }
            ExprKind::Fold { expr, arms } => {
                in_expr(expr)
                    || arms
                        .iter()
                        .any(|a| a.guards.iter().any(in_expr) || in_expr(&a.body))
            }
            ExprKind::Record { fields } => fields.iter().any(|(_, e)| in_expr(e)),
            ExprKind::FieldAccess { record, .. } => in_expr(record),
            ExprKind::Tuple(elems) | ExprKind::ListLit(elems) => elems.iter().any(in_expr),
            ExprKind::Is { expr, .. } => in_expr(expr),
            ExprKind::Name(_)
            | ExprKind::IntLit(_)
            | ExprKind::FloatLit(_)
            | ExprKind::StrLit(_) => false,
        }
    }
    for decl in &module.decls {
        match decl {
            crate::ast::Decl::FuncDef { body, .. } => {
                if in_expr(body) {
                    return true;
                }
            }
            crate::ast::Decl::TypeAnno { methods, .. } => {
                for m in methods {
                    if let crate::ast::Decl::FuncDef { body, .. } = m {
                        if in_expr(body) {
                            return true;
                        }
                    }
                }
            }
        }
    }
    false
}

/// Run the frontend through defunc and return the rewritten module.
#[allow(clippy::needless_pass_by_value, reason = "helper used by tests")]
fn compile_through_defunc(source: &str) -> (crate::ast::Module<'static>, crate::symbol::SymbolTable) {
    // Leak the arena so the returned module has a `'static` lifetime.
    // This is a test-only helper; the real pipeline doesn't need this.
    let arena = Box::leak(Box::new(SourceArena::new()));
    let file_id = arena.add("<test>".to_owned(), source.to_owned());
    let parsed = crate::syntax::parse::parse(arena.content(file_id), file_id).unwrap();
    let mut resolved = crate::resolve::resolve_imports(parsed, arena, None).unwrap();
    resolved.module = crate::fold_lift::lift(resolved.module, &mut resolved.symbols);
    resolved.module = crate::flatten_patterns::flatten(resolved.module, &mut resolved.symbols);
    crate::topo::compute(&mut resolved.module, &resolved.symbols).unwrap();
    let infer_result = crate::types::infer::check(
        arena,
        &mut resolved.module,
        &resolved.scope,
        &resolved.symbols,
        &resolved.fields,
    )
    .unwrap();
    let (mono_module, mono_infer) =
        crate::mono::specialize(resolved.module, infer_result, &mut resolved.symbols);
    let defunc_module = crate::defunc::rewrite(
        mono_module,
        arena,
        &resolved.scope,
        &mono_infer,
        &mut resolved.symbols,
    );
    let pre_prune_decls = crate::decl_info::build(
        arena,
        &defunc_module,
        &resolved.scope,
        &mono_infer,
        &resolved.symbols,
    );
    let pruned = crate::reachable::prune(defunc_module, &pre_prune_decls, &resolved.symbols);
    (pruned, resolved.symbols)
}

#[test]
fn defunc_no_lambdas_in_map_program() {
    // `List.map` has an inline lambda. After defunc, every lambda
    // in the module should be replaced with a constructor call.
    let source = "\
main : I64 -> I64
main = |arg| List.sum(List.map([1, 2, 3], |x| x * 2))";
    let (module, _) = compile_through_defunc(source);
    assert!(
        !any_lambda_in_module(&module),
        "defunc left lambdas in the module: {module:?}",
    );
}

#[test]
fn defunc_no_lambdas_in_user_higher_order() {
    // User-defined higher-order function with a lambda at the
    // call site. Exercises the non-list-walk rewrite path.
    let source = "\
apply : I64, (I64 -> I64) -> I64
apply = |x, f| f(x)

main : I64 -> I64
main = |arg| apply(5, |y| y * 2 + 1)";
    let (module, _) = compile_through_defunc(source);
    assert!(
        !any_lambda_in_module(&module),
        "defunc left lambdas in the module",
    );
}

#[test]
fn prune_drops_unused_stdlib_methods() {
    // A minimal program that only uses arithmetic — no stdlib list
    // methods. After prune, `List.map`, `List.sum`, etc. should be
    // gone from the module's decls. `List` itself (the TypeAnno)
    // stays because `decl_info` still reads it.
    let source = "\
main : I64 -> I64
main = |arg| 1 + 2 + 3";
    let (module, symbols) = compile_through_defunc(source);
    for decl in &module.decls {
        if let crate::ast::Decl::TypeAnno {
            name: type_name,
            methods,
            ..
        } = decl
        {
            if symbols.display(*type_name) == "List" {
                for m in methods {
                    if let crate::ast::Decl::FuncDef { name, .. } = m {
                        let method_name = symbols.display(*name);
                        // Only annotation-only methods (no body) and
                        // dead-code-eliminated ones should be here;
                        // this simple program doesn't call any.
                        panic!(
                            "unexpected reachable List method after prune: {method_name}"
                        );
                    }
                }
            }
        }
    }
}

#[test]
fn prune_keeps_reachable_chain() {
    // A → B → C call chain. All three should survive.
    let source = "\
c : I64 -> I64
c = |x| x + 1

b : I64 -> I64
b = |x| c(x) * 2

a : I64 -> I64
a = |x| b(x)

main : I64 -> I64
main = |arg| a(5)";
    let (module, symbols) = compile_through_defunc(source);
    let func_names: Vec<String> = module
        .decls
        .iter()
        .filter_map(|d| {
            if let crate::ast::Decl::FuncDef { name, .. } = d {
                Some(symbols.display(*name).to_owned())
            } else {
                None
            }
        })
        .collect();
    for expected in ["a", "b", "c", "main"] {
        assert!(
            func_names.iter().any(|n| n == expected),
            "expected {expected} to survive prune, got {func_names:?}"
        );
    }
}

#[test]
fn defunc_emits_apply_function() {
    // The `__apply_K` function for a user-defined HO callable
    // should exist after defunc.
    let source = "\
apply : I64, (I64 -> I64) -> I64
apply = |x, f| f(x)

main : I64 -> I64
main = |arg| apply(5, |y| y * 2)";
    let (module, symbols) = compile_through_defunc(source);
    let has_apply = module.decls.iter().any(|d| {
        if let crate::ast::Decl::FuncDef { name, .. } = d {
            symbols.display(*name).starts_with("__apply_apply_")
        } else {
            false
        }
    });
    assert!(has_apply, "expected __apply_apply_* in module decls");
}

// ============================================================
// AST snapshot tests
//
// These snapshot the post-parse AST for representative programs.
// When the AST format intentionally changes, refresh snapshots with:
//
//     UPDATE_EXPECT=1 cargo test ast_snapshots
//
// ============================================================

mod ast_snapshots {
    use crate::ast::{self, Decl};
    use crate::source::SourceArena;
    use expect_test::expect_file;

    fn render_raw(source_path: &str, source: &str) -> String {
        let mut arena = SourceArena::new();
        let file_id = arena.add(source_path.to_owned(), source.to_owned());
        let parsed = crate::syntax::parse::parse(arena.content(file_id), file_id)
            .unwrap_or_else(|e| panic!("parse failed for {source_path}: {e:?}"));
        format!("{parsed}")
    }

    /// Render the fully-inferred AST for the user's source file only
    /// (stdlib decls filtered out). Exercises ast_display with types
    /// populated by inference. Runs fold-lift between resolve and infer,
    /// so snapshots show the lifted form rather than the raw `Fold`.
    fn render_typed(source_path: &str, source: &str) -> String {
        let mut arena = SourceArena::new();
        let file_id = arena.add(source_path.to_owned(), source.to_owned());
        let parsed = crate::syntax::parse::parse(arena.content(file_id), file_id)
            .unwrap_or_else(|e| panic!("parse failed for {source_path}: {e:?}"));
        let mut resolved = crate::resolve::resolve_imports(parsed, &mut arena, None)
            .unwrap_or_else(|e| panic!("resolve failed for {source_path}: {e:?}"));
        resolved.module = crate::fold_lift::lift(resolved.module, &mut resolved.symbols);
        resolved.module = crate::flatten_patterns::flatten(resolved.module, &mut resolved.symbols);
        crate::topo::compute(&mut resolved.module, &resolved.symbols)
            .unwrap_or_else(|e| panic!("topo failed for {source_path}: {e:?}"));
        crate::types::infer::check(
            &arena,
            &mut resolved.module,
            &resolved.scope,
            &resolved.symbols,
            &resolved.fields,
        )
        .unwrap_or_else(|e| panic!("infer failed for {source_path}: {e:?}"));

        // Filter to user-file decls only to keep snapshots compact. The
        // `file.start == 0` condition catches synthesized `__fold_N`
        // helpers: they inherit the span of the original fold, which is
        // in the user file, so they stay in the snapshot.
        let user_decls: Vec<Decl<'_>> = resolved
            .module
            .decls
            .iter()
            .filter(|d| d.span().file == file_id)
            .cloned()
            .collect();
        let user_module = ast::Module {
            exports: resolved.module.exports.clone(),
            imports: resolved.module.imports.clone(),
            decls: user_decls,
        };
        crate::ast_display::render(&user_module, &resolved.symbols, &resolved.fields)
    }

    /// Render a compact summary of the resolved module: imports, then decl
    /// names grouped by source file. Catches regressions in `resolve` (e.g.
    /// a missing stdlib import) without bloating snapshots with the full
    /// stdlib AST on every program.
    fn render_resolved(source_path: &str, source: &str) -> String {
        let mut arena = SourceArena::new();
        let file_id = arena.add(source_path.to_owned(), source.to_owned());
        let parsed = crate::syntax::parse::parse(arena.content(file_id), file_id)
            .unwrap_or_else(|e| panic!("parse failed for {source_path}: {e:?}"));
        let resolved = crate::resolve::resolve_imports(parsed, &mut arena, None)
            .unwrap_or_else(|e| panic!("resolve failed for {source_path}: {e:?}"));

        let mut out = String::from("resolved:\n");
        if resolved.module.imports.is_empty() {
            out.push_str("  imports: (none)\n");
        } else {
            out.push_str("  imports:\n");
            for imp in &resolved.module.imports {
                out.push_str("    ");
                out.push_str(imp.module);
                if !imp.exposing.is_empty() {
                    out.push_str(" exposing (");
                    for (i, name) in imp.exposing.iter().enumerate() {
                        if i > 0 {
                            out.push_str(", ");
                        }
                        out.push_str(name);
                    }
                    out.push(')');
                }
                out.push('\n');
            }
        }

        // Group decl names by source file path (from arena).
        // Preserves the order decls appear in the module.
        let mut groups: Vec<(String, Vec<String>)> = Vec::new();
        for decl in &resolved.module.decls {
            let span = decl.span();
            let path = arena.path(span.file).to_owned();
            let name = match decl {
                Decl::TypeAnno { name, .. } | Decl::FuncDef { name, .. } => {
                    resolved.symbols.display(*name).to_owned()
                }
            };
            if let Some((_, names)) = groups.iter_mut().find(|(p, _)| *p == path) {
                names.push(name);
            } else {
                groups.push((path, vec![name]));
            }
        }
        out.push_str("  decls by file:\n");
        for (path, names) in &groups {
            out.push_str("    ");
            out.push_str(path);
            out.push_str(": ");
            for (i, n) in names.iter().enumerate() {
                if i > 0 {
                    out.push_str(", ");
                }
                out.push_str(n);
            }
            out.push('\n');
        }
        out
    }

    macro_rules! snapshot_raw {
        ($test_name:ident, $program:literal) => {
            #[test]
            fn $test_name() {
                let source = include_str!(concat!("../programs/", $program));
                let rendered = render_raw($program, source);
                expect_file![concat!(
                    env!("CARGO_MANIFEST_DIR"),
                    "/tests/snapshots/",
                    $program,
                    ".raw.txt"
                )]
                .assert_eq(&rendered);
            }
        };
    }

    macro_rules! snapshot_resolved {
        ($test_name:ident, $program:literal) => {
            #[test]
            fn $test_name() {
                let source = include_str!(concat!("../programs/", $program));
                let rendered = render_resolved($program, source);
                expect_file![concat!(
                    env!("CARGO_MANIFEST_DIR"),
                    "/tests/snapshots/",
                    $program,
                    ".resolved.txt"
                )]
                .assert_eq(&rendered);
            }
        };
    }

    macro_rules! snapshot_typed {
        ($test_name:ident, $program:literal) => {
            #[test]
            fn $test_name() {
                let source = include_str!(concat!("../programs/", $program));
                let rendered = render_typed($program, source);
                expect_file![concat!(
                    env!("CARGO_MANIFEST_DIR"),
                    "/tests/snapshots/",
                    $program,
                    ".typed.txt"
                )]
                .assert_eq(&rendered);
            }
        };
    }

    snapshot_raw!(tree_sum_raw, "tree_sum.ori");
    snapshot_raw!(nat_to_i64_raw, "nat_to_i64.ori");
    snapshot_raw!(bool_raw, "bool.ori");
    snapshot_raw!(list_import_raw, "list_import.ori");
    snapshot_raw!(records_raw, "records.ori");
    snapshot_raw!(echo_raw, "echo.ori");

    snapshot_resolved!(tree_sum_resolved, "tree_sum.ori");
    snapshot_resolved!(nat_to_i64_resolved, "nat_to_i64.ori");
    snapshot_resolved!(bool_resolved, "bool.ori");
    snapshot_resolved!(list_import_resolved, "list_import.ori");
    snapshot_resolved!(records_resolved, "records.ori");
    snapshot_resolved!(echo_resolved, "echo.ori");

    snapshot_typed!(tree_sum_typed, "tree_sum.ori");
    snapshot_typed!(nat_to_i64_typed, "nat_to_i64.ori");
    snapshot_typed!(bool_typed, "bool.ori");
    snapshot_typed!(list_import_typed, "list_import.ori");
    snapshot_typed!(records_typed, "records.ori");
    snapshot_typed!(echo_typed, "echo.ori");
}
