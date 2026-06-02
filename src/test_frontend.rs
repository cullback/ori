use crate::passes::resolve::Resolved;
use crate::source::{FileId, SourceArena};
use crate::ssa::eval::Scalar;

// ---- Shared pipeline helpers ----

/// Parse source and run resolve (the only IO pass).
fn parse_and_resolve(source: &str) -> (SourceArena, FileId, Resolved<'static>) {
    parse_and_resolve_named("<test>", source)
}

fn parse_and_resolve_named(path: &str, source: &str) -> (SourceArena, FileId, Resolved<'static>) {
    let mut arena = SourceArena::new();
    let file_id = arena.add(path.to_owned(), source.to_owned());
    let parsed = crate::syntax::parse::parse(arena.content(file_id), file_id).unwrap();
    let resolved = crate::passes::resolve::resolve_imports(parsed, &mut arena, None).unwrap();
    (arena, file_id, resolved)
}

/// Run pre-mono passes (fold_lift, flatten, topo) + type inference.
fn through_infer(
    resolved: &mut Resolved<'_>,
) -> crate::types::infer::InferResult {
    crate::passes::fold_lift::lift(resolved);
    crate::passes::flatten_patterns::flatten(resolved).unwrap();
    crate::passes::topo::compute(resolved).unwrap();
    crate::types::infer::check(resolved).unwrap()
}

/// Full compile: through infer, then mono + lambda passes + lower → SSA.
///
/// Every SSA pass is followed by a `validate` check. If a pass
/// produces structurally-broken SSA the test fails here with the
/// pass name, rather than later during eval with a confusing
/// runtime panic.
/// Like `compile` but stops right after `lower` — no opt passes.
/// Used by diagnostic tests to inspect lower's raw output.
fn compile_until_lower(source: &str) -> (crate::ssa::Module, Vec<crate::ssa::Value>) {
    let (_arena, _file_id, mut resolved) = parse_and_resolve(source);
    let infer_result = through_infer(&mut resolved);
    let mut mono =
        crate::passes::mono::specialize(resolved.module, infer_result, resolved.symbols);
    crate::passes::lambda::lift::lift(&mut mono);
    let lambda_solution = crate::passes::lambda::solve::solve(&mono);
    crate::passes::lambda::specialize::specialize(&mut mono, &lambda_solution);
    crate::passes::lambda::narrow::narrow(&mut mono);
    // Catch any synthesized Expr left with the inference placeholder
    // type. Fails immediately rather than letting lower silently
    // degrade (see e_user_hof_multislot_* tests for the bug class).
    validate_ast_types(&mono, "after lambda passes");
    let pre_prune_decls = crate::passes::decl_info::build(&mono);
    crate::passes::reachable::prune(&mut mono, &pre_prune_decls);
    let (ssa_module, input_vals) = crate::lower::lower(&mono, &resolved.fields).unwrap();
    crate::ssa::validate::check(&ssa_module, "lower");
    (ssa_module, input_vals)
}

fn validate_ast_types(mono: &crate::passes::mono::Monomorphized<'_>, after: &str) {
    let errs = crate::passes::validate_ast_types::validate(&mono.module, &mono.symbols);
    if !errs.is_empty() {
        panic!(
            "AST type validation failed {after}: placeholder Type::Var(0) on \
             post-inference expressions (use Expr::typed not Expr::new):\n  {}",
            errs.join("\n  ")
        );
    }
}

fn compile(source: &str) -> (crate::ssa::Module, Vec<crate::ssa::Value>) {
    let (mut ssa_module, input_vals) = compile_until_lower(source);
    // Match the binary's pipeline so tests and `cargo run` see the
    // same optimized SSA. Single source of truth: `opt::run_full_pipeline`,
    // which calls `validate::check` between every pass.
    crate::opt::run_full_pipeline(&mut ssa_module);
    (ssa_module, input_vals)
}

// ---- Test runners ----

/// Compile and run an Ori program via SSA with the given I64 input.
fn run(source: &str, input: i64) -> Scalar {
    run_with_heap(source, input).0
}

/// Like `run` but also returns the final `Heap`, so tests can inspect
/// allocation stats (e.g. assert `peak_live` stays bounded for a
/// program that should mutate in place).
#[allow(dead_code)]
fn run_with_heap(source: &str, input: i64) -> (Scalar, crate::ssa::eval::Heap) {
    let (ssa_module, input_vals) = compile(source);
    let mut heap = crate::ssa::eval::new_heap();
    crate::ssa::eval::load_statics(&ssa_module, &mut heap);
    // Stats start after harness setup so they reflect program behavior.
    heap.alloc_count = 0;
    heap.fresh_alloc_count = 0;
    heap.free_count = 0;
    heap.peak_live = 0;
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
    // Reset again after arg setup, since args themselves shouldn't
    // count against the program's stats.
    heap.alloc_count = 0;
    heap.fresh_alloc_count = 0;
    heap.free_count = 0;
    heap.peak_live = 0;
    let result = crate::ssa::eval::eval(&ssa_module, &mut heap, &ssa_args);
    (result, heap)
}

fn run_i64(source: &str, input: i64) -> i64 {
    match run(source, input) {
        Scalar::I64(n) => n,
        other => panic!("expected I64 result, got {other:?}"),
    }
}

#[test]
fn e_single_variant_no_heap() {
    // Phase E: single-variant non-fieldless tag unions skip both the
    // tag and the payload heap object. `Wrapped(42).x` should produce
    // the wrapped value directly with no heap allocation for the
    // tag-union shell or payload.
    let source = "\
main : I64 -> I64
main = |_| (
    r = Wrapped(42)
    if r : Wrapped(x) then x
)";
    let (result, heap) = run_with_heap(source, 0);
    assert_eq!(result, Scalar::I64(42));
    assert_eq!(heap.alloc_count, 0,
        "expected zero allocs for single-variant tag union, got {}",
        heap.alloc_count);
}

#[test]
fn e_captured_closure_in_walk() {
    // A closure-with-captures used in a walk. The list literal
    // `[1, 2, 3]` is `static_promote`d so it contributes no
    // runtime allocs. The closure captures `n` (one I64). With
    // per-call-site lambda set keying, the walk's set is
    // singleton, and Phase E lowering should collapse the
    // closure value to `Multi(n)` — the capture lives in a
    // register (threaded through the walk loop's block params),
    // no payload heap, no tag shell. Expected allocs: zero.
    let source = "\
main : I64 -> I64
main = |arg| (
    n = arg + 10
    [1, 2, 3].walk(0, |acc, x| acc + n + x)
)";
    let (result, heap) = run_with_heap(source, 0);
    // walk: 0 + 10 + 1 + 10 + 2 + 10 + 3 = 36
    assert_eq!(result, Scalar::I64(36));
    assert_eq!(heap.alloc_count, 0,
        "expected 0 allocs (Phase E: closure decomposes to register \
         captures; list is static), got {}",
        heap.alloc_count);
}

#[test]
fn e_two_walks_same_signature_singleton_each() {
    // Two walks at the same `(I64, I64) -> I64` step type.
    // Pre per-call-site keying both walks shared one lambda set
    // (set contained two closures → multi-variant → went through
    // `__apply_K` dispatcher and the closure value lived on the
    // heap). With per-call-site keying each walk has its own
    // singleton set, so each closure decomposes into register
    // captures (Phase E).
    let source = "\
main : I64 -> I64
main = |arg| (
    a = arg + 10
    b = arg + 20
    s1 = [1, 2].walk(0, |acc, x| acc + a + x)
    s2 = [3, 4].walk(s1, |acc, x| acc + b + x)
    s2
)";
    let (result, heap) = run_with_heap(source, 0);
    // walk1: 0 + 10 + 1 + 10 + 2 = 23
    // walk2: 23 + 20 + 3 + 20 + 4 = 70
    assert_eq!(result, Scalar::I64(70));
    // Both lists `[1, 2]` and `[3, 4]` are compile-time constants and
    // get `static_promote`d (no runtime allocs). Both closures
    // decompose via Phase E (per-call-site singleton sets, captures
    // threaded as block params). Net: zero runtime allocs.
    assert_eq!(heap.alloc_count, 0,
        "expected 0 allocs (lists are static, closures are Phase E), got {}",
        heap.alloc_count);
}

#[test]
fn e_user_hof_singleton_callsite() {
    // User HOF with one call site. The lambda set for `f` is a
    // singleton (only one closure flows into it), so under Phase E
    // the closure value should decompose to Multi(captures) at the
    // call site and `f(n)` inside `apply` should be a direct call.
    // Expected allocs: zero.
    let source = "\
apply : (I64 -> I64), I64 -> I64
apply = |f, n| f(n)

main : I64 -> I64
main = |arg| (
    x = 10
    apply(|y| y + x, arg)
)";
    let (result, heap) = run_with_heap(source, 5);
    assert_eq!(result, Scalar::I64(15));
    // The closure captures `x`. With Phase E, the closure value is
    // Multi([x]) in registers — no heap object.
    println!("e_user_hof_singleton_callsite allocs: {}", heap.alloc_count);
    assert_eq!(heap.alloc_count, 0,
        "expected 0 allocs (closure decomposed via Phase E), got {}",
        heap.alloc_count);
}

#[test]
fn e_user_hof_two_callsites_same_type() {
    // Two call sites of `apply` with different closures of the same
    // type. Pre-Stage-2 these merged into a 2-variant lambda set,
    // forcing the D2 (tag, payload_ptr) heap shape (2 allocs per
    // closure: 4 total). Post-Stage-2 `lambda_narrow` clones `apply`
    // per call site; each clone's HO param is a singleton TagUnion,
    // Phase E decomposes the closure into register captures, and the
    // body's `__apply_K` dispatch inlines as a direct call.
    let source = "\
apply : (I64 -> I64), I64 -> I64
apply = |f, n| f(n)

main : I64 -> I64
main = |arg| (
    a = arg + 10
    b = arg + 20
    x1 = apply(|y| y + a, 1)
    x2 = apply(|y| y + b, 2)
    x1 + x2
)";
    let (result, heap) = run_with_heap(source, 5);
    // x1 = 1 + 15 = 16; x2 = 2 + 25 = 27; sum = 43
    assert_eq!(result, Scalar::I64(43));
    assert_eq!(heap.alloc_count, 0,
        "expected 0 allocs (per-call-site narrowing → Phase E for both \
         closures), got {}",
        heap.alloc_count);
}

#[test]
fn e_user_hof_multislot_single_callsite() {
    // Single call site, multi-slot capture. Before the fix:
    // lambda_specialize's singleton path created a capture-Name
    // expression with placeholder type, so `lower::to_slots` couldn't
    // expand the multi-slot capture at the lifted-func call boundary.
    let source = "\
apply : (I64 -> I64), I64 -> I64
apply = |f, n| f(n)

main : I64 -> I64
main = |arg| (
    extras = [arg + 1, arg + 2, arg + 3]
    apply(|y| y + extras.get(0).unwrap(), 10)
)";
    // arg=5 → extras=[6,7,8] → 10 + 6 = 16
    let result = run_i64(source, 5);
    assert_eq!(result, 16);
}

#[test]
fn e_user_hof_multislot_capture() {
    // User HOF whose closure captures a multi-slot value (a List,
    // which decomposes to 3 SSA slots: len, cap, data). Two call
    // sites so `lambda_narrow` clones the callee per site. Each
    // clone's singleton TagDecl + body must receive and pass the
    // capture as 3 flat slots to the lifted function — not as a
    // single pointer-to-tuple. Without the flattening fix, the
    // clone's pattern bind would extract one Value (a pointer)
    // where the lifted function expects 3 slots, and the runtime
    // would mis-interpret bytes (typically panicking with
    // "unsupported binop Add on Ptr, I64" once the pointer gets
    // arithmetically combined).
    let source = "\
apply : (I64 -> I64), I64 -> I64
apply = |f, n| f(n)

main : I64 -> I64
main = |arg| (
    extras = [arg + 1, arg + 2, arg + 3]
    x1 = apply(|y| y + extras.get(0).unwrap(), 10)
    x2 = apply(|y| y + extras.get(1).unwrap(), 20)
    x1 + x2
)";
    // arg = 5 → extras = [6, 7, 8]
    // x1 = 10 + 6 = 16; x2 = 20 + 7 = 27; sum = 43
    let result = run_i64(source, 5);
    assert_eq!(result, 43);
}

#[test]
fn e_user_hof_multislot_heterogeneous_dispatch() {
    // Heterogeneous closure flow (runtime-conditional `if cond then
    // fn_a else fn_b`) into a user HOF, where both branches capture
    // multi-slot values. `lambda_narrow` can't narrow this (the
    // closure is a variable, not a tag-constructor call at the call
    // site), so dispatch goes through `lambda_specialize`'s
    // synthesized `__apply_K` multi-variant dispatcher. Before the
    // fix, the dispatcher's body had the same untyped-Name latent
    // bug as the singleton path — it crashed at runtime.
    let source = "\
apply : (I64 -> I64), I64 -> I64
apply = |f, n| f(n)

main : I64 -> I64
main = |arg| (
    xs = [arg + 1, arg + 2]
    ys = [arg + 10, arg + 20]
    f = if arg > 0 then (|n| n + xs.get(0).unwrap()) else (|n| n + ys.get(0).unwrap())
    apply(f, 100)
)";
    // arg=5 → xs=[6,7], cond=true → 100 + 6 = 106
    let result = run_i64(source, 5);
    assert_eq!(result, 106);
}

#[test]
fn e_user_hof_heterogeneous_callsite() {
    // A single call site where the closure choice is a runtime
    // condition (one of two lifted lambdas can flow in). Narrowing
    // can't help here — the callee's HO param genuinely needs the
    // multi-variant tag union. Verify the program still runs
    // correctly (correctness check; alloc shape stays D2).
    let source = "\
apply : (I64 -> I64), I64 -> I64
apply = |f, n| f(n)

main : I64 -> I64
main = |arg| (
    x = arg + 10
    y = arg + 20
    apply(if arg > 0 then (|n| n + x) else (|n| n + y), 7)
)";
    let result = run_i64(source, 5);
    assert_eq!(result, 22);
}

#[test]
fn d1_inline_tuple_list_elements() {
    // Phase D1: List(Tuple(I64, I64)) stores each tuple as two
    // inline I64 slots (16-byte stride) in the data buffer rather
    // than allocating a separate heap object per element. The
    // 3-element list literal allocates exactly the data buffer
    // (3 * 16 = 48 bytes) plus the 24-byte list header — no
    // per-element heap objects.
    let source = "\
main : I64 -> I64
main = |_| (
    pairs = [(1, 2), (3, 4), (5, 6)]
    (a, b) = pairs.get(1).unwrap()
    a + b
)";
    let (result, heap) = run_with_heap(source, 0);
    assert_eq!(result, Scalar::I64(7));
    // Allocs: data buffer (1) + list header (1) + Ok payload (1) +
    // tag union shell (1) + tuple materialized for payload (1) = 5.
    // The key D1 win: no per-element tuple heap object inside the
    // data buffer.
    assert!(heap.alloc_count <= 5,
        "expected ≤5 allocs (no per-element tuple heap), got {}",
        heap.alloc_count);
}




#[allow(dead_code, reason = "used by structural-tag inference tests")]
fn infer_func_type(source: &str, func: &str) -> String {
    let (_arena, _file_id, mut resolved) = parse_and_resolve(source);
    let infer_result = through_infer(&mut resolved);
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

#[allow(dead_code, reason = "used by error-message tests")]
fn infer_err(source: &str) -> String {
    let (arena, _file_id, mut resolved) = parse_and_resolve(source);
    crate::passes::fold_lift::lift(&mut resolved);
    crate::passes::flatten_patterns::flatten(&mut resolved).unwrap();
    crate::passes::topo::compute(&mut resolved).unwrap();
    match crate::types::infer::check(&mut resolved) {
        Ok(_) => panic!("expected inference to fail, but it succeeded"),
        Err(e) => e.format(&arena),
    }
}

fn run_u64(source: &str, input: i64) -> u64 {
    match run(source, input) {
        Scalar::U64(n) => n,
        other => panic!("expected U64 result, got {other:?}"),
    }
}

// ============================================================
// Heap statistics — sanity check that the counters fire.
// ============================================================

#[test]
fn heap_stats_scalar_program_allocates_nothing() {
    // Pure scalar arithmetic should produce zero allocations.
    let source = "\
main : I64 -> I64
main = |arg| arg * 2 + 7";
    let (_, heap) = run_with_heap(source, 5);
    assert_eq!(heap.alloc_count, 0);
    assert_eq!(heap.fresh_alloc_count, 0);
    assert_eq!(heap.free_count, 0);
    assert_eq!(heap.peak_live, 0);
}

#[test]
fn heap_stats_baseline_for_list_construction() {
    // List construction + consumption shouldn't leak. We use a list
    // whose `.get` result actually flows into the return value so
    // dead-alloc elimination can't kill the data buffer (it has a
    // genuine reader). Whether or not the header survives is up to
    // lower's optimizations; the invariant is just "no leaks."
    let source = "\
main : I64 -> I64
main = |arg| [1, arg, 3].get(1).unwrap()";
    let (result, heap) = run_with_heap(source, 42);
    assert_eq!(result, Scalar::I64(42));
    assert_eq!(heap.count_live_objects(), 0,
        "leak: {} live objects at exit", heap.count_live_objects());
}

#[test]
fn fbip_list_set_reuses_unique_buffer() {
    // FBIP: when xs is uniquely owned (rc=1), `xs.set(i, v)` should
    // mutate the data buffer in place — no fresh heap allocation
    // for the data buffer. Verified via `alloc_count` (logical
    // allocs including reuse) vs `fresh_alloc_count` (real heap
    // growth). The gap is the in-place reuse.
    let source = "\
main : I64 -> I64
main = |arg| (
    xs = List.repeat(arg, 5)
    ys = xs.set(2, 99)
    ys.get(2).unwrap()
)";
    let (_, heap) = run_with_heap(source, 0);
    assert!(heap.alloc_count > heap.fresh_alloc_count,
        "FBIP regression: every alloc was fresh ({} == {}). \
         Expected `list.set` to reuse the unique data buffer in place.",
        heap.alloc_count, heap.fresh_alloc_count);
}

#[test]
fn fbip_list_append_reuses_unique_buffer() {
    // FBIP for list.append: when xs is uniquely owned, append should
    // resize-in-place rather than allocate a fresh buffer + copy.
    // Same convention as fbip_list_set: alloc_count counts logical
    // allocs (including in-place reuse via cow_resize_dyn);
    // fresh_alloc_count counts real heap growth. Gap > 0 means reuse.
    let source = "\
main : I64 -> I64
main = |arg| (
    xs = List.repeat(arg, 5)
    ys = xs.append(99)
    ys.get(5).unwrap()
)";
    let (result, heap) = run_with_heap(source, 7);
    assert_eq!(result, Scalar::I64(99));
    assert!(heap.alloc_count > heap.fresh_alloc_count,
        "FBIP regression: list.append didn't reuse unique buffer ({} == {})",
        heap.alloc_count, heap.fresh_alloc_count);
    assert_eq!(heap.count_live_objects(), 0,
        "leak: {} live objects at exit", heap.count_live_objects());
}

#[test]
fn fbip_record_update_reuses_unique_base() {
    // Phase B decomposes the record entirely: no heap object exists,
    // so { p & x: 99 } is pure value substitution at the slot —
    // strictly better than FBIP's in-place mutation. Originally this
    // asserted reuse via alloc_count > fresh_alloc_count; with zero
    // allocs that's moot. FBIP for records still applies when the
    // record escapes onto the heap (e.g. stored in a list).
    let source = "\
Point : { x : I64, y : I64 }
main : I64 -> I64
main = |arg| (
    p = { x: arg, y: arg + 1 }
    q = { p & x: 99 }
    q.x + q.y
)";
    let (result, heap) = run_with_heap(source, 5);
    assert_eq!(result, Scalar::I64(105));
    assert_eq!(heap.alloc_count, 0,
        "expected zero allocs on decomposed record path, got {}",
        heap.alloc_count);
    assert_eq!(heap.count_live_objects(), 0);
}

#[test]
fn fbip_record_update_clones_when_shared() {
    // Phase B: decomposed records make "sharing" free — the update
    // produces a fresh `q` slot-Vec by replacing one Value in p's
    // slot-Vec, and p's binding still names the original slots. Both
    // can be read independently with zero heap activity. The
    // shared-base / cloned-result distinction only applies to heap-
    // resident records.
    let source = "\
Point : { x : I64, y : I64 }
main : I64 -> I64
main = |arg| (
    p = { x: arg, y: arg + 1 }
    q = { p & x: 99 }
    p.x + p.y + q.x + q.y
)";
    let (result, heap) = run_with_heap(source, 5);
    // p.x + p.y + q.x + q.y = 5 + 6 + 99 + 6 = 116
    assert_eq!(result, Scalar::I64(116));
    assert_eq!(heap.alloc_count, 0,
        "expected zero allocs on decomposed record path, got {}",
        heap.alloc_count);
    assert_eq!(heap.count_live_objects(), 0);
}

#[test]
fn fbip_list_set_clones_when_shared() {
    // FBIP shared path for list: xs is read after the set, so set
    // must clone the data buffer (not in-place).
    let source = "\
main : I64 -> I64
main = |arg| (
    xs = List.repeat(arg, 5)
    ys = xs.set(2, 99)
    a = ys.get(2).unwrap()
    b = xs.get(2).unwrap()
    a + b
)";
    let (result, heap) = run_with_heap(source, 7);
    // ys.get(2) = 99; xs.get(2) = 7 (unchanged). Sum = 106.
    assert_eq!(result, Scalar::I64(106));
    assert_eq!(heap.count_live_objects(), 0,
        "leak: {} objects still live at program end", heap.count_live_objects());
}

#[test]
#[ignore = "diagnostic"]
fn fbip_inspect_record_update_with_ptr_field() {
    let source = "\
HasList : { xs : List(I64), n : I64 }
main : I64 -> I64
main = |arg| (
    r = { xs: [1, 2, 3], n: arg }
    s = { r & xs: [10, 20, 30, 40] }
    s.n + s.xs.get(0).unwrap()
)";
    let (m, _) = compile(source);
    eprintln!("{m}");
}

#[test]
fn fbip_record_update_with_ptr_field_unique() {
    // FBIP with an RcPtr-typed field: confirm rc accounting is
    // correct when the field is a heap pointer (the auto-rc-on-Store
    // must release the old value and claim the new).
    let source = "\
HasList : { xs : List(I64), n : I64 }
main : I64 -> I64
main = |arg| (
    r = { xs: [1, 2, 3], n: arg }
    s = { r & xs: [10, 20, 30, 40] }
    s.n + s.xs.get(0).unwrap()
)";
    let (result, heap) = run_with_heap(source, 100);
    // s.n = 100; s.xs.get(0) = 10. Sum = 110.
    assert_eq!(result, Scalar::I64(110));
    assert_eq!(heap.count_live_objects(), 0,
        "leak: {} objects still live at program end", heap.count_live_objects());
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
    let (result, heap) = run_with_heap(source, 0);
    assert_eq!(result, Scalar::I64(3));
    // Phase B decomposes the tuple — no heap alloc anywhere on the
    // construct→destructure→use path.
    assert_eq!(heap.alloc_count, 0,
        "expected zero allocs on decomposed tuple path, got {}",
        heap.alloc_count);
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
    let (result, heap) = run_with_heap(source, 0);
    assert_eq!(result, Scalar::I64(73));
    // Sig expansion: swap's return is decomposed at the boundary —
    // the call produces two parallel result Values and main binds
    // them directly. No heap roundtrip.
    assert_eq!(heap.alloc_count, 0,
        "expected zero allocs on decomposed tuple-returning call, got {}",
        heap.alloc_count);
}

#[test]
fn list_header_decomposed_avoids_materialize() {
    // Phase C: List(T) decomposes to (len, cap, data) — only the data
    // buffer hits the heap. List.range allocates one data buffer; len
    // is consumed directly from the result slot, no header materialize.
    let source = "\
main : I64 -> U64
main = |arg| List.range(0, 5).len()";
    let (result, heap) = run_with_heap(source, 0);
    assert_eq!(result, Scalar::U64(5));
    // The data buffer is the only heap alloc; the (len, cap, data)
    // header doesn't exist as a heap object anymore.
    assert_eq!(heap.alloc_count, 1,
        "expected one heap alloc (data buffer) for decomposed list, got {}",
        heap.alloc_count);
}

#[test]
fn d2_tag_union_payload_decomposed() {
    // Phase D2: Non-fieldless tag unions decompose to (tag, payload).
    // Constructors allocate only the payload (variant fields) — no tag
    // slot inside. Pattern matching reads tag from the register-resident
    // slot and fields from payload at offset 0, 8, ... Building
    // `Ok(42)` from `Result(I64, Str)` and unwrapping should produce
    // 42 with only the payload heap object (8 bytes) plus the
    // materialized tag-union shell (16 bytes) — no inline-tag-and-field
    // 16-byte alloc with field@8.
    let source = "\
main : I64 -> I64
main = |arg| (
    r = Ok(arg + 1)
    r.unwrap()
)";
    assert_eq!(run_i64(source, 41), 42);
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
    let (result, heap) = run_with_heap(source, 0);
    assert_eq!(result, Scalar::I64(10));
    // The outer tuple is Multi (no header). Inner tuples materialize
    // via lower_expr on each element, but elim_dead_allocs kills them
    // since their only readers are the destructure's Loads at fixed
    // offsets. Net result: zero heap allocs.
    assert_eq!(heap.alloc_count, 0,
        "expected zero allocs for nested tuple roundtrip, got {}",
        heap.alloc_count);
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
main = |arg| List.get([10, 20, 30], 1).unwrap()";

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
main = |arg| List.get(List.reverse([10, 20, 30]), 0).unwrap()";

    // reversed = [30, 20, 10], first element is 30
    assert_eq!(run_i64(source, 0), 30);
}

#[test]
fn builtin_list_set() {
    let source = "\
main : I64 -> I64
main = |arg| List.get(List.set([10, 20, 30], 1, 99), 1).unwrap()";

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
main = |arg| List.get(List.reverse([10, 20, 30]), 0).unwrap()";

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
fn builtin_list_trail_running_sum() {
    // trail with an add reducer gives running totals:
    // [1, 2, 3, 4].trail(0, add) = [1, 3, 6, 10]
    let source = "\
main : I64 -> I64
main = |arg| (
    sums = List.trail([1, 2, 3, 4], 0, |acc, x| acc + x)
    List.get(sums, 3).unwrap()
)";
    assert_eq!(run_i64(source, 0), 10);
}

#[test]
fn builtin_list_trail_middle_element() {
    // Verify an intermediate element of the running-sum output,
    // not just the last — catches accidental reverses or
    // off-by-ones.
    let source = "\
main : I64 -> I64
main = |arg| (
    sums = List.trail([1, 2, 3, 4], 0, |acc, x| acc + x)
    List.get(sums, 1).unwrap()
)";
    assert_eq!(run_i64(source, 0), 3);
}

#[test]
fn builtin_list_trail_running_product() {
    // Running product via trail: [2, 3, 4].trail(1, mul)
    //   result[0] = 1 * 2 = 2
    //   result[1] = 2 * 3 = 6
    //   result[2] = 6 * 4 = 24
    let source = "\
main : I64 -> I64
main = |arg| (
    ps = List.trail([2, 3, 4], 1, |acc, x| acc * x)
    List.get(ps, 2).unwrap()
)";
    assert_eq!(run_i64(source, 0), 24);
}

#[test]
fn builtin_list_trail_empty() {
    // Empty input produces empty output (length 0).
    let source = "\
main : I64 -> U64
main = |arg| (
    empty : List(I64)
    empty = []
    sums = List.trail(empty, 0, |acc, x| acc + x)
    List.len(sums)
)";
    assert_eq!(run_u64(source, 0), 0);
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
main = |arg| [10, 20, 30].get(1).unwrap()";

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
main = |arg| Str.get(\"Hello\", 0).unwrap()";

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
#[should_panic(expected = "expected `Foo -> I64`")]
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

// ============================================================
// Constructor-as-function (bidirectional eta-expansion)
// ============================================================

#[test]
fn constructor_as_function_declared() {
    // A declared constructor (`Ok`) passed directly as a function
    // argument. Bidirectional inference sees that `apply` expects
    // an `I64 -> Result(I64, Str)` in its second slot and
    // eta-expands `Ok` into `|x| Ok(x)` during the post-inference
    // rewrite.
    let source = "\
apply : I64, (I64 -> Result(I64, Str)) -> Result(I64, Str)
apply = |n, f| f(n)

main : I64 -> I64
main = |arg| (
    r = apply(42, Ok)
    if r
        : Ok(x) then x
        : Err(_) then 0
)";
    assert_eq!(run_i64(source, 0), 42);
}

#[test]
fn constructor_as_function_structural() {
    // Same thing for a structural constructor that was never
    // declared anywhere. The expected arrow type from `apply`'s
    // second parameter gives `Wrapped` arity 1, and the post-
    // inference rewrite produces `|x| Wrapped(x)` which defunc then
    // handles like any other lambda argument.
    let source = "\
apply : I64, (I64 -> [Wrapped(I64)]) -> [Wrapped(I64)]
apply = |n, f| f(n)

main : I64 -> I64
main = |arg| (
    r = apply(42, Wrapped)
    if r
        : Wrapped(x) then x
)";
    assert_eq!(run_i64(source, 0), 42);
}

#[test]
fn method_ref_i64_add_in_trail() {
    // `I64.add` used as a first-class function via method reference.
    // Eta-expansion produces `|a, b| I64.add(a, b)`, defunc builds a
    // closure, and lower routes the inner call to the builtin add op.
    // [1, 2, 3, 4].trail(0, I64.add) = [1, 3, 6, 10], index 3 = 10.
    let source = "\
main : I64 -> I64
main = |arg| (
    sums = List.trail([1, 2, 3, 4], 0, I64.add)
    List.get(sums, 3).unwrap()
)";
    assert_eq!(run_i64(source, 0), 10);
}

#[test]
fn method_ref_i64_mul_in_trail() {
    // Same path with a different builtin op, to catch mishandling
    // that would only break one operator.
    let source = "\
main : I64 -> I64
main = |arg| (
    ps = List.trail([2, 3, 4], 1, I64.mul)
    List.get(ps, 2).unwrap()
)";
    assert_eq!(run_i64(source, 0), 24);
}

#[test]
fn method_ref_i64_add_in_walk() {
    // Method reference as the reducer for a plain walk (not trail).
    // Exercises the same eta-expansion path through a different HO
    // call site.
    let source = "\
main : I64 -> I64
main = |arg| List.walk([1, 2, 3, 4], 0, I64.add)";
    assert_eq!(run_i64(source, 0), 10);
}

// ============================================================
// Literal patterns
// ============================================================

#[test]
fn literal_pattern_int_match() {
    let source = "\
classify : I64 -> I64
classify = |n| if n
    : 1 then 10
    : 2 then 20
    : 3 then 30
    else 0

main : I64 -> I64
main = |arg| classify(2)";
    assert_eq!(run_i64(source, 0), 20);
}

#[test]
fn literal_pattern_char_lit() {
    // Char literal in pattern position: '(' is 40 as U8.
    let source = "\
main : I64 -> I64
main = |arg| (
    c : U8
    c = 40
    if c
        : '(' then 1
        : ')' then 2
        else 0
)";
    assert_eq!(run_i64(source, 0), 1);
}

#[test]
fn literal_pattern_str() {
    // String-literal patterns dispatch via content equality (Str =
    // List(U8) → ensure_eq_func), not pointer equality.
    let source = "\
classify : Str -> I64
classify = |s| if s
    : \"red\" then 1
    : \"green\" then 2
    : \"blue\" then 3
    else 0

main : I64 -> I64
main = |arg| classify(\"green\")";
    assert_eq!(run_i64(source, 0), 2);
}

#[test]
fn literal_pattern_str_no_match_falls_through() {
    let source = "\
classify : Str -> I64
classify = |s| if s
    : \"red\" then 1
    : \"green\" then 2
    else 99

main : I64 -> I64
main = |arg| classify(\"purple\")";
    assert_eq!(run_i64(source, 0), 99);
}

#[test]
fn nested_tuple_in_constructor_pattern_with_dynamic_args() {
    // Construct a tagged value carrying a tuple; match on it. With
    // constant constructor args, eval const-folds and hides the bug.
    // With dynamic args, the destructure's val.ty is the placeholder
    // type-var that flatten_patterns left behind, so lower defaults
    // each tuple slot to RcPtr — yielding `Add on Ptr, I64` at eval.
    let source = "\
Wrap : [MkWrap((I64, I64))]

main : I64 -> I64
main = |arg| (
    w = MkWrap((arg, arg + 1))
    if w
        : MkWrap((a, b)) then a + b
)";
    assert_eq!(run_i64(source, 5), 11);
}

#[test]
fn tuple_returning_fn_threaded_through_trail() {
    // Regression: SROA proposed promoting `step`'s `(I64, I64)` return
    // to Agg(2), the verifier denied it (the trail accumulator needs
    // the result as an RcPtr), and the body's alloc was incorrectly
    // promoted anyway — yielding a Return(Agg(2)) in a function still
    // declaring RcPtr. Caught only by soft-validation; now strict.
    let source = "\
step : (I64, I64), U8 -> (I64, I64)
step = |(x, y), ch|
    if ch
      : 'r' then (x + 1, y)
      : 'l' then (x - 1, y)
      else (x, y)

main : I64 -> I64
main = |arg| (
    moves = \"rrlrr\".to_utf8()
    trail = moves.trail((0, 0), step)
    n : I64
    n = arg
    n
)";
    // Just compile & run — the failure mode is validator panicking,
    // not a wrong value.
    assert_eq!(run_i64(source, 7), 7);
}

#[test]
fn list_pattern_arm_with_guard_and_return_falls_through_on_guard_fail() {
    // Regression: when a list-pattern arm has both guards and `return`,
    // a guard-failure must fall through to the next arm — not return
    // the fall-through value from the enclosing function.
    //
    // For xs = [-5]:
    //   - Arm 1 pattern `[x]` matches but guard `x > 0` fails.
    //   - Should fall through to `else 100`.
    //   - result = 100, function returns result + 1 = 101.
    let source = "\
f : List(I64) -> I64
f = |xs| (
    result = if xs
        : [x] and x > 0 return x
        else 100
    result + 1
)

main : I64 -> I64
main = |arg| f([-5])";
    assert_eq!(run_i64(source, 0), 101);
}

#[test]
fn list_is_exact_length() {
    let source = "\
check : List(I64) -> I64
check = |xs| if (xs is [a, b]) then 1 else 0

main : I64 -> I64
main = |arg| check([10, 20])";
    assert_eq!(run_i64(source, 0), 1);
}

#[test]
fn list_is_exact_length_mismatch() {
    let source = "\
check : List(I64) -> I64
check = |xs| if (xs is [a, b]) then 1 else 0

main : I64 -> I64
main = |arg| check([10, 20, 30])";
    assert_eq!(run_i64(source, 0), 0);
}

#[test]
fn list_is_spread_n2_rejects_shorter() {
    // Regression: `is [a, b, ..rest]` (n=2 with spread) was emitting
    // `len != 1` only, so len=0 would falsely satisfy the pattern.
    let source = "\
check : List(I64) -> I64
check = |xs| if (xs is [a, b, ..rest]) then 1 else 0

main : I64 -> I64
main = |arg| check([])";
    assert_eq!(run_i64(source, 0), 0);
}

#[test]
fn list_is_spread_n2_accepts_long_enough() {
    let source = "\
check : List(I64) -> I64
check = |xs| if (xs is [a, b, ..rest]) then 1 else 0

main : I64 -> I64
main = |arg| check([10, 20, 30, 40])";
    assert_eq!(run_i64(source, 0), 1);
}

#[test]
fn literal_pattern_negative() {
    let source = "\
sign : I64 -> I64
sign = |n| if n
    : 0 then 0
    : -1 then 99
    else 1

main : I64 -> I64
main = |arg| sign(-1)";
    assert_eq!(run_i64(source, 0), 99);
}

#[test]
fn literal_pattern_else_fallthrough() {
    let source = "\
main : I64 -> I64
main = |arg| if arg
    : 42 then 1
    else 0";
    assert_eq!(run_i64(source, 5), 0);
}

#[test]
#[should_panic(expected = "requires an `else` branch")]
fn literal_pattern_no_else_errors() {
    let source = "\
main : I64 -> I64
main = |arg| if arg
    : 1 then 10
    : 2 then 20";
    run_i64(source, 0);
}

// ============================================================
// Dot-lambda syntax
// ============================================================

#[test]
fn dot_lambda_method_call() {
    // `.add(10)` desugars to `|x| x.add(10)`, used as map callback.
    let source = "\
main : I64 -> I64
main = |arg| (
    xs = List.map([1, 2, 3], .add(10))
    List.get(xs, 1).unwrap()
)";
    assert_eq!(run_i64(source, 0), 12);
}

#[test]
fn dot_lambda_mul() {
    // `.mul(3)` desugars to `|x| x.mul(3)`.
    let source = "\
main : I64 -> I64
main = |arg| (
    xs = List.map([2, 3, 4], .mul(3))
    List.get(xs, 0).unwrap()
)";
    assert_eq!(run_i64(source, 0), 6);
}

#[test]
fn constructor_as_value_stays_nullary() {
    // Bare `Red` in a value context (no arrow expected) keeps its
    // nullary-constructor-value interpretation. This is the default
    // path — no eta-expansion.
    let source = "\
describe : [Red, Green, Blue] -> I64
describe = |c| if c
    : Red then 1
    : Green then 2
    : Blue then 3

main : I64 -> I64
main = |arg| describe(Red)";
    assert_eq!(run_i64(source, 0), 1);
}

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
// Error message attribution on call arguments
// ============================================================

#[test]
fn error_msg_call_arg_attribution() {
    // A bad argument to a named function gets an error that names
    // both the function and the argument position, and renders
    // expected vs actual types rather than an unattributed
    // "cannot unify" message.
    let source = "\
double : I64 -> I64
double = |n| n * 2

main : I64 -> I64
main = |arg| double(\"not a number\")";
    let err = infer_err(source);
    assert!(
        err.contains("in argument 1 of `double`"),
        "expected call-context attribution, got: {err}"
    );
    assert!(
        err.contains("expected `I64`") && err.contains("got `Str`"),
        "expected expected/got format, got: {err}"
    );
}

#[test]
fn error_msg_call_arg_index() {
    // The argument index is the 1-based position within the call,
    // not a flat counter across all calls in the program.
    let source = "\
add3 : I64, I64, I64 -> I64
add3 = |a, b, c| a + b + c

main : I64 -> I64
main = |arg| add3(1, \"oops\", 3)";
    let err = infer_err(source);
    assert!(
        err.contains("in argument 2 of `add3`"),
        "expected argument-2 attribution, got: {err}"
    );
}

#[test]
fn error_msg_binop_mismatch() {
    // Binop operands are symmetric, so the error uses a
    // "left/right" framing rather than "expected/got".
    let source = "\
intfn : I64 -> I64
intfn = |n| n

strfn : I64 -> Str
strfn = |n| \"x\"

main : I64 -> I64
main = |arg| intfn(arg) + strfn(arg)";
    let err = infer_err(source);
    assert!(
        err.contains("in `+`"),
        "expected binop attribution, got: {err}"
    );
    assert!(
        err.contains("left operand is `I64`") && err.contains("right operand is `Str`"),
        "expected left/right framing, got: {err}"
    );
}

#[test]
fn error_msg_match_arm_body() {
    // A match arm whose body type conflicts with a previous arm's
    // type produces an attribution pointing at "match arm body".
    let source = "\
intfn : I64 -> I64
intfn = |n| n
strfn : I64 -> Str
strfn = |n| \"x\"

pick : I64 -> I64
pick = |n| if n == 0 then intfn(n) else strfn(n)";
    let err = infer_err(source);
    assert!(
        err.contains("in match arm body"),
        "expected match arm attribution, got: {err}"
    );
    assert!(
        err.contains("expected `I64`") && err.contains("got `Str`"),
        "expected expected/got format, got: {err}"
    );
}

#[test]
fn error_msg_function_annotation_mismatch() {
    // The function body's inferred type doesn't match the declared
    // annotation. The error names the function by name.
    let source = "\
double : I64 -> Str
double = |n| n * 2";
    let err = infer_err(source);
    assert!(
        err.contains("function `double`"),
        "expected function attribution, got: {err}"
    );
    assert!(
        err.contains("expected `I64 -> Str`") || err.contains("expected `I64`"),
        "expected concrete expected type in message, got: {err}"
    );
}

#[test]
fn error_msg_let_hint_mismatch() {
    // A let binding with a TypeHint whose concrete type doesn't
    // match a concrete RHS produces an attribution pointing at
    // the binding name.
    let source = "\
main : I64 -> I64
main = |arg| (
    y : I64
    y = \"hello\"
    arg
)";
    let err = infer_err(source);
    assert!(
        err.contains("let binding `y`"),
        "expected let binding attribution, got: {err}"
    );
    assert!(
        err.contains("expected `I64`") && err.contains("got `Str`"),
        "expected expected/got format, got: {err}"
    );
}

#[test]
fn error_msg_tag_union_mismatch_in_call() {
    // When the expected type is a closed tag union and the argument
    // is an open row containing an unlisted tag, the error shows
    // both rendered forms so the user can see which tag is extra.
    let source = "\
describe : [Red, Green, Blue] -> I64
describe = |c| if c
    : Red then 1
    : Green then 2
    : Blue then 3

main : I64 -> I64
main = |arg| describe(Yellow)";
    let err = infer_err(source);
    assert!(
        err.contains("in argument 1 of `describe`"),
        "expected call-context attribution, got: {err}"
    );
    assert!(
        err.contains("[Red, Green, Blue]") && err.contains("Yellow"),
        "expected to see both expected and actual tag unions, got: {err}"
    );
}

// ============================================================
// ? operator (error propagation)
// ============================================================

#[test]
fn try_op_ok_passes_through() {
    // `?` on an Ok value extracts the payload and continues.
    let source = "\
validate : I64 -> Result(I64, Str)
validate = |n| if n == 0 then Err(\"zero\") else Ok(n)

double : I64 -> Result(I64, Str)
double = |n| (
    x = validate(n)?
    Ok(x * 2)
)

unwrap : Result(I64, Str) -> I64
unwrap = |r| if r
    : Ok(x) then x
    : Err(_) then 0 - 1

main : I64 -> I64
main = |arg| unwrap(double(5))";
    assert_eq!(run_i64(source, 0), 10);
}

#[test]
fn try_op_err_returns_early() {
    // `?` on an Err value returns the Err directly, bypassing the
    // rest of the enclosing function.
    let source = "\
validate : I64 -> Result(I64, Str)
validate = |n| if n == 0 then Err(\"zero\") else Ok(n)

double : I64 -> Result(I64, Str)
double = |n| (
    x = validate(n)?
    Ok(x * 2)
)

unwrap : Result(I64, Str) -> I64
unwrap = |r| if r
    : Ok(x) then x
    : Err(_) then 0 - 1

main : I64 -> I64
main = |arg| unwrap(double(0))";
    assert_eq!(run_i64(source, 0), -1);
}

#[test]
fn try_op_chain_two() {
    // Two `?` in sequence. The error row of the enclosing function
    // grows to include both inner error types via row polymorphism.
    let source = "\
a : I64 -> Result(I64, Str)
a = |n| if n == 1 then Err(\"from_a\") else Ok(n + 10)

b : I64 -> Result(I64, Str)
b = |n| if n == 2 then Err(\"from_b\") else Ok(n + 100)

pipeline : I64 -> Result(I64, Str)
pipeline = |n| (
    x = a(n)?
    y = b(x)?
    Ok(y)
)

unwrap : Result(I64, Str) -> I64
unwrap = |r| if r
    : Ok(x) then x
    : Err(_) then 0 - 1

main : I64 -> I64
main = |arg| unwrap(pipeline(5))";
    // 5 -> a -> Ok(15); 15 -> b -> Ok(115)
    assert_eq!(run_i64(source, 0), 115);
}

#[test]
fn try_op_chain_first_fails() {
    // First ? in the chain returns Err. Second call never runs.
    let source = "\
a : I64 -> Result(I64, Str)
a = |n| if n == 1 then Err(\"from_a\") else Ok(n + 10)

b : I64 -> Result(I64, Str)
b = |n| if n == 2 then Err(\"from_b\") else Ok(n + 100)

pipeline : I64 -> Result(I64, Str)
pipeline = |n| (
    x = a(n)?
    y = b(x)?
    Ok(y)
)

unwrap : Result(I64, Str) -> I64
unwrap = |r| if r
    : Ok(x) then x
    : Err(_) then 0 - 1

main : I64 -> I64
main = |arg| unwrap(pipeline(1))";
    assert_eq!(run_i64(source, 0), -1);
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
    let (arena, _file_id, mut resolved) = parse_and_resolve(source);
    crate::passes::fold_lift::lift(&mut resolved);
    let err = crate::passes::topo::compute(&mut resolved)
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
    // Stop at lower so mono / lambda-specialize / etc. produce
    // their distinctive output without opt (especially `inline`)
    // collapsing it. Tests that introspect SSA structure rely on
    // this to inspect the front-end's choices directly.
    compile_until_lower(source).0
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
            ExprKind::RecordUpdate { base, updates } => {
                in_expr(base) || updates.iter().any(|(_, e)| in_expr(e))
            }
            ExprKind::FieldAccess { record, .. } => in_expr(record),
            ExprKind::Tuple(elems) | ExprKind::ListLit(elems) => elems.iter().any(in_expr),
            ExprKind::Is { expr, .. } => in_expr(expr),
            ExprKind::Closure { captures, .. } => captures.iter().any(in_expr),
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
fn compile_through_defunc(source: &str) -> (crate::ast::Module<'static>, crate::symbol::SymbolTable) {
    let (_arena, _file_id, mut resolved) = parse_and_resolve(source);
    let infer_result = through_infer(&mut resolved);
    let mut mono =
        crate::passes::mono::specialize(resolved.module, infer_result, resolved.symbols);
    crate::passes::lambda::lift::lift(&mut mono);
    let lambda_solution = crate::passes::lambda::solve::solve(&mono);
    crate::passes::lambda::specialize::specialize(&mut mono, &lambda_solution);
    crate::passes::lambda::narrow::narrow(&mut mono);
    validate_ast_types(&mono, "after lambda passes (defunc helper)");
    let pre_prune_decls = crate::passes::decl_info::build(&mono);
    crate::passes::reachable::prune(&mut mono, &pre_prune_decls);
    (mono.module, mono.symbols)
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
fn defunc_emits_apply_or_clone() {
    // Two lambdas flow into the same HO parameter through two call
    // sites. After `lambda_specialize` the merged set's `__apply_K`
    // dispatcher is synthesized; after `lambda_narrow`, each call
    // site retargets to a singleton clone of `apply` and `__apply_K`
    // becomes unreachable. Both shapes — pre-narrow and post-narrow
    // — are valid post-defunc outputs; assert that EITHER an
    // `__apply_apply_*` dispatcher OR `apply__narrow*` clones exist.
    let source = "\
apply : I64, (I64 -> I64) -> I64
apply = |x, f| f(x)

main : I64, Bool -> I64
main = |arg, b| if b then apply(5, |y| y * 2) else apply(5, |y| y + 1)";
    let (module, symbols) = compile_through_defunc(source);
    let mut has_apply_or_clone = false;
    for d in &module.decls {
        if let crate::ast::Decl::FuncDef { name, .. } = d {
            let n = symbols.display(*name);
            if n.starts_with("__apply_apply_") || n.starts_with("apply__narrow") {
                has_apply_or_clone = true;
                break;
            }
        }
    }
    assert!(
        has_apply_or_clone,
        "expected __apply_apply_* or apply__narrow* in module decls"
    );
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

    fn render_typed(source_path: &str, source: &str) -> String {
        let (_arena, file_id, mut resolved) = super::parse_and_resolve_named(source_path, source);
        super::through_infer(&mut resolved);

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
        let (arena, _file_id, resolved) = super::parse_and_resolve_named(source_path, source);

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

// ============================================================
// RC reuse safety
// ============================================================

#[test]
fn trail_record_set_grow_reuse() {
    // Regression: insert_reuse would convert RcDec+Alloc into Reset+Reuse
    // for values that were passed to calls (like __list_repeat). The callee
    // stores the value N times without rc_inc, so Reset's uniqueness check
    // was wrong and Reuse would overwrite shared memory.
    //
    // trail stores new_acc in both state.acc AND state.out (via append).
    // When the resulting list is walked to build a Set, the 7th insert
    // triggers Set.grow which calls __list_repeat. Without the fix, grow
    // would corrupt the bucket array and produce a set of size 1.
    let source = "\
import set

main : I64 -> U64
main = |_| (
    start = { x: 0, y: 0 }
    moves = [1, 1, 1, 1, 1, 1]
    positions = moves.trail(start, |pos, _| { x: pos.x + 1, y: 0 })
    positions.walk(Set.single(start), |s, pos| s.insert(pos)).len()
)";
    // start + 6 distinct positions = 7
    assert_eq!(run_u64(source, 0), 7);
}

#[test]
fn pack_trail_set_grow() {
    // Regression: record packing + trail + Set.grow interaction.
    let source = "\
import set
main : I64 -> U64
main = |_| (
    start = { x: 0, y: 0 }
    moves = [1, 1, 1, 1, 1, 1]
    trail_result = moves.trail(start, |pos, _| { x: pos.x + 1, y: 0 })
    trail_result.walk(Set.single(start), |s, pos| s.insert(pos)).len()
)";
    assert_eq!(run_u64(source, 0), 7);
}

#[test]
fn bare_polymorphic_function_reference() {
    // Regression: passing a polymorphic function as a bare name (not
    // wrapped in a lambda) would crash with "undefined name" because
    // monomorphization didn't specialize the function for value-position
    // references.
    let source = "\
inc = |(x, y), _| (x + 1, y)

main : I64 -> I64
main = |_| (
    (result, _) = [1, 2, 3].trail((0, 0), inc).get(2).unwrap()
    result
)";
    // trail with inc: (0,0) -> (1,0) -> (2,0) -> (3,0); element at index 2 = (3,0)
    assert_eq!(run_i64(source, 0), 3);
}

#[test]
fn set_from_list_with_tuples() {
    // Regression: Set.from_list lost the element type when the type
    // variable in the scheme was unified to a different representative
    // during inference. The scheme's vars list used the original
    // variable ID while the resolved type used the representative,
    // causing the monomorphizer to extract the wrong substitution.
    let source = "\
import set

main : I64 -> U64
main = |_| Set.from_list([(0, 0), (1, 0), (2, 0), (1, 0)]).len()";
    // 4 elements, 3 unique
    assert_eq!(run_u64(source, 0), 3);
}

#[test]
fn bitwise_operations_u32() {
    // bit_and
    let source = "\
main : I64 -> U64
main = |_| (
    a : U32
    a = 255
    b : U32
    b = 15
    result : U32
    result = a.bit_and(b)
    if result == 15 then 1 else 0
)";
    assert_eq!(run_u64(source, 0), 1);

    // bit_or, bit_xor, shl, shr
    let source2 = "\
main : I64 -> U64
main = |_| (
    a : U32
    a = 240
    b : U32
    b = 15
    or_ok = (a | b) == 255
    xor_ok = (a ^ b) == 255
    shl_ok = b.shl(4) == 240
    shr_ok = a.shr(4) == 15
    rot_ok = a.rotate_left(28) == 15
    not_ok = b.bit_not() == 4294967280
    if or_ok and xor_ok and shl_ok and shr_ok and rot_ok and not_ok then 1 else 0
)";
    assert_eq!(run_u64(source2, 0), 1);
}

#[test]
fn md5_empty_string() {
    // Full inline MD5 test - tests bitwise ops, U32 from_u8/to_u8, and the algorithm
    let source = r#"
s_table : List(U32)
s_table = [
    7, 12, 17, 22, 7, 12, 17, 22, 7, 12, 17, 22, 7, 12, 17, 22,
    5,  9, 14, 20, 5,  9, 14, 20, 5,  9, 14, 20, 5,  9, 14, 20,
    4, 11, 16, 23, 4, 11, 16, 23, 4, 11, 16, 23, 4, 11, 16, 23,
    6, 10, 15, 21, 6, 10, 15, 21, 6, 10, 15, 21, 6, 10, 15, 21
]

k_table : List(U32)
k_table = [
    3614090360, 3905402710, 606105819, 3250441966,
    4118548399, 1200080426, 2821735955, 4249261313,
    1770035416, 2336552879, 4294925233, 2304563134,
    1804603682, 4254626195, 2792965006, 1236535329,
    4129170786, 3225465664, 643717713, 3921069994,
    3593408605, 38016083, 3634488961, 3889429448,
    568446438, 3275163606, 4107603335, 1163531501,
    2850285829, 4243563512, 1735328473, 2368359562,
    4294588738, 2272392833, 1839030562, 4259657740,
    2763975236, 1272893353, 4139469664, 3200236656,
    681279174, 3936430074, 3572445317, 76029189,
    3654602809, 3873151461, 530742520, 3299628645,
    4096336452, 1126891415, 2878612391, 4237533241,
    1700485571, 2399980690, 4293915773, 2240044497,
    1873313359, 4264355552, 2734768916, 1309151649,
    4149444226, 3174756917, 718787259, 3951481745
]

pack_le : U8, U8, U8, U8 -> U32
pack_le = |b0, b1, b2, b3|
    U32.from_u8(b0)
        .bit_or(U32.from_u8(b1).shl(8))
        .bit_or(U32.from_u8(b2).shl(16))
        .bit_or(U32.from_u8(b3).shl(24))

build_words : List(U8), U64 -> List(U32)
build_words = |bytes, offset|
    List.range(0, 16).walk([], |acc, i| (
        j = offset + i * 4
        w = pack_le(
            bytes.get(j).unwrap(),
            bytes.get(j + 1).unwrap(),
            bytes.get(j + 2).unwrap(),
            bytes.get(j + 3).unwrap()
        )
        acc.append(w)
    ))

round_fg : U32, U32, U32, U64 -> (U32, U64)
round_fg = |b, c, d, i|
    if i < 16 then
        (b.bit_and(c).bit_or(b.bit_not().bit_and(d)), i)
    else if i < 32 then
        (d.bit_and(b).bit_or(d.bit_not().bit_and(c)), (5 * i + 1) % 16)
    else if i < 48 then
        (b.bit_xor(c).bit_xor(d), (3 * i + 5) % 16)
    else
        (c.bit_xor(b.bit_or(d.bit_not())), (7 * i) % 16)

round_loop = |a, b, c, d, m|
    List.range(0, 64).walk({ a: a, b: b, c: c, d: d }, |state, i| (
        (f, g) = round_fg(state.b, state.c, state.d, i)
        temp = state.a + f + k_table.get(i).unwrap() + m.get(g).unwrap()
        new_b = state.b + temp.rotate_left(s_table.get(i).unwrap())
        { a: state.d, b: new_b, c: state.b, d: state.c }
    ))

pad_zeros : List(U8) -> List(U8)
pad_zeros = |msg|
    List.range(0, 64).walk_until(msg, |m, x|
        if m.len() % 64 == 56 then Break(m)
        else Continue(m.append(0)))

append_length : List(U8), U64 -> List(U8)
append_length = |msg, bit_len|
    msg.append(bit_len.bit_and(255).to_u8())
       .append(bit_len.shr(8).bit_and(255).to_u8())
       .append(bit_len.shr(16).bit_and(255).to_u8())
       .append(bit_len.shr(24).bit_and(255).to_u8())
       .append(bit_len.shr(32).bit_and(255).to_u8())
       .append(bit_len.shr(40).bit_and(255).to_u8())
       .append(bit_len.shr(48).bit_and(255).to_u8())
       .append(bit_len.shr(56).bit_and(255).to_u8())

pad : List(U8) -> List(U8)
pad = |msg| (
    orig_len = msg.len()
    padded = pad_zeros(msg.append(128))
    append_length(padded, orig_len * 8)
)

unpack_le : U32 -> List(U8)
unpack_le = |w| [
    w.to_u8(),
    w.shr(8).to_u8(),
    w.shr(16).to_u8(),
    w.shr(24).to_u8()
]

main : I64 -> U64
main = |_| (
    padded = pad([])
    words : List(U32)
    words = build_words(padded, 0)
    a0 : U32
    a0 = 1732584193
    b0 : U32
    b0 = 4023233417
    c0 : U32
    c0 = 2562383102
    d0 : U32
    d0 = 271733878
    result = round_loop(a0, b0, c0, d0, words)
    result_a = a0 + result.a
    # MD5("") first word should be 0xd98c1dd4 = 3652501972
    # Actually: d41d8cd9 -> first 4 bytes are d4, 1d, 8c, d9
    # little-endian U32: 0xd98c1dd4 = 3652501972
    result = unpack_le(result_a)
    # First byte of MD5("") should be 0xd4 = 212
    if result.get(0).unwrap() == 212 then 1 else 0
)
"#;
    assert_eq!(run_u64(source, 0), 1);
}

#[test]
fn u32_from_u8() {
    let source = "\
main : I64 -> U64
main = |_| (
    x : U32
    x = U32.from_u8(42)
    if x == 42 then 1 else 0
)";
    assert_eq!(run_u64(source, 0), 1);
}

#[test]
#[ignore = "diagnostic; run with --ignored --nocapture"]
fn audit_ssa_cleanliness() {
    audit_ssa_cleanliness_inner(/*run_opt=*/true);
}

#[test]
#[ignore = "diagnostic; run with --ignored --nocapture"]
fn audit_ssa_cleanliness_raw() {
    audit_ssa_cleanliness_inner(/*run_opt=*/false);
}

/// Compare raw vs optimized SSA on runtime metrics (alloc_count,
/// fresh_alloc_count, peak_live). Some opt passes (static_promote,
/// retype_statics) move work off the heap without changing IR shape
/// much — inst count alone underestimates their value.
#[test]
#[ignore = "diagnostic; run with --ignored --nocapture"]
fn audit_opt_runtime_impact() {
    let programs = [
        ("list_set", "main : I64 -> I64\nmain = |arg| (\n    xs = List.repeat(arg, 5)\n    ys = xs.set(2, 99)\n    ys.get(2).unwrap()\n)", 0i64),
        ("rec_update", "Point = { x : I64, y : I64 }\nmain : I64 -> I64\nmain = |arg| (\n    p = { x: arg, y: arg + 1 }\n    q = { p & x: 99 }\n    q.x + q.y\n)", 5),
        // List literal — should be promotable to static.
        ("list_literal", "main : I64 -> I64\nmain = |_| List.sum([10, 20, 12, 100])", 0),
        ("rec_const", "Point = { x : I64, y : I64 }\nmain : I64 -> I64\nmain = |_| (\n    p = { x: 10, y: 20 }\n    p.x + p.y\n)", 0),
        // Repeated calls — chance for inline/const fold.
        ("repeated_calls", "double : I64 -> I64\ndouble = |x| x + x\nmain : I64 -> I64\nmain = |arg| double(double(arg)) + double(arg)", 7),
    ];
    eprintln!("\n{:12}  {:>8} {:>8} {:>8}   {:>8} {:>8} {:>8}",
        "program", "raw_alc", "raw_fr", "raw_pk", "opt_alc", "opt_fr", "opt_pk");
    for (label, source, input) in &programs {
        let (raw_alc, raw_fresh, raw_peak) = run_get_stats(source, *input, false);
        let (opt_alc, opt_fresh, opt_peak) = run_get_stats(source, *input, true);
        eprintln!(
            "{label:12}  {raw_alc:>8} {raw_fresh:>8} {raw_peak:>8}   {opt_alc:>8} {opt_fresh:>8} {opt_peak:>8}",
        );
    }
    eprintln!("\n--- list_literal IR (opt) ---");
    let (m, _) = compile(programs[2].1);
    eprintln!("{m}");
    eprintln!("\n--- list_literal IR (raw) ---");
    let (m, _) = compile_until_lower(programs[2].1);
    eprintln!("{m}");
}

fn run_get_stats(source: &str, input: i64, run_opt: bool) -> (u64, u64, u64) {
    let (ssa_module, input_vals) = if run_opt {
        compile(source)
    } else {
        compile_until_lower(source)
    };
    let mut heap = crate::ssa::eval::new_heap();
    crate::ssa::eval::load_statics(&ssa_module, &mut heap);
    heap.alloc_count = 0;
    heap.fresh_alloc_count = 0;
    heap.free_count = 0;
    heap.peak_live = 0;
    let ssa_args: Vec<Scalar> = input_vals
        .iter()
        .enumerate()
        .map(|(i, _)| {
            if i == 0 {
                Scalar::I64(input)
            } else {
                let data = heap.alloc(0);
                let header = heap.alloc(3);
                heap.store(header, 0, Scalar::U64(0));
                heap.store(header, 1, Scalar::U64(0));
                heap.store(header, 2, Scalar::Ptr(data));
                Scalar::Ptr(header)
            }
        })
        .collect();
    heap.alloc_count = 0;
    heap.fresh_alloc_count = 0;
    heap.free_count = 0;
    heap.peak_live = 0;
    let _ = crate::ssa::eval::eval(&ssa_module, &mut heap, &ssa_args);
    (heap.alloc_count, heap.fresh_alloc_count, heap.peak_live)
}

fn audit_ssa_cleanliness_inner(run_opt: bool) {
    let programs = [
        ("identity", "main : I64 -> I64\nmain = |x| x"),
        ("list_set", "main : I64 -> I64\nmain = |arg| (\n    xs = List.repeat(arg, 5)\n    ys = xs.set(2, 99)\n    ys.get(2).unwrap()\n)"),
        ("rec_update", "Point = { x : I64, y : I64 }\nmain : I64 -> I64\nmain = |arg| (\n    p = { x: arg, y: arg + 1 }\n    q = { p & x: 99 }\n    q.x + q.y\n)"),
        ("walk_sum", "main : U64 -> U64\nmain = |n| (\n    xs = List.range(0, n)\n    xs.walk(0, |acc, x| acc + x)\n)"),
    ];

    eprintln!("\n=== audit (run_opt={run_opt}) ===");

    let mut t_insts = 0usize;
    let mut t_rc = 0usize;
    let mut t_warn = 0usize;
    let mut t_blocks = 0usize;
    let mut t_funcs = 0usize;

    eprintln!();
    for (label, source) in &programs {
        let (module, _) = if run_opt { compile(source) } else { compile_until_lower(source) };
        let report = crate::ssa::validate::validate(&module);
        let mut insts = 0usize;
        let mut rc = 0usize;
        let mut blocks = 0usize;
        let mut funcs = 0usize;
        for func in module.functions.values() {
            funcs += 1;
            for block in func.blocks.values() {
                blocks += 1;
                for inst in &block.insts {
                    insts += 1;
                    if matches!(inst, crate::ssa::Inst::RcInc(..) | crate::ssa::Inst::RcDec(..)) {
                        rc += 1;
                    }
                }
            }
        }
        t_insts += insts;
        t_rc += rc;
        t_warn += report.warnings.len();
        t_blocks += blocks;
        t_funcs += funcs;
        eprintln!("{label:12} funcs={funcs:3} blocks={blocks:4} insts={insts:5} rc={rc:4} warn={}", report.warnings.len());
        for w in report.warnings.iter().take(2) {
            eprintln!("           warn: {w}");
        }
    }
    eprintln!("---");
    eprintln!("TOTAL        funcs={t_funcs:3} blocks={t_blocks:4} insts={t_insts:5} rc={t_rc:4} warn={t_warn}");
    eprintln!("rc fraction: {:.1}%", 100.0 * t_rc as f64 / t_insts.max(1) as f64);

    // Dump all IRs for visual inspection.
    for i in 0..programs.len() {
        eprintln!("\n--- {} IR ---", programs[i].0);
        let (m, _) = if run_opt { compile(programs[i].1) } else { compile_until_lower(programs[i].1) };
        eprintln!("{m}");
    }
}

#[test]
fn core_lowering_roundtrips_simple_arithmetic() {
    // End-to-end validation that AST → Core → SSA produces a working
    // program for the slice we've implemented so far.
    //
    // Source: `main = |n| n + 1`. Expected eval result on input 5: 6.
    let source = "\
main : I64 -> I64
main = |n| n + 1
";
    let (_arena, _file_id, mut resolved) = parse_and_resolve(source);
    let infer_result = through_infer(&mut resolved);
    let mut mono = crate::passes::mono::specialize(
        resolved.module,
        infer_result,
        resolved.symbols,
    );
    crate::passes::lambda::lift::lift(&mut mono);
    let lambda_solution = crate::passes::lambda::solve::solve(&mono);
    crate::passes::lambda::specialize::specialize(&mut mono, &lambda_solution);
    crate::passes::lambda::narrow::narrow(&mut mono);

    // Find the user's `main` function decl.
    let main_decl = mono.module.decls.iter().find(|d| matches!(d,
        crate::ast::Decl::FuncDef { name, .. }
            if mono.symbols.display(*name) == "main"
    )).expect("expected `main` decl");
    let crate::ast::Decl::FuncDef { params, body, .. } = main_decl else {
        unreachable!();
    };
    assert_eq!(params.len(), 1, "main takes one param");
    let n_sym = params[0];

    // Lower the body AST → Core.
    let core_body = crate::passes::core::lower::lower_expr(body)
        .expect("Core lowering should succeed for n + 1");

    // Lower Core → SSA by hand: one function, one entry block, with
    // `n` as a function param.
    let mut b = crate::ssa::Builder::new();
    let n_val = b.add_func_param(crate::ssa::ScalarType::I64);
    let _entry = b.create_block();
    b.switch_to(crate::ssa::BlockId(0));
    let mut locals = std::collections::HashMap::new();
    locals.insert(n_sym, n_val);
    let decls = crate::passes::decl_info::DeclInfo::default();
    let mut ctx = crate::passes::core::to_ssa::Ctx {
        builder: &mut b,
        symbols: &mono.symbols,
        decls: &decls,
        locals,
        fieldless: std::collections::HashMap::new(),
    };
    let result = crate::passes::core::to_ssa::lower(&mut ctx, &core_body)
        .expect("Core→SSA should succeed");
    drop(ctx);
    b.ret(result);
    b.finish_function("__main", crate::ssa::ScalarType::I64);
    let module = b.build("__main");
    crate::ssa::validate::check(&module, "core e2e");

    // Eval with n=5.
    let mut heap = crate::ssa::eval::new_heap();
    crate::ssa::eval::load_statics(&module, &mut heap);
    let result = crate::ssa::eval::eval(&module, &mut heap, &[Scalar::I64(5)]);
    assert_eq!(result, Scalar::I64(6), "5 + 1 should evaluate to 6");
}

#[test]
fn core_lowering_roundtrips_if_with_bool() {
    // Round-trip a program with an If through Core. The AST has
    //   if (n == 0) : True then 1 : False then 0
    // which lowers to Core::Match with two Constructor arms over a
    // fieldless [True, False] union. Core→SSA emits a SwitchInt.
    let source = "\
main : I64 -> I64
main = |n| if n == 0 : True then 1 : False then 0
";
    let (_arena, _file_id, mut resolved) = parse_and_resolve(source);
    let infer_result = through_infer(&mut resolved);
    let mut mono = crate::passes::mono::specialize(
        resolved.module,
        infer_result,
        resolved.symbols,
    );
    crate::passes::lambda::lift::lift(&mut mono);
    let lambda_solution = crate::passes::lambda::solve::solve(&mono);
    crate::passes::lambda::specialize::specialize(&mut mono, &lambda_solution);
    crate::passes::lambda::narrow::narrow(&mut mono);
    let decls = crate::passes::decl_info::build(&mono);

    let ctx = crate::passes::core::lower::LowerCtx { fields: &resolved.fields };
    let main_decl = mono.module.decls.iter().find(|d| matches!(d,
        crate::ast::Decl::FuncDef { name, .. }
            if mono.symbols.display(*name) == "main"
    )).expect("expected `main` decl");
    let crate::ast::Decl::FuncDef { params, body, .. } = main_decl else {
        unreachable!();
    };
    let n_sym = params[0];

    let core_body = crate::passes::core::lower::lower_expr_with(&ctx, body)
        .expect("Core lowering should succeed");

    let mut b = crate::ssa::Builder::new();
    let n_val = b.add_func_param(crate::ssa::ScalarType::I64);
    let _entry = b.create_block();
    b.switch_to(crate::ssa::BlockId(0));
    let mut locals = std::collections::HashMap::new();
    locals.insert(n_sym, n_val);
    let mut core_ctx = crate::passes::core::to_ssa::Ctx {
        builder: &mut b,
        symbols: &mono.symbols,
        decls: &decls,
        locals,
        fieldless: decls.fieldless_tags.clone(),
    };
    let result = crate::passes::core::to_ssa::lower(&mut core_ctx, &core_body)
        .expect("Core→SSA should succeed");
    drop(core_ctx);
    b.ret(result);
    b.finish_function("__main", crate::ssa::ScalarType::I64);
    let module = b.build("__main");
    crate::ssa::validate::check(&module, "core if e2e");

    // Eval with n=0 (expect True → 1) and n=5 (expect False → 0).
    let mut heap = crate::ssa::eval::new_heap();
    crate::ssa::eval::load_statics(&module, &mut heap);
    let r0 = crate::ssa::eval::eval(&module, &mut heap, &[Scalar::I64(0)]);
    assert_eq!(r0, Scalar::I64(1), "n=0 should select True arm");

    let mut heap = crate::ssa::eval::new_heap();
    crate::ssa::eval::load_statics(&module, &mut heap);
    let r5 = crate::ssa::eval::eval(&module, &mut heap, &[Scalar::I64(5)]);
    assert_eq!(r5, Scalar::I64(0), "n=5 should select False arm");
}

#[test]
fn loop_analysis_recognizes_walk() {
    // A range-driven walk that lower emits as a header/body/exit
    // loop with an IV (the counter) and an accumulator. The
    // analysis should find exactly one loop in __main with step 1.
    let source = "\
main : I64 -> I64
main = |n| (
    List.range(0, 100).walk(0, |acc, _| acc + 1)
)";
    let module = compile_to_ssa(source);
    let main_func = module.functions.get("__main")
        .expect("__main not present");
    let info = crate::ssa::loops::analyze(main_func);
    assert!(!info.loops.is_empty(), "expected at least one loop in __main, got none.\nIR:\n{}", main_func);
    let lp = &info.loops[0];
    assert_eq!(lp.step, 1, "expected step=1 from range, got {}", lp.step);
}
