# Compiler passes

Pipeline in `src/main.rs::compile`. Every phase between `resolve` and
`ssa::lower` is a pure `Module -> Module` rewrite on a single AST
type (`ast::Module`). Phase ordering is load-bearing; the notes below
flag the reasons.

```
source
  ↓ parse                raw::Module
  ↓ resolve_imports      ast::Module + ModuleScope + SymbolTable + FieldInterner
  ↓ fold_lift            ast::Module (no Fold nodes)
  ↓ flatten_patterns     ast::Module (shallow patterns, no list patterns)
  ↓ topo                 ast::Module (decls in call-graph order)
  ↓ infer                ast::Module with Expr.ty filled in, InferResult
  ↓ mono                 ast::Module (monomorphic only)
  ↓ lambda_lift          ast::Module (Lambdas → Closure nodes + lifted FuncDefs)
  ↓ lambda_solve         LambdaSolution (which closures flow where)
  ↓ lambda_specialize    ast::Module (no Lambda/Closure nodes, apply dispatch)
  ↓ decl_info            side tables for lowering
  ↓ reachable::prune     ast::Module (only reachable decls)
  ↓ ssa::lower           ssa::Module
  ↓ ssa::eval            runtime result
```

## parse — `src/syntax/parse.rs`

PEG parser (pest) with Pratt operator precedence. Produces
`raw::Module<'src>`, a shallow syntax tree that still holds names as
`&'src str`. No scoping, no types.

Parse-time desugars:

- **Char literals** — `'x'` → `IntLit(code_point)`
- **String interpolation** — `"${e}"` → `MethodCall` concat chain
- **Dot-lambdas** — `.method(args)` → `|x| x.method(args)`
- **Record field punning** — `{ value, rest }` → `{ value: value, rest: rest }`
- **Record builder** — `Type.method({ f1: e1, f2: e2 })` → nested `map2` calls
- **`expect` declarations** — `expect expr` → `__expect_N` value binding + synthetic `main` if no user main
- **`lib {}` header** — parsed and ignored (future use)

## resolve_imports — `src/resolve.rs`

Walks `import` statements, recursively parses imported files, and
converts the raw tree into `ast::Module<'src>` via `ast::from_raw`.

`from_raw` does the real work:

- Allocates a `SymbolId` for every binding site (top-level, params,
  locals, pattern bindings) through `SymbolTable`.
- Runs a scope-stack name resolver that rewrites every `Name`, call
  target, and pattern reference to carry its resolved `SymbolId`.
- Threads `is`-bindings through `and`, `then`, and `return` positions
  so `x is Ok(y) and use(y)` sees `y` on the RHS.
- Interns every record field name via `FieldInterner` into
  `FieldSym(u32)`.

Outputs `Resolved { module, scope, symbols, fields }`. The
`SymbolTable` is threaded (mutably where later passes allocate) and
the `FieldInterner` is read-only from here on.

## fold_lift — `src/fold_lift.rs`

Eliminates `ExprKind::Fold`. Each fold becomes a `Call` to a freshly
synthesized `__fold_N` helper whose body is an `If` match on the
scrutinee. Recursive constructor fields are rebound via
`let rec = __fold_N(rec_orig, ...)` at the top of each arm body, so
the helper's own recursion carries the work.

Captures are collected via `ast::free_names` and passed as extra
parameters. Synthetic spans use a `usize::MAX - n` counter to avoid
collisions with real source spans.

**Runs before infer** so that inference sees the synthesized helpers
as plain recursive functions — no special fold-inference path.

## topo — `src/topo.rs`

Builds the call graph (`Call.target`, `QualifiedCall` segments,
`MethodCall.resolved`), detects cycles, and reorders `module.decls` in
topological order. Cycles with more than one node are System T
violations (user recursion) and are reported as errors; self-loops are
allowed for `__fold_N` helpers.

**Runs after fold_lift** so the lifted helpers participate in the
order, and **before infer** so free functions are inferred in
dependency order, enabling real top-level let-polymorphism.

## flatten_patterns — `src/flatten_patterns.rs`

Normalizes patterns so the lowerer only handles shallow cases.

- **Nested constructor patterns** — `Ok(Cons(h, t))` → fresh temp +
  `is` guard chain: `Ok(__pat_0) and __pat_0 is Cons(h, t)`.
- **Nested tuple/record patterns** — hoisted to `Destructure`
  statements prepended to the arm body.
- **List patterns** — `[first, ..rest]` desugared to length checks +
  `List.get` / `List.sublist` calls. The entire `If` with list pattern
  arms becomes a nested if-else chain on `List.len`. Guards on list
  pattern arms become inner if-then-else on the guard expression.
- **List `is` patterns** — `x is [first, ..rest]` → length comparison.

After this pass, no `Pattern::List` survives in the AST. Each
synthesized expression gets a unique span via `fresh_span` to avoid
span collisions in inference's `expr_types` side table.

**Runs before infer** so synthesized expressions have placeholder
`Expr.ty` that inference fills in naturally.

## infer — `src/types/infer.rs`

Hindley-Milner with row polymorphism, driven through `types/engine.rs`
(pure HM, no AST knowledge). Populates `Expr.ty` on every node in
place.

Three sub-passes:

- **2a** — transparency setup (`Str := List(U8)`), body-less
  validation of user method annotations. Parameterized transparent
  types store `(Vec<TypeVar>, Type)` in the transparent map so App
  unification can substitute type params. `Type := {}` builtins are
  excluded from transparency to prevent all numeric types unifying
  through the empty record.
- **2b** — infer free `FuncDef` bodies in topo order, generalizing
  each scheme on exit. A function self-registers its own mono scheme
  during body inference so `__fold_N` recursive calls resolve.
  Zero-param value bindings infer the body directly (not wrapped in
  Arrow) and unify with annotations if present.
- **2c** — infer method bodies per `TypeAnno`, with opaque
  transparency scoped to that block.

Bidirectional type checking: `check_expr` pushes expected types into
lambdas. When the expected type is an opaque `App` that's transparent
to an `Arrow`, the underlying Arrow's param types flow into the
lambda's environment via `check_lambda`. This enables calling opaque
values as functions inside `.()` blocks (e.g. `p(input)` where
`p : Parser(a)`).

Comparison operators `<`, `>`, `<=`, `>=` push a `compare` method
constraint (like `==` pushes `equals`), returning `Bool`.

Method annotations are eagerly resolved to `Scheme`s in Pass 1
(previously only stdlib methods did this) to avoid polluting free
functions that call not-yet-inferred methods.

Outputs `InferResult { func_schemes, constructor_schemes }`. No more
side tables keyed by span — everything that was one in pre-refactor
code lives on `Expr.ty` now.

## mono — `src/mono.rs`

Worklist monomorphization. Starts from `main` (already concrete) and
drains `(SymbolId, Vec<Type>)` specialization requests.

For each request:

1. Normalize the type vector (resolve vars, collapse `Str ↔ List(U8)`,
   canonicalize record rows and field order).
2. If already specialized, reuse.
3. Otherwise clone the `FuncDef` body, substitute type vars, allocate
   a fresh `SymbolId` with a mangled display name
   (e.g. `List.sum__I64`), and rewrite call sites in the body to
   reference specialized targets. New requests go on the worklist.

Free functions called at mono-identity types reuse their original
`SymbolId` as an optimization. Methods are always emitted as
top-level `FuncDef`s — the method/free-function distinction goes away
here. Constructors stay polymorphic; `decl_info` recomputes field
layouts per call site.

Outputs a module with only monomorphic `FuncDef`s, plus a new
`InferResult` whose `func_schemes` are all `Type::Arrow`. Non-
termination is impossible because System T forbids user recursion.

## lambda_lift — `src/lambda_lift.rs`

Converts every `Lambda` expression into a top-level `FuncDef` with
captures as extra leading parameters, replacing the Lambda node with
a `Closure { func, captures }` value. The lifted FuncDefs are
prepended before the function whose body references their Closure
(inner lambdas before outer), giving a topo-compatible ordering for
the solve pass.

After this pass, no `Lambda` nodes survive. Every former lambda is a
named function `__lifted_N(cap0, cap1, ..., param0, param1, ...)`.

## lambda_solve — `src/lambda_solve.rs`

0-CFA flow analysis: determines which lifted functions can flow into
each higher-order parameter position. Iterates to fixpoint over the
module (typically 2–4 passes). Each iteration:

1. Scans each function body for HO call sites (local variables or
   parameters called as functions).
2. Traces `Closure` values through call arguments, let bindings,
   method receivers, and function return values.
3. Propagates HO status through capture chains: if `__lifted_N`'s
   capture parameter `i` is called, the enclosing function's
   corresponding parameter is also HO.
4. Merges lambda sets bidirectionally when the same closures flow
   through multiple paths.

Outputs `LambdaSolution`: a list of lambda sets (each with entries
mapping lifted functions to tag names + captures) and a map from
`(func_name, param_index)` to lambda set index.

A completion sweep ensures every `Closure` in the module is in at
least one lambda set, creating fallback singletons for any the flow
analysis missed.

## lambda_specialize — `src/lambda_specialize.rs`

Consumes the `LambdaSolution` and rewrites the module:

1. **Synthesize** per lambda set:
   - A `TagDecl` closure type, one variant per lambda, carrying
     captures as fields.
   - An `__apply_K` `FuncDef` that dispatches on the closure tag.
2. **Rewrite** `Closure` nodes → constructor calls packing captures.
3. **Rewrite** HO calls (`f(x)` where `f` is a closure-carrying
   variable) → `__apply_K(f, x)`.

After this pass there are no `Lambda` or `Closure` nodes — every
call has a known, first-order target.

## decl_info — `src/decl_info.rs`

Not a pass; a lookup-table build. Reads the specialized module and
produces `DeclInfo`:

- `funcs` — set of all callable display names
- `func_arities` — parameter count per callable
- `func_return_types` — concrete `ScalarType` per callable
- `constructors` — tag index, field count, recursive-field flags, and
  per-field `ScalarType` for each tag union variant (including
  lambda_specialize-synthesized closure tags)
- `constructor_schemes` — raw schemes from inference, used for layout

Used by `reachable::prune` (for `__apply_{walk}_2` aliasing) and by
`ssa::lower`.

## reachable::prune — `src/reachable.rs`

DFS from `main` over `Call.target` / `MethodCall.resolved` /
`QualifiedCall` segments / `Name` references. Drops unreachable
`FuncDef`s at both the top level and inside `TypeAnno.methods`.
`TypeAnno` decls themselves stay so `decl_info` keeps constructor
bookkeeping. Zero-param value bindings are always kept (lambda_specialize may
rewrite their Name references in ways that break the trace).

Special case: `List.walk` and its variants are lowered with an
implicit `__apply_{mangled}_2` call that's emitted at lower time
(never in the AST). Reachability has to seed those apply functions
explicitly or lowering panics.

Returns a new `ast::Module` with the pruned decl list.

## ssa::lower — `src/ssa/lower.rs`

Straight AST → SSA translator. No rewriting, no method resolution,
no reachability filtering — all of that was done upstream.

Per `ExprKind` dispatch to an emitter that writes instructions into
an `ssa::Builder`. Notable bits:

- **Match compiler** — arms lower to a switch on the discriminant
  plus per-tag blocks; `is`-binding flow through `and` chains
  propagates via SSA block parameters.
- **Constructor layout** — the `con_layout(name, ctx_ty)` helper
  unifies declared and structural constructor layout lookup.
  Declared constructors (from `TypeAnno` tag unions like `Color : [Red,
  Green, Blue]`) read `(tag_index, max_fields, field_types)` from
  `decl_info.constructors`. Structural constructors (bare uppercase
  names that aren't declared anywhere) derive the same layout on the
  fly from the enclosing expression's `Type::TagUnion` — tags are
  sorted by name, the constructor's position is its tag index, and
  `max_fields` is the max payload arity across all tags in the union.
  Per-specialization dense indices, no global tag interner. This is
  the "layout selection" step from the tag unions design, inlined
  into lowering rather than run as a separate pass.
- **List walk loops** — `List.walk(xs, init, f)` emits a loop that
  calls the `__apply_K` dispatcher for each element, not a function
  call. This is why reachability has to seed the apply function.
- **List builtin intrinsics** — `List.get`, `List.len`,
  `List.sublist`, etc. inline directly to SSA instructions instead of
  going through a call.
- **`__num_to_str`** — numeric-to-string conversions route through a
  builtin table rather than a real function.
- **`compare` builtin** — emits `Lt`/`Eq` comparisons and branches to
  construct the `Order` tag union (`Lt`/`Eq`/`Gt`).
- **Record update** — `{ base & field: val }` copies unchanged fields
  from the base record, substitutes updated ones.
- **Zero-param value bindings** — `Name` references to known
  zero-arity functions emit a zero-arg `call` instruction.
- **Record equality** — `==` on record types emits field-by-field
  comparison with short-circuit branching. Recurses for nested records.
- **Record `to_str`** — `.to_str()` on records emits inline string
  building: `"{ field: val, ... }"`. Uses `__str_concat` builtin.

Reads `func_schemes` from `InferResult` directly (for return-type
lookups) rather than from `decl_info`. Variable environment is
`HashMap<SymbolId, Value>`; no string-keyed lookups survive.

Outputs `ssa::Module`. From here `ssa::eval` runs the program, or
`--dump-ssa` prints it.

## Shape constraints worth remembering

- **`Module -> Module` everywhere** between resolve and lower. No
  `&mut` threading through sub-passes, no shared state other than the
  `SymbolTable` (mutable where new names are allocated) and the
  `FieldInterner` (read-only after resolve).
- **Types live on `Expr.ty`.** No side tables keyed by span. Rewrites
  carry their types; mono substitutes in place.
- **System T is load-bearing.** The DAG call graph is why topo-sort
  is a single pass, why mono can't diverge, and why there are no SCCs
  anywhere in the compiler.
- **Reserved `__` prefix** for compiler-synthesized names (`__fold_N`,
  `__apply_K`, `__main`, specialized mangled names). No user program
  uses the prefix.
- **Zero `unsafe`** in `src/`. Earlier drafts of lambda_specialize and mono used
  raw-pointer splits and `transmute` to work around borrow checker
  issues with in-place body rewrites; both were replaced by
  `std::mem::take` and borrowed `StoredBody` respectively.
