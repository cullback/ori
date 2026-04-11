# Compiler phases

Pipeline in `src/main.rs::compile`. Every phase between `resolve` and
`ssa::lower` is a pure `Module -> Module` rewrite on a single AST
type (`ast::Module`). Phase ordering is load-bearing; the notes below
flag the reasons.

```
source
  ↓ parse                raw::Module
  ↓ resolve_imports      ast::Module + ModuleScope + SymbolTable + FieldInterner
  ↓ fold_lift            ast::Module (no Fold nodes)
  ↓ topo                 ast::Module (decls in call-graph order)
  ↓ infer                ast::Module with Expr.ty filled in, InferResult
  ↓ mono                 ast::Module (monomorphic only)
  ↓ defunc               ast::Module (no Lambda nodes)
  ↓ decl_info            side tables for lowering
  ↓ reachable::prune     ast::Module (only reachable decls)
  ↓ ssa::lower           ssa::Module
  ↓ ssa::eval            runtime result
```

## parse — `src/syntax/parse.rs`

Recursive-descent parser. Produces `raw::Module<'src>`, a shallow
syntax tree that still holds names as `&'src str`. No scoping, no
types. Sole output: raw AST + per-node spans into `SourceArena`.

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

## infer — `src/types/infer.rs`

Hindley-Milner with row polymorphism, driven through `types/engine.rs`
(pure HM, no AST knowledge). Populates `Expr.ty` on every node in
place.

Three sub-passes:
- **2a** — transparency setup (`Str := List(U8)`), body-less
  validation of user method annotations.
- **2b** — infer free `FuncDef` bodies in topo order, generalizing
  each scheme on exit. A function self-registers its own mono scheme
  during body inference so `__fold_N` recursive calls resolve.
- **2c** — infer method bodies per `TypeAnno`, with opaque
  transparency scoped to that block.

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

## defunc — `src/defunc.rs`

Lambda elimination via standard defunctionalization.

1. **Scan** every reachable function body for lambda sites and
   higher-order parameters. Group lambdas by the HO parameter slot
   they flow into (a "lambda set").
2. **Synthesize** per set:
   - A `TagDecl` closure type, one variant per lambda, each carrying
     the lambda's captured values as fields.
   - An `__apply_K` `FuncDef` that takes the closure plus the original
     arguments and dispatches on tag.
3. **Rewrite** call sites: each lambda argument becomes a constructor
   call building the closure from captures; each HO call becomes
   `__apply_K(closure, args...)`.

Uses `std::mem::take` on the body `Option<Expr>` slot to rewrite each
entry in place without `unsafe` borrow splits.

After this phase there are no `Lambda` nodes and no higher-order
parameters — every call has a known, first-order target.

## decl_info — `src/decl_info.rs`

Not a pass; a lookup-table build. Reads the defunc'd module and
produces `DeclInfo`:

- `funcs` — set of all callable display names
- `func_arities` — parameter count per callable
- `func_return_types` — concrete `ScalarType` per callable
- `constructors` — tag index, field count, recursive-field flags, and
  per-field `ScalarType` for each tag union variant (including
  defunc-synthesized closure tags)
- `constructor_schemes` — raw schemes from inference, used for layout

Used by `reachable::prune` (for `__apply_{walk}_2` aliasing) and by
`ssa::lower`.

## reachable::prune — `src/reachable.rs`

DFS from `main` over `Call.target` / `MethodCall.resolved` /
`QualifiedCall` segments. Drops unreachable `FuncDef`s at both the
top level and inside `TypeAnno.methods`. `TypeAnno` decls themselves
stay so `decl_info` keeps constructor bookkeeping.

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
- **List builtin intrinsics** — `List.get`, `List.len`, etc. inline
  directly to SSA instructions instead of going through a call.
- **`__num_to_str`** — numeric-to-string conversions route through a
  5-entry builtin table rather than a real function.

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
- **Zero `unsafe`** in `src/`. Earlier drafts of defunc and mono used
  raw-pointer splits and `transmute` to work around borrow checker
  issues with in-place body rewrites; both were replaced by
  `std::mem::take` and borrowed `StoredBody` respectively.
