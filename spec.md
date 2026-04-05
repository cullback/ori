# Ori Language Technical Spec

**A total functional language with fold-only recursion, compiled for native performance and automatic parallelism.**

- predicative System F with inductive types and structural recursion

---

## 1. Core Calculus

Based on Gödel's System T extended with user-defined inductive types, parametric polymorphism (Hindley-Milner), tagged unions, records, and generalized fold.

Not Turing-complete. Expressive enough for virtually all string-in/string-out computation: solvers, compilers, parsers, data processing, formatters, crypto, CAS, graph algorithms.

### What is not allowed

- No self-recursive functions. No mutual recursion. The function call graph must be a DAG (enforced by topological sort at compile time).
- No general fixpoints, no `let rec`, no Y combinator.
- The only recursion primitive is `fold` over inductive data types.

### What fold gives you

- Fold walks an inductive structure bottom-up, one constructor layer at a time.
- Each arm in a fold destructures the constructor's fields, plus binds one recursive result per recursive field.
- Zero recursive fields = base case. One = linear recursion (loop). Two = binary recursion (parallel fork-join).
- Termination is guaranteed by construction, not by a checker.

### Pure/Effect separation

- Pure functions (`fn`) can only call pure functions. Total, parallelizable, aggressively optimizable.
- Effectful functions (`eff fn`) can call both pure and effectful functions, including FFI.
- Enforced by type system during checking. Erased at IR level.
- The pure core is never compromised. Effects are glue at the boundary.

---

## 2. Type System

- ML-style parametric polymorphism with full Hindley-Milner inference.
- No dependent types. Type checking is decidable, inference is complete. Programmers rarely write annotations.
- Functional equality only on data types, not function types.

### Data types

- Numeric primitives: `U8, U16, U32, U64, I8, I16, I32, I64, F32, F64`
- `List[T]` — built-in, backed by contiguous array (see §4)
- Tagged unions, records, and tuples are all the same construct: tagged product types.
- `Bool = True | False` — just a two-variant tagged union, not a primitive.
- `String` — newtype over `List[U8]` with UTF-8 validity guaranteed at construction.
- User-defined inductive types with any number of constructors and recursive fields.

---

## 3. Core IR

Six terms. Same count as GHC Core, but `Lam` is replaced by `Fold`. No lambdas in the IR — lambda lifting has already happened.

```
Core : [
  Var(SymbolId),
  Lit(Literal),
  App { func: SymbolId, args: List(Core) },
  Let { name: SymbolId, val: Core, body: Core },
  Match { expr: Core, arms: List((Pattern, Core)) },
  Fold { expr: Core, arms: List((Pattern, List(SymbolId), Core)) }
]
```

`Match` arms: pattern → body. `Fold` arms: pattern → list of recursive result binders → body.

### Core values (interpreter)

```
Value : [
  VNum(NumVal),
  VList(List(Value)),
  VConstruct { tag: SymbolId, fields: List(Value) }
]
```

Three variants. Bool, Option, tuples, records, all user types are `VConstruct`.

### Program structure

```
Program : {
  types: Map(SymbolId, TypeDef),
  funcs: Map(SymbolId, FuncDef),
  entry: SymbolId
}

FuncDef : {
  params: List((SymbolId, Type)),
  ret: Type,
  body: Core,
  extern: Bool,
  effectful: Bool
}
```

---

## 4. Lists, Strings, and Arrays

`List[T]` is the only sequence type. Semantically it has `Nil` and `Cons` constructors and supports `fold`. Physically it is backed by a contiguous array: `{ data: Ptr[T], len: U64 }`.

### Fold over lists compiles to a while-loop over contiguous memory.

### Primitive operations (not expressible as fold)

```
len:       List[T] -> Nat                    -- O(1)
get:       List[T] -> Nat -> Option[T]       -- O(1)
slice:     List[T] -> Nat -> Nat -> List[T]  -- O(1) view
tabulate:  Nat -> (Nat -> T) -> List[T]      -- construction
concat:    List[T] -> List[T] -> List[T]     -- join
```

All primitives are total. `get` returns `Option[T]`.

### Strings

`String` is a newtype over `List[U8]`. Same representation, same performance. UTF-8 validity enforced at construction via `from_utf8: List[U8] -> Option[String]`. `.bytes()` is zero-cost identity.

---

## 5. Compilation Pipeline

```
Surface syntax
  → Parse
  → Type check (HM inference, DAG check, pure/eff check)
  → Lower to Core IR
  → Constant folding / simplification
  → Inlining (bottom-up, safe because DAG)
  → Fold-fold fusion (deforestation)
  → Accumulator introduction (fold → loop)
  → Lambda lifting
  → Monomorphization (specialize all polymorphism)
  → Defunctionalization (eliminate higher-order functions)
  → Unboxing / representation selection
  → Perceus reference counting with reuse analysis
  → Emit C or LLVM IR
```

### Why each pass is simpler than in a general language

- **Inlining**: no cycles to worry about, no infinite unrolling risk.
- **Fusion**: both producer and consumer are folds, fusion rules are mechanical.
- **Defunctionalization**: set of all function values is finite and statically known. Defunctionalized code inherits the DAG property.
- **Unboxing**: after monomorphization and defunctionalization, every type is concrete and every function is first-order. Sizes and layouts are fully known.

---

## 6. Unboxed Types and Native Representation

After monomorphization + defunctionalization, the compiler knows the exact size and layout of every value.

- `Nat` / `U64` → machine register
- `F64` → floating-point register
- Pairs/records → structs or register pairs, flat in memory
- Small enums (Bool, Option[U64]) → tagged integer
- `List[T]` → pointer + length (contiguous buffer)
- No boxing, no pointer indirection, no tag words on scalars

The generated code is essentially C: structs, loops, direct calls, switch statements.

---

## 7. Memory Management

No tracing garbage collector. Three strategies layered:

1. **Stack/register allocation** for scalars and small unboxed values. No management needed.
2. **Perceus reference counting with reuse analysis** for heap-allocated inductive data. When an old value is consumed and a new value of the same size is constructed, reuse the memory in-place. Totality strengthens this: the compiler can often prove uniqueness statically, eliminating runtime refcount checks.
3. **Region inference** as fallback for array buffers. Purity guarantees no aliasing, so the compiler knows when a buffer's lifetime ends.

### Why Perceus is better in Ori than in Koka

- All data types are inductive and immutable → no cycles, ever.
- Fold structurally consumes input → uniqueness of consumed values is often provable at compile time.
- Totality → every refcount eventually reaches zero, no leaks from non-termination.

---

## 8. Parallelism

Fold makes the parallelism structure explicit and safe by construction.

- Fold over a tree with two recursive children → the two subresults are independent → parallel fork-join.
- No alias analysis, no escape analysis, no effect tracking needed. Independence is structural.
- Compatible with HVM2-style interaction combinator evaluation for the outer task distribution.
- Inner loops remain tight native code (unboxed, vectorizable).

---

## 9. Equational Reasoning and Optimization Guarantees

Because every expression denotes a value (no bottom, no divergence):

- **Substitution of equals for equals** is always valid.
- **Reordering** is always safe. No observable effect differences.
- **Dead code elimination** is always correct. Unused subexpressions can't have side effects.
- **Memoization** is always sound. Same inputs → same output.
- **Speculative evaluation** is safe. Evaluating an expression you might not need can't diverge.
- **SIMD vectorization** of fold-over-array is straightforward. The pattern is a sequential reduction over contiguous memory, which LLVM auto-vectorizes.

---

## 10. FFI

```
extern fn fast_hash(data: List[U8]) -> U64          -- pure C function
extern eff fn sqlite_query(db: Handle, sql: String) -> Result[Rows, Error]  -- effectful
```

- Pure `extern fn`: compiler can inline, reorder, parallelize calls.
- Effectful `extern eff fn`: compiler preserves call order, no speculative execution.
- Calling convention is simple: values in, value out, no callbacks, no global state.
- C header generation is automatic.

---

## 11. What You Can Build

SAT solvers, computer algebra systems, compilers, parsers, code formatters, format converters (HTML/Markdown/JSON), data analysis pipelines, graph algorithms, regex engines, cryptographic primitives, image processing, parser combinators, puzzle solvers (AoC, LeetCode, Project Euler), build systems, theorem provers.

Basically any finite-input → finite-output computation whose termination you could prove by hand.

## 12. What You Cannot Build

Web servers, REPLs, game loops, operating systems, databases — anything intentionally non-terminating. These live in the `eff` shell or the host language, calling into Ori for pure computation.

Self-interpretation — Ori cannot interpret itself (diagonalization). A bounded-step simulator is possible.

---

## 13. v0.1 — Core IR + Interpreter

**Goal:** validate fold semantics, nothing else.

**Deliverables:**

1. Data structures: `Core`, `Value`, `Type`, `TypeDef`, `FuncDef`, `Program`
2. Evaluator: one function, six cases (Var, Lit, App, Let, Match, Fold)
3. `fold_value`: pattern match value, recursively fold children for k-bindings, evaluate arm
4. Test programs constructed as IR in host language: factorial, list sum, list map, tree sum, tree depth
5. Verify by hand

**Not in scope:** parser, type checker, surface syntax, compilation, optimization, effects, FFI.
