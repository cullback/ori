# Memory Management Pipeline

## Goals

1. **Unboxed when possible.** Small composites (≤8 fields) stay in
   registers as `Agg(n)`. Heap allocation only when a value is stored
   into a collection or escapes through a pointer.

2. **In-place mutation when RC=1, else clone.** When a heap object has
   exactly one owner, reuse its memory for the next allocation of the
   same shape. When shared, clone before mutating.

3. **Static reference counting.** Determine ownership, lifetimes, and
   drop points at compile time. Only fall back to a runtime refcount
   field when aliasing is truly data-dependent — a boxed value stored
   into a list a variable number of times.

## Type-generic design

The analysis operates on Ptr-typed SSA values. It does not know about
lists, tags, or closures — it sees Alloc, Store, Load, and whether
values are Ptr-typed.

Every heap-allocated type follows the same pattern:

```
ptr = Alloc(n)                // or AllocDyn(n)
Store(ptr, 0, field_0)        // each field is Ptr or scalar
Store(ptr, 1, field_1)
...
```

Ownership, reuse, and RC decisions are made per-Store:

- Storing a scalar (U64, I32, etc.) → no memory management concern.
- Storing a Ptr that is Unique and at its last use → ownership
  transfer. No RC needed.
- Storing a Ptr that is Borrowed or still used later → rc_inc.

This applies identically to recursive tags (`Store(node, 1, left)`),
closures (`Store(clos, 1, captured_x)`), and list headers
(`Store(hdr, 2, data_ptr)`).

Drop cascading is also generic: when freeing a Unique object, the
pass needs to know which slots contain Ptrs (to cascade-free or
move-out children). This is derived from the Store patterns — scan
`Alloc(dest, n)` then all `Store(dest, offset, val)` to record each
slot's type. No type metadata needed.

The only pattern that produces data-dependent aliasing is `StoreDyn`
with a loop-varying index — the same Ptr stored into a buffer an
unknown number of times. Today this only comes from list data buffers,
but the analysis doesn't special-case lists. Any `StoreDyn` of a Ptr
in a loop body triggers the same rc_inc fallback.

## System T properties that make this work

- **No self-recursion.** The call graph is a DAG — whole-program
  analysis bottom-up with no approximation.
- **All functions are total.** Every call terminates — no infinite
  loops to reason about.
- **Pure, no side effects.** No hidden mutation or aliasing — every
  use of every value is visible in the SSA.
- **Explicit block params.** Every cross-block value flow goes through
  block params. A value's scope is its defining block — no liveness
  analysis needed.

## Pass ordering

After lowering and general optimization, memory management runs as a
single pipeline. Each pass is listed with its inputs, outputs, and
what it depends on.

```
     ┌─────────────────────┐
     │   lower + optimize   │
     └──────────┬──────────┘
                │
┌───────────────▼──────────────┐
│  1. rc_layout_analysis       │ whole-program
│     which types need RC?     │
└───────────────┬──────────────┘
                │
┌───────────────▼──────────────┐
│  2. ownership_analysis       │ per-function
│     unique/borrowed, reuse   │
│     pairs, rc_inc sites      │
└───────────────┬──────────────┘
                │
┌───────────────▼──────────────┐
│  3. emit_drops               │ per-function
│     insert Free, Drop+Reuse, │
│     move-out, RcInc          │
└───────────────┬──────────────┘
                │
┌───────────────▼──────────────┐
│  4. insert_rc_fallback       │ per-function
│     runtime RC for rc_inc    │
│     sites only               │
└───────────────┬──────────────┘
                │
┌───────────────▼──────────────┐
│  5. elide_static_rc          │ per-function
│  6. fuse_inc_dec             │
│  7. optimize (final)         │
└──────────────────────────────┘
```

### 1. RC layout analysis (whole-program)

**Input:** Entire module after optimization.
**Output:** Which alloc kinds need a runtime RC field.

Scans every function for rc_inc sites (stores of Ptr values where the
store count is data-dependent). Groups by alloc kind — if any value
with `AllocKind::Static(3)` ever gets rc_inc'd, all 3-word
allocations get an RC prefix. Same for `AllocKind::Dynamic`.

| Alloc kind    | Without RC                | With RC                       |
| ------------- | ------------------------- | ----------------------------- |
| `Alloc(n)`    | `{field_0, ..., field_n}` | `{rc, field_0, ..., field_n}` |
| `AllocDyn(n)` | `{slot_0, ..., slot_n}`   | `{rc, slot_0, ..., slot_n}`   |

The RC field goes on the **aliased object**, not the container. In
`List.repeat(n, some_str)`, `some_str` is the value that gains
multiple references, so its alloc kind gets the RC prefix.

The grouping is per alloc-kind (size), not per semantic type. A 3-word
tag and a 3-word list header are the same alloc kind, so if either
needs RC, both get it. In practice this rarely matters — the false
positive costs one word per allocation, and few programs have two
types of the same size where only one gets aliased.

**Why first:** Every subsequent pass needs to know whether an alloc
kind has an RC field, because it affects whether Free cascades,
whether in-place mutation checks a refcount, and what offsets stores
use.

**Status:** `ownership::analyze_module` computes `RcLayout` but the
layout isn't applied to codegen yet.

### 2. Ownership analysis (per-function)

**Input:** One function, plus RC layout from step 1.
**Output:** `Analysis { ownership, alloc_kinds, reuse_pairs, rc_inc_sites }`.

Four phases:

**Phase 2a — Classify ownership.** Every Ptr value is Unique or
Borrowed. Allocs and call results are Unique. Function params and
heap loads are Borrowed. Block params inherit: Unique if all incoming
values are Unique, Borrowed otherwise (fixpoint for loops).

**Phase 2b — Track alloc kinds through phis.** Each Ptr value's alloc
kind (`Static(n)` or `Dynamic`) propagates through block params. If
all incoming edges agree, the param inherits the kind. Conflicting
kinds → unknown. This is what lets us see that a loop accumulator
is always a 3-word list header.

**Phase 2c — Find reuse pairs.** A Unique value dies in its block if
it's not in any successor's args. For each dying Unique with a known
alloc kind, find a compatible Alloc later in the same block. The pair
means: drop the old, reuse its memory for the new.

**Phase 2d — Find rc_inc sites.** A Store of a Ptr into a heap object
needs rc_inc unless it's an ownership transfer (Unique, last use, not
forwarded to a successor). These are the only sites where runtime RC
is needed.

**Why before emit_drops:** The analysis is read-only — it doesn't
modify the SSA. The transformation pass consumes its results.

**Status:** Fully implemented in `ownership.rs`. Analysis only, no
transformation.

### 3. Emit drops and reuse (per-function) — NOT YET IMPLEMENTED

**Input:** Function + ownership Analysis from step 2.
**Output:** Modified SSA with Drop, Free, Reuse, RcInc, and move-out
instructions.

This is the core transformation pass that replaces `insert_rc` for
statically-owned values:

**Unique values that die with a reuse pair:**

```
token = Drop(old_val)       // free header, cascade-free children
new_val = Reuse(token, 3)   // reuse old_val's memory for new alloc
```

Tokens are first-class SSA values. They flow through block params, so
loop accumulators get in-place reuse across iterations.

**Unique values that die without reuse:**

```
Free(old_val)               // free immediately, cascade children
```

**Borrowed values:** No action. The owner will free them.

**rc_inc sites:** Emit `RcInc(val)` before the store. Only at sites
identified by the analysis — not blanket coverage.

**Move-out semantics:** When dropping a Unique parent that contains
Ptr children, each child is either cascade-freed (not live after
the drop) or moved out (still live — ownership transfers to a local
value). The analysis detects this: if a `Load` of a Ptr from a
Unique parent produces a value that's still used after the parent's
last use, that slot is moved out.

```
child = Load(parent, 2)     // child is borrowed from parent
...                          // child still used here
token = Drop(parent)         // parent dropped — but child was loaded
// child is now Unique (parent's reference is gone, child was moved out)
```

Without move-out, the Drop would cascade-free the child while it's
still in use.

**Why this order:** Must run after ownership analysis (needs its
results) and before any RC fallback (which only handles the sites
this pass couldn't resolve statically).

### 4. Insert RC fallback (per-function) — PARTIALLY EXISTS

**Input:** Function after emit_drops, plus list of rc_inc sites from
ownership analysis.
**Output:** SSA with runtime RcInc/RcDec for data-dependent aliasing.

For types whose layout includes an RC field (from step 1), insert
runtime reference counting only at the sites identified by the
ownership analysis. This is a scoped version of today's `insert_rc` —
it doesn't touch values that were handled statically.

The only case: a boxed value stored into a list's data buffer a
data-dependent number of times. The store gets `RcInc`, and when the
list is freed, each element gets `RcDec` (cascade).

Most programs produce zero rc_inc sites, making this pass a no-op.

**Status:** Today's `insert_rc` exists but applies blanket RC to
everything. It needs to be scoped to only the unresolved sites.

### 5–7. Cleanup passes (per-function) — EXIST

**`elide_static_rc`**: Removes RcInc/RcDec on StaticRef values
(compile-time constants with sentinel refcount). Correct and complete.

**`fuse_inc_dec`**: Cancels adjacent RcInc/RcDec pairs within the same
block where the refcount elevation isn't observed between them.
With the ownership-driven pipeline producing fewer RC ops, there are
fewer pairs to fuse.

**`optimize` (final)**: Standard DCE, constant folding, jump threading.
Cleans up dead instructions left by the memory passes.

### Whole-program ownership signatures — NOT YET IMPLEMENTED

Orthogonal to the per-function pipeline. Runs once during
ownership analysis, bottom-up over the call DAG.

For each function, determines whether each Ptr parameter is
**borrowed** (only read) or **consumed** (escapes into the return
value):

```
fn map_inc(input: borrowed ptr) -> ptr
fn repeat(n: u64, val: borrowed ptr) -> ptr
```

At each call site, the caller knows which args it still owns after
the call. Consumed args transfer ownership to the callee, which can
drop/reuse without RC. Borrowed args remain owned by the caller.

Currently all function params are treated as Borrowed (conservative).
Adding consumed params unlocks reuse inside callees without inlining.

### Data buffer reuse — NOT YET IMPLEMENTED

Header reuse (3-word list header → 3-word list header) works today
via Drop+Reuse with matching alloc kinds.

Data buffers are harder: the buffer grows by 1 element each iteration,
so sizes don't match. Two options:

1. **Realloc.** Resize in place when possible, copy when not.
   Amortized O(1) with capacity doubling. The list header already
   stores capacity in slot[1] — we just need to exploit it.

2. **Token with size check.** Reuse if new size ≤ old capacity,
   alloc fresh otherwise. Same amortized cost, more explicit in SSA.

Either way, the key insight: when the old data buffer is Unique and
the new buffer is one element larger, we can grow in place instead of
allocating + copying.

## Worked examples by type

The analysis is type-generic — these examples show that the same
Ptr-based rules handle every heap-allocated type uniformly.

### Recursive tag: `Node(left, right)`

```
left  = call build_left(...)          // Unique (call result)
right = call build_right(...)         // Unique (call result)
node  = Alloc(3)                      // Unique
Store(node, 0, tag)                   // U64 — ignored
Store(node, 1, left)                  // Ptr, Unique, last use → ownership transfer, no RC
Store(node, 2, right)                 // Ptr, Unique, last use → ownership transfer, no RC
```

**Result:** zero RC ops. Both children are consumed by the parent.

What about `Node(x, x)` — same value stored twice?

```
x    = call make_thing(...)           // Unique
node = Alloc(3)
Store(node, 0, tag)
Store(node, 1, x)                    // Ptr, Unique, but NOT last use (x used again below)
Store(node, 2, x)                    // Ptr, Unique, last use
```

The first store is not the last use of `x`, so it's not an ownership
transfer → rc_inc. But this is **statically visible** — we can see at
compile time that `x` is stored exactly twice. The type needs an RC
field, but the count is known: emit one `RcInc(x)` at the first store.

### Closure capturing two values

```
clos = Alloc(3)
Store(clos, 0, code_ptr)             // Ptr (function pointer), Unique, last use → transfer
Store(clos, 1, captured_x)           // Ptr, depends on ownership of captured_x
Store(clos, 2, captured_y)           // Ptr, depends on ownership of captured_y
```

If `captured_x` is a function parameter (Borrowed), storing it needs
rc_inc — the closure is keeping a reference the caller doesn't know
about. If `captured_x` is a local Unique value at its last use, it's
an ownership transfer — no RC.

Same rules, same analysis. No closure-specific logic.

### List header

```
hdr = Alloc(3)
Store(hdr, 0, len)                   // U64 — ignored
Store(hdr, 1, cap)                   // U64 — ignored
Store(hdr, 2, data_ptr)             // Ptr, Unique, last use → ownership transfer
```

**Result:** zero RC ops. The data buffer is consumed by the header.

### List data buffer — the one special case

```
data = AllocDyn(n)
// in a loop body:
  StoreDyn(data, i, elem)            // Ptr, dynamic index
```

`StoreDyn` with a loop-varying index means the same `elem` could be
stored 0 times, 1 time, or N times depending on runtime data. The
analysis can't count the stores statically → rc_inc.

This is the **only** pattern that triggers runtime RC. It's not
special-cased for lists — any `StoreDyn` of a Ptr in a loop body
triggers the same fallback. Lists just happen to be the only type
with variable arity.

### List.map with scalar elements — no RC at all

```
// map(+1) over List(I32)
b_body(i, acc, len, data):
  elem = LoadDyn(data, i)            // I32 — not Ptr, ignored
  mapped = Add(elem, 1)              // I32
  ...
  StoreDyn(new_data, old_len, mapped) // I32 — not Ptr, ignored
  new_acc = Alloc(3)
  ...
  jump b_header(i+1, new_acc, len, data)
```

No Ptr stored into the data buffer → zero RC ops, zero rc_inc sites.
The accumulator header gets in-place reuse (Unique, same alloc kind).

### List.repeat(n, boxed_val) — the RC fallback

```
b_body(i, acc):
  ...
  StoreDyn(new_data, old_len, val)   // Ptr, Borrowed (func param), in loop
  ...
```

`val` is Borrowed (function parameter) and stored into a dynamically-
indexed buffer in a loop body. rc_inc on every iteration. This is the
one case where the runtime refcount field is needed.

## When runtime RC is needed — summary

The analysis flags rc_inc at any `Store`/`StoreDyn` of a Ptr where
the stored value is not an ownership transfer (Unique at last use).
In practice, the cases that survive are:

| Pattern                                            | Static or runtime?       | Why                                 |
| -------------------------------------------------- | ------------------------ | ----------------------------------- |
| `Store(ptr, fixed_offset, unique_val)` at last use | Static (transfer)        | One owner, known at compile time    |
| `Store(ptr, fixed_offset, borrowed_val)`           | Static (rc_inc, counted) | Fixed offset, count visible in SSA  |
| `Store(ptr, fixed_offset, val)` used again later   | Static (rc_inc, counted) | Fixed offset, count visible in SSA  |
| `StoreDyn(ptr, loop_idx, ptr_val)` in loop body    | **Runtime RC**           | Store count depends on runtime data |

Only the last row needs a runtime refcount field in the type's layout.
Everything else is resolved statically.
