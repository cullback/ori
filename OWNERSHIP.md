# Static Ownership Analysis

Static ownership analysis handles the common case (>95% of pointer
operations) at compile time with zero runtime cost. For the one case
where aliasing is data-dependent — a boxed value stored into a list a
variable number of times — we fall back to Perceus-style runtime
reference counting.

## Why the current approach falls short

The existing pipeline: `insert_rc` adds `RcInc`/`RcDec` everywhere,
then `insert_reuse` tries to pair `RcDec` + `Alloc` into
`Reset`/`Reuse` (check RC=1 at runtime, reuse allocation if unique).

`insert_reuse` only pairs within a single basic block, and only when
the dec'd value was the direct result of an `Alloc` instruction. This
fails for the most important case: **loop-carried accumulators**, where
the value flows through block parameters (phis) and loses provenance.

Example: `list.map(f)` lowers to a loop that appends to an accumulator
each iteration. The accumulator is a block param, not an alloc result,
so `insert_reuse` never fires. The result is O(n) copy-on-every-append
with no reuse.

## Key insight: System T gives us everything

Ori is based on Godel's System T:
- **No self-recursion.** The call graph is a DAG.
- **All functions are total.** Every call terminates.
- **Pure, no side effects.** No hidden mutation or aliasing.

This means we have **complete static visibility** into every function's
behavior. We can analyze the whole program bottom-up (topo-sort the
call DAG) and determine, for each function parameter, whether it's
consumed (escapes into the return value) or borrowed (only read from).
No fixed-point iteration, no approximation.

In SSA form, every use of every value is visible. We always know
statically *when* a value's lifetime ends (its last use). And in pure
functional code, most values flow linearly — each intermediate result
is consumed exactly once.

## Ownership model

Every `Ptr`-typed SSA value has one of two ownership statuses:

- **Unique**: exactly one reference exists. The value can be dropped at
  its last use, producing a reuse token for a subsequent allocation.
- **Borrowed**: a reference into a living object. Someone else owns the
  underlying memory. Do not free.

Classification rules:

| Definition site            | Ownership |
|---------------------------|-----------|
| `Alloc` / `AllocDyn`     | Unique    |
| Function parameter        | Borrowed  |
| `Load` of Ptr from heap  | Borrowed  |
| `Call` result (Ptr)       | Unique    |
| Block param (phi)         | Unique if **all** incoming values are Unique; Borrowed otherwise |

## Reuse tokens

When a Unique value reaches its last use, we emit a **drop** that
produces a reuse token. The token is a first-class SSA value that
carries the allocation's memory. A subsequent `Alloc` can consume the
token: if the sizes are compatible, it reuses the memory; otherwise it
frees the old and allocates fresh.

Because tokens are SSA values, they flow through block params
naturally. This solves the cross-block problem that `insert_reuse`
can't handle.

### Example: list-map accumulator

```
b_loop(i: u64, acc: ptr):        // acc is Unique (all incoming are alloc 3)
  done = eq i, len
  branch done ? b_exit(acc) : b_body

b_body:
  old_len = load acc[0]
  old_data = load acc[2]          // borrowed from acc
  token_hdr = drop_unique acc     // free header, move out slot[2]
  ...
  new_acc = reuse token_hdr, 3    // reuse acc's 3-word header
  ...
  jump b_loop(i+1, new_acc)
```

The token threads through the loop: each iteration drops the old
accumulator header and reuses it for the new one. Zero allocation
per iteration for the header.

## Move-out semantics

When dropping a Unique object that contains Ptr-typed slots, we need
to decide what happens to each child pointer:

- **Cascade-free**: decrement the child (recursive free if RC hits 0).
  Used when the child is not needed after the parent is dropped.
- **Move-out**: transfer ownership of the child to a local variable.
  Used when the child is still live after the parent's drop point.

The analysis detects move-out automatically: if a `Load` of a Ptr
from a Unique parent produces a value that's still live when the
parent is dropped, that slot is moved out rather than cascade-freed.

After move-out, the child becomes Unique (sole owner, since the
parent's reference is gone).

## Alloc kind tracking through phis

To pair drops with compatible allocs, we need to know each value's
allocation size. For values defined by `Alloc(n)`, the kind is
`Static(n)`. For `AllocDyn`, it's `Dynamic`.

Block params inherit their alloc kind from incoming values. If all
incoming values have the same kind (e.g., all are `Static(3)`), the
param has that kind. If kinds conflict, the param's kind is unknown
and can't participate in same-size reuse.

## The three boxed types

Ori has three kinds of heap-allocated values:

| Type           | Arity          | Aliasing pattern        |
|---------------|----------------|------------------------|
| Lists          | Variable (N elements) | Same element stored N times in a loop |
| Recursive tags | Fixed per variant     | `Node(x, x)` — always statically visible |
| Closures       | Fixed captures        | Each capture is a distinct variable |

**Only lists create data-dependent aliasing.** Tags and closures have
fixed arity, so any aliasing is visible in the SSA and countable at
compile time.

## When runtime RC is actually needed

Almost never. The one genuine case:

> A boxed value stored as an element of a list, a data-dependent
> number of times.

Concrete examples:
- `List.repeat(n, some_str)` — same string stored N times
- `xs.walk([], |acc, _| acc.append(captured))` — captured value
  appended on each iteration

In these cases, the element's reference count depends on runtime data
(the list length or how many times a condition is true). We can't
resolve it at compile time.

**Any boxed type** (list, tag, closure) can be the target of this
aliasing — it just needs to be a list element. So all heap objects
retain an RC field, but it's only ever dynamically incremented at one
site: **storing a boxed element into a list's data buffer.**

Everything else — tag construction, closure capture, value passing,
loop accumulators — is handled by static ownership.

## Heap object layout: conditional RC field

Every heap object has the same base layout for its type. Whether the
layout includes an RC field is a **per-type, compile-time decision**
made by whole-program analysis.

The analysis scans all rc_inc sites in the program. If a concrete
type (e.g., `Str`, `List(I32)`, `Tree`) ever appears at a
data-dependent store site, its layout gets an RC prefix:

| Needs RC? | List layout              | Tag layout (Node)           |
|-----------|-------------------------|-----------------------------|
| No        | `{len, cap, data}`      | `{tag, left, right}`        |
| Yes       | `{rc, len, cap, data}`  | `{rc, tag, left, right}`    |

After monomorphization, every function knows the concrete layout of
each type it operates on. Field offsets are baked into the generated
code — `len` is at offset 0 or 1 depending on whether RC is present.
No runtime branching, no wasted space on types that don't need RC.

Example: if `Str` is only ever used in `map`/`filter` chains where
each string is unique, Str's layout is `{len, cap, data}` — three
words, no RC overhead. If somewhere in the program `List.repeat(n,
some_str)` appears, Str's layout becomes `{rc, len, cap, data}` for
the entire program.

## Whole-program ownership signatures

Since the call graph is a DAG, we can compute each function's ownership
signature bottom-up:

```
fn foo(a: borrowed ptr, b: consumed ptr) -> ptr
```

- **Borrowed**: the function only reads from this parameter. Caller
  retains ownership.
- **Consumed**: the parameter (or data derived from it) appears in the
  return value. Ownership transfers to the callee.

At each call site, the caller knows exactly which arguments are
borrowed (still owned after the call) and which are consumed (ownership
transferred). No need to inline — the signature tells you everything.

For builtins (which can't be analyzed), we annotate ownership by hand.

## Data buffer reuse (future work)

The header reuse (e.g., 3-word list header) is straightforward: drop
produces a token, alloc consumes it, same size.

The data buffer is harder because sizes differ across iterations
(growing by 1 each time). Options:

1. **Realloc**: resize in place if possible, copy if not. Amortized
   O(1) with capacity doubling.
2. **Token with size check**: reuse if new size <= old capacity, alloc
   fresh otherwise.

The current SSA stores capacity in the list header (slot[1]) but
never exploits it. A realloc-based approach would use capacity for
amortized growth.

## Implementation plan

1. `src/ssa/ownership.rs` — the analysis pass, tested on hand-built
   SSA modules.
2. Start with the easy win: header reuse for loop accumulators (token
   through phis).
3. Add move-out detection for Ptr children of dropped Unique objects.
4. Add data buffer reuse (realloc or token-based).
5. Integrate into the main pipeline, replacing `insert_rc` +
   `insert_reuse` for the static cases.
6. Keep RC as a fallback for the list-element-store edge case.
