# Tooling

Ori ships two binaries: `ori` for running, building, and testing, and `ori-lsp` for editor integration. Both link the same compiler library, so information shown at edit time matches what the compiler uses at build time.

## CLI

One binary, one entry point, subcommands for everything. Modeled loosely on `cargo` but without the build-tool/compiler split — there is no separate `oric` that editors bypass.

### `ori run`

Compile and execute. The entry point is `main!` in the file argument, or the project's default binary if no argument is given.

```
ori run              # run the project's default binary
ori run script.rb    # run a single file as a script
ori run -- --flag    # forward arguments to the program
```

Single-file scripts compile to a cached temporary location — no project setup required. Projects with an `app { }` header read their platform and dependencies from the header and link accordingly. Build artifacts are cached, so re-running a program without changes is near-instant.

### `ori build`

Produce an executable or library artifact without running it.

```
ori build              # debug build (default)
ori build --release    # full optimization pipeline
```

Debug builds prioritize compile time: minimal inlining, debug info, arithmetic overflow checks. Release builds run monomorphization, fusion, Perceus, defunctionalization, and the SSA optimization pipeline. Overflow panics in debug and wraps in release — see [operators](operators.md).

### `ori test`

Run `expect` tests across the project.

```
ori test                    # run all tests
ori test --filter parse     # run only tests whose enclosing definition matches
ori test path/to/file.rb    # run tests in one file
```

`expect` tests are compiler-integrated, live inline with the code they cover, and strip from release builds. Top-level `expect` runs here. Inline `expect` inside function bodies runs via `ori dev` against real execution. Doc tests (code blocks in doc comments) run alongside — see [comments](comments.md#doc-tests).

Failure output prints every intermediate binding in the failing expression, not just the final comparison. No assertion library to pick or configure.

### `ori dev`

Run the program with inline `expect` checks enabled.

```
ori dev              # run with inline checks active
ori dev --watch      # re-run on file changes
```

Inline checks are real code paths during `dev`, not compiled-out asserts. `ori build --release` strips them entirely.

### `ori check`

Type-check the project without producing output. Used by editors for live diagnostics and by CI for pre-build gating.

```
ori check            # type-check everything
ori check file.rb    # type-check one file and its dependencies
```

### `ori fmt`

Format source files. Deterministic — no config, no options, no rule selection. One canonical format.

```
ori fmt              # format all files in the project
ori fmt --check      # exit nonzero if any file isn't formatted
```

### `ori new` and `ori init`

Scaffold a new project. `new` creates a directory; `init` uses the current directory.

```
ori new hello            # create hello/ with a default app
ori init                 # initialize in the current directory
ori new --lib my-lib     # scaffold a library instead
```

A new project gets an `app.rb` or `lib.rb` with sensible defaults and one example source file. No build script, no separate config file, no lockfile — the header block at the top of `app.rb` is the entire project configuration. See [modules](modules.md#app-header).

### `ori docs`

Generate API documentation from doc comments. Doc tests are verified before shipping — a broken example in a doc block is a compile error, not a warning.

```
ori docs             # generate into target/docs/
ori docs --open      # generate and open in browser
```

## Language server

`ori-lsp` implements the Language Server Protocol for editors: hover, go-to-definition, find-references, completions, rename, code actions, live diagnostics. Standard LSP surface — the interesting part is the information exposed on hover, most of which other languages don't compute at all.

### Hover

Hovering over a binding shows its type and doc comment, and a set of **analysis annotations** drawn from the compiler's own passes.

**Type and documentation.** Standard LSP fare — inferred type and the definition's doc comment.

**Reference count behavior.** For any binding, shows whether Perceus inserts `dup` or `drop` operations around it, and at which call sites the compiler proves uniqueness is preserved:

```
tokens : List(Token)

Perceus analysis:
- Line 42: unique, consumed by parse_header
- Line 45: shared, dup inserted before the second use
- Drop inserted at line 48 (end of scope)
```

This surfaces information the compiler already computes during Perceus insertion but hides by default. An unexpected `dup` usually means you can restructure to eliminate it — seeing it inline makes that optimization an edit-time activity, not a profiler round-trip.

**Recursion shape and stack behavior.** For any function, shows how its recursion compiles. Pure Ori has no general recursion — `fold` is the only recursion primitive, and folds compile to loops rather than stack-growing calls. The hover surfaces which loop shape a `fold` turns into:

```
tree_sum : Tree(I64) -> I64

Recursion: fold over Tree
Compiles to: parallel divide-and-conquer (independent branches)
Stack growth: none (iteration, not recursion)
```

```
list_walk : List(a), s, (s, a -> s) -> s

Recursion: fold over List
Compiles to: while loop with accumulator in register
Stack growth: none (tail position of fold body hoisted)
```

This is the Ori equivalent of "is this function tail recursive?" from languages that expose TCO. In Ori the answer is always yes for pure code (fold never grows the stack), but the specific loop shape matters for understanding performance, and the hover shows it.

**Fusion analysis.** At a pipeline of fold-based operations, shows whether intermediate collections get materialized or fused into a single pass:

```
xs.map(f).keep_if(g).walk(init, h)

Fusion:
- map → keep_if: fused
- keep_if → walk: fused
- Result: single pass, 0 intermediate allocations
```

If fusion is blocked (for example by a `?` escape inside a closure), the hover explains why.

**Lambda set resolution.** For a higher-order call, shows the set of concrete closures that can reach that call site after defunctionalization:

```
items.walk(0, step)

Lambda set at call site:
- closure_at_line_40
- closure_at_line_47
Dispatch: tagged switch (2 variants, direct calls)
```

This tells you whether an indirect call went through a vtable at runtime or got resolved to a specific function by the defunctionalizer.

**Specialization info.** For any generic function, shows which monomorphized specializations the compiler generates, and their code size. Useful for diagnosing code-size blowup from over-specialization.

**Heap allocations.** Inline hints mark lines that allocate on the heap. Ori is stack-by-default, so heap allocations are relatively rare and worth flagging — especially inside tight loops where an unexpected allocation usually means an optimization opportunity.

### Diagnostics, completions, navigation

Diagnostics use the same error messages as `ori check`. Type errors, shadowing attempts (all shadowing is an error), and exhaustiveness failures appear as you type.

Completions are type-directed: at a dot-dispatch site, only methods available on the receiver's type are suggested. No global fuzzy-match across everything in scope.

Find-references and rename are cheap because the call graph is a DAG and monomorphized. Every reference is direct — no virtual dispatch to chase, no dynamic overloading to disambiguate.

## Design rationale

> Why one CLI binary instead of separate compiler and build tool?

The `rustc` / `cargo` split is a legacy of an era when compilers were slow enough that you'd call them directly from hand-written makefiles. Modern compilers are fast enough that the build tool always calls the compiler, and Ori's project model is simple enough that cargo-level complexity isn't needed. One binary means one version number, one doc site, one place to look when something breaks. `rustc` alone is almost never useful; `ori` with no build-tool component would be the same. Bundle them.

> Why no formatter configuration?

Formatter config is pure bikeshedding overhead. Every project debates tab width, line length, trailing comma style, and the debates produce zero value. Pick one format, ship it, move on — `gofmt` validated this approach years ago. The bikeshedding surface area isn't worth the perceived flexibility.

> Why surface Perceus and fusion info in hover?

Most languages hide the optimizer from the programmer. You write code, you benchmark, you read generated assembly, you tweak, you re-run. This cycle is slow and requires learning your compiler's output format to debug performance.

Ori's optimizer is structured enough that the relevant information — is this value shared, does this pipeline fuse, is this call directly dispatched — can be computed at analysis time and shown inline. Making it visible in hover turns performance work into an edit-time activity.

This is tractable specifically because Ori's call graph is a DAG and analyses are single-pass. The LSP can afford to run the same passes the compiler runs, on every keystroke, and surface the results at hover speed. In a language with cyclic call graphs and fixed-point iteration, this wouldn't fit in the editor response budget.

> Why no built-in debugger?

Debuggers fit uncomfortably with pure functional code. Stepping through immutable, referentially transparent functions gives you less information than `expect` tests that print intermediate bindings or `dbg` printf-style debugging. The `dbg` builtin prints a value plus its source location without any type constraints, covering most of what step-through debugging provides.

For effectful code where a debugger genuinely helps, Ori compiles to standard native code with DWARF debug info, so `lldb`, `gdb`, and IDE debuggers all work on the compiled binary.

> Why `ori dev` separate from `ori run`?

`ori run` produces the same code `ori build` produces, so it's safe to use for iterative testing of production-shaped performance. `ori dev` enables inline `expect` checks, which add overhead and shouldn't be present in benchmark runs. Keeping the modes distinct makes it clear which one you're in.
