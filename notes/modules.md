# Modules

Every file is a module. Modules contain types, functions, and constants. Visibility is controlled by `exports` — names not exported are private.

## Module resolution

All imports resolve from the enclosing root — the project root by default, or the root directory of a [`lib { }`](#lib-header) boundary. A module is either a single file or a directory with a self-named entry file:

```
import foo          → foo.rb           (single-file module)
import foo          → foo/foo.rb       (directory module)
import foo.bar      → foo/bar.rb       (sub-module)
import foo.bar.baz  → foo/bar/baz.rb   (nested sub-module)
```

This applies uniformly — a module inside `foo/` imports siblings as `import foo.helper`, not `import ./helper`. Every import is an absolute path from the enclosing root.

Having both `foo.rb` and `foo/` is a compile error — a module is one or the other. Similarly, a local module with the same name as a package in the `app` or `lib` header is a compile error — rename one or use `as` to alias the import.

Promoting a single-file module to a directory is a mechanical refactor: `mkdir foo && mv foo.rb foo/foo.rb`. All import sites stay the same.

Inside a [`lib { }`](#lib-header) boundary, the root resets to the lib's directory. A module inside `json/` (where `json/json.rb` has a `lib { }` header) writes `import decode` to import `json/decode.rb` — it doesn't know or care where it sits in the project tree. This makes libraries portable: internal imports are identical whether the library is in a standalone repo, downloaded to a cache, or vendored into any directory.

> Why file = module with no wiring?

In Rust, a file isn't part of your program until the parent module declares `mod foo;`. Forgetting this means orphan files that silently compile to nothing — matklad documented this as a common source of confusion. Go, Zig, OCaml, Erlang, and Haskell all use file = module with no declarations, and this predictability is consistently praised. Ori follows the same model: if a file exists, it's a module.

> Why `foo/foo.rb` instead of `foo/mod.rb` or `foo/index.rb`?

`mod.rb` and `index.rb` are indistinguishable in editor tabs — every tab says the same thing. `foo/foo.rb` shows `foo.rb` in the tab, which tells you what it is. Rust moved away from `mod.rs` for exactly this reason.

> Why root-relative instead of relative imports?

Relative imports (`./`, `../`) create two mental models for the same operation and degrade as projects grow — `../../../Shared/Utils` is a code smell in every language that allows it. The JavaScript ecosystem proved this out: developers hated relative imports enough to build tooling (`@/` path aliases) that simulates absolute imports. Python's PEP 8 explicitly recommends absolute imports over relative.

Root-relative imports are statically determinable — the import path tells you exactly where the file is. They're greppable, predictable, and there's only one way to import anything.

The tradeoff: renaming a directory requires updating imports inside it (`import foo.helper` → `import bar.helper`). But this is a mechanical find-and-replace, the compiler catches every miss, and it happens rarely compared to how often you read and write imports.

## Exports

`exports` at the top of a module lists everything that's public. Names not in `exports` are private:

```ruby
# math.rb
exports [clamp, lerp, pi]

pi = 3.14159265358979
clamp = |val, lo, hi| val.max(lo).min(hi)
lerp = |a, b, t| a + (b - a) * t
deg_to_rad = |d| d * pi / 180.0   # not exported, private
```

For type-centered modules, exporting a type exports its methods with it:

```ruby
# dict.rb
exports [Dict]

Dict(key, val) := [...].(
    get : Dict(key, val), key -> Result(val, [NotFound])
    insert : Dict(key, val), key, val -> Dict(key, val)
)

# Internal helpers — not in exports, not reachable from outside
index_at = |h, depth| ...
```

Mixed exports — types, free functions, and constants:

```ruby
# http.rb
exports [Request, Response, get!, post!, default_timeout]

default_timeout = 30_000

Request :: { method: Str, url: Str, headers: List((Str, Str)), body: List(U8) }.(...)
Response :: { status: U16, headers: List((Str, Str)), body: List(U8) }.(...)

get! = |url| send!(Request.new("GET", url))
post! = |url, body| send!(Request.new("POST", url).with_body(body))
send! = |req| ...  # not exported
```

A module without `exports` is fully private — only usable by sibling modules within the same directory.

> Why `exports` instead of `pub` on each declaration?

An explicit export list at the top of the file means you see the public API immediately without scanning the entire file. This gives the benefit of Haskell's module export lists and OCaml's `.mli` signature files without a separate file to maintain. The tradeoff (Haskell's pain point) is that adding a public name requires updating the list — but in practice this is low-friction since it's a single line at the top of the file, not a separate manifest.

Aaron Turon's 2017 survey of top Rust crates found that `pub` alone doesn't tell the full visibility story — understanding actual visibility requires tracing all `pub use` re-exports across the module tree. With `exports`, what you see at the top of the file is the complete truth. It also keeps imports and re-exports as distinct operations: `import` brings names in for internal use, `exports` controls what goes out. Rust conflates these with `pub use`.

> Why does exporting a type export all its methods?

A type's methods are its interface — exporting the type without them would leave callers with a value they can't use. Listing methods individually in `exports` would be redundant and error-prone. `exports` controls what leaves the module (types, free functions, constants); methods travel with their type. Private helpers are free functions in the module, not methods on the type.

## Imports

```ruby
import json.decode                         # from named package
import my_module                           # local module (from project root)
import foo.helper                          # sub-module (foo/helper.rb)
import json.decode as json_decode          # renaming
import dict exposing [Dict]                # bring type into scope
import math exposing [clamp, pi]           # bring free functions into scope
import "schema.json" as schema : Str       # file embedding (compile-time)
import "logo.png" as logo : List(U8)
```

All imports resolve from the enclosing root — there are no relative imports. Platform modules are auto-imported. File embedding bakes file contents into the binary as `Str` or `List(U8)`.

Imports are qualified by default — `import dict` gives you `dict.Dict` for types, `dict.Dict.get(d, k)` for methods, and `dict.some_helper()` for free functions. Use `exposing` to bring types and free functions into bare scope:

```ruby
import dict exposing [Dict]

d = Dict.empty()              # instead of dict.Dict.empty()
Dict.insert(d, "key", 42)     # methods always through the type
```

`exposing` doesn't pull out methods — they're always accessed through their type name. This matches Erlang's always-qualify model (`Module:function()`), which generates near-zero complaints in practice.

> Why no wildcard imports?

`exposing` requires listing each name explicitly — there is no `exposing [*]`. Wildcard imports hide dependencies, break when upstream adds names, and prevent parallel name resolution across modules. Every major style guide (Python PEP 8, Google Java, ESLint) discourages them. If a feature exists but the universal recommendation is to never use it, it shouldn't be in the language.

> Why are imports side-effect-free?

In Python, Ruby, JavaScript, and Go, importing a module executes code — creating invisible ordering dependencies and slowing startup. Go's `init()` pattern means a program's behavior depends on which init functions ran, in an order determined by the import graph. In Ori, imports are purely declarative. Pure functional semantics make this automatic — there's no top-level code to execute.

## App and lib headers

There are two kinds of dependency headers: `app` for entry points and `lib` for libraries.

### App header

The `app` header selects a platform and maps short names to package sources. A module with `app` must define `main` — it's an entry point. Dep mappings are project-scoped — available to every module in the project.

A file without any header is a pure stdin/stdout filter:

```ruby
main = |input, _args| (
    lines = input.split_on("\n")
    Ok("${lines.len()} lines")
)
```

```ruby
main : Str, List(Str) -> Result(Str, Str)
```

- `Str` — stdin, read in full
- `List(Str)` — command-line args (lossy UTF-8)
- `Ok(str)` → stdout, exit 0; `Err(str)` → stderr, exit 1

No effects, no dependencies — a pure function. Single-file scripts work without any project folder or configuration.

When you need effects, add an `app` header with a `platform` key:

```ruby
app {
    platform: "https://github.com/ori-lang/basic-cli/v0.1.0/BLAKE3HASH.tar.br"
}

main! = || (
    Stdout.line!("hello")
)
```

When you need third-party packages, add them to the same header:

```ruby
app {
    platform: "https://github.com/ori-lang/basic-cli/v0.1.0/BLAKE3HASH.tar.br"
    json: "https://github.com/user/json/v1.0.0/BLAKE3HASH.tar.br"
}

import json.decode

main! = || (
    content = File.read!("data.json")?
    data = decode.from_str(content)?
    Stdout.line!("loaded ${data.name}")
)
```

The `platform` key identifies which package provides the runtime. Platform modules are auto-imported since there's exactly one platform per app.

### Lib header

The `lib` header declares dependencies for a library. A `lib { }` creates a **hermetic boundary**:

1. **Root reset** — imports inside the lib resolve from the lib's directory, not the project root
2. **Dep isolation** — only deps declared in the `lib { }` are visible; app-level deps are not accessible (compile error)

```ruby
# json/json.rb
lib {
    utf8: "https://github.com/user/utf8/v1.0.0/BLAKE3HASH.tar.br"
}

exports [decode, encode]

import decode
import encode
```

Inside `json/` and its sub-modules, `import utf8.parser` resolves via the lib mapping and `import decode` resolves to `json/decode.rb`. Outside `json/`, neither `utf8` nor the lib's internal modules are reachable through the lib mapping.

If a module inside `json/` tries to use an app-level dep that isn't declared in the `lib { }`, the compiler rejects it — the lib is hermetic. You can look at a `lib { }` block and know *exactly* what the library depends on, with no hidden coupling to the parent project.

There is no conceptual difference between "a library I downloaded" and "a directory in my project that has its own deps." A published package is just a directory module with a `lib { }` header. The mental model:

- **No header** — regular module, resolves from project root, uses app deps
- **`app { }`** — entry point, sets the project root, project-scoped deps
- **`lib { }`** — hermetic boundary, resets the root, isolated deps

### Packages

A package is a directory module whose root re-exports what should be public. Sub-modules have their own `exports`. The root module controls the package's public surface by choosing what to re-export. Internal helper modules either don't have `exports` or aren't re-exported by the root — either way, external consumers can't reach them.

No separate package manifest needed — `lib { }` declares deps, `exports` defines the API.

### Vendoring

To vendor a dependency — bringing it into your repo to manage yourself:

1. Copy the package folder into your project (e.g., `libs/json/`)
2. Remove `json` from your `app { }` header
3. Update import sites: `import json.decode` → `import libs.json.decode`

Nothing inside the vendored library changes — because its imports resolve from its own `lib { }` root, internal imports are identical regardless of where the library sits in the tree. The library's `lib { }` block travels with the code, so its own dependencies still resolve. You don't need to merge transitive deps into your `app { }`.

### Diamond dependencies

If two libraries depend on different versions of the same package, each has its own `lib { }` with its own hermetic copy. Hermetic scoping is what makes this possible — the two versions live in isolated namespaces with no way to collide.

Most ecosystems that technically support diamond deps still break in practice. Node's `instanceof` fails across diamonds because the constructor objects differ — two copies of the same class are distinct at runtime. Java's classloader conflicts arise for the same reason. Go's `init()` functions execute once per import, but two copies of the same package run `init()` twice with unpredictable ordering. Python's import system caches by module name, so diamond deps silently share a single copy (breaking if the versions differ). Several Ori properties eliminate these failure modes:

- **No global state** — two versions can't step on each other's singletons or shared mutable caches
- **No import side effects** — loading both versions doesn't trigger conflicting initialization
- **Monomorphization** — no runtime type identity to get confused; everything compiles to concrete code with no runtime type system to conflict
- **Structural equality** — values are compared by structure, not identity, so structurally identical values from different versions are equal

The cost is binary size, which is a reasonable tradeoff for correctness.

### Managing dependencies

```bash
ori add json 1.0.0          # fetches, hashes, writes app/lib { } entry
ori update json              # bumps to latest patch (default)
ori update json --minor      # bumps to latest minor
ori update json --major      # bumps to latest major
ori update                   # updates all deps (patch only by default)
```

Or just paste a URL from docs or a README — the hash is in the URL, so copy-paste is safe.

### Supply chain security

Package URLs embed a BLAKE3 hash — the compiler verifies downloads against it, rejecting tampered or corrupted content. Once verified, packages are cached locally and never re-fetched. The `app { }` and `lib { }` blocks *are* the lockfile — no separate `package-lock.json`, `go.sum`, or `Cargo.lock` needed.

The hash is computed from the package content at the time you `add` or `update`. If someone compromises a server and swaps the tarball — or force-pushes a git tag, or replaces a release artifact — the hash won't match and the compiler rejects it. The source of truth and the verification are the same artifact.

Most ecosystems split this across two files: npm has `package.json` (intent) + `package-lock.json` (verification), Go has `go.mod` + `go.sum`, Cargo has `Cargo.toml` + `Cargo.lock`. The lock file can drift, be forgotten, or be skipped. In Ori, there's nothing to skip — the hash is in the URL that humans see and commit.

Ori's model is content-addressed at the package level — a dependency is identified by its content hash, not by a name, version number, or hosting location. This aligns with the Nix/Guix insight that version numbers are a legacy approximation of content identity from the era of floppy disks and CD-ROMs. The hash *is* the version — two packages with the same hash are the same artifact, regardless of what URL they were fetched from or what version string the author assigned.

> Why `app` and `lib` instead of one header?

`app` is an entry point — it has a platform, a `main`, and project-scoped deps. `lib` is a hermetic boundary — no platform, no `main`, isolated deps, and a reset import root. The separation makes libraries genuinely portable: a lib carries its deps with it and doesn't depend on what the parent project provides.

> Why are libs hermetic?

If a lib could silently use app-level deps, it would "work" in your project but break when extracted, vendored, or used in another project that doesn't have those deps. Hermetic scoping catches missing declarations at the point of authoring, not extraction. It also eliminates an entire class of "works on my machine" bugs — if it compiles, the lib is self-contained.

> Why reset the import root?

Without root reset, a library's internal imports encode its location in the project tree (`import libs.json.decode`). Moving or vendoring the library requires rewriting every internal import. With root reset, internal imports are location-independent (`import decode`) — the library is identical whether it's in a standalone repo, downloaded to a cache, or vendored into any directory. This is what makes vendoring zero-edit for the vendored code.

> Why no dependency resolution?

Dependency resolution is NP-complete when packages specify version ranges — ecosystems like npm, Cargo, and pub use SAT solvers to find compatible version assignments, with backtracking, failure modes, and resolution algorithms that users can't predict. Ori sidesteps this entirely. Every dependency is a URL+hash — an exact artifact, not a range. `ori add` resolves the version once at add time and writes the pinned result. After that, builds just fetch known artifacts. No solver, no backtracking, no resolution phase.

The `ori update` command is where version logic lives, but it's a human-initiated action that rewrites the header — not an implicit resolution step during builds. Diamond dependencies don't need resolution either — each lib is hermetic with its own copy. There's no global dependency graph to solve.

> Why no lockfile?

The `app { }` and `lib { }` blocks already pin exact content via hashes. A lockfile would be redundant — it would contain the same information in a less readable format. Eliminating it also removes the most common source of merge conflicts in collaborative projects and means new clones build immediately with no `install` step.

> Why `app { }` instead of URL imports?

Dependency declarations are project configuration, not module code. A URL doesn't behave like a regular import — it triggers network fetches, has versioning semantics, and needs hash verification. Putting this in a dedicated header keeps module code clean (`import json.decode`, not `import "https://...".decode`) and centralizes the project's external surface in one place.

Go ties package identity to DNS — `import "github.com/user/repo"` means losing your domain means losing your package, and moving hosting requires every downstream project to update every import statement. Ori decouples identity from hosting: import sites use short names (`import json.decode`), and the `app { }` header maps names to URLs in one place. Swapping a package URL or moving hosts updates one line in the header, not every file that imports from it.

Deno tried URL-based imports (`import { serve } from "https://deno.land/std/http/server.ts"`) and retreated — long URLs cluttered code, version conflicts emerged, and server reliability became a dependency. They converged on import maps (centralized name→URL mappings), which is essentially what `app { }` provides from the start.

> Why not a separate deps file?

A single-file script should work without a project folder. Putting deps in a separate manifest means even trivial programs need two files and a directory. The `app { }` header keeps everything in one file — platform, deps, and code. For larger projects the header is still just a few lines at the top of the entry module.

> Why no package registry?

Centralized registries (npm, crates.io, PyPI) are a single point of compromise — an attacker who breaches the registry can replace any package. They also create a naming authority: name-squatting, typosquatting (`lodsah` instead of `lodash`), and namespace disputes are inherent to any system where a central authority assigns globally unique names. Registry downtime blocks builds for every project that depends on it.

Ori's URL+hash model is decentralized — packages can be hosted anywhere (GitHub, GitLab, S3, corporate servers, a personal domain). The hash verifies integrity regardless of the host. Private packages work naturally: point the URL at an internal server, no separate registry tooling needed. There's no naming authority to game because package names are project-local — the `app { }` header maps whatever short name you choose to a URL.

The tradeoff is discovery — there's no central place to browse and search packages. But discovery is a documentation and website problem, not a compiler problem. A curated package index (like Elm's or Haskell's Hackage) can exist as a web service without the compiler depending on it at build time.

## Platform header

A platform declares its expected entry point and provided modules:

```ruby
platform {
    entry: main! : List(Str) => Result((), e) where [e.ToStr]
    provides: [Stdout, Stdin, File, Process, Task]
}
```

Platform functions are declared in Ori (types only) and implemented in the host language. The entry type uses an open error union — `?` inside `main!` unifies errors automatically, and the platform prints unhandled errors via `ToStr`. Different platforms for different domains:

```ruby
entry: main! : List(Str) => Result((), e) where [e.ToStr]   # CLI tool
entry: handle! : Request => Response                          # web server
entry: pages : List(Page)                                     # static site generator
```

## Type-centered modules

The common pattern: a module organized around a single type. The type owns its methods in a `.( )` block, which defines [dot dispatch](methods.md):

```ruby
# path.rb
exports [Path]

Path := [
    Unix(List(U8)),
    Windows(List(U8)),
].(
    from_bytes : List(U8) -> Path
    to_bytes : Path -> List(U8)
    equals : Path, Path -> Bool
    hash : _
)
```

Modules don't *require* a type — utility modules with free functions and constants work fine. Type-centered organization is the pit of success, not a mandate.

> Why tie modules to types?

Pit of success — the language nudges you toward type-centered organization, which is the common pattern anyway. Modules without a natural type work fine as collections of free functions — `math.clamp(x, 0, 100)`.

This also means the type's module is the single authority for its functions — no third party can define functions on a type they don't own. This is more restrictive than Rust's `impl` blocks (which allow impls in other crates, subject to orphan rules), but it eliminates an entire class of coherence problems. The type author doesn't need to depend on a trait crate to provide an implementation — they just define a function with the right name and signature, and any constraint that matches is satisfied structurally.

For type declarations (`:`, `:=`, `::`), methods, where clauses, and constraints, see [tags](tags.md#type-declarations) and [type system](methods.md).

## Design comparison

Ori's module system combines the most-praised properties across languages while avoiding their common footguns:

- **File = module** (Go, Zig, OCaml, Erlang) — no `mod` declarations, no orphan files, no wiring
- **Explicit export list** (Haskell, OCaml, Erlang) — public API visible at the top of the file, private by default; imports and re-exports are distinct operations
- **Qualified by default** (Erlang, Haskell) — every use site shows provenance; `exposing` for selective unqualified access
- **Root-relative imports only** (Go, Java, Haskell) — one import mechanism, statically determinable, no `../` chains
- **No wildcard imports** (Elm, Roc) — enables parallel name resolution, prevents upstream breakage
- **Package visibility via re-exports** (Rust `pub use`) — the root module controls the package surface without a separate `provides` manifest
- **Hermetic libraries** — `lib { }` creates a boundary: deps are isolated, import root resets; libraries are portable and vendoring requires no internal edits
- **No dependency resolution** — exact URL+hash pinning, no version ranges, no SAT solvers; `ori add` resolves once, builds just fetch
- **No lockfile** — BLAKE3 hashes in URLs pin exact content; the source code is the lockfile
- **No separate manifest** — deps live in the source file, so single-file scripts need no project folder
- **No package registry** — decentralized hosting (any URL), project-local naming, no central point of compromise; private packages work without extra tooling
- **Content-addressed deps** (Nix, Guix) — hash identifies the artifact, not a name or version number; same hash = same package regardless of host or version string
- **Safe diamond deps** — hermetic scoping + no runtime type identity + no global state + structural equality; two versions of the same package can coexist without the `instanceof`/classloader/`init()` failures that plague Node, Java, and Go
- **Structural constraints** (Go interfaces) — no orphan rules, no ecosystem lock-in; libraries interoperate without deep trait hierarchies, reducing transitive dependency pyramids
- **No import side effects** — pure functional semantics, no `init()`, no import-time code execution
- **No circular dependencies** — pure functional, acyclic by construction

Nearly every major language has undergone a painful module system migration — Go's GOPATH to modules, Node's CommonJS to ESM, Python 2 to 3 imports, Rust's 2015 to 2018 edition, Java's classpath to JPMS. These transitions consistently rank among the most disruptive events in each ecosystem's history. The strongest predictor of developer satisfaction with a module system is not power or flexibility but predictability. Getting the module system right in v1 matters more than any specific design choice, because changing it later imposes costs that dwarf the benefits of any particular approach.

## References

- [v2 Refining Static Dispatch and Modules](https://docs.google.com/document/d/12URaMmsgatVVwW-paKNWeCAsc862Cqp-npcUzqRk704/edit)
  - <https://roc.zulipchat.com/#narrow/channel/304641-ideas/topic/static.20dispatch.20revisions/with/545565024>
