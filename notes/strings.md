# Strings

Strings are UTF-8 encoded. Double-quoted with `${}` interpolation. Triple-quoted for multiline with indent stripping. Single-quoted for character literals (which are just numbers).

## String interpolation

Expressions inside `${}` within a string literal are evaluated and converted to strings. Only one string type — no `f`-string prefix or backtick distinction:

```ruby
name = "world"
greeting = "hello ${name}"
msg = "the answer is ${x + 1}"
bio = "${user.name} is ${user.age} years old"

# Literal ${ is escaped as \${
template = "use \${braces} for interpolation"
```

> Why `${}` instead of bare `{}`?

Bare `{}` (Rust/Python-style) requires escaping every literal brace — strings containing JSON, code, CSS, or LaTeX become cluttered with doubled braces: `"body {{ color: {color}; }}"`. With `${}`, braces are just braces: `"body { color: ${color}; }"` reads like the actual output. The two-character `${` sequence almost never appears naturally in strings, so escaping is essentially a non-issue.

> Why not `\()` or `$()`?

`\()` (Swift/Roc-original) makes paths and URLs hard to read (`"/users/\(name)/posts"`) and breaks Vim editor tooling. `$()` fixes those issues but nests awkwardly inside parens-and-commas calling: `$(foo.to_str())`. `${}` avoids both problems. Roc went through all three (`\()` → `$()` → `${}`) and settled on `${}`.

## Multiline strings

Triple-quoted strings with Swift-style indent stripping. The closing `"""` defines the leading edge — all content is dedented relative to its column:

```ruby
sql = """
    SELECT *
    FROM users
    WHERE age > 30
    """

json = """
    {
      "name": "Alice",
      "age": 30
    }
    """
```

Lines indented more than the closing `"""` keep their relative indentation. Lines indented less than the closing `"""` are a compile error.

Interpolation works the same as single-line strings:

```ruby
query = """
    SELECT *
    FROM ${table}
    WHERE id = ${id}
    """
```

No quote escaping needed — double quotes inside a triple-quoted string are literal. The only sequence that needs escaping is `"""` itself (rare in practice).

> Why `"""` instead of letting `"` span multiple lines?

The value of `"""` isn't being multiline — it's the indent stripping. The closing `"""` on its own line acts as a ruler defining the content's left edge. If `"` strings could span lines, there's no natural way to communicate the indent level — the closing `"` sits at the end of content, not on its own line. You'd need a heuristic or a new rule, which is just reinventing `"""` with more ambiguity.

Without a separate multiline syntax, you'd either give up indent stripping (Python's `textwrap.dedent()` problem — refactoring code changes string content) or make `"` strings context-dependent (single-line `"` has no stripping, multiline `"` does). Two syntaxes with distinct behavior is clearer than one syntax with modal behavior.

`"""` also means double quotes inside the string are literal — no escaping needed for JSON, HTML attributes, or prose containing quotation marks.

> Why `"""` with indent stripping instead of per-line prefixes (`\\`)?

Zig-style `\\` prefixes give per-line tokenizable lexing — the lexer never needs multi-line state. But lexing is already trivially fast (a single boolean flag for "inside a string"), and the parser already tracks multi-line state for `()` and `{}` nesting. Every mainstream language with multiline strings (Python, Swift, Kotlin, Java) uses multi-line tokens without performance issues. The `"""` syntax is more familiar, reads cleaner, and makes copy/paste easier.

> Why closing-delimiter indent stripping instead of raw content (Python/Rust)?

Without indent stripping, the string's value changes when you refactor code to a different nesting level. Python requires `textwrap.dedent()`, Rust requires the `indoc!` macro — both punt the problem to the caller. Swift's approach makes the closing `"""` an explicit ruler: everything to the right of it is content, everything to the left is a compile error. No ambiguity, no silent whitespace changes.

## Character literals

Single-quoted character literals desugar to integer literals during lexing — `'('` becomes `40`, `'A'` becomes `65`, `'👩'` becomes `128105`. After desugaring, the compiler doesn't know they were ever written as characters. The type is `a where [a.Num]`, identical to any other number literal, resolved by context:

```ruby
# Byte context — '(' is U8
input.bytes().walk(0, |floor, byte|
    if byte == '(' then floor + 1 else floor - 1
)

# Code point context — '👩' is CodePoint
input.code_points().keep_if(|cp| cp == '👩')
```

A character literal that doesn't fit in the contextual type is a compile error — `'👩'` in a `U8` context fails because 128105 > 255. This is the same overflow check that applies to any numeric literal (`let x : U8 = 256` also fails).

### Character literals and opaque types

Character literals work with `CodePoint` through [context-based construction](tags.md#constructor-access) — the same mechanism that lets bare values unify with nominal types when the context expects it. In `cp == '👩'` where `cp : CodePoint`, the literal `'👩'` constructs a `CodePoint` directly. This doesn't bypass `CodePoint`'s validation because the compiler already rejects invalid code points at the literal level — surrogates (U+D800–U+DFFF) and values above U+10FFFF cannot be written as character literals.

Haskell, Zig, and Roc all let polymorphic literals flow into wrapper types through context. Haskell's `5` has type `Num a => a` and desugars to `fromInteger 5`. Zig's `comptime_int` coerces to whatever integer type the target demands. Ori's approach is the same principle applied to character literals — the literal is a number, and the type context determines what it becomes.

### Comparison at each level

The iteration level determines the comparison type. Byte-level iteration yields `U8` — compare against ASCII character literals. Code-point iteration yields `CodePoint` — compare against any Unicode scalar. You cannot accidentally mix levels:

```ruby
# Bytes — compare against ASCII
input.bytes().keep_if(|b| b == '{')        # fine, 123 fits in U8
input.bytes().keep_if(|b| b == '€')        # COMPILE ERROR, 8364 > 255

# Code points — compare against any Unicode scalar
input.code_points().keep_if(|cp| cp == '€')    # fine
input.code_points().keep_if(|cp| cp == '{')    # also fine

# Graphemes — compare against strings
input.graphemes().keep_if(|g| g == "👨‍👩‍👧‍👦")   # grapheme cluster, Str == Str
```

The compiler enforces the boundary: trying to compare a byte against a non-ASCII character literal is a type error, not a silent bug. This catches the mistake that Go and C allow — comparing a `byte` against a multi-byte character's code point value, which succeeds for the wrong reasons.

> Why not a dedicated `Char` type as a language primitive?

Code points are the awkward middle child of string processing — too big for parsing (4 bytes vs 1, requires UTF-8 decoding), too small for correct text (`'👨‍👩‍👧‍👦'` is 7 code points but 1 grapheme cluster). Parsing and protocols work with bytes. User-visible text works with grapheme clusters. Code points sit between them, useful mainly for Unicode normalization and character classification.

Rust's `char` (4-byte Unicode scalar value) is the cautionary tale. The name suggests a "character" but it doesn't represent one — `'👨‍👩‍👧‍👦'` is 7 `char` values, not 1. Rust needed `b'x'` as an escape hatch because `char` was too heavy for the byte-level work that dominates parsing. Forgetting the `b` prefix causes a type mismatch between `u8` and `char` — a friction point that wouldn't exist if character literals were just numbers. A 2014 RFC to rename `char` to `codepoint` was closed without action, leaving the confusing name in place.

Zig and Roc both validate the alternative: character literals as plain integers, no dedicated char type. Zig's `comptime_int` coercion catches out-of-range values at compile time with zero runtime cost. Roc's `Num *` wildcard type lets character literals flow into `U8`, `U32`, or any numeric type. Neither language reports ergonomic problems from the absence of a `Char` type — the parsing code is actually cleaner.

Keeping character literals as numbers gives byte-level ergonomics without friction. For the rarer code-point-level work (normalization, case mapping, `is_alphabetic`), a `CodePoint :: U32` opaque type in the standard library provides validation and a natural home for classification functions — without burdening the language or the common byte-level case.

## String handling

Strings are UTF-8 encoded. Three levels of iteration, each returning a different unit:

```ruby
# Bytes — raw UTF-8 bytes, fast, for parsing and ASCII work
input.bytes() : Iter(U8)

# Code points — Unicode scalar values, for normalization and classification
input.code_points() : Iter(CodePoint)

# Graphemes — user-visible characters (extended grapheme clusters), for display/UI
input.graphemes() : Iter(Str)
```

**Bytes** are the primary tool for parsing and protocols — ASCII delimiters, JSON structure, HTTP headers are all single-byte operations. Character literals (`'('`, `'"'`, `'\n'`) work directly as `U8` in byte context.

**Graphemes** are the correct unit for user-visible text — splitting, trimming, truncating, and counting "characters" as users perceive them. Standard library string functions that operate on "characters" (like `trim`, `split_on`) respect grapheme cluster boundaries. The Unicode segmentation table ships with the standard library — since `.graphemes()` is part of the `Str` API, the implementation must be available without external packages. Rust's decision to push grapheme segmentation to an external crate despite `.chars()` docs saying "grapheme clusters may be what you actually want" is a well-documented pain point.

**Code points** sit between them, used for Unicode normalization, case mapping, and character classification. `CodePoint :: U32` is an opaque type in the standard library that guarantees a valid Unicode scalar value (not a surrogate, not > 0x10FFFF):

```ruby
CodePoint :: U32.(
    from_u32 : U32 -> Result(CodePoint, [InvalidCodePoint])
    to_u32 : CodePoint -> U32
    is_alphabetic : CodePoint -> Bool
    is_digit : CodePoint -> Bool
    is_whitespace : CodePoint -> Bool
    to_lowercase : CodePoint -> CodePoint
    to_uppercase : CodePoint -> CodePoint
)
```

There is no `.len()` on `Str` — "length" is ambiguous for strings. Use the explicit variant:

```ruby
input.count_bytes() : U64        # O(1), byte length
input.count_code_points() : U64  # O(n), walks the string
input.count_graphemes() : U64    # O(n), walks the string
```

> Why no `.len()` on strings?

`"café".len()` could reasonably be 5 (bytes), 4 (code points), or 4 (graphemes) — and for `"👨‍👩‍👧‍👦"` those numbers are 25, 7, and 1. Roc makes `.len()` a compile error that points you to `count_utf8_bytes`. Explicit names prevent an entire class of off-by-one bugs in internationalized code.

> Why three levels instead of just bytes and graphemes?

Graphemes require a Unicode segmentation table and are expensive to iterate. Many operations don't need that — counting non-ASCII characters, normalizing to NFC/NFD, or classifying characters by Unicode category all work at the code point level without the overhead of grapheme segmentation. The three levels give you the right tool for each job: bytes for speed, code points for Unicode semantics, graphemes for correctness with human text.

> Why one string type instead of separate types for bytes, text, and OS strings?

Languages that separate string representations end up with type proliferation driven by memory-management trade-offs, not semantic ones. Haskell has `String`, `Text`, `ShortText`, `ByteString`, `ShortByteString`, `Bytes`, and `OsString` — each with distinct properties around pinned vs unpinned memory, strict vs lazy evaluation, and slicable vs non-slicable storage. Rust has `String`, `&str`, `OsString`, `OsStr`, `CString`, `CStr`, and `Vec<char>`. The types exist because the language runtime forces choices about memory layout at the type level.

Ori collapses the representation axis: one reference-counted UTF-8 buffer (`Str`), no pinned/unpinned distinction (Perceus RC, no GC), no strict/lazy split (strict evaluation), no owned/borrowed split (no lifetimes). The semantic axis — bytes vs code points vs graphemes — is exposed through iteration methods on the single type, not through separate types. This gives the same level of control (byte-level parsing, code-point classification, grapheme-correct display) without the conversion boilerplate that dominates string-heavy Haskell and Rust code.

Platform-specific string types (`OsString` in Rust/Haskell) handle the fact that Unix filepaths are arbitrary bytes and Windows filepaths are UTF-16. Ori's platform model pushes this to the FFI boundary — the platform provides `Str` to the application, and the platform implementation handles encoding. The application never sees raw OS bytes.

`CodePoint :: U32` is the Unicode Scalar Value type that Haskell's `Char` should have been — it excludes surrogates (U+D800–U+DFFF) by construction, which `Char` does not. Haskell's `Text.pack` silently replaces surrogates with U+FFFD; Ori's `CodePoint.from_u32` returns an explicit `Err`. And `.graphemes()` returning `Iter(Str)` provides the grapheme cluster iteration that Haskell still lacks in its standard library (requiring `text-icu` for grapheme boundary detection).

## String equality

String equality is **byte equality** — two strings are equal if and only if their UTF-8 byte sequences are identical. This means `"é"` (U+00E9, single code point) and `"é"` (U+0065 + U+0301, e + combining accent) are **not equal**, even though they render identically.

```ruby
"é" == "é"    # false if one is composed and the other is decomposed
```

For canonical equivalence, normalize first:

```ruby
a = "é"                          # might be NFC or NFD
b = "é"                          # might be the other form
a.normalize(Nfc) == b.normalize(Nfc)   # true — compare after normalization
```

> Why byte equality instead of canonical equivalence?

Swift is the only major language that does canonical equivalence by default — `"é" == "é"` is `true` in Swift even when the byte representations differ. This is more correct for user-facing text but has real costs: equality requires NFC/NFD normalization tables, comparison is slower, and the behavior surprises developers debugging byte-level issues ("these strings look the same but have different bytes — why?").

Every other systems language — Rust, Go, Zig, C, Roc — uses byte equality. The pragmatic argument: most string comparisons in programs are against known literals (API keys, HTTP headers, JSON field names, command-line flags), which are already in a consistent normalization form. The cases where canonical equivalence matters — user-provided names, search queries, internationalized text — are better handled by explicit normalization at the system boundary (when reading user input) rather than on every comparison.

Byte equality is also consistent with structural equality everywhere else in the language. Records, tags, lists, and numbers all compare by their representation. Making strings a special case would break the uniformity and add a hidden cost to the most common operation on strings.

> Why not normalize all strings on construction?

Normalizing every string to NFC on construction (like ICU's `NormalizationTransformation`) would make byte equality equivalent to canonical equivalence. But normalization is lossy for some workflows — round-tripping through normalization can change byte offsets that matter for parsers, and some protocols require specific normalization forms (NFD for HFS+, NFC for the web). Normalizing at the boundary rather than on construction preserves the original bytes when needed.
