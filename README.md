<div align="center">
    <img alt="Wax" src="https://raw.githubusercontent.com/olson-sean-k/wax/master/doc/wax.svg?sanitize=true" width="320"/>
</div>
<br/>

**Wax** is a Rust library that provides opinionated and portable globs that can
be matched against file paths and directory trees.

[![GitHub](https://img.shields.io/badge/GitHub-olson--sean--k/wax-8da0cb?logo=github&style=for-the-badge)](https://github.com/olson-sean-k/wax)
[![docs.rs](https://img.shields.io/badge/docs.rs-wax-66c2a5?logo=rust&style=for-the-badge)](https://docs.rs/wax)
[![crates.io](https://img.shields.io/crates/v/wax.svg?logo=rust&style=for-the-badge)](https://crates.io/crates/wax)

## Basic Usage

Match a specific path against a glob:

```rust
use wax::Glob;

let glob = Glob::new("*.png").unwrap();
if glob.is_match("logo.png") {
    // ...
}
```

Match a specific path against a glob and extract captures:

```rust
use wax::{BytePath, Glob};

let glob = Glob::new("**/{*.{go,rs}}").unwrap();

let path = BytePath::from_path("src/main.go");
let captures = glob.captures(&path).unwrap();

// Prints `main.go`.
println!("{}", captures.get(2).unwrap().as_str().unwrap());
```

Match files in a directory tree against a glob:

```rust
use wax::Glob;

let glob = Glob::new("**/*.{md,txt}").unwrap();
for entry in glob.walk("doc", usize::MAX) {
    // ...
}
```

See more details below.

## Construction

Globs are encoded as strings called glob expressions that resemble Unix paths
consisting of nominal components delimited by separators. Wax exposes its APIs
via the [`Glob`] type, which is constructed from a glob expression via inherent
functions or standard conversion traits. All data is borrowed where possible but
can be copied into owned instances using `into_owned`.

```rust
use wax::Glob;

let glob = Glob::new("site/img/logo.svg").unwrap();
assert!(!glob.has_root());
```

Regardless of platform or operating system, globs always use the same format. In
particular, Forward slash `/` is **always** the path separator and back slashes
`\` are forbidden (back slash is used for escape sequences, but the literal
sequence `\\` is not supported). This means that it is impossible to represent
`\` in nominal path components, but this character is generally forbidden as
such and its disuse avoids confusion.

Globs enforce various consistency rules regarding metacharacters, patterns, and
component boundaries (separators and tree wildcards; see below).

## Patterns

Globs resemble Unix paths, but additionally support patterns that can be matched
against paths and directory trees. Patterns use a syntax that resembles globbing
in Unix shells and similar tools.

```rust
use wax::Glob;

let glob = Glob::new("**/*.{go,rs}").unwrap();
assert!(glob.is_match("src/lib.rs"));
```

Globs use a consistent and opinionated format and patterns are **not**
configurable; the semantics of a particular glob are always the same. For
example, `*` **never** matches across directory boundaries (see below).

### Wildcards

Wildcards match some amount of arbitrary text in paths and are the most
fundamental pattern provided by globs.

The tree wildcard `**` matches zero or more sub-directories. **This is the only
way to match across arbitrary directory boundaries**; all other wildcards do
**not** match across directory boundaries. When a tree wildcard participates in
a match and does not terminate the pattern, its capture includes a trailing
forward slash `/`. If a tree wildcard does not participate in a match, then its
capture is an empty string. Tree wildcards must be delimited by forward slashes
or a termination (such as the beginning and/or end of a glob or sub-glob). Tree
wildcards and path separators are distinct and any adjacent forward slashes that
form a tree wildcard are parsed together. If a glob consists solely of a tree
wildcard, then it matches all files in the working directory tree.

The zero-or-more wildcards `*` and `$` match zero or more of any character
**except path separators**. Zero-or-more wildcards cannot be adjacent to other
zero-or-more wildcards. The `*` wildcard is eager and will match the longest
possible text while the `$` wildcard is lazy and will match the shortest
possible text. When followed by a literal, `*` stops at the last occurrence of
that literal while `$` stops at the first occurence.

The exactly-one wildcard `?` matches any single character **except path
separators**. Exactly-one wildcards do not group automatically, so a pattern of
contiguous wildcards such as `???` form distinct captures for each `?` wildcard.
An alternative can be used to group exactly-one wildcards into a single capture,
such as `{???}` (see [below](#alternatives)).

### Character Classes

Character classes match any single character from a group of literals and ranges
**except path separators**. Classes are delimited by square brackets `[...]`.
Individual character literals are specified as is, such as `[ab]` to match
either `a` or `b`. Character ranges are formed from two characters separated by
a hyphen, such as `[x-z]` to match `x`, `y`, or `z`.

Any number of character literals and ranges can be used within a single
character class. For example, `[qa-cX-Z]` matches any of `q`, `a`, `b`, `c`,
`X`, `Y`, or `Z`.

Character classes may be negated by including an exclamation mark `!` at the
beginning of the class pattern. For example, `[!a]` matches any character except
for `a`.

Note that character classes can also be used to escape metacharacters like `*`,
`$`, etc., though globs also support escaping via a backslash `\`. To match the
control characters `[`, `]`, and `-` within a character class, they must be
escaped via a backslash, such as `[a\-]` to match `a` or `-`.

### Alternatives

Alternatives match an arbitrary sequence of comma separated sub-globs delimited
by curly braces `{...,...}`. For example, `{a?c,x?z,foo}` matches any of the
sub-globs `a?c`, `x?z`, or `foo`. Alternatives may be arbitrarily nested, such
as in `{a,{b,{c,d}}}`.

Alternatives form a single capture group regardless of the contents of their
sub-globs. This capture is formed from the complete match of the sub-glob, so if
the sub-glob `a?c` matches `abc` in `{a?c,x?z}`, then the capture text will be
`abc` (**not** `b` as it would be outside of an alternative sequence).
Alternatives can be used to group capture text using a single sub-glob, such as
`{*.{go,rs}}` to capture an entire file name with a particular extension or
`{???}` to group a sequence of exactly-one wildcards.

Sub-globs must consider both neighboring patterns and component boundaries. For
example, wildcards must respect adjacency rules, so `*{a,b*}` is allowed but
`*{a,*b}` is not. Furthermore, component boundaries may never be adjacent, so
`a/{b/,c/**/}d` and `a{/b,/c}` are allowed but `a/{b/,/**/c}/d` and `a/{/b,/c}`
are not.

Both path separators and tree wildcards are considered component boundaries and
tree wildcards are parsed together with their surrounding forward slashes: `**`,
`/**`, `**/`, and `/**/` are all considered tree wildcards and produce no
independent path separators. This is typically intuitive, but means that despite
no adjacent forward slashes, `a/{**/b,c}` and `{a/**,b}/c` are not allowed just
as `a//**` is not allowed.

## Flags and Case Sensitivity

Flags toggle the matching behavior of globs. Importantly, flags are a part of a
glob expression rather than a separate API. Behaviors are toggled immediately
following flags in the order in which they appear in glob expressions. Flags are
delimited by parenthesis with a leading question mark `(?...)` and may appear
anywhere within a glob expression so long as they do not split tree wildcards
(for example, `a/*(?i)*`). Each flag is represented by a single character and
can be negated by preceding the corresponding character with a dash `-`. Flags
are toggled in the order in which they appear within `(?...)`.

The only supported flag is the case-insensitivty flag `i`. By default, glob
expressions use the same case sensitivity as the target platforms's file system
(case-sensitive on Unix and case-insensitive on Windows), but `i` can be used to
toggle this explicitly as needed. For example, `(?-i)photos/**/*.(?i){jpg,jpeg}`
matches file paths beneath a `photos` directory with a case-sensitive base and a
case-**in**sensitive extension `jpg` or `jpeg`.

Wax considers literals, their configured case sensitivity, and the case
sensitivity of the target platform's file system when partitioning glob
expressions with [`Glob::partitioned`] (see
[below](#partitioning-and-semantic-literals)). Partitioning is unaffected in
glob expressions with no flags.

## Errors and Diagnostics

The [`GlobError`] type represents error conditions that can occur when parsing a
glob expression, validating a glob expression, or walking a directory tree with
a glob. [`GlobError`] and its sub-errors implement the standard [`Error`] and
[`Display`] traits via [`thiserror`][thiserror], which express basic information
about failures.

Wax optionally integrates with the [`miette`][miette] crate, which can be used
to capture and display diagnostics. This can be useful for reporting errors to
users that provide glob expressions.

```
Error: glob::rule

  x invalid glob expression: adjacent zero-or-more wildcards `*` or `$` in alternative
   ,----
 1 | doc/**/*{.md,*.txt}
   :        ^^^^^^|^^^^^
   :              `-- here
   `----
```

Diagnostics are disabled by default and can be enabled with the `diagnostics`
feature. This can be done via Cargo in a crate's `Cargo.toml` file.

```toml
[dependency.wax]
version = "^0.0.0"
features = ["diagnostics"]
```

## Unsupported Path Features

Any components not recognized as separators nor patterns are interpreted as
literals. In combination with strict rules, this means **some platform-specific
path features cannot be used directly in globs**. This limitation is by design
and additional code may be necessary to bridge this gap for some use cases.

### Partitioning and Semantic Literals

Globs support no notion of a current or parent directory. The path components
`.` and `..` are interpreted as literals and only match paths with the
corresponding components (even on Unix and Windows). For example, the glob
`src/../*.rs` matches the path `src/../lib.rs` but does **not** match the path
`lib.rs`.

Parent directory components have unclear meaning and far less utility when they
follow patterns in a glob. However, such components are intuitive and are often
important for escaping a working directory when they precede patterns (i.e., as
a prefix). For example, the glob `../src/**/*.rs` has more obvious meaning than
the glob `src/**/../*.rs`. As seen above though, the first glob would only match
the literal path component `..` and not paths that replace this with a parent
directory.

[`Glob::partitioned`] can be used to parse glob expressions that contain
semantic components that precede patterns and would be interpreted as literals
(namely `..`). [`Glob::partitioned`] partitions a glob expression into an
invariant [`PathBuf`] prefix and a variant [`Glob`] postfix. Here, invariant
means that the partition contains no glob patterns and resolves the same literal
paths on the target platform's file system (has invariant literals and/or case
sensitivity). The path can be used as needed in combination with the glob.

```rust
use std::path::Path;
use wax::Glob;

let path = Path::new("."); // Working directory.
let (prefix, glob) = Glob::partitioned("../site/img/*.{jpg,png}").unwrap();
for entry in glob.walk(path.join(prefix), usize::MAX) {
    // ...
}
```

Additionally, [`Glob::has_semantic_literals`] can be used to detect literal
components in a glob that have special semantics on the target platform.

```rust
use wax::Glob;

let glob = Glob::new("../**/src/**/main.rs").unwrap();
assert!(glob.has_semantic_literals());
```

### Schemes and Prefixes

While globs can be rooted, they cannot include schemes nor Windows path
prefixes. For example, the Windows UNC share path `\\server\share\src` cannot be
represented directly as a glob.

This can be limiting, but the design of Wax explicitly forbids this: Windows
prefixes and other volume components are not portable. Instead, when this is
needed, an additional native path or working directory can be used, such as [the
`--tree` option provided by Nym][nym]. In most contexts, globs are applied
relative to some such working directory.

[miette]: https://github.com/zkat/miette
[nym]: https://github.com/olson-sean-k/nym
[thiserror]: https://github.com/dtolnay/thiserror

[`Display`]: https://doc.rust-lang.org/std/fmt/trait.Display.html
[`Error`]: https://doc.rust-lang.org/std/error/trait.Error.html
[`Glob`]: https://docs.rs/wax/*/wax/struct.Glob.html
[`Glob::has_semantic_literals`]: https://docs.rs/wax/*/wax/struct.Glob.html#method.has_semantic_literals
[`Glob::partitioned`]: https://docs.rs/wax/*/wax/struct.Glob.html#method.partitioned
[`GlobError`]: https://docs.rs/wax/*/wax/enum.GlobError.html
[`PathBuf`]: https://doc.rust-lang.org/std/path/struct.PathBuf.html
