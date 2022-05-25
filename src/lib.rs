//! Wax provides opinionated and portable globs that can be matched against file
//! paths and directory trees. Globs use a familiar syntax and support
//! expressive features with semantics that emphasize component boundaries.
//!
//! See the [repository
//! documentation](https://github.com/olson-sean-k/wax/blob/master/README.md)
//! for details about glob expressions and patterns.

#![cfg_attr(docsrs, feature(doc_cfg))]
#![doc(
    html_favicon_url = "https://raw.githubusercontent.com/olson-sean-k/wax/master/doc/wax-favicon.svg?sanitize=true"
)]
#![doc(
    html_logo_url = "https://raw.githubusercontent.com/olson-sean-k/wax/master/doc/wax.svg?sanitize=true"
)]
#![deny(
    clippy::cast_lossless,
    clippy::checked_conversions,
    clippy::cloned_instead_of_copied,
    clippy::explicit_into_iter_loop,
    clippy::filter_map_next,
    clippy::flat_map_option,
    clippy::from_iter_instead_of_collect,
    clippy::if_not_else,
    clippy::manual_ok_or,
    clippy::map_unwrap_or,
    clippy::match_same_arms,
    clippy::redundant_closure_for_method_calls,
    clippy::redundant_else,
    clippy::unreadable_literal,
    clippy::unused_self
)]

mod capture;
mod diagnostics;
mod encode;
mod rule;
mod token;
mod walk;

use bstr::ByteVec;
use itertools::{Itertools as _, Position};
#[cfg(feature = "diagnostics-report")]
use miette::Diagnostic;
use regex::Regex;
use std::borrow::{Borrow, Cow};
use std::convert::Infallible;
use std::ffi::OsStr;
use std::fmt::{self, Debug, Display, Formatter};
use std::path::{Path, PathBuf};
use std::str::{self, FromStr};
use thiserror::Error;

#[cfg(feature = "diagnostics-inspect")]
use crate::diagnostics::inspect;
#[cfg(feature = "diagnostics-report")]
use crate::diagnostics::report::{self, IteratorExt as _, ResultExt as _};
use crate::token::{Annotation, IntoTokens, InvariantText, Token, Tokenized};

pub use crate::capture::MatchedText;
#[cfg(feature = "diagnostics-inspect")]
pub use crate::diagnostics::inspect::CapturingToken;
#[cfg(feature = "diagnostics-report")]
pub use crate::diagnostics::report::{DiagnosticResult, DiagnosticResultExt};
#[cfg(feature = "diagnostics-inspect")]
pub use crate::diagnostics::Span;
pub use crate::encode::CompileError;
pub use crate::rule::RuleError;
pub use crate::token::ParseError;
pub use crate::walk::{
    FilterTarget, FilterTree, IteratorExt, LinkBehavior, Negation, Walk, WalkBehavior, WalkEntry,
    WalkError,
};

#[cfg(windows)]
const PATHS_ARE_CASE_INSENSITIVE: bool = true;
#[cfg(not(windows))]
const PATHS_ARE_CASE_INSENSITIVE: bool = false;

trait ResultExt<T, E> {
    fn expect_encoding(self) -> T;
}

impl<T, E> ResultExt<T, E> for Result<T, E>
where
    E: Debug,
{
    fn expect_encoding(self) -> T {
        self.expect("unexpected encoding")
    }
}

trait CharExt: Sized {
    /// Returns `true` if the character (code point) has casing.
    fn has_casing(self) -> bool;
}

impl CharExt for char {
    fn has_casing(self) -> bool {
        self.is_lowercase() != self.is_uppercase()
    }
}

trait StrExt {
    /// Returns `true` if any characters in the string have casing.
    fn has_casing(&self) -> bool;
}

impl StrExt for str {
    fn has_casing(&self) -> bool {
        self.chars().any(CharExt::has_casing)
    }
}

trait PositionExt<T> {
    fn as_tuple(&self) -> (Position<()>, &T);

    fn map<U, F>(self, f: F) -> Position<U>
    where
        F: FnMut(T) -> U;

    fn interior_borrow<B>(&self) -> Position<&B>
    where
        T: Borrow<B>;
}

impl<T> PositionExt<T> for Position<T> {
    fn as_tuple(&self) -> (Position<()>, &T) {
        match *self {
            Position::First(ref item) => (Position::First(()), item),
            Position::Middle(ref item) => (Position::Middle(()), item),
            Position::Last(ref item) => (Position::Last(()), item),
            Position::Only(ref item) => (Position::Only(()), item),
        }
    }

    fn map<U, F>(self, mut f: F) -> Position<U>
    where
        F: FnMut(T) -> U,
    {
        match self {
            Position::First(item) => Position::First(f(item)),
            Position::Middle(item) => Position::Middle(f(item)),
            Position::Last(item) => Position::Last(f(item)),
            Position::Only(item) => Position::Only(f(item)),
        }
    }

    fn interior_borrow<B>(&self) -> Position<&B>
    where
        T: Borrow<B>,
    {
        match *self {
            Position::First(ref item) => Position::First(item.borrow()),
            Position::Middle(ref item) => Position::Middle(item.borrow()),
            Position::Last(ref item) => Position::Last(item.borrow()),
            Position::Only(ref item) => Position::Only(item.borrow()),
        }
    }
}

trait SliceExt<T> {
    fn terminals(&self) -> Option<Terminals<&T>>;
}

impl<T> SliceExt<T> for [T] {
    fn terminals(&self) -> Option<Terminals<&T>> {
        match self.len() {
            0 => None,
            1 => Some(Terminals::Only(self.first().unwrap())),
            _ => Some(Terminals::StartEnd(
                self.first().unwrap(),
                self.last().unwrap(),
            )),
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum Terminals<T> {
    Only(T),
    StartEnd(T, T),
}

impl<T> Terminals<T> {
    pub fn map<U, F>(self, mut f: F) -> Terminals<U>
    where
        F: FnMut(T) -> U,
    {
        match self {
            Terminals::Only(only) => Terminals::Only(f(only)),
            Terminals::StartEnd(start, end) => Terminals::StartEnd(f(start), f(end)),
        }
    }
}

/// A representation of a glob expression that can be matched against paths.
///
/// Matching is a logical operation and does **not** interact with a file
/// system. To handle path operations, use [`Path`] and/or [`PathBuf`] and their
/// associated operations. See [`Glob::partition`] for more about globs and path
/// operations.
///
/// [`Glob::partition`]: crate::Glob::partition
/// [`Path`]: std::path::Path
/// [`PathBuf`]: std::path::PathBuf
pub trait Pattern<'t>: IntoTokens<'t> {
    /// Returns `true` if a path matches the pattern.
    ///
    /// The given types must be convertible into a [`CandidatePath`].
    ///
    /// [`CandidatePath`]: crate::CandidatePath
    fn is_match<'p>(&self, path: impl Into<CandidatePath<'p>>) -> bool;

    /// Gets matched text in a [`CandidatePath`].
    ///
    /// Returns `None` if the [`CandidatePath`] does not match the pattern.
    ///
    /// [`CandidatePath`]: crate::CandidatePath
    fn matched<'p>(&self, path: &'p CandidatePath<'_>) -> Option<MatchedText<'p>>;

    /// Gets the variance of the pattern.
    ///
    /// An invariant glob expression is essentially constant or literal and has
    /// no patterns that resolve differently than an equivalent path does using
    /// the platform's file system APIs. For example, the expression
    /// `path/to/file.txt` is always invariant and resolves identically to the
    /// paths `path/to/file.txt` and `path\to\file.txt` on Unix and Windows,
    /// respectively.
    ///
    /// A variant glob expression does not resolve the same way as any path used
    /// with the platform's file system APIs. This is typically because the
    /// expression matches multiple texts using a regular pattern, such as in
    /// the expression `**/*.rs`.
    ///
    /// Note that this considers potentially invariant patterns such as
    /// `path/[t][o]/{file.txt}`, which is invariant on Unix. Variance also
    /// considers flags and the case sensitivity of literals. For example,
    /// `(?i)file.text` is invariant on Windows but is not on Unix. Variance is
    /// therefore platform dependent, as it is based on the behavior of file
    /// system APIs.
    fn variance(&self) -> Variance;
}

// TODO: It is not possible to use the `#[doc(cfg())]` attribute on the
//       `Diagnostic` implementation generated by procedural macros.
//       `Diagnostic` could be implemented without macros, but `GlobError` is
//       particularly well suited to them. Use a manual implementation with
//       `#[doc(cfg())]` to mark the implementation as feature dependent in
//       documentation if that changes.
/// Errors concerning [`Glob`]s and [`Pattern`]s.
///
/// This is the primary error type used by Wax APIs. Each variant exposes a
/// particular error type that describes the details of its associated error
/// condition.
///
/// When the `diagnostics-report` feature is enabled, this and other error types
/// implement the [`Diagnostic`] trait.
///
/// [`Diagnostic`]: miette::Diagnostic
/// [`Glob`]: crate::Glob
/// [`Pattern`]: crate::Pattern
#[derive(Debug, Error)]
#[non_exhaustive]
#[cfg_attr(feature = "diagnostics-report", derive(Diagnostic))]
pub enum GlobError<'t> {
    /// A glob expression failed to compile.
    ///
    /// This error occurs when a glob expression (or some part of a glob
    /// expression) cannot be compiled. See the documentation for
    /// [`CompileError`].
    ///
    /// [`CompileError`]: crate::CompileError
    #[error(transparent)]
    #[cfg_attr(feature = "diagnostics-report", diagnostic(transparent))]
    Compile(CompileError),
    /// A glob expression failed to parse.
    ///
    /// This error occurs when attempting to construct a [`Glob`] from a glob
    /// expression that cannot be parsed. See the documentation for
    /// [`ParseError`].
    ///
    /// [`Glob`]: crate::Glob
    /// [`ParseError`]: crate::ParseError
    #[error(transparent)]
    #[cfg_attr(feature = "diagnostics-report", diagnostic(transparent))]
    Parse(ParseError<'t>),
    /// A glob expression parsed but is malformed.
    ///
    /// This error occurs when a glob expression violates rules regarding
    /// patterns, such as using adjacent zero-or-more wildcards. See the
    /// documentation for [`RuleError`].
    ///
    /// [`RuleError`]: crate::RuleError
    #[error(transparent)]
    #[cfg_attr(feature = "diagnostics-report", diagnostic(transparent))]
    Rule(RuleError<'t>),
    /// An error occurred while walking a directory tree.
    ///
    /// This error occurs while matching files in a directory tree against a
    /// [`Glob`]. See the documentation for [`WalkError`].
    ///
    /// [`Glob`]: crate::Glob
    /// [`WalkError`]: crate::WalkError
    #[error("failed to walk directory tree: {0}")]
    #[cfg_attr(feature = "diagnostics-report", diagnostic(code = "wax::glob::walk"))]
    Walk(WalkError),
}

impl<'t> GlobError<'t> {
    /// Clones any borrowed data into an owning instance.
    pub fn into_owned(self) -> GlobError<'static> {
        match self {
            GlobError::Compile(error) => GlobError::Compile(error),
            GlobError::Parse(error) => GlobError::Parse(error.into_owned()),
            GlobError::Rule(error) => GlobError::Rule(error.into_owned()),
            GlobError::Walk(error) => GlobError::Walk(error),
        }
    }
}

impl From<CompileError> for GlobError<'_> {
    fn from(error: CompileError) -> Self {
        GlobError::Compile(error)
    }
}

impl From<Infallible> for GlobError<'_> {
    fn from(_: Infallible) -> Self {
        unreachable!()
    }
}

impl<'t> From<ParseError<'t>> for GlobError<'t> {
    fn from(error: ParseError) -> Self {
        GlobError::Parse(error.into_owned())
    }
}

impl<'t> From<RuleError<'t>> for GlobError<'t> {
    fn from(error: RuleError<'t>) -> Self {
        GlobError::Rule(error)
    }
}

impl From<WalkError> for GlobError<'_> {
    fn from(error: WalkError) -> Self {
        GlobError::Walk(error)
    }
}

/// Path that can be matched against a [`Glob`] or [`Pattern`].
///
/// `CandidatePath`s are always UTF-8 encoded. On some platforms this requires a
/// lossy conversion that uses Unicode replacement codepoints `�` whenever a
/// part of a path cannot be represented as valid UTF-8 (such as Windows). This
/// means that some byte sequences cannot be matched.
///
/// [`Glob`]: crate::Glob
/// [`Pattern`]: crate::Pattern
#[derive(Clone)]
pub struct CandidatePath<'b> {
    text: Cow<'b, str>,
}

impl<'b> CandidatePath<'b> {
    /// Clones any borrowed data into an owning instance.
    pub fn into_owned(self) -> CandidatePath<'static> {
        CandidatePath {
            text: self.text.into_owned().into(),
        }
    }
}

impl AsRef<str> for CandidatePath<'_> {
    fn as_ref(&self) -> &str {
        self.text.as_ref()
    }
}

impl Debug for CandidatePath<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self.text)
    }
}

impl Display for CandidatePath<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.text)
    }
}

impl<'b> From<&'b OsStr> for CandidatePath<'b> {
    fn from(text: &'b OsStr) -> Self {
        CandidatePath {
            text: match Vec::from_os_str_lossy(text) {
                Cow::Borrowed(bytes) => str::from_utf8(bytes).expect_encoding().into(),
                Cow::Owned(bytes) => String::from_utf8(bytes).expect_encoding().into(),
            },
        }
    }
}

impl<'b> From<&'b Path> for CandidatePath<'b> {
    fn from(path: &'b Path) -> Self {
        CandidatePath::from(path.as_os_str())
    }
}

impl<'b> From<&'b str> for CandidatePath<'b> {
    fn from(text: &'b str) -> Self {
        CandidatePath { text: text.into() }
    }
}

/// Variance of a [`Pattern`].
///
/// The variance of a pattern describes the kinds of paths it can match with
/// respect to the platform file system APIs. [`Pattern`]s are either variant or
/// invariant.
///
/// [`Pattern`]: crate::Pattern
/// [`Variance`]: crate::Variance
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum Variance {
    /// A [`Pattern`] is invariant and equivalent to a native path.
    ///
    /// An invariant [`Pattern`] is equivalent to a native path and resolves the
    /// same way as such a native path does when used with the platform's file
    /// system APIs. These APIs may differ, so variance is platform dependent.
    ///
    /// Invariant expressions are not limited to literals and separators. Some
    /// non-literal expressions may be invariant, such as in the expression
    /// `path/[t][o]/{file,file}.txt`, which is invariant on Unix (but not on
    /// Windows, because the character class expressions do not consider
    /// casing).
    ///
    /// [`Pattern`]: crate::Pattern
    Invariant(
        /// An equivalent native path that describes the invariant [`Pattern`].
        /// For example, the invariant expression `path/to/file.txt` can be
        /// described by the paths `path/to/file.txt` and `path\to\file.txt` on
        /// Unix and Windows, respectively.
        PathBuf,
    ),
    /// A [`Pattern`] is variant and resolves differently than any native path.
    ///
    /// A variant [`Pattern`] has no equivalent native path. Most globs are
    /// variant and match a variety of paths, as invariant [`Pattern`]s have no
    /// more utility than a native path.
    ///
    /// Variant expressions may be formed from only literals or other
    /// expressions that seem to be strictly variant at first blush. For
    /// example, the variance of literals considers the case sensitivity of the
    /// platform's file system APIs, so the expression `(?i)path/to/file.txt` is
    /// variant on Unix (but not on Windows). Similarly, the expression
    /// `path/[t][o]/file.txt` is variant on Windows (but not on Unix).
    ///
    /// [`Pattern`]: crate::Pattern
    Variant,
}

impl Variance {
    pub fn is_invariant(&self) -> bool {
        matches!(self, Variance::Invariant(_))
    }

    pub fn is_variant(&self) -> bool {
        matches!(self, Variance::Variant)
    }
}

impl From<token::Variance<InvariantText<'_>>> for Variance {
    fn from(variance: token::Variance<InvariantText<'_>>) -> Self {
        match variance {
            token::Variance::Invariant(text) => {
                Variance::Invariant(PathBuf::from(text.to_string().into_owned()))
            },
            token::Variance::Variant(_) => Variance::Variant,
        }
    }
}

/// Pattern that can be matched against paths and directory trees.
///
/// `Glob`s are constructed from strings called glob expressions that resemble
/// Unix paths consisting of nominal components delimited by separators. Glob
/// expressions support various patterns that match and capture specified text
/// in a path. These patterns can be used to match individual paths and to match
/// and walk directory trees.
///
/// # Examples
///
/// A `Glob` can be used to determine if a path matches a pattern via the
/// [`Pattern`] trait.
///
/// ```rust
/// use wax::{Glob, Pattern};
///
/// let glob = Glob::new("*.png").unwrap();
/// assert!(glob.is_match("apple.png"));
/// ```
///
/// Patterns form captures, which can be used to isolate matching sub-text.
///
/// ```rust
/// use wax::{CandidatePath, Glob, Pattern};
///
/// let glob = Glob::new("**/{*.{go,rs}}").unwrap();
/// let candidate = CandidatePath::from("src/lib.rs");
/// assert_eq!("lib.rs", glob.matched(&candidate).unwrap().get(2).unwrap());
/// ```
///
/// To match a `Glob` against a directory tree, the [`walk`] function can be
/// used to get an iterator over matching paths.
///
/// ```rust,no_run
/// use wax::Glob;
///
/// let glob = Glob::new("**/*.(?i){jpg,jpeg}").unwrap();
/// for entry in glob.walk("./Pictures") {
///     let entry = entry.unwrap();
///     println!("JPEG: {:?}", entry.path());
/// }
/// ```
///
/// [`Pattern`]: crate::Pattern
/// [`walk`]: crate::Glob::walk
#[derive(Clone, Debug)]
pub struct Glob<'t> {
    pub(crate) tokenized: Tokenized<'t>,
    pub(crate) regex: Regex,
}

impl<'t> Glob<'t> {
    fn compile<T>(tokens: impl IntoIterator<Item = T>) -> Result<Regex, CompileError>
    where
        T: Borrow<Token<'t>>,
    {
        encode::compile(tokens)
    }

    // TODO: Document pattern syntax in the crate documentation and refer to it
    //       here.
    /// Constructs a [`Glob`] from a glob expression.
    ///
    /// A glob expression is UTF-8 encoded text that resembles a Unix path
    /// consisting of nominal components delimited by separators and patterns
    /// that can be matched against native paths.
    ///
    /// # Errors
    ///
    /// Returns an error if the glob expression could not be parsed or is
    /// malformed. See the documentation for [`ParseError`] and [`RuleError`].
    ///
    /// [`Glob`]: crate::Glob
    /// [`ParseError`]: crate::ParseError
    /// [`RuleError`]: crate::RuleError
    pub fn new(expression: &'t str) -> Result<Self, GlobError<'t>> {
        let tokenized = parse_and_check(expression)?;
        let regex = Glob::compile(tokenized.tokens())?;
        Ok(Glob { tokenized, regex })
    }

    /// Constructs a [`Glob`] from a glob expression with diagnostics.
    ///
    /// This function is the same as [`Glob::new`], but additionally returns
    /// detailed diagnostics on both success and failure.
    ///
    /// See [`Glob::diagnostics`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use wax::{DiagnosticResultExt as _, Glob};
    ///
    /// let result = Glob::diagnosed("(?i)readme.{md,mkd,markdown}");
    /// for diagnostic in result.diagnostics() {
    ///     eprintln!("{}", diagnostic);
    /// }
    /// if let Some(glob) = result.ok_value() { /* ... */ }
    /// ```
    ///
    /// [`Glob`]: crate::Glob
    /// [`Glob::diagnostics`]: crate::Glob::diagnostics
    /// [`Glob::new`]: crate::Glob::new
    #[cfg(feature = "diagnostics-report")]
    #[cfg_attr(docsrs, doc(cfg(feature = "diagnostics-report")))]
    pub fn diagnosed(expression: &'t str) -> DiagnosticResult<'t, Self> {
        parse_and_diagnose(expression).and_then_diagnose(|tokenized| {
            Glob::compile(tokenized.tokens())
                .into_error_diagnostic()
                .map_value(|regex| Glob { tokenized, regex })
        })
    }

    /// Partitions a [`Glob`] into an invariant [`PathBuf`] prefix and variant
    /// [`Glob`] postfix.
    ///
    /// The invariant prefix contains no glob patterns nor other variant
    /// components and therefore can be interpreted as a native path. The
    /// [`Glob`] postfix is variant and contains the remaining components that
    /// follow the prefix. For example, the glob expression `.local/**/*.log`
    /// would produce the path `.local` and glob `**/*.log`. It is possible for
    /// either partition to be empty.
    ///
    /// Literal components may be considered variant if they contain characters
    /// with casing and the configured case sensitivity differs from the target
    /// platform's file system. For example, the case-insensitive literal
    /// expression `(?i)photos` is considered variant on Unix and invariant on
    /// Windows, because the literal `photos` resolves differently in Unix file
    /// system APIs.
    ///
    /// Partitioning a [`Glob`] allows any invariant prefix to be used as a
    /// native path to establish a working directory or to interpret semantic
    /// components that are not recognized by globs, such as parent directory
    /// `..` components.
    ///
    /// Partitioned [`Glob`]s are never rooted. If the glob expression has a
    /// root component, then it is always included in the invariant [`PathBuf`]
    /// prefix.
    ///
    /// # Examples
    ///
    /// To match files in a directory tree while respecting semantic components
    /// like `..` on platforms that support it, the invariant prefix can be
    /// applied to a working directory. In the following example, [`walk`] reads
    /// and therefore resolves the path `./../site/img`, respecting the meaning
    /// of the `.` and `..` components.
    ///
    /// ```rust,no_run
    /// use std::path::Path;
    /// use wax::Glob;
    ///
    /// let directory = Path::new("."); // Working directory.
    /// let (prefix, glob) = Glob::new("../site/img/*.{jpg,png}").unwrap().partition();
    /// for entry in glob.walk(directory.join(prefix)) {
    ///     // ...
    /// }
    /// ```
    ///
    /// To match paths against a [`Glob`] while respecting semantic components,
    /// the invariant prefix and candidate path can be canonicalized. The
    /// following example canonicalizes both the working directory joined with
    /// the prefix as well as the candidate path and then attempts to match the
    /// [`Glob`] if the candidate path contains the prefix.
    ///
    /// ```rust,no_run
    /// use dunce; // Avoids UNC paths on Windows.
    /// use std::path::Path;
    /// use wax::{Glob, Pattern};
    ///
    /// let path: &Path = /* ... */ // Candidate path.
    /// # Path::new("");
    ///     
    /// let directory = Path::new("."); // Working directory.
    /// let (prefix, glob) = Glob::new("../../src/**").unwrap().partition();
    /// let prefix = dunce::canonicalize(directory.join(&prefix)).unwrap();
    /// if dunce::canonicalize(path)
    ///     .unwrap()
    ///     .strip_prefix(&prefix)
    ///     .map(|path| glob.is_match(path))
    ///     .unwrap_or(false)
    /// {
    ///     // ...
    /// }
    /// ```
    ///
    /// The above examples illustrate particular approaches, but the invariant
    /// prefix can be used to interact with native paths as needed for a given
    /// application.
    ///
    /// [`Glob`]: crate::Glob
    /// [`ParseError`]: crate::ParseError
    /// [`PathBuf`]: std::path::PathBuf
    /// [`RuleError`]: crate::RuleError
    /// [`walk`]: crate::Glob::walk
    pub fn partition(self) -> (PathBuf, Self) {
        let Glob { tokenized, .. } = self;
        let (prefix, tokenized) = tokenized.partition();
        let regex = Glob::compile(tokenized.tokens()).expect("failed to compile partitioned glob");
        (prefix, Glob { tokenized, regex })
    }

    /// Clones any borrowed data into an owning instance.
    pub fn into_owned(self) -> Glob<'static> {
        let Glob { tokenized, regex } = self;
        Glob {
            tokenized: tokenized.into_owned(),
            regex,
        }
    }

    /// Gets an iterator over matching files in a directory tree.
    ///
    /// This function matches a [`Glob`] against an entire directory tree,
    /// returning each matching file as a [`WalkEntry`]. [`Glob`]s are the only
    /// patterns that support this operation; it is not possible to match
    /// combinators over directory trees.
    ///
    /// As with [`Path::join`] and [`PathBuf::push`], the base directory can be
    /// escaped or overridden by rooted [`Glob`]s. In many cases, the current
    /// working directory `.` is an appropriate base directory and will be
    /// intuitively ignored if the [`Glob`] is rooted, such as in
    /// `/mnt/media/**/*.mp4`. The [`has_root`] function can be used to check if
    /// a [`Glob`] is rooted.
    ///
    /// This function uses the default [`WalkBehavior`]. To configure the
    /// behavior of the traversal, see [`Glob::walk_with_behavior`].
    ///
    /// Unlike functions in [`Pattern`], **this operation is semantic and
    /// interacts with the file system**.
    ///
    /// # Examples
    ///
    /// ```rust,no_run
    /// use wax::Glob;
    ///
    /// let glob = Glob::new("**/*.(?i){jpg,jpeg}").unwrap();
    /// for entry in glob.walk("./Pictures") {
    ///     let entry = entry.unwrap();
    ///     println!("JPEG: {:?}", entry.path());
    /// }
    /// ```
    ///
    /// Because [`Glob`]s do not support general negations, the [`not`] iterator
    /// adaptor can be used when walking a directory tree to filter
    /// [`WalkEntry`]s using arbitary patterns. **This should be preferred over
    /// external iterator filtering, because it does not traverse directory
    /// trees that match terminal negations.**
    ///
    /// ```rust,no_run
    /// use wax::Glob;
    ///
    /// let glob = Glob::new("**/*.(?i){jpg,jpeg,png}").unwrap();
    /// for entry in glob
    ///     .walk("./Pictures")
    ///     .not(["**/(i?){background<s:0,1>,wallpaper<s:0,1>}/**"])
    ///     .unwrap()
    /// {
    ///     let entry = entry.unwrap();
    ///     println!("{:?}", entry.path());
    /// }
    /// ```
    ///
    /// [`Glob`]: crate::Glob
    /// [`Glob::walk_with_behavior`]: crate::Glob::walk_with_behavior
    /// [`has_root`]: crate::Glob::has_root
    /// [`not`]: crate::Walk::not
    /// [`Path::join`]: std::path::Path::join
    /// [`PathBuf::push`]: std::path::PathBuf::push
    /// [`Pattern`]: crate::Pattern
    /// [`WalkBehavior`]: crate::WalkBehavior
    /// [`WalkEntry`]: crate::WalkEntry
    pub fn walk(&self, directory: impl AsRef<Path>) -> Walk {
        self.walk_with_behavior(directory, WalkBehavior::default())
    }

    /// Gets an iterator over matching files in a directory tree.
    ///
    /// This function is the same as [`Glob::walk`], but it additionally accepts
    /// a [`WalkBehavior`]. This can be used to configure how the traversal
    /// interacts with symbolic links, the maximum depth from the root, etc.
    ///
    /// Depth is relative to the root directory of the traversal, which is
    /// determined by joining the given path and any invariant prefix of the
    /// [`Glob`]. See [`Walk::root`].
    ///
    /// # Examples
    ///
    /// ```rust,no_run
    /// use wax::{Glob, WalkBehavior};
    ///
    /// let glob = Glob::new("**/*.(?i){jpg,jpeg}").unwrap();
    /// for entry in glob.walk_with_behavior("./Pictures", WalkBehavior::default()) {
    ///     let entry = entry.unwrap();
    ///     println!("JPEG: {:?}", entry.path());
    /// }
    /// ```
    ///
    /// By default, symbolic links are read as normal files and their targets
    /// are ignored. To follow symbolic links and traverse any directories that
    /// they reference, specify a [`LinkBehavior`].
    ///
    /// ```rust,no_run
    /// use wax::{Glob, LinkBehavior};
    ///
    /// let glob = Glob::new("**/*.txt").unwrap();
    /// for entry in glob.walk_with_behavior("/var/log", LinkBehavior::ReadTarget) {
    ///     let entry = entry.unwrap();
    ///     println!("Log: {:?}", entry.path());
    /// }
    /// ```
    ///
    /// [`Glob`]: crate::Glob
    /// [`Glob::walk`]: crate::Glob::walk
    /// [`LinkBehavior`]: crate::LinkBehavior
    /// [`Walk::root`]: crate::Walk::root
    /// [`WalkBehavior`]: crate::WalkBehavior
    pub fn walk_with_behavior(
        &self,
        directory: impl AsRef<Path>,
        behavior: impl Into<WalkBehavior>,
    ) -> Walk {
        walk::walk(self, directory, behavior)
    }

    /// Gets non-error [`Diagnostic`]s.
    ///
    /// This function requires a receiving [`Glob`] and so does not report
    /// error-level [`Diagnostic`]s. It can be used to get non-error diagnostics
    /// after constructing or [partitioning] a [`Glob`].
    ///
    /// See [`Glob::diagnosed`].
    ///
    /// [`Diagnostic`]: miette::Diagnostic
    /// [`Glob`]: crate::Glob
    /// [`Glob::diagnosed`]: crate::Glob::diagnosed
    ///
    /// [partitioning]: crate::Glob::partition
    #[cfg(feature = "diagnostics-report")]
    #[cfg_attr(docsrs, doc(cfg(feature = "diagnostics-report")))]
    pub fn diagnostics(&self) -> impl Iterator<Item = Box<dyn Diagnostic + '_>> {
        report::diagnostics(&self.tokenized)
    }

    /// Gets metadata for capturing sub-expressions.
    ///
    /// This function returns an iterator over capturing tokens, which describe
    /// the index and location within the glob expression of sub-expressions
    /// that capture matched text. For example, in the expression `src/**/*.rs`,
    /// both `**` and `*` form captures.
    #[cfg(feature = "diagnostics-inspect")]
    #[cfg_attr(docsrs, doc(cfg(feature = "diagnostics-inspect")))]
    pub fn captures(&self) -> impl '_ + Clone + Iterator<Item = CapturingToken> {
        inspect::captures(self.tokenized.tokens())
    }

    /// Returns `true` if the glob is rooted.
    ///
    /// As with Unix paths, a glob expression is rooted if it begins with a
    /// separator `/`. Patterns may also root an expression, such as
    /// `</root:1,>`.
    pub fn has_root(&self) -> bool {
        self.tokenized
            .tokens()
            .first()
            .map_or(false, Token::has_root)
    }

    /// Returns `true` if the glob has literals that have non-nominal semantics
    /// on the target platform.
    ///
    /// The most notable semantic literals are the relative path components `.`
    /// and `..`, which refer to a current and parent directory on Unix and
    /// Windows operating systems, respectively. These are interpreted as
    /// literals in glob expressions, and so only match paths that contain these
    /// exact nominal components and never paths that consider relative
    /// relationships.
    ///
    /// See [`Glob::partition`].
    ///
    /// [`Glob::partition`]: crate::Glob::partition
    pub fn has_semantic_literals(&self) -> bool {
        token::literals(self.tokenized.tokens()).any(|(_, literal)| literal.is_semantic_literal())
    }
}

impl FromStr for Glob<'static> {
    type Err = GlobError<'static>;

    fn from_str(expression: &str) -> Result<Self, Self::Err> {
        Glob::new(expression)
            .map(Glob::into_owned)
            .map_err(GlobError::into_owned)
    }
}

impl<'t> IntoTokens<'t> for Glob<'t> {
    type Annotation = Annotation;

    fn into_tokens(self) -> Vec<Token<'t, Self::Annotation>> {
        let Glob { tokenized, .. } = self;
        tokenized.into_tokens()
    }
}

impl<'t> Pattern<'t> for Glob<'t> {
    fn is_match<'p>(&self, path: impl Into<CandidatePath<'p>>) -> bool {
        let path = path.into();
        self.regex.is_match(path.as_ref())
    }

    fn matched<'p>(&self, path: &'p CandidatePath<'_>) -> Option<MatchedText<'p>> {
        self.regex.captures(path.as_ref()).map(From::from)
    }

    fn variance(&self) -> Variance {
        self.tokenized.variance().into()
    }
}

impl<'t> TryFrom<&'t str> for Glob<'t> {
    type Error = GlobError<'t>;

    fn try_from(expression: &'t str) -> Result<Self, Self::Error> {
        Glob::new(expression)
    }
}

/// Combinator that matches any of its component [`Pattern`]s.
///
/// An instance of `Any` is constructed using the [`any`] function, which
/// combines multiple [`Pattern`]s for more ergonomic and efficient matching.
///
/// [`any`]: crate::any
/// [`Pattern`]: crate::Pattern
#[derive(Clone, Debug)]
pub struct Any<'t> {
    pub(crate) token: Token<'t, ()>,
    pub(crate) regex: Regex,
}

impl<'t> Any<'t> {
    fn compile(token: &Token<'t, ()>) -> Result<Regex, CompileError> {
        encode::compile([token])
    }
}

impl<'t> IntoTokens<'t> for Any<'t> {
    type Annotation = ();

    fn into_tokens(self) -> Vec<Token<'t, Self::Annotation>> {
        let Any { token, .. } = self;
        vec![token]
    }
}

impl<'t> Pattern<'t> for Any<'t> {
    fn is_match<'p>(&self, path: impl Into<CandidatePath<'p>>) -> bool {
        let path = path.into();
        self.regex.is_match(path.as_ref())
    }

    fn matched<'p>(&self, path: &'p CandidatePath<'_>) -> Option<MatchedText<'p>> {
        self.regex.captures(path.as_ref()).map(From::from)
    }

    fn variance(&self) -> Variance {
        self.token.variance::<InvariantText>().into()
    }
}

// TODO: It may be useful to use dynamic dispatch via `dyn Pattern` and an
//       object safe `ToTokens` trait instead. This allows for a variety of
//       types to be combined in an `any` call and would be especially useful if
//       additional combinators are introduced (namely a `Not` combinator, as
//       `All` is a bit odd and not very useful in this context.
/// Combinator that emits a [`Pattern`] that matches if any of its input
/// [`Pattern`]s match.
///
/// This function accepts an [`IntoIterator`] with items that can be converted
/// into a [`Pattern`] type. The output [`Any`] implements [`Pattern`] by
/// matching any of its component [`Pattern`]s. [`Any`] is often more ergonomic
/// and efficient than matching against multiple [`Glob`]s or other
/// [`Pattern`]s. Moreover, because `any` accepts any type that can be converted
/// into a [`Pattern`], it is possible to combine opaque patterns from foreign
/// code.
///
/// [`Any`] groups all captures and therefore only exposes the complete text of
/// a match. It is not possible to index a particular capturing token in the
/// component patterns.
///
/// # Examples
///
/// To match a path against multiple patterns, the patterns can first be
/// combined into an [`Any`].
///
/// ```rust
/// use wax::{Glob, Pattern};
///
/// let any = wax::any::<Glob, _>([
///     "src/**/*.rs",
///     "tests/**/*.rs",
///     "doc/**/*.md",
///     "pkg/**/PKGBUILD",
/// ])
/// .unwrap();
/// if any.is_match("src/lib.rs") { /* ... */ }
/// ```
///
/// Opaque patterns can also be combined, such as [`Glob`]s from foreign code.
///
/// ```rust
/// use wax::{Glob, GlobError, Pattern};
///
/// fn unknown() -> Result<Glob<'static>, GlobError<'static>> {
///     /* ... */
///     # Glob::new("")
/// }
///
/// let known = Glob::new("**/*.txt").unwrap();
/// let unknown = unknown().unwrap();
/// if wax::any::<Glob, _>([known, unknown])
///     .unwrap()
///     .is_match("README.md")
/// { /* ... */ }
/// ```
///
/// # Errors
///
/// Returns an error if any of the inputs could not be converted into the target
/// [`Pattern`] type `P`. If the inputs are of type `P`, then this function is
/// infallible.
///
/// [`Any`]: crate::Any
/// [`Glob`]: crate::Glob
/// [`IntoIterator`]: std::iter::IntoIterator
/// [`Pattern`]: crate::Pattern
pub fn any<'t, P, I>(patterns: I) -> Result<Any<'t>, GlobError<'t>>
where
    GlobError<'t>: From<<I::Item as TryInto<P>>::Error>,
    P: Pattern<'t>,
    I: IntoIterator,
    I::Item: TryInto<P>,
{
    let tokens = patterns
        .into_iter()
        .map(TryInto::try_into)
        .map_ok(|pattern| {
            pattern
                .into_tokens()
                .into_iter()
                .map(Token::unannotate)
                .collect::<Vec<_>>()
        })
        .collect::<Result<Vec<_>, _>>()?;
    let token = token::any(tokens);
    let regex = Any::compile(&token)?;
    Ok(Any { token, regex })
}

/// Returns `true` if a path matches a glob expression.
///
/// This function directly matches an expression without exposing an
/// intermediate [`Glob`]. Prefer [`Glob::is_match`] if an expression is matched
/// more than once. The given path must be convertible into a [`CandidatePath`].
///
/// # Errors
///
/// Returns an error if the glob expression could not be parsed or is
/// malformed. See the documentation for [`ParseError`] and [`RuleError`].
///
/// [`CandidatePath`]: crate::CandidatePath
/// [`Glob`]: crate::Glob
/// [`Glob::is_match`]: crate::Glob::is_match
/// [`ParseError`]: crate::ParseError
/// [`RuleError`]: crate::RuleError
pub fn is_match<'p>(
    expression: &str,
    path: impl Into<CandidatePath<'p>>,
) -> Result<bool, GlobError> {
    let glob = Glob::new(expression)?;
    Ok(glob.is_match(path))
}

/// Gets text in a [`CandidatePath`] that matches a glob expression.
///
/// This function directly matches an expression without exposing an
/// intermediate [`Glob`]. Prefer [`Glob::matched`] if an expression is matched
/// more than once. Returns `None` if the [`CandidatePath`] does not match
/// expression.
///
/// # Errors
///
/// Returns an error if the glob expression could not be parsed or is
/// malformed. See the documentation for [`ParseError`] and [`RuleError`].
///
/// # Examples
///
/// ```rust
/// use wax::CandidatePath;
///
/// let expression = "**/(?i)textures/*-<[0-9]:2>px.{png,tiff}";
/// let path = CandidatePath::from("data/textures/stone-64px.png");
/// if let Some(matched) = wax::matched(expression, &path).unwrap() { /* ... */ }
/// ```
///
/// [`CandidatePath`]: crate::CandidatePath
/// [`Glob`]: crate::Glob
/// [`Glob::matched`]: crate::Glob::matched
/// [`ParseError`]: crate::ParseError
/// [`RuleError`]: crate::RuleError
pub fn matched<'i, 'p>(
    expression: &'i str,
    path: &'p CandidatePath<'_>,
) -> Result<Option<MatchedText<'p>>, GlobError<'i>> {
    let glob = Glob::new(expression)?;
    Ok(glob.matched(path))
}

/// Gets an iterator over matching files in a directory tree.
///
/// This function matches a glob expression against an entire directory tree,
/// returning each matching file as a [`WalkEntry`]. The expression is matched
/// directly without exposing an intermediate [`Glob`]. Prefer [`Glob::walk`] if
/// an expression is matched more than once.
///
/// # Errors
///
/// Returns an error if the glob expression could not be parsed or is malformed.
/// See the documentation for [`ParseError`] and [`RuleError`].
///
/// # Examples
///
/// ```rust,no_run
/// for entry in wax::walk("**/*.(?i){jpg,jpeg}", "./Pictures").unwrap() {
///     let entry = entry.unwrap();
///     println!("JPEG: {:?}", entry.path());
/// }
/// ```
///
/// [`Glob`]: crate::Glob
/// [`ParseError`]: crate::ParseError
/// [`RuleError`]: crate::RuleError
/// [`WalkEntry`]: crate::WalkEntry
pub fn walk(expression: &str, directory: impl AsRef<Path>) -> Result<Walk<'static>, GlobError> {
    walk_with_behavior(expression, directory, WalkBehavior::default())
}

/// Gets an iterator over matching files in a directory tree.
///
/// This function is the same as [`walk`], but it additionally accepts a
/// [`WalkBehavior`]. This can be used to configure how the traversal interacts
/// with symbolic links, the maximum depth from the root, etc.
///
/// # Errors
///
/// Returns an error if the glob expression could not be parsed or is malformed.
/// See the documentation for [`ParseError`] and [`RuleError`].
///
/// # Examples
///
/// ```rust,no_run
/// use wax::LinkBehavior;
///
/// for entry in wax::walk_with_behavior("**/*.txt", "/var/log", LinkBehavior::ReadTarget).unwrap()
/// {
///     let entry = entry.unwrap();
///     println!("Log: {:?}", entry.path());
/// }
/// ```
///
/// [`ParseError`]: crate::ParseError
/// [`RuleError`]: crate::RuleError
/// [`walk`]: crate::walk()
/// [`WalkBehavior`]: crate::WalkBehavior
pub fn walk_with_behavior(
    expression: &str,
    directory: impl AsRef<Path>,
    behavior: impl Into<WalkBehavior>,
) -> Result<Walk<'static>, GlobError> {
    let (prefix, glob) = Glob::new(expression)?.partition();
    Ok(glob
        .walk_with_behavior(directory.as_ref().join(prefix), behavior)
        .into_owned())
}

/// Escapes text as a literal glob expression.
///
/// This function escapes any and all meta-characters in the given string, such
/// that all text is interpreted as a literal or separator when read as a glob
/// expression.
///
/// # Examples
///
/// This function can be used to escape opaque strings, such as a string
/// obtained from a user that must be interpreted literally.
///
/// ```rust
/// use wax::Glob;
///
/// // An opaque file name that this code does not construct.
/// let name: String = {
///     /* ... */
///     # String::from("file.txt")
/// };
///
/// // Do not allow patterns in `name`.
/// let expression = format!("{}{}", "**/", wax::escape(&name));
/// if let glob = Glob::new(&expression) { /* ... */ }
/// ```
///
/// Sometimes part of a path contains numerous meta-characters. This function
/// can be used to reliably escape them while making the unescaped part of the
/// expression a bit easier to read.
///
/// ```rust
/// use wax::Glob;
///
/// let expression = format!("{}{}", "logs/**/", wax::escape("ingest[01](L).txt"));
/// let glob = Glob::new(&expression).unwrap();
/// ```
// It is possible to call this function using a mutable reference, which may
// appear to mutate the parameter in place.
#[must_use]
pub fn escape(unescaped: &str) -> Cow<str> {
    const ESCAPE: char = '\\';

    if unescaped.chars().any(is_meta_character) {
        let mut escaped = String::new();
        for x in unescaped.chars() {
            if is_meta_character(x) {
                escaped.push(ESCAPE);
            }
            escaped.push(x);
        }
        escaped.into()
    }
    else {
        unescaped.into()
    }
}

// TODO: Is it possible for `:` and `,` to be contextual meta-characters?
/// Returns `true` if the given character is a meta-character.
///
/// This function does **not** return `true` for contextual meta-characters that
/// may only be escaped in particular contexts, such as hyphens `-` in character
/// class expressions. To detect these characters, use
/// [`is_contextual_meta_character`].
///
/// [`is_contextual_meta_character`]: crate::is_contextual_meta_character
pub const fn is_meta_character(x: char) -> bool {
    matches!(
        x,
        '?' | '*' | '$' | ':' | '<' | '>' | '(' | ')' | '[' | ']' | '{' | '}' | ','
    )
}

/// Returns `true` if the given character is a contextual meta-character.
///
/// Contextual meta-characters may only be escaped in particular contexts, such
/// as hyphens `-` in character class expressions. Elsewhere, they are
/// interpreted as literals. To detect non-contextual meta-characters, use
/// [`is_meta_character`].
///
/// [`is_meta_character`]: crate::is_meta_character
pub const fn is_contextual_meta_character(x: char) -> bool {
    matches!(x, '-')
}

fn parse_and_check(expression: &str) -> Result<Tokenized, GlobError> {
    let tokenized = token::parse(expression)?;
    rule::check(&tokenized)?;
    Ok(tokenized)
}

#[cfg(feature = "diagnostics-report")]
fn parse_and_diagnose(expression: &str) -> DiagnosticResult<Tokenized> {
    token::parse(expression)
        .into_error_diagnostic()
        .and_then_diagnose(|tokenized| {
            rule::check(&tokenized)
                .into_error_diagnostic()
                .map_value(|_| tokenized)
        })
        .and_then_diagnose(|tokenized| {
            report::diagnostics(&tokenized)
                .into_non_error_diagnostic()
                .map_value(|_| tokenized)
        })
}

// TODO: Construct paths from components in tests. In practice, using string
//       literals works, but is technically specific to platforms that support
//       `/` as a separator.
#[cfg(test)]
mod tests {
    use std::path::Path;

    use crate::{Any, CandidatePath, Glob, GlobError, Pattern};

    #[test]
    fn escape() {
        assert_eq!(crate::escape(""), "");
        assert_eq!(
            crate::escape("?*$:<>()[]{},"),
            "\\?\\*\\$\\:\\<\\>\\(\\)\\[\\]\\{\\}\\,",
        );
        assert_eq!(crate::escape("/usr/local/lib"), "/usr/local/lib");
        assert_eq!(
            crate::escape("record[D00,00].txt"),
            "record\\[D00\\,00\\].txt",
        );
        assert_eq!(
            crate::escape("Do You Remember Love?.mp4"),
            "Do You Remember Love\\?.mp4",
        );
        assert_eq!(crate::escape("左{}右"), "左\\{\\}右");
        assert_eq!(crate::escape("*中*"), "\\*中\\*");
    }

    #[test]
    fn build_glob_with_eager_zom_tokens() {
        Glob::new("*").unwrap();
        Glob::new("a/*").unwrap();
        Glob::new("*a").unwrap();
        Glob::new("a*").unwrap();
        Glob::new("a*b").unwrap();
        Glob::new("/*").unwrap();
    }

    #[test]
    fn build_glob_with_lazy_zom_tokens() {
        Glob::new("$").unwrap();
        Glob::new("a/$").unwrap();
        Glob::new("$a").unwrap();
        Glob::new("a$").unwrap();
        Glob::new("a$b").unwrap();
        Glob::new("/$").unwrap();
    }

    #[test]
    fn build_glob_with_one_tokens() {
        Glob::new("?").unwrap();
        Glob::new("a/?").unwrap();
        Glob::new("?a").unwrap();
        Glob::new("a?").unwrap();
        Glob::new("a?b").unwrap();
        Glob::new("??a??b??").unwrap();
        Glob::new("/?").unwrap();
    }

    #[test]
    fn build_glob_with_one_and_zom_tokens() {
        Glob::new("?*").unwrap();
        Glob::new("*?").unwrap();
        Glob::new("*/?").unwrap();
        Glob::new("?*?").unwrap();
        Glob::new("/?*").unwrap();
        Glob::new("?$").unwrap();
    }

    #[test]
    fn build_glob_with_tree_tokens() {
        Glob::new("**").unwrap();
        Glob::new("**/").unwrap();
        Glob::new("/**").unwrap();
        Glob::new("**/a").unwrap();
        Glob::new("a/**").unwrap();
        Glob::new("**/a/**/b/**").unwrap();
        Glob::new("{**/a,b/c}").unwrap();
        Glob::new("{a/b,c/**}").unwrap();
        Glob::new("<**/a>").unwrap();
        Glob::new("<a/**>").unwrap();
    }

    #[test]
    fn build_glob_with_class_tokens() {
        Glob::new("a/[xy]").unwrap();
        Glob::new("a/[x-z]").unwrap();
        Glob::new("a/[xyi-k]").unwrap();
        Glob::new("a/[i-kxy]").unwrap();
        Glob::new("a/[!xy]").unwrap();
        Glob::new("a/[!x-z]").unwrap();
        Glob::new("a/[xy]b/c").unwrap();
    }

    #[test]
    fn build_glob_with_alternative_tokens() {
        Glob::new("a/{x?z,y$}b*").unwrap();
        Glob::new("a/{???,x$y,frob}b*").unwrap();
        Glob::new("a/{???,x$y,frob}b*").unwrap();
        Glob::new("a/{???,{x*z,y$}}b*").unwrap();
        Glob::new("a{/**/b/,/b/**/}ca{t,b/**}").unwrap();
    }

    #[test]
    fn build_glob_with_repetition_tokens() {
        Glob::new("<a:0,1>").unwrap();
        Glob::new("<a:0,>").unwrap();
        Glob::new("<a:2>").unwrap();
        Glob::new("<a:>").unwrap();
        Glob::new("<a>").unwrap();
        Glob::new("<a<b:0,>:0,>").unwrap();
        // Rooted repetitions are accepted if the lower bound is one or greater.
        Glob::new("</root:1,>").unwrap();
        Glob::new("<[!.]*/:0,>[!.]*").unwrap();
    }

    #[test]
    fn build_glob_with_literal_escaped_wildcard_tokens() {
        Glob::new("a/b\\?/c").unwrap();
        Glob::new("a/b\\$/c").unwrap();
        Glob::new("a/b\\*/c").unwrap();
        Glob::new("a/b\\*\\*/c").unwrap();
    }

    #[test]
    fn build_glob_with_class_escaped_wildcard_tokens() {
        Glob::new("a/b[?]/c").unwrap();
        Glob::new("a/b[$]/c").unwrap();
        Glob::new("a/b[*]/c").unwrap();
        Glob::new("a/b[*][*]/c").unwrap();
    }

    #[test]
    fn build_glob_with_literal_escaped_alternative_tokens() {
        Glob::new("a/\\{\\}/c").unwrap();
        Glob::new("a/{x,y\\,,z}/c").unwrap();
    }

    #[test]
    fn build_glob_with_class_escaped_alternative_tokens() {
        Glob::new("a/[{][}]/c").unwrap();
        Glob::new("a/{x,y[,],z}/c").unwrap();
    }

    #[test]
    fn build_glob_with_literal_escaped_class_tokens() {
        Glob::new("a/\\[a-z\\]/c").unwrap();
        Glob::new("a/[\\[]/c").unwrap();
        Glob::new("a/[\\]]/c").unwrap();
        Glob::new("a/[a\\-z]/c").unwrap();
    }

    #[test]
    fn build_glob_with_flags() {
        Glob::new("(?i)a/b/c").unwrap();
        Glob::new("(?-i)a/b/c").unwrap();
        Glob::new("a/(?-i)b/c").unwrap();
        Glob::new("a/b/(?-i)c").unwrap();
        Glob::new("(?i)a/(?-i)b/(?i)c").unwrap();
    }

    #[test]
    fn build_any_combinator() {
        crate::any::<Glob, _>([
            Glob::new("src/**/*.rs").unwrap(),
            Glob::new("doc/**/*.md").unwrap(),
            Glob::new("pkg/**/PKGBUILD").unwrap(),
        ])
        .unwrap();
        crate::any::<Glob, _>(["src/**/*.rs", "doc/**/*.md", "pkg/**/PKGBUILD"]).unwrap();
    }

    #[test]
    fn build_any_nested_combinator() {
        crate::any::<Any, _>([
            crate::any::<Glob, _>(["a/b", "c/d"]).unwrap(),
            crate::any::<Glob, _>(["{e,f,g}", "{h,i}"]).unwrap(),
        ])
        .unwrap();
    }

    #[test]
    fn reject_glob_with_invalid_separator_tokens() {
        assert!(Glob::new("//a").is_err());
        assert!(Glob::new("a//b").is_err());
        assert!(Glob::new("a/b//").is_err());
        assert!(Glob::new("a//**").is_err());
        assert!(Glob::new("{//}a").is_err());
        assert!(Glob::new("{**//}").is_err());
    }

    #[test]
    fn reject_glob_with_adjacent_tree_or_zom_tokens() {
        assert!(Glob::new("***").is_err());
        assert!(Glob::new("****").is_err());
        assert!(Glob::new("**/**").is_err());
        assert!(Glob::new("a{**/**,/b}").is_err());
        assert!(Glob::new("**/*/***").is_err());
        assert!(Glob::new("**$").is_err());
        assert!(Glob::new("**/$**").is_err());
        assert!(Glob::new("{*$}").is_err());
        assert!(Glob::new("<*$:1,>").is_err());
    }

    #[test]
    fn reject_glob_with_tree_adjacent_literal_tokens() {
        assert!(Glob::new("**a").is_err());
        assert!(Glob::new("a**").is_err());
        assert!(Glob::new("a**b").is_err());
        assert!(Glob::new("a*b**").is_err());
        assert!(Glob::new("**/**a/**").is_err());
    }

    #[test]
    fn reject_glob_with_adjacent_one_tokens() {
        assert!(Glob::new("**?").is_err());
        assert!(Glob::new("?**").is_err());
        assert!(Glob::new("?**?").is_err());
        assert!(Glob::new("?*?**").is_err());
        assert!(Glob::new("**/**?/**").is_err());
    }

    #[test]
    fn reject_glob_with_unescaped_meta_characters_in_class_tokens() {
        assert!(Glob::new("a/[a-z-]/c").is_err());
        assert!(Glob::new("a/[-a-z]/c").is_err());
        assert!(Glob::new("a/[-]/c").is_err());
        // NOTE: Without special attention to escaping and character parsing,
        //       this could be mistakenly interpreted as an empty range over the
        //       character `-`. This should be rejected.
        assert!(Glob::new("a/[---]/c").is_err());
        assert!(Glob::new("a/[[]/c").is_err());
        assert!(Glob::new("a/[]]/c").is_err());
    }

    #[test]
    fn reject_glob_with_invalid_alternative_zom_tokens() {
        assert!(Glob::new("*{okay,*}").is_err());
        assert!(Glob::new("{okay,*}*").is_err());
        assert!(Glob::new("${okay,*error}").is_err());
        assert!(Glob::new("{okay,error*}$").is_err());
        assert!(Glob::new("{*,okay}{okay,*}").is_err());
        assert!(Glob::new("{okay,error*}{okay,*error}").is_err());
    }

    #[test]
    fn reject_glob_with_invalid_alternative_tree_tokens() {
        assert!(Glob::new("{**}").is_err());
        assert!(Glob::new("slash/{**/error}").is_err());
        assert!(Glob::new("{error/**}/slash").is_err());
        assert!(Glob::new("slash/{okay/**,**/error}").is_err());
        assert!(Glob::new("{**/okay,error/**}/slash").is_err());
        assert!(Glob::new("{**/okay,prefix{error/**}}/slash").is_err());
        assert!(Glob::new("{**/okay,slash/{**/error}}postfix").is_err());
        assert!(Glob::new("{error/**}{okay,**/error").is_err());
    }

    #[test]
    fn reject_glob_with_invalid_alternative_separator_tokens() {
        assert!(Glob::new("/slash/{okay,/error}").is_err());
        assert!(Glob::new("{okay,error/}/slash").is_err());
        assert!(Glob::new("slash/{okay,/error/,okay}/slash").is_err());
        assert!(Glob::new("{okay,error/}{okay,/error}").is_err());
    }

    #[test]
    fn reject_glob_with_rooted_alternative_tokens() {
        assert!(Glob::new("{okay,/}").is_err());
        assert!(Glob::new("{okay,/**}").is_err());
        assert!(Glob::new("{okay,/error}").is_err());
        assert!(Glob::new("{okay,/**/error}").is_err());
    }

    #[test]
    fn reject_glob_with_invalid_repetition_bounds_tokens() {
        assert!(Glob::new("<a/:0,0>").is_err());
    }

    #[test]
    fn reject_glob_with_invalid_repetition_zom_tokens() {
        assert!(Glob::new("<*:0,>").is_err());
        assert!(Glob::new("<a/*:0,>*").is_err());
        assert!(Glob::new("*<*a:0,>").is_err());
    }

    #[test]
    fn reject_glob_with_invalid_repetition_tree_tokens() {
        assert!(Glob::new("<**:0,>").is_err());
        assert!(Glob::new("</**/a/**:0,>").is_err());
        assert!(Glob::new("<a/**:0,>/").is_err());
        assert!(Glob::new("/**</a:0,>").is_err());
    }

    #[test]
    fn reject_glob_with_invalid_repetition_separator_tokens() {
        assert!(Glob::new("</:0,>").is_err());
        assert!(Glob::new("</a/:0,>").is_err());
        assert!(Glob::new("<a/:0,>/").is_err());
    }

    // Rooted repetitions are rejected if their lower bound is zero; any other
    // lower bound is accepted.
    #[test]
    fn reject_glob_with_rooted_repetition_tokens() {
        assert!(Glob::new("</root:0,>maybe").is_err());
        assert!(Glob::new("</root>").is_err());
    }

    #[test]
    fn reject_glob_with_oversized_invariant_repetition_tokens() {
        assert!(matches!(Glob::new("<a:65536>"), Err(GlobError::Rule(_))));
        assert!(matches!(Glob::new("<long:16500>"), Err(GlobError::Rule(_))));
        assert!(matches!(
            Glob::new("a<long:16500>b"),
            Err(GlobError::Rule(_)),
        ));
        assert!(matches!(
            Glob::new("{<a:65536>,<long:16500>}"),
            Err(GlobError::Rule(_)),
        ));
    }

    #[test]
    fn reject_glob_with_invalid_flags() {
        assert!(Glob::new("(?)a").is_err());
        assert!(Glob::new("(?-)a").is_err());
        assert!(Glob::new("()a").is_err());
    }

    #[test]
    fn reject_glob_with_adjacent_tokens_through_flags() {
        assert!(Glob::new("/(?i)/").is_err());
        assert!(Glob::new("$(?i)$").is_err());
        assert!(Glob::new("*(?i)*").is_err());
        assert!(Glob::new("**(?i)?").is_err());
        assert!(Glob::new("a(?i)**").is_err());
        assert!(Glob::new("**(?i)a").is_err());
    }

    #[test]
    fn reject_glob_with_oversized_program() {
        assert!(matches!(
            Glob::new("<a*:1000000>"),
            Err(GlobError::Compile(_))
        ));
    }

    #[test]
    fn reject_any_combinator() {
        assert!(crate::any::<Glob, _>(["{a,b,c}", "{d, e}", "f/{g,/error,h}",]).is_err())
    }

    #[test]
    fn match_glob_with_empty_expression() {
        let glob = Glob::new("").unwrap();

        assert!(glob.is_match(Path::new("")));

        assert!(!glob.is_match(Path::new("abc")));
    }

    #[test]
    fn match_glob_with_only_invariant_tokens() {
        let glob = Glob::new("a/b").unwrap();

        assert!(glob.is_match(Path::new("a/b")));

        assert!(!glob.is_match(Path::new("aa/b")));
        assert!(!glob.is_match(Path::new("a/bb")));
        assert!(!glob.is_match(Path::new("a/b/c")));

        // There are no variant tokens with which to capture, but the matched
        // text should always be available.
        assert_eq!(
            "a/b",
            glob.matched(&CandidatePath::from(Path::new("a/b")))
                .unwrap()
                .complete(),
        );
    }

    #[test]
    fn match_glob_with_tree_tokens() {
        let glob = Glob::new("a/**/b").unwrap();

        assert!(glob.is_match(Path::new("a/b")));
        assert!(glob.is_match(Path::new("a/x/b")));
        assert!(glob.is_match(Path::new("a/x/y/z/b")));

        assert!(!glob.is_match(Path::new("a")));
        assert!(!glob.is_match(Path::new("b/a")));

        assert_eq!(
            "x/y/z/",
            glob.matched(&CandidatePath::from(Path::new("a/x/y/z/b")))
                .unwrap()
                .get(1)
                .unwrap(),
        );
    }

    #[test]
    fn match_glob_with_tree_and_zom_tokens() {
        let glob = Glob::new("**/*.ext").unwrap();

        assert!(glob.is_match(Path::new("file.ext")));
        assert!(glob.is_match(Path::new("a/file.ext")));
        assert!(glob.is_match(Path::new("a/b/file.ext")));

        let path = CandidatePath::from(Path::new("a/file.ext"));
        let matched = glob.matched(&path).unwrap();
        assert_eq!("a/", matched.get(1).unwrap());
        assert_eq!("file", matched.get(2).unwrap());
    }

    #[test]
    fn match_glob_with_eager_and_lazy_zom_tokens() {
        let glob = Glob::new("$-*.*").unwrap();

        assert!(glob.is_match(Path::new("prefix-file.ext")));
        assert!(glob.is_match(Path::new("a-b-c.ext")));

        let path = CandidatePath::from(Path::new("a-b-c.ext"));
        let matched = glob.matched(&path).unwrap();
        assert_eq!("a", matched.get(1).unwrap());
        assert_eq!("b-c", matched.get(2).unwrap());
        assert_eq!("ext", matched.get(3).unwrap());
    }

    #[test]
    fn match_glob_with_class_tokens() {
        let glob = Glob::new("a/[xyi-k]/**").unwrap();

        assert!(glob.is_match(Path::new("a/x/file.ext")));
        assert!(glob.is_match(Path::new("a/y/file.ext")));
        assert!(glob.is_match(Path::new("a/j/file.ext")));

        assert!(!glob.is_match(Path::new("a/b/file.ext")));

        let path = CandidatePath::from(Path::new("a/i/file.ext"));
        let matched = glob.matched(&path).unwrap();
        assert_eq!("i", matched.get(1).unwrap());
    }

    #[test]
    fn match_glob_with_non_ascii_class_tokens() {
        let glob = Glob::new("a/[金銀]/**").unwrap();

        assert!(glob.is_match(Path::new("a/金/file.ext")));
        assert!(glob.is_match(Path::new("a/銀/file.ext")));

        assert!(!glob.is_match(Path::new("a/銅/file.ext")));

        let path = CandidatePath::from(Path::new("a/金/file.ext"));
        let matched = glob.matched(&path).unwrap();
        assert_eq!("金", matched.get(1).unwrap());
    }

    #[test]
    fn match_glob_with_literal_escaped_class_tokens() {
        let glob = Glob::new("a/[\\[\\]\\-]/**").unwrap();

        assert!(glob.is_match(Path::new("a/[/file.ext")));
        assert!(glob.is_match(Path::new("a/]/file.ext")));
        assert!(glob.is_match(Path::new("a/-/file.ext")));

        assert!(!glob.is_match(Path::new("a/b/file.ext")));

        let path = CandidatePath::from(Path::new("a/[/file.ext"));
        let matched = glob.matched(&path).unwrap();
        assert_eq!("[", matched.get(1).unwrap());
    }

    #[cfg(any(unix, windows))]
    #[test]
    fn match_glob_with_empty_class_tokens() {
        // A character class is "empty" if it only matches separators on the
        // target platform. Such a character class only matches `NUL` and so
        // effectively matches nothing.
        let glob = Glob::new("a[/]b").unwrap();

        assert!(!glob.is_match(Path::new("a/b")));
    }

    #[test]
    fn match_glob_with_alternative_tokens() {
        let glob = Glob::new("a/{x?z,y$}b/*").unwrap();

        assert!(glob.is_match(Path::new("a/xyzb/file.ext")));
        assert!(glob.is_match(Path::new("a/yb/file.ext")));

        assert!(!glob.is_match(Path::new("a/xyz/file.ext")));
        assert!(!glob.is_match(Path::new("a/y/file.ext")));
        assert!(!glob.is_match(Path::new("a/xyzub/file.ext")));

        let path = CandidatePath::from(Path::new("a/xyzb/file.ext"));
        let matched = glob.matched(&path).unwrap();
        assert_eq!("xyz", matched.get(1).unwrap());
    }

    #[test]
    fn match_glob_with_nested_alternative_tokens() {
        let glob = Glob::new("a/{y$,{x?z,?z}}b/*").unwrap();

        let path = CandidatePath::from(Path::new("a/xyzb/file.ext"));
        let matched = glob.matched(&path).unwrap();
        assert_eq!("xyz", matched.get(1).unwrap());
    }

    #[test]
    fn match_glob_with_alternative_tree_tokens() {
        let glob = Glob::new("a{/foo,/bar,/**/baz}/qux").unwrap();

        assert!(glob.is_match(Path::new("a/foo/qux")));
        assert!(glob.is_match(Path::new("a/foo/baz/qux")));
        assert!(glob.is_match(Path::new("a/foo/bar/baz/qux")));

        assert!(!glob.is_match(Path::new("a/foo/bar/qux")));
    }

    #[test]
    fn match_glob_with_alternative_repetition_tokens() {
        let glob = Glob::new("log-{<[0-9]:3>,<[0-9]:4>-<[0-9]:2>-<[0-9]:2>}.txt").unwrap();

        assert!(glob.is_match(Path::new("log-000.txt")));
        assert!(glob.is_match(Path::new("log-1970-01-01.txt")));

        assert!(!glob.is_match(Path::new("log-abc.txt")));
        assert!(!glob.is_match(Path::new("log-nope-no-no.txt")));
    }

    #[test]
    fn match_glob_with_repetition_tokens() {
        let glob = Glob::new("a/<[0-9]:6>/*").unwrap();

        assert!(glob.is_match(Path::new("a/000000/file.ext")));
        assert!(glob.is_match(Path::new("a/123456/file.ext")));

        assert!(!glob.is_match(Path::new("a/00000/file.ext")));
        assert!(!glob.is_match(Path::new("a/0000000/file.ext")));
        assert!(!glob.is_match(Path::new("a/bbbbbb/file.ext")));

        let path = CandidatePath::from(Path::new("a/999999/file.ext"));
        let matched = glob.matched(&path).unwrap();
        assert_eq!("999999", matched.get(1).unwrap());
    }

    #[test]
    fn match_glob_with_negative_repetition_tokens() {
        let glob = Glob::new("<[!.]*/>[!.]*").unwrap();

        assert!(glob.is_match(Path::new("a/b/file.ext")));

        assert!(!glob.is_match(Path::new(".a/b/file.ext")));
        assert!(!glob.is_match(Path::new("a/.b/file.ext")));
        assert!(!glob.is_match(Path::new("a/b/.file.ext")));
    }

    #[test]
    fn match_glob_with_nested_repetition_tokens() {
        let glob = Glob::new("log<-<[0-9]:3>:1,2>.txt").unwrap();

        assert!(glob.is_match(Path::new("log-000.txt")));
        assert!(glob.is_match(Path::new("log-123-456.txt")));

        assert!(!glob.is_match(Path::new("log-abc.txt")));
        assert!(!glob.is_match(Path::new("log-123-456-789.txt")));

        let path = CandidatePath::from(Path::new("log-987-654.txt"));
        let matched = glob.matched(&path).unwrap();
        assert_eq!("-987-654", matched.get(1).unwrap());
    }

    #[test]
    fn match_glob_with_repeated_alternative_tokens() {
        let glob = Glob::new("<{a,b}:1,>/**").unwrap();

        assert!(glob.is_match(Path::new("a/file.ext")));
        assert!(glob.is_match(Path::new("b/file.ext")));
        assert!(glob.is_match(Path::new("aaa/file.ext")));
        assert!(glob.is_match(Path::new("bbb/file.ext")));

        assert!(!glob.is_match(Path::new("file.ext")));
        assert!(!glob.is_match(Path::new("c/file.ext")));

        let path = CandidatePath::from(Path::new("aa/file.ext"));
        let matched = glob.matched(&path).unwrap();
        assert_eq!("aa", matched.get(1).unwrap());
    }

    #[test]
    fn match_glob_with_rooted_tree_token() {
        let glob = Glob::new("/**/{var,.var}/**/*.log").unwrap();

        assert!(glob.is_match(Path::new("/var/log/network.log")));
        assert!(glob.is_match(Path::new("/home/nobody/.var/network.log")));

        assert!(!glob.is_match(Path::new("./var/cron.log")));
        assert!(!glob.is_match(Path::new("mnt/var/log/cron.log")));

        let path = CandidatePath::from(Path::new("/var/log/network.log"));
        let matched = glob.matched(&path).unwrap();
        assert_eq!("/", matched.get(1).unwrap());
    }

    #[test]
    fn match_glob_with_flags() {
        let glob = Glob::new("(?-i)photos/**/*.(?i){jpg,jpeg}").unwrap();

        assert!(glob.is_match(Path::new("photos/flower.jpg")));
        assert!(glob.is_match(Path::new("photos/flower.JPEG")));

        assert!(!glob.is_match(Path::new("Photos/flower.jpeg")));
    }

    #[test]
    fn match_glob_with_escaped_flags() {
        let glob = Glob::new("a\\(b\\)").unwrap();

        assert!(glob.is_match(Path::new("a(b)")));
    }

    #[test]
    fn match_any_combinator() {
        let any = crate::any::<Glob, _>(["src/**/*.rs", "doc/**/*.md", "pkg/**/PKGBUILD"]).unwrap();

        assert!(any.is_match("src/lib.rs"));
        assert!(any.is_match("doc/api.md"));
        assert!(any.is_match("pkg/arch/lib-git/PKGBUILD"));

        assert!(!any.is_match("img/icon.png"));
        assert!(!any.is_match("doc/LICENSE.tex"));
        assert!(!any.is_match("pkg/lib.rs"));
    }

    #[test]
    fn partition_glob_with_variant_and_invariant_parts() {
        let (prefix, glob) = Glob::new("a/b/x?z/*.ext").unwrap().partition();

        assert_eq!(prefix, Path::new("a/b"));

        assert!(glob.is_match(Path::new("xyz/file.ext")));
        assert!(glob.is_match(Path::new("a/b/xyz/file.ext").strip_prefix(prefix).unwrap()));
    }

    #[test]
    fn partition_glob_with_only_variant_wildcard_parts() {
        let (prefix, glob) = Glob::new("x?z/*.ext").unwrap().partition();

        assert_eq!(prefix, Path::new(""));

        assert!(glob.is_match(Path::new("xyz/file.ext")));
        assert!(glob.is_match(Path::new("xyz/file.ext").strip_prefix(prefix).unwrap()));
    }

    #[test]
    fn partition_glob_with_only_invariant_literal_parts() {
        let (prefix, glob) = Glob::new("a/b").unwrap().partition();

        assert_eq!(prefix, Path::new("a/b"));

        assert!(glob.is_match(Path::new("")));
        assert!(glob.is_match(Path::new("a/b").strip_prefix(prefix).unwrap()));
    }

    #[test]
    fn partition_glob_with_variant_alternative_parts() {
        let (prefix, glob) = Glob::new("{x,z}/*.ext").unwrap().partition();

        assert_eq!(prefix, Path::new(""));

        assert!(glob.is_match(Path::new("x/file.ext")));
        assert!(glob.is_match(Path::new("z/file.ext").strip_prefix(prefix).unwrap()));
    }

    #[test]
    fn partition_glob_with_invariant_alternative_parts() {
        let (prefix, glob) = Glob::new("{a/b}/c").unwrap().partition();

        assert_eq!(prefix, Path::new("a/b/c"));

        assert!(glob.is_match(Path::new("")));
        assert!(glob.is_match(Path::new("a/b/c").strip_prefix(prefix).unwrap()));
    }

    #[test]
    fn partition_glob_with_invariant_repetition_parts() {
        let (prefix, glob) = Glob::new("</a/b:3>/c").unwrap().partition();

        assert_eq!(prefix, Path::new("/a/b/a/b/a/b/c"));

        assert!(glob.is_match(Path::new("")));
        assert!(glob.is_match(Path::new("/a/b/a/b/a/b/c").strip_prefix(prefix).unwrap()));
    }

    #[test]
    fn partition_glob_with_literal_dots_and_tree_tokens() {
        let (prefix, glob) = Glob::new("../**/*.ext").unwrap().partition();

        assert_eq!(prefix, Path::new(".."));

        assert!(glob.is_match(Path::new("xyz/file.ext")));
        assert!(glob.is_match(Path::new("../xyz/file.ext").strip_prefix(prefix).unwrap()));
    }

    #[test]
    fn partition_glob_with_rooted_tree_token() {
        let (prefix, glob) = Glob::new("/**/*.ext").unwrap().partition();

        assert_eq!(prefix, Path::new("/"));
        assert!(!glob.has_root());

        assert!(glob.is_match(Path::new("file.ext")));
        assert!(glob.is_match(Path::new("/root/file.ext").strip_prefix(prefix).unwrap()));
    }

    #[test]
    fn partition_glob_with_rooted_zom_token() {
        let (prefix, glob) = Glob::new("/*/*.ext").unwrap().partition();

        assert_eq!(prefix, Path::new("/"));
        assert!(!glob.has_root());

        assert!(glob.is_match(Path::new("root/file.ext")));
        assert!(glob.is_match(Path::new("/root/file.ext").strip_prefix(prefix).unwrap()));
    }

    #[test]
    fn partition_glob_with_rooted_literal_token() {
        let (prefix, glob) = Glob::new("/root/**/*.ext").unwrap().partition();

        assert_eq!(prefix, Path::new("/root"));
        assert!(!glob.has_root());

        assert!(glob.is_match(Path::new("file.ext")));
        assert!(glob.is_match(Path::new("/root/file.ext").strip_prefix(prefix).unwrap()));
    }

    #[test]
    fn query_glob_variance() {
        assert!(Glob::new("").unwrap().variance().is_invariant());
        assert!(Glob::new("/a/file.ext").unwrap().variance().is_invariant());
        assert!(Glob::new("/a/{file.ext}")
            .unwrap()
            .variance()
            .is_invariant());
        assert!(Glob::new("{a/b/file.ext}")
            .unwrap()
            .variance()
            .is_invariant());
        assert!(Glob::new("{a,a}").unwrap().variance().is_invariant());
        #[cfg(windows)]
        assert!(Glob::new("{a,A}").unwrap().variance().is_invariant());
        assert!(Glob::new("<a/b:2>").unwrap().variance().is_invariant());
        #[cfg(unix)]
        assert!(Glob::new("/[a]/file.ext")
            .unwrap()
            .variance()
            .is_invariant());
        #[cfg(unix)]
        assert!(Glob::new("/[a-a]/file.ext")
            .unwrap()
            .variance()
            .is_invariant());
        #[cfg(unix)]
        assert!(Glob::new("/[a-aaa-a]/file.ext")
            .unwrap()
            .variance()
            .is_invariant());

        assert!(Glob::new("/a/{b,c}").unwrap().variance().is_variant());
        assert!(Glob::new("<a/b:1,>").unwrap().variance().is_variant());
        assert!(Glob::new("/[ab]/file.ext").unwrap().variance().is_variant());
        assert!(Glob::new("**").unwrap().variance().is_variant());
        assert!(Glob::new("/a/*.ext").unwrap().variance().is_variant());
        assert!(Glob::new("/a/b*").unwrap().variance().is_variant());
        #[cfg(unix)]
        assert!(Glob::new("/a/(?i)file.ext")
            .unwrap()
            .variance()
            .is_variant());
        #[cfg(windows)]
        assert!(Glob::new("/a/(?-i)file.ext")
            .unwrap()
            .variance()
            .is_variant());
    }

    #[test]
    fn query_glob_has_root() {
        assert!(Glob::new("/root").unwrap().has_root());
        assert!(Glob::new("/**").unwrap().has_root());
        assert!(Glob::new("</root:1,>").unwrap().has_root());

        assert!(!Glob::new("").unwrap().has_root());
        // This is not rooted, because character classes may not match
        // separators. This example compiles an "empty" character class, which
        // attempts to match `NUL` and so effectively matches nothing.
        #[cfg(any(unix, windows))]
        assert!(!Glob::new("[/]root").unwrap().has_root());
        // The leading forward slash in tree tokens is meaningful. When omitted,
        // at the beginning of an expression, the resulting glob is not rooted.
        assert!(!Glob::new("**/").unwrap().has_root());
    }

    #[cfg(any(unix, windows))]
    #[test]
    fn query_glob_has_semantic_literals() {
        assert!(Glob::new("../src/**").unwrap().has_semantic_literals());
        assert!(Glob::new("*/a/../b.*").unwrap().has_semantic_literals());
        assert!(Glob::new("{a,..}").unwrap().has_semantic_literals());
        assert!(Glob::new("<a/..>").unwrap().has_semantic_literals());
        assert!(Glob::new("<a/{b,..,c}/d>").unwrap().has_semantic_literals());
        assert!(Glob::new("./*.txt").unwrap().has_semantic_literals());
    }
}
