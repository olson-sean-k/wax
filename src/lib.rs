//! Wax provides opinionated and portable globs that can be matched against file
//! paths and directory trees. Globs use a familiar syntax and support
//! expressive features with semantics that emphasize component boundaries.

#![doc(
    html_favicon_url = "https://raw.githubusercontent.com/olson-sean-k/wax/master/doc/wax-favicon.svg?sanitize=true"
)]
#![doc(
    html_logo_url = "https://raw.githubusercontent.com/olson-sean-k/wax/master/doc/wax.svg?sanitize=true"
)]
#![cfg_attr(docsrs, feature(doc_cfg))]

mod capture;
mod diagnostics;
mod encode;
mod fragment;
mod rule;
mod token;

use bstr::ByteVec;
use itertools::{Itertools as _, Position};
#[cfg(feature = "diagnostics-report")]
use miette::Diagnostic;
use regex::Regex;
use std::borrow::{Borrow, Cow};
use std::cmp;
use std::convert::TryFrom;
use std::ffi::OsStr;
use std::fmt::{self, Debug, Display, Formatter};
use std::fs::{FileType, Metadata};
use std::iter::Fuse;
use std::path::{Component, Path, PathBuf};
use std::str::{self, FromStr};
use thiserror::Error;
use walkdir::{self, DirEntry, WalkDir};

pub use walkdir::Error as WalkError;

#[cfg(feature = "diagnostics-inspect")]
use crate::diagnostics::inspect;
#[cfg(feature = "diagnostics-report")]
use crate::diagnostics::report::{self, BoxedDiagnostic};
use crate::token::{Token, Tokenized};

pub use crate::capture::MatchedText;
#[cfg(feature = "diagnostics-inspect")]
pub use crate::diagnostics::inspect::CapturingToken;
#[cfg(feature = "diagnostics-report")]
pub use crate::diagnostics::report::{DiagnosticGlob, DiagnosticResult, DiagnosticResultExt};
#[cfg(feature = "diagnostics-inspect")]
pub use crate::diagnostics::Span;
pub use crate::rule::RuleError;
pub use crate::token::ParseError;

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
    fn has_casing(self) -> bool;
}

impl CharExt for char {
    fn has_casing(self) -> bool {
        self.is_lowercase() != self.is_uppercase()
    }
}

trait StrExt {
    fn has_casing(&self) -> bool;
}

impl StrExt for str {
    fn has_casing(&self) -> bool {
        self.chars().any(|x| x.has_casing())
    }
}

trait IteratorExt: Iterator + Sized {
    fn adjacent(self) -> Adjacent<Self>
    where
        Self::Item: Clone;
}

impl<I> IteratorExt for I
where
    I: Iterator,
{
    fn adjacent(self) -> Adjacent<Self>
    where
        Self::Item: Clone,
    {
        Adjacent::new(self)
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Adjacency<T> {
    Only { item: T },
    First { item: T, right: T },
    Middle { left: T, item: T, right: T },
    Last { left: T, item: T },
}

impl<T> Adjacency<T> {
    pub fn into_tuple(self) -> (Option<T>, T, Option<T>) {
        match self {
            Adjacency::Only { item } => (None, item, None),
            Adjacency::First { item, right } => (None, item, Some(right)),
            Adjacency::Middle { left, item, right } => (Some(left), item, Some(right)),
            Adjacency::Last { left, item } => (Some(left), item, None),
        }
    }
}

struct Adjacent<I>
where
    I: Iterator,
{
    input: Fuse<I>,
    adjacency: Option<Adjacency<I::Item>>,
}

impl<I> Adjacent<I>
where
    I: Iterator,
{
    fn new(input: I) -> Self {
        let mut input = input.fuse();
        let adjacency = match (input.next(), input.next()) {
            (Some(item), Some(right)) => Some(Adjacency::First { item, right }),
            (Some(item), None) => Some(Adjacency::Only { item }),
            (None, None) => None,
            // The input iterator is fused, so this cannot occur.
            (None, Some(_)) => unreachable!(),
        };
        Adjacent { input, adjacency }
    }
}

impl<I> Iterator for Adjacent<I>
where
    I: Iterator,
    I::Item: Clone,
{
    type Item = Adjacency<I::Item>;

    fn next(&mut self) -> Option<Self::Item> {
        let next = self.input.next();
        self.adjacency.take().map(|adjacency| {
            self.adjacency = match adjacency.clone() {
                Adjacency::First {
                    item: left,
                    right: item,
                }
                | Adjacency::Middle {
                    item: left,
                    right: item,
                    ..
                } => {
                    if let Some(right) = next {
                        Some(Adjacency::Middle { left, item, right })
                    }
                    else {
                        Some(Adjacency::Last { left, item })
                    }
                }
                Adjacency::Only { .. } | Adjacency::Last { .. } => None,
            };
            adjacency
        })
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
            1 => Some(Terminals::Only(&self[0])),
            _ => Some(Terminals::StartEnd(
                self.first().unwrap(),
                self.last().unwrap(),
            )),
        }
    }
}

#[derive(Clone, Copy, Debug)]
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

// TODO: Is is not possible to use the `#[doc(cfg())]` attribute on the
//       `Diagnostic` implementation generated by procedural macros.
//       `Diagnostic` could be implemented without macros, but `GlobError` is
//       particularly well suited to them. Use a manual implementation with
//       `#[doc(cfg())]` if that changes to mark the implementation as feature
//       dependent in documentation.
#[derive(Debug, Error)]
#[non_exhaustive]
#[cfg_attr(feature = "diagnostics-report", derive(Diagnostic))]
pub enum GlobError<'t> {
    #[error(transparent)]
    #[cfg_attr(feature = "diagnostics-report", diagnostic(transparent))]
    Parse(ParseError<'t>),
    #[error(transparent)]
    #[cfg_attr(feature = "diagnostics-report", diagnostic(transparent))]
    Rule(RuleError<'t>),
    #[error("failed to walk directory tree: {0}")]
    #[cfg_attr(feature = "diagnostics-report", diagnostic(code = "wax::glob::walk"))]
    Walk(WalkError),
}

impl<'t> GlobError<'t> {
    pub fn into_owned(self) -> GlobError<'static> {
        match self {
            GlobError::Parse(error) => GlobError::Parse(error.into_owned()),
            GlobError::Rule(error) => GlobError::Rule(error.into_owned()),
            GlobError::Walk(error) => GlobError::Walk(error),
        }
    }
}

impl<'t> From<ParseError<'t>> for GlobError<'t> {
    fn from(error: ParseError) -> Self {
        GlobError::Parse(error.into_owned())
    }
}

impl From<WalkError> for GlobError<'static> {
    fn from(error: WalkError) -> Self {
        GlobError::Walk(error)
    }
}

impl<'t> From<RuleError<'t>> for GlobError<'t> {
    fn from(error: RuleError<'t>) -> Self {
        GlobError::Rule(error)
    }
}

#[derive(Clone)]
pub struct CandidatePath<'b> {
    text: Cow<'b, str>,
}

impl<'b> CandidatePath<'b> {
    pub fn into_owned(self) -> CandidatePath<'static> {
        CandidatePath {
            text: self.text.into_owned().into(),
        }
    }
}

impl<'b> AsRef<str> for CandidatePath<'b> {
    fn as_ref(&self) -> &str {
        self.text.as_ref()
    }
}

impl<'b> Debug for CandidatePath<'b> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self.text)
    }
}

impl<'b> Display for CandidatePath<'b> {
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

#[derive(Clone, Debug)]
pub struct Glob<'t> {
    tokenized: Tokenized<'t>,
    regex: Regex,
}

impl<'t> Glob<'t> {
    fn compile<T>(tokens: impl IntoIterator<Item = T>) -> Regex
    where
        T: Borrow<Token<'t>>,
    {
        encode::compile(tokens)
    }

    pub fn new(expression: &'t str) -> Result<Self, GlobError<'t>> {
        let tokenized = parse_and_check(expression)?;
        let regex = Glob::compile(tokenized.tokens());
        Ok(Glob { tokenized, regex })
    }

    /// Partitions a glob expression into an invariant `PathBuf` prefix and
    /// variant `Glob` postfix.
    ///
    /// The invariant prefix contains no glob patterns nor other variant
    /// components and therefore can be interpreted as a native path. The `Glob`
    /// postfix is variant and contains the remaining components (in particular,
    /// patterns) that follow the prefix. For example, the glob expression
    /// `.local/**/*.log` would produce the path `.local` and glob `**/*.log`.
    /// It is possible for either partition to be empty.
    ///
    /// Literal components may be considered variant if they contain characters
    /// with casing and the configured case sensitivity differs from the target
    /// platform's file system. For example, the case-insensitive literal
    /// expression `(?i)photos` is considered variant on Unix and invariant on
    /// Windows, because the literal `photos` resolves differently in Unix file
    /// system APIs than `Glob` APIs (which respect the configured
    /// case-insensitivity).
    ///
    /// Partitioning a glob expression allows any invariant prefix to be used as
    /// a native path to establish a working directory or to interpret semantic
    /// components that are not recognized by globs, such as parent directory
    /// `..` components.
    ///
    /// Partitioned `Glob`s are never rooted. If the glob expression has a root
    /// component, then it is always included in the invariant `PathBuf` prefix.
    ///
    /// # Errors
    ///
    /// Returns an error if the glob expression cannot be parsed or violates
    /// glob component rules.
    ///
    /// # Examples
    ///
    /// To match files in a directory tree while respecting semantic components
    /// like `..` on platforms that support it, the invariant prefix can be
    /// applied to a working directory. In the following example, `walk` reads
    /// and therefore resolves the path `./../site/img`, respecting the meaning
    /// of the `.` and `..` components.
    ///
    /// ```rust,no_run
    /// use std::path::Path;
    /// use wax::Glob;
    ///
    /// let directory = Path::new("."); // Working directory.
    /// let (prefix, glob) = Glob::partitioned("../site/img/*.{jpg,png}").unwrap();
    /// for entry in glob.walk(directory.join(prefix), usize::MAX) {
    ///     // ...
    /// }
    /// ```
    ///
    /// To match paths against a glob while respecting semantic components, the
    /// invariant prefix and candidate path can be canonicalized. The following
    /// example canonicalizes both the working directory joined with the prefix
    /// as well as the candidate path and then attempts to match the glob if the
    /// candidate path contains the prefix.
    ///
    /// ```rust,no_run
    /// use dunce; // Avoids UNC paths on Windows.
    /// use std::path::Path;
    /// use wax::Glob;
    ///
    /// let path: &Path = /* ... */ // Candidate path.
    /// # Path::new("");
    ///     
    /// let directory = Path::new("."); // Working directory.
    /// let (prefix, glob) = Glob::partitioned("../../src/**").unwrap();
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
    pub fn partitioned(expression: &'t str) -> Result<(PathBuf, Self), GlobError<'t>> {
        let mut tokenized = parse_and_check(expression)?;
        let prefix = tokenized.partition();
        let regex = Glob::compile(tokenized.tokens());
        Ok((prefix, Glob { tokenized, regex }))
    }

    pub fn into_owned(self) -> Glob<'static> {
        let Glob { tokenized, regex } = self;
        Glob {
            tokenized: tokenized.into_owned(),
            regex,
        }
    }

    pub fn is_match<'p>(&self, path: impl Into<CandidatePath<'p>>) -> bool {
        let path = path.into();
        self.regex.is_match(path.as_ref())
    }

    pub fn matched<'p>(&self, path: &'p CandidatePath<'_>) -> Option<MatchedText<'p>> {
        self.regex.captures(path.as_ref()).map(From::from)
    }

    pub fn walk(&self, directory: impl AsRef<Path>, depth: usize) -> Walk {
        let directory = directory.as_ref();
        // The directory tree is traversed from `root`, which may include an
        // invariant prefix from the glob pattern. `Walk` patterns are only
        // applied to path components following the `prefix` (distinct from the
        // glob pattern prefix) in `root`.
        let (root, prefix, depth) = token::invariant_prefix_path(self.tokenized.tokens())
            .map(|prefix| {
                let root = directory.join(&prefix).into();
                if prefix.is_absolute() {
                    // Absolute paths replace paths with which they are joined,
                    // in which case there is no prefix.
                    (root, PathBuf::new().into(), depth)
                }
                else {
                    // TODO: If the depth is exhausted by an invariant prefix
                    //       path, then `Walk` should yield no entries. This
                    //       computes a depth of zero when this occurs, so
                    //       entries may still be yielded.
                    // `depth` is relative to the input `directory`, so count
                    // any components added by an invariant prefix path from the
                    // glob.
                    let depth = depth - cmp::min(depth, prefix.components().count());
                    (root, directory.into(), depth)
                }
            })
            .unwrap_or_else(|| {
                let root = Cow::from(directory);
                (root.clone(), root, depth)
            });
        let regexes = Walk::compile(self.tokenized.tokens());
        Walk {
            regex: Cow::Borrowed(&self.regex),
            regexes,
            prefix: prefix.into_owned(),
            walk: WalkDir::new(root)
                .follow_links(false)
                .max_depth(depth)
                .into_iter(),
        }
    }

    #[cfg(feature = "diagnostics-report")]
    #[cfg_attr(docsrs, doc(cfg(feature = "diagnostics-report")))]
    pub fn diagnostics(&self) -> impl Iterator<Item = Box<dyn Diagnostic + '_>> {
        report::diagnostics(&self.tokenized)
    }

    #[cfg(feature = "diagnostics-inspect")]
    #[cfg_attr(docsrs, doc(cfg(feature = "diagnostics-inspect")))]
    pub fn captures(&self) -> impl '_ + Clone + Iterator<Item = CapturingToken> {
        inspect::captures(self.tokenized.tokens())
    }

    pub fn is_invariant(&self) -> bool {
        // TODO: This may be expensive.
        self.tokenized
            .tokens()
            .iter()
            .all(|token| token.to_invariant_string().is_some())
    }

    pub fn has_root(&self) -> bool {
        self.tokenized
            .tokens()
            .first()
            .map(|token| token.is_rooted())
            .unwrap_or(false)
    }

    pub fn has_semantic_literals(&self) -> bool {
        token::literals(self.tokenized.tokens()).any(|(_, literal)| literal.is_semantic_literal())
    }
}

#[cfg_attr(docsrs, doc(cfg(feature = "diagnostics-report")))]
#[cfg(feature = "diagnostics-report")]
impl<'t> DiagnosticGlob<'t> for Glob<'t> {
    fn new(expression: &'t str) -> DiagnosticResult<'t, Self> {
        parse_and_diagnose(expression).map(|(tokenized, diagnostics)| {
            let regex = Glob::compile(tokenized.tokens());
            (Glob { tokenized, regex }, diagnostics)
        })
    }

    fn partitioned(expression: &'t str) -> DiagnosticResult<'t, (PathBuf, Self)> {
        parse_and_diagnose(expression).map(|(mut tokenized, diagnostics)| {
            let prefix = tokenized.partition();
            let regex = Glob::compile(tokenized.tokens());
            ((prefix, Glob { tokenized, regex }), diagnostics)
        })
    }
}

impl<'t> TryFrom<&'t str> for Glob<'t> {
    type Error = GlobError<'t>;

    fn try_from(expression: &'t str) -> Result<Self, Self::Error> {
        Glob::new(expression)
    }
}

impl FromStr for Glob<'static> {
    type Err = GlobError<'static>;

    fn from_str(expression: &str) -> Result<Self, Self::Err> {
        Glob::new(expression)
            .map(|glob| glob.into_owned())
            .map_err(|error| error.into_owned())
    }
}

/// Traverses a directory tree via a `Walk` instance.
///
/// This macro emits an interruptable loop that executes a block of code
/// whenever a `WalkEntry` or error is encountered while traversing a directory
/// tree. The block may return from its function or otherwise interrupt and
/// subsequently resume the loop.
///
/// Note that if the block attempts to emit a `WalkEntry` across a function
/// boundary that the entry must copy its contents via `into_owned`.
macro_rules! walk {
    ($state:expr => |$entry:ident| $f:block) => {
        use itertools::EitherOrBoth::{Both, Left, Right};
        use itertools::Position::{First, Last, Middle, Only};

        // `while-let` avoids a mutable borrow of `walk`, which would prevent a
        // subsequent call to `skip_current_dir` within the loop body.
        #[allow(clippy::while_let_on_iterator)]
        #[allow(unreachable_code)]
        'walk: while let Some(entry) = $state.walk.next() {
            let entry = match entry {
                Ok(entry) => entry,
                Err(error) => {
                    let $entry = Err(error.into());
                    $f
                    continue; // May be unreachable.
                }
            };
            let depth = cmp::max(entry.depth(), 1) - 1;
            let path = entry
                .path()
                .strip_prefix(&$state.prefix)
                .expect("path is not in tree");
            for candidate in path
                .components()
                .skip(depth)
                .filter_map(|component| match component {
                    Component::Normal(component) => Some(CandidatePath::from(component)),
                    _ => None,
                })
                .zip_longest($state.regexes.iter().skip(depth))
                .with_position()
            {
                match candidate.as_tuple() {
                    (First(_) | Middle(_), Both(component, regex)) => {
                        if !regex.is_match(component.as_ref()) {
                            // Do not descend into directories that do not match
                            // the corresponding component regex.
                            if entry.file_type().is_dir() {
                                $state.walk.skip_current_dir();
                            }
                            continue 'walk;
                        }
                    }
                    (Last(_) | Only(_), Both(component, regex)) => {
                        if regex.is_match(component.as_ref()) {
                            let path = CandidatePath::from(path);
                            if let Some(matched) =
                                $state.regex.captures(path.as_ref()).map(MatchedText::from)
                            {
                                let $entry = Ok(WalkEntry {
                                    entry: Cow::Borrowed(&entry),
                                    matched,
                                });
                                $f
                            }
                        }
                        else {
                            // Do not descend into directories that do not match
                            // the corresponding component regex.
                            if entry.file_type().is_dir() {
                                $state.walk.skip_current_dir();
                            }
                        }
                    }
                    (_, Left(_component)) => {
                        let path = CandidatePath::from(path);
                        if let Some(matched) =
                            $state.regex.captures(path.as_ref()).map(MatchedText::from)
                        {
                            let $entry = Ok(WalkEntry {
                                entry: Cow::Borrowed(&entry),
                                matched,
                            });
                            $f
                            continue 'walk; // May be unreachable.
                        }
                    }
                    (_, Right(_regex)) => {
                        continue 'walk;
                    }
                }
            }
        }
    }
}

/// Describes a file matching a `Glob` in a directory tree.
#[derive(Debug)]
pub struct WalkEntry<'e> {
    entry: Cow<'e, DirEntry>,
    matched: MatchedText<'e>,
}

impl<'e> WalkEntry<'e> {
    pub fn into_owned(self) -> WalkEntry<'static> {
        let WalkEntry { entry, matched } = self;
        WalkEntry {
            entry: Cow::Owned(entry.into_owned()),
            matched: matched.into_owned(),
        }
    }

    pub fn into_path(self) -> PathBuf {
        match self.entry {
            Cow::Borrowed(entry) => entry.path().to_path_buf(),
            Cow::Owned(entry) => entry.into_path(),
        }
    }

    pub fn path(&self) -> &Path {
        self.entry.path()
    }

    pub fn to_candidate_path(&self) -> CandidatePath<'_> {
        self.path().into()
    }

    pub fn file_type(&self) -> FileType {
        self.entry.file_type()
    }

    pub fn metadata(&self) -> Result<Metadata, GlobError<'static>> {
        self.entry.metadata().map_err(From::from)
    }

    pub fn depth(&self) -> usize {
        self.entry.depth()
    }

    pub fn matched(&self) -> &MatchedText<'e> {
        &self.matched
    }
}

/// Iterator over files matching a `Glob` in a directory tree.
#[derive(Debug)]
pub struct Walk<'g> {
    regex: Cow<'g, Regex>,
    regexes: Vec<Regex>,
    prefix: PathBuf,
    walk: walkdir::IntoIter,
}

impl<'g> Walk<'g> {
    fn compile<'t, I>(tokens: I) -> Vec<Regex>
    where
        I: IntoIterator<Item = &'t Token<'t>>,
        I::IntoIter: Clone,
    {
        let mut regexes = Vec::new();
        for component in token::components(tokens) {
            if component
                .tokens()
                .iter()
                .any(|token| token.has_component_boundary())
            {
                // Stop at component boundaries, such as tree wildcards or any
                // boundary within an alternative token.
                break;
            }
            else {
                regexes.push(Glob::compile(component.tokens().iter().cloned()));
            }
        }
        regexes
    }

    pub fn into_owned(self) -> Walk<'static> {
        let Walk {
            regex,
            regexes,
            prefix,
            walk,
        } = self;
        Walk {
            regex: Cow::Owned(regex.into_owned()),
            regexes,
            prefix,
            walk,
        }
    }

    /// Calls a closure on each matched file or error.
    ///
    /// This function does not copy the contents of paths and captures when
    /// emitting entries and so may be more efficient than external iteration
    /// via `Iterator` (and `Iterator::for_each`).
    pub fn for_each(mut self, mut f: impl FnMut(Result<WalkEntry, GlobError>)) {
        walk!(self => |entry| {
            f(entry);
        });
    }
}

impl<'g> Iterator for Walk<'g> {
    type Item = Result<WalkEntry<'static>, GlobError<'static>>;

    fn next(&mut self) -> Option<Self::Item> {
        walk!(self => |entry| {
            return Some(entry.map(|entry: WalkEntry| entry.into_owned()));
        });
        None
    }
}

pub fn is_match<'p>(
    expression: &str,
    path: impl Into<CandidatePath<'p>>,
) -> Result<bool, GlobError> {
    let glob = Glob::new(expression)?;
    Ok(glob.is_match(path))
}

pub fn walk(
    expression: &str,
    directory: impl AsRef<Path>,
    depth: usize,
) -> Result<Walk<'static>, GlobError> {
    let (prefix, glob) = Glob::partitioned(expression)?;
    Ok(glob
        .walk(directory.as_ref().join(prefix), depth)
        .into_owned())
}

/// Escapes text as a literal glob expression.
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
/// This function does not return `true` for contextual meta-characters that may
/// only be escaped in particular contexts, such as hyphens `-` in character
/// class expressions.
pub const fn is_meta_character(x: char) -> bool {
    matches!(
        x,
        '?' | '*' | '$' | ':' | '<' | '>' | '(' | ')' | '[' | ']' | '{' | '}' | ','
    )
}

/// Returns `true` if the given character is a contextual meta-character.
///
/// Contextual meta-characters may only be escaped in particular contexts, such
/// as hyphens `-` in character class expressions.
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
    let (tokenized, parse_error_diagnostic) = match token::parse(expression) {
        Ok(tokenized) => (Some(tokenized), None),
        Err(diagnostic) => (None, Some(Box::new(diagnostic) as BoxedDiagnostic)),
    };
    let rule_error_diagnostic = tokenized.as_ref().and_then(|tokenized| {
        rule::check(tokenized)
            .err()
            .map(|diagnostic| Box::new(diagnostic) as BoxedDiagnostic)
    });
    let non_error_diagnostics = tokenized.as_ref().into_iter().flat_map(report::diagnostics);
    let diagnostics = non_error_diagnostics
        .chain(rule_error_diagnostic)
        .chain(parse_error_diagnostic)
        .collect();
    if let Some(tokenized) = tokenized {
        Ok((tokenized, diagnostics))
    }
    else {
        Err(diagnostics.try_into().expect("parse failed with no error"))
    }
}

// TODO: Construct paths from components in tests. In practice, using string
//       literals works, but is technically specific to platforms that support
//       `/` as a separator.
#[cfg(test)]
mod tests {
    use std::path::Path;

    use crate::{Adjacency, CandidatePath, Glob, IteratorExt as _};

    #[test]
    fn adjacent() {
        let mut adjacent = Option::<i32>::None.into_iter().adjacent();
        assert_eq!(adjacent.next(), None);

        let mut adjacent = Some(0i32).into_iter().adjacent();
        assert_eq!(adjacent.next(), Some(Adjacency::Only { item: 0 }));
        assert_eq!(adjacent.next(), None);

        let mut adjacent = (0i32..3).adjacent();
        assert_eq!(
            adjacent.next(),
            Some(Adjacency::First { item: 0, right: 1 })
        );
        assert_eq!(
            adjacent.next(),
            Some(Adjacency::Middle {
                left: 0,
                item: 1,
                right: 2
            })
        );
        assert_eq!(adjacent.next(), Some(Adjacency::Last { left: 1, item: 2 }));
        assert_eq!(adjacent.next(), None);
    }

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
    fn reject_glob_with_invalid_separator_tokens() {
        assert!(Glob::new("//a").is_err());
        assert!(Glob::new("a//b").is_err());
        assert!(Glob::new("a/b//").is_err());
        assert!(Glob::new("a//**").is_err());
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
    fn partition_glob_with_variant_and_invariant_parts() {
        let (prefix, glob) = Glob::partitioned("a/b/x?z/*.ext").unwrap();

        assert_eq!(prefix, Path::new("a/b"));

        assert!(glob.is_match(Path::new("xyz/file.ext")));
        assert!(glob.is_match(Path::new("a/b/xyz/file.ext").strip_prefix(prefix).unwrap()));
    }

    #[test]
    fn partition_glob_with_only_variant_wildcard_parts() {
        let (prefix, glob) = Glob::partitioned("x?z/*.ext").unwrap();

        assert_eq!(prefix, Path::new(""));

        assert!(glob.is_match(Path::new("xyz/file.ext")));
        assert!(glob.is_match(Path::new("xyz/file.ext").strip_prefix(prefix).unwrap()));
    }

    #[test]
    fn partition_glob_with_only_invariant_literal_parts() {
        let (prefix, glob) = Glob::partitioned("a/b").unwrap();

        assert_eq!(prefix, Path::new("a/b"));

        assert!(glob.is_match(Path::new("")));
        assert!(glob.is_match(Path::new("a/b").strip_prefix(prefix).unwrap()));
    }

    #[test]
    fn partition_glob_with_variant_alternative_parts() {
        let (prefix, glob) = Glob::partitioned("{x,z}/*.ext").unwrap();

        assert_eq!(prefix, Path::new(""));

        assert!(glob.is_match(Path::new("x/file.ext")));
        assert!(glob.is_match(Path::new("z/file.ext").strip_prefix(prefix).unwrap()));
    }

    #[test]
    fn partition_glob_with_invariant_alternative_parts() {
        let (prefix, glob) = Glob::partitioned("{a/b}/c").unwrap();

        assert_eq!(prefix, Path::new("a/b/c"));

        assert!(glob.is_match(Path::new("")));
        assert!(glob.is_match(Path::new("a/b/c").strip_prefix(prefix).unwrap()));
    }

    #[test]
    fn partition_glob_with_invariant_repetition_parts() {
        let (prefix, glob) = Glob::partitioned("</a/b:3>/c").unwrap();

        assert_eq!(prefix, Path::new("/a/b/a/b/a/b/c"));

        assert!(glob.is_match(Path::new("")));
        assert!(glob.is_match(Path::new("/a/b/a/b/a/b/c").strip_prefix(prefix).unwrap()));
    }

    #[test]
    fn partition_glob_with_literal_dots_and_tree_tokens() {
        let (prefix, glob) = Glob::partitioned("../**/*.ext").unwrap();

        assert_eq!(prefix, Path::new(".."));

        assert!(glob.is_match(Path::new("xyz/file.ext")));
        assert!(glob.is_match(Path::new("../xyz/file.ext").strip_prefix(prefix).unwrap()));
    }

    #[test]
    fn partition_glob_with_rooted_tree_token() {
        let (prefix, glob) = Glob::partitioned("/**/*.ext").unwrap();

        assert_eq!(prefix, Path::new("/"));
        assert!(!glob.has_root());

        assert!(glob.is_match(Path::new("file.ext")));
        assert!(glob.is_match(Path::new("/root/file.ext").strip_prefix(prefix).unwrap()));
    }

    #[test]
    fn partition_glob_with_rooted_zom_token() {
        let (prefix, glob) = Glob::partitioned("/*/*.ext").unwrap();

        assert_eq!(prefix, Path::new("/"));
        assert!(!glob.has_root());

        assert!(glob.is_match(Path::new("root/file.ext")));
        assert!(glob.is_match(Path::new("/root/file.ext").strip_prefix(prefix).unwrap()));
    }

    #[test]
    fn partition_glob_with_rooted_literal_token() {
        let (prefix, glob) = Glob::partitioned("/root/**/*.ext").unwrap();

        assert_eq!(prefix, Path::new("/root"));
        assert!(!glob.has_root());

        assert!(glob.is_match(Path::new("file.ext")));
        assert!(glob.is_match(Path::new("/root/file.ext").strip_prefix(prefix).unwrap()));
    }

    #[test]
    fn query_glob_is_invariant() {
        assert!(Glob::new("").unwrap().is_invariant());
        assert!(Glob::new("/a/file.ext").unwrap().is_invariant());
        assert!(Glob::new("/a/{file.ext}").unwrap().is_invariant());
        assert!(Glob::new("{a/b/file.ext}").unwrap().is_invariant());
        assert!(Glob::new("<a/b:2>").unwrap().is_invariant());
        #[cfg(unix)]
        assert!(Glob::new("/[a]/file.ext").unwrap().is_invariant());
        #[cfg(unix)]
        assert!(Glob::new("/[a-a]/file.ext").unwrap().is_invariant());

        assert!(!Glob::new("/a/{b,c}").unwrap().is_invariant());
        assert!(!Glob::new("<a/b:1,>").unwrap().is_invariant());
        assert!(!Glob::new("/[ab]/file.ext").unwrap().is_invariant());
        assert!(!Glob::new("**").unwrap().is_invariant());
        assert!(!Glob::new("/a/*.ext").unwrap().is_invariant());
        assert!(!Glob::new("/a/b*").unwrap().is_invariant());
        #[cfg(unix)]
        assert!(!Glob::new("/a/(?i)file.ext").unwrap().is_invariant());
        #[cfg(windows)]
        assert!(!Glob::new("/a/(?-i)file.ext").unwrap().is_invariant());
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
