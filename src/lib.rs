#![doc(
    html_favicon_url = "https://raw.githubusercontent.com/olson-sean-k/wax/master/doc/wax-favicon.svg?sanitize=true"
)]
#![doc(
    html_logo_url = "https://raw.githubusercontent.com/olson-sean-k/wax/master/doc/wax.svg?sanitize=true"
)]

mod capture;
mod encode;
mod fragment;
mod rule;
mod span;
mod token;

use bstr::ByteVec;
use itertools::{Itertools as _, Position};
#[cfg(feature = "diagnostics")]
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

use crate::token::Token;

pub use crate::capture::Captures;
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

#[derive(Debug, Error)]
#[non_exhaustive]
#[cfg_attr(feature = "diagnostics", derive(Diagnostic))]
pub enum GlobError<'t> {
    #[error(transparent)]
    #[cfg_attr(feature = "diagnostics", diagnostic(transparent))]
    Parse(ParseError<'t>),
    #[error(transparent)]
    #[cfg_attr(feature = "diagnostics", diagnostic(transparent))]
    Rule(RuleError<'t>),
    #[error("failed to walk directory tree: {0}")]
    #[cfg_attr(feature = "diagnostics", diagnostic(code = "glob::walk"))]
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
pub struct EncodedPath<'b> {
    text: Cow<'b, str>,
}

impl<'b> EncodedPath<'b> {
    pub fn into_owned(self) -> EncodedPath<'static> {
        EncodedPath {
            text: self.text.into_owned().into(),
        }
    }
}

impl<'b> AsRef<str> for EncodedPath<'b> {
    fn as_ref(&self) -> &str {
        self.text.as_ref()
    }
}

impl<'b> Debug for EncodedPath<'b> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self.text)
    }
}

impl<'b> Display for EncodedPath<'b> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.text)
    }
}

impl<'b> From<&'b OsStr> for EncodedPath<'b> {
    fn from(text: &'b OsStr) -> Self {
        EncodedPath {
            text: match Vec::from_os_str_lossy(text) {
                Cow::Borrowed(bytes) => str::from_utf8(bytes).expect_encoding().into(),
                Cow::Owned(bytes) => String::from_utf8(bytes).expect_encoding().into(),
            },
        }
    }
}

impl<'b> From<&'b Path> for EncodedPath<'b> {
    fn from(path: &'b Path) -> Self {
        EncodedPath::from(path.as_os_str())
    }
}

impl<'b> From<&'b str> for EncodedPath<'b> {
    fn from(text: &'b str) -> Self {
        EncodedPath { text: text.into() }
    }
}

#[derive(Clone, Debug)]
pub struct Glob<'t> {
    tokens: Vec<Token<'t>>,
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
        let tokens = token::parse(expression)?;
        let regex = Glob::compile(tokens.iter());
        Ok(Glob { tokens, regex })
    }

    /// Partitions a glob expression into an invariant `PathBuf` prefix and
    /// variant `Glob` postfix.
    ///
    /// The invariant prefix contains no glob patterns nor other variant
    /// components and therefore can be interpretted as a native path. The
    /// `Glob` postfix is variant and contains the remaining components (in
    /// particular, patterns) that follow the prefix. For example, the glob
    /// expression `.local/**/*.log` would produce the path `.local` and glob
    /// `**/*.log`. It is possible for either partition to be empty.
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
        // Get the invariant prefix for the token sequence.
        let mut tokens = token::parse(expression)?;
        let prefix = token::invariant_prefix_path(tokens.iter()).unwrap_or_else(PathBuf::new);

        // Drain invariant tokens from the beginning of the token sequence.
        // Unroot any tokens at the beginning of the sequence (tree wildcards)
        tokens.drain(0..token::invariant_prefix_upper_bound(&tokens));
        tokens.first_mut().map(Token::unroot);

        let regex = Glob::compile(tokens.iter());
        Ok((prefix, Glob { tokens, regex }))
    }

    pub fn into_owned(self) -> Glob<'static> {
        let Glob { tokens, regex } = self;
        let tokens = tokens.into_iter().map(|token| token.into_owned()).collect();
        Glob { tokens, regex }
    }

    pub fn has_root(&self) -> bool {
        token::invariant_prefix_path(self.tokens.iter())
            .map(|prefix| prefix.has_root())
            .unwrap_or(false)
    }

    #[cfg(any(unix, windows))]
    pub fn has_semantic_literals(&self) -> bool {
        token::components(self.tokens.iter()).any(|component| {
            component
                .literal()
                .map(|literal| matches!(literal.text().as_ref(), "." | ".."))
                .unwrap_or(false)
        })
    }

    #[cfg(not(any(unix, windows)))]
    pub fn has_semantic_literals(&self) -> bool {
        false
    }

    pub fn is_match<'p>(&self, path: impl Into<EncodedPath<'p>>) -> bool {
        let path = path.into();
        self.regex.is_match(path.as_ref())
    }

    pub fn captures<'p>(&self, path: &'p EncodedPath<'_>) -> Option<Captures<'p>> {
        self.regex.captures(path.as_ref()).map(From::from)
    }

    pub fn walk(&self, directory: impl AsRef<Path>, depth: usize) -> Walk {
        let directory = directory.as_ref();
        // The directory tree is traversed from `root`, which may include an
        // invariant prefix from the glob pattern. `Walk` patterns are only
        // applied to path components following the `prefix` (distinct from the
        // glob pattern prefix) in `root`.
        let (prefix, root) = token::invariant_prefix_path(self.tokens.iter())
            .map(|prefix| {
                let root = directory.join(&prefix).into();
                if prefix.is_absolute() {
                    // Absolute paths replace paths with which they are joined,
                    // in which case there is no prefix.
                    (PathBuf::new().into(), root)
                }
                else {
                    (directory.into(), root)
                }
            })
            .unwrap_or_else(|| {
                let root = Cow::from(directory);
                (root.clone(), root)
            });
        let regexes = Walk::compile(self.tokens.iter());
        Walk {
            regex: Cow::Borrowed(&self.regex),
            regexes,
            prefix: prefix.into_owned(),
            walk: WalkDir::new(root)
                .follow_links(false)
                .min_depth(1)
                .max_depth(depth)
                .into_iter(),
        }
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
                    Component::Normal(component) => Some(EncodedPath::from(component)),
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
                            let path = EncodedPath::from(path);
                            if let Some(captures) =
                                $state.regex.captures(path.as_ref()).map(Captures::from)
                            {
                                let $entry = Ok(WalkEntry {
                                    entry: Cow::Borrowed(&entry),
                                    captures,
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
                        let path = EncodedPath::from(path);
                        if let Some(captures) =
                            $state.regex.captures(path.as_ref()).map(Captures::from)
                        {
                            let $entry = Ok(WalkEntry {
                                entry: Cow::Borrowed(&entry),
                                captures,
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
    captures: Captures<'e>,
}

impl<'e> WalkEntry<'e> {
    pub fn into_owned(self) -> WalkEntry<'static> {
        let WalkEntry { entry, captures } = self;
        WalkEntry {
            entry: Cow::Owned(entry.into_owned()),
            captures: captures.into_owned(),
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

    pub fn to_encoded_path(&self) -> EncodedPath<'_> {
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

    pub fn captures(&self) -> &Captures<'e> {
        &self.captures
    }
}

/// Iterator over files matching a `Glob` in a directory tree.
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

/// Returns `true` if the given character is a meta-character.
///
/// This function does not return `true` for contextual meta-characters that may
/// only be escaped in particular contexts, such as hyphens `-` in character
/// class expressions.
pub const fn is_meta_character(x: char) -> bool {
    matches!(x, '?' | '*' | '$' | '(' | ')' | '[' | ']' | '{' | '}' | ',')
}

/// Returns `true` if the given character is a contextual meta-character.
///
/// Contextual meta-characters may only be escaped in particular contexts, such
/// as hyphens `-` in character class expressions.
pub const fn is_contextual_meta_character(x: char) -> bool {
    matches!(x, '-')
}

// TODO: Construct paths from components in tests. In practice, using string
//       literals works, but is technically specific to platforms that support
//       `/` as a separator.
#[cfg(test)]
mod tests {
    use std::path::Path;

    use crate::{Adjacency, EncodedPath, Glob, IteratorExt as _};

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
        assert_eq!(crate::escape("/usr/local/lib"), "/usr/local/lib",);
        assert_eq!(
            crate::escape("record[D00,00].txt"),
            "record\\[D00\\,00\\].txt",
        );
        assert_eq!(
            crate::escape("Do You Remember Love?.mp4"),
            "Do You Remember Love\\?.mp4",
        );
        assert_eq!(crate::escape("左{}右"), "左\\{\\}右",);
        assert_eq!(crate::escape("*中*"), "\\*中\\*",);
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
    fn reject_glob_with_adjacent_tree_or_zom_tokens() {
        assert!(Glob::new("***").is_err());
        assert!(Glob::new("****").is_err());
        assert!(Glob::new("**/**").is_err());
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
    fn reject_glob_with_invalid_separator_tokens() {
        assert!(Glob::new("//a").is_err());
        assert!(Glob::new("a//b").is_err());
        assert!(Glob::new("a/b//").is_err());
    }

    #[test]
    fn reject_glob_with_invalid_alternative_separator_tokens() {
        assert!(Glob::new("/slash/{okay,/error}").is_err());
        assert!(Glob::new("{okay,error/}/slash").is_err());
        assert!(Glob::new("slash/{okay,/error/,okay}/slash").is_err());
        assert!(Glob::new("{okay,error/}{okay,/error}").is_err());
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
    fn match_glob_with_tree_tokens() {
        let glob = Glob::new("a/**/b").unwrap();

        assert!(glob.is_match(Path::new("a/b")));
        assert!(glob.is_match(Path::new("a/x/b")));
        assert!(glob.is_match(Path::new("a/x/y/z/b")));

        assert!(!glob.is_match(Path::new("a")));
        assert!(!glob.is_match(Path::new("b/a")));

        assert_eq!(
            "x/y/z/",
            glob.captures(&EncodedPath::from(Path::new("a/x/y/z/b")))
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

        let path = EncodedPath::from(Path::new("a/file.ext"));
        let captures = glob.captures(&path).unwrap();
        assert_eq!("a/", captures.get(1).unwrap());
        assert_eq!("file", captures.get(2).unwrap());
    }

    #[test]
    fn match_glob_with_eager_and_lazy_zom_tokens() {
        let glob = Glob::new("$-*.*").unwrap();

        assert!(glob.is_match(Path::new("prefix-file.ext")));
        assert!(glob.is_match(Path::new("a-b-c.ext")));

        let path = EncodedPath::from(Path::new("a-b-c.ext"));
        let captures = glob.captures(&path).unwrap();
        assert_eq!("a", captures.get(1).unwrap());
        assert_eq!("b-c", captures.get(2).unwrap());
        assert_eq!("ext", captures.get(3).unwrap());
    }

    #[test]
    fn match_glob_with_class_tokens() {
        let glob = Glob::new("a/[xyi-k]/**").unwrap();

        assert!(glob.is_match(Path::new("a/x/file.ext")));
        assert!(glob.is_match(Path::new("a/y/file.ext")));
        assert!(glob.is_match(Path::new("a/j/file.ext")));

        assert!(!glob.is_match(Path::new("a/b/file.ext")));

        let path = EncodedPath::from(Path::new("a/i/file.ext"));
        let captures = glob.captures(&path).unwrap();
        assert_eq!("i", captures.get(1).unwrap());
    }

    #[test]
    fn match_glob_with_non_ascii_class_tokens() {
        let glob = Glob::new("a/[金銀]/**").unwrap();

        assert!(glob.is_match(Path::new("a/金/file.ext")));
        assert!(glob.is_match(Path::new("a/銀/file.ext")));

        assert!(!glob.is_match(Path::new("a/銅/file.ext")));

        let path = EncodedPath::from(Path::new("a/金/file.ext"));
        let captures = glob.captures(&path).unwrap();
        assert_eq!("金", captures.get(1).unwrap());
    }

    #[test]
    fn match_glob_with_literal_escaped_class_tokens() {
        let glob = Glob::new("a/[\\[\\]\\-]/**").unwrap();

        assert!(glob.is_match(Path::new("a/[/file.ext")));
        assert!(glob.is_match(Path::new("a/]/file.ext")));
        assert!(glob.is_match(Path::new("a/-/file.ext")));

        assert!(!glob.is_match(Path::new("a/b/file.ext")));

        let path = EncodedPath::from(Path::new("a/[/file.ext"));
        let captures = glob.captures(&path).unwrap();
        assert_eq!("[", captures.get(1).unwrap());
    }

    #[test]
    fn match_glob_with_alternative_tokens() {
        let glob = Glob::new("a/{x?z,y$}b/*").unwrap();

        assert!(glob.is_match(Path::new("a/xyzb/file.ext")));
        assert!(glob.is_match(Path::new("a/yb/file.ext")));

        assert!(!glob.is_match(Path::new("a/xyz/file.ext")));
        assert!(!glob.is_match(Path::new("a/y/file.ext")));
        assert!(!glob.is_match(Path::new("a/xyzub/file.ext")));

        let path = EncodedPath::from(Path::new("a/xyzb/file.ext"));
        let captures = glob.captures(&path).unwrap();
        assert_eq!("xyz", captures.get(1).unwrap());
    }

    #[test]
    fn match_glob_with_nested_alternative_tokens() {
        let glob = Glob::new("a/{y$,{x?z,?z}}b/*").unwrap();

        let path = EncodedPath::from(Path::new("a/xyzb/file.ext"));
        let captures = glob.captures(&path).unwrap();
        assert_eq!("xyz", captures.get(1).unwrap());
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
    fn match_glob_with_rooted_tree_token() {
        let glob = Glob::new("/**/{var,.var}/**/*.log").unwrap();

        assert!(glob.is_match(Path::new("/var/log/network.log")));
        assert!(glob.is_match(Path::new("/home/nobody/.var/network.log")));

        assert!(!glob.is_match(Path::new("./var/cron.log")));
        assert!(!glob.is_match(Path::new("mnt/var/log/cron.log")));

        let path = EncodedPath::from(Path::new("/var/log/network.log"));
        let captures = glob.captures(&path).unwrap();
        assert_eq!("/", captures.get(1).unwrap());
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
    fn partition_glob_with_literal_and_non_literal_parts() {
        let (prefix, glob) = Glob::partitioned("a/b/x?z/*.ext").unwrap();

        assert_eq!(prefix, Path::new("a/b"));

        assert!(glob.is_match(Path::new("xyz/file.ext")));
        assert!(glob.is_match(Path::new("a/b/xyz/file.ext").strip_prefix(prefix).unwrap()));
    }

    #[test]
    fn partition_glob_with_only_non_literal_parts() {
        let (prefix, glob) = Glob::partitioned("x?z/*.ext").unwrap();

        assert_eq!(prefix, Path::new(""));

        assert!(glob.is_match(Path::new("xyz/file.ext")));
        assert!(glob.is_match(Path::new("xyz/file.ext").strip_prefix(prefix).unwrap()));
    }

    #[test]
    fn partition_glob_with_only_literal_parts() {
        let (prefix, glob) = Glob::partitioned("a/b").unwrap();

        assert_eq!(prefix, Path::new("a/b"));

        assert!(glob.is_match(Path::new("")));
        assert!(glob.is_match(Path::new("a/b").strip_prefix(prefix).unwrap()));
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
}
