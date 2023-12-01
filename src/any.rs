use regex::Regex;
use std::convert::Infallible;

use crate::capture::MatchedText;
use crate::encode::{self, CompileError};
use crate::rule::Checked;
use crate::token::{self, InvariantText, Token};
use crate::{BuildError, CandidatePath, Pattern, Program, Variance};

/// Combinator that matches any of its component [`Program`]s.
///
/// An instance of `Any` is constructed using the [`any`] function, which combines multiple
/// [`Program`]s for more ergonomic and efficient matching.
///
/// [`any`]: crate::any
/// [`Program`]: crate::Program
#[derive(Clone, Debug)]
pub struct Any<'t> {
    pub(in crate) tree: Checked<Token<'t, ()>>,
    pub(in crate) program: Regex,
}

impl<'t> Any<'t> {
    fn compile(token: &Token<'t, ()>) -> Result<Regex, CompileError> {
        encode::compile([token])
    }
}

impl<'t> Pattern<'t> for Any<'t> {
    type Tokens = Token<'t, ()>;
    type Error = Infallible;
}

impl<'t> Program<'t> for Any<'t> {
    fn is_match<'p>(&self, path: impl Into<CandidatePath<'p>>) -> bool {
        let path = path.into();
        self.program.is_match(path.as_ref())
    }

    fn matched<'p>(&self, path: &'p CandidatePath<'_>) -> Option<MatchedText<'p>> {
        self.program.captures(path.as_ref()).map(From::from)
    }

    fn variance(&self) -> Variance {
        self.tree.as_ref().variance::<InvariantText>().into()
    }

    fn is_exhaustive(&self) -> bool {
        token::is_exhaustive(Some(self.tree.as_ref()))
    }
}

// TODO: It may be useful to use dynamic dispatch via trait objects instead. This would allow for a
//       variety of types to be composed in an `any` call and would be especially useful if
//       additional combinators are introduced.
/// Constructs a combinator that matches if any of its input [`Pattern`]s match.
///
/// This function accepts an [`IntoIterator`] with items that implement [`Pattern`], such as
/// [`Glob`] and `&str`. The output [`Any`] implements [`Program`] by matching its component
/// [`Program`]s. [`Any`] is often more ergonomic and efficient than matching individually against
/// multiple [`Program`]s.
///
/// [`Any`] groups all captures and therefore only exposes the complete text of a match. It is not
/// possible to index a particular capturing token in the component patterns. Combinators only
/// support logical matching and cannot be used to semantically match (walk) a directory tree.
///
/// # Examples
///
/// To match a path against multiple patterns, the patterns can first be combined into an [`Any`].
///
/// ```rust
/// use wax::{Glob, Program};
///
/// let any = wax::any([
///     "src/**/*.rs",
///     "tests/**/*.rs",
///     "doc/**/*.md",
///     "pkg/**/PKGBUILD",
/// ])
/// .unwrap();
/// assert!(any.is_match("src/lib.rs"));
/// ```
///
/// [`Glob`]s and other compiled [`Program`]s can also be composed into an [`Any`].
///
/// ```rust
/// use wax::{Glob, Program};
///
/// let red = Glob::new("**/red/**/*.txt").unwrap();
/// let blue = Glob::new("**/*blue*.txt").unwrap();
/// assert!(wax::any([red, blue]).unwrap().is_match("red/potion.txt"));
/// ```
///
/// This function can only combine patterns of the same type, but intermediate combinators can be
/// used to combine different types into a single combinator.
///
/// ```rust
/// use wax::{Glob, Program};
///
/// # fn fallible() -> Result<(), wax::BuildError> {
/// let glob = Glob::new("**/*.txt")?;
///
/// // ...
///
/// #[rustfmt::skip]
/// let any = wax::any([
///     wax::any([glob])?,
///     wax::any([
///         "**/*.pdf",
///         "**/*.tex",
///     ])?,
/// ])?;
/// assert!(any.is_match("doc/lattice.tex"));
/// # Ok(())
/// # }
/// ```
///
/// # Errors
///
/// Returns an error if any of the inputs fail to build. If the inputs are a compiled [`Program`]
/// type such as [`Glob`], then this only occurs if the compiled program is too large.
///
/// [`Any`]: crate::Any
/// [`Glob`]: crate::Glob
/// [`IntoIterator`]: std::iter::IntoIterator
/// [`Pattern`]: crate::Pattern
/// [`Program`]: crate::Program
pub fn any<'t, I>(patterns: I) -> Result<Any<'t>, BuildError>
where
    I: IntoIterator,
    I::Item: Pattern<'t>,
{
    let tree = Checked::any(
        patterns
            .into_iter()
            .map(TryInto::try_into)
            .collect::<Result<Vec<_>, _>>()
            .map_err(Into::into)?,
    );
    let program = Any::compile(tree.as_ref())?;
    Ok(Any { tree, program })
}
