#![cfg(feature = "diagnostics-inspect")]

use std::path::PathBuf;

use crate::diagnostics::Span;
use crate::token::{self, InvariantText, Token};

/// Token that captures matched text in a glob expression.
///
/// # Examples
///
/// `CapturingToken`s can be used to isolate sub-expressions.
///
/// ```rust
/// use wax::Glob;
///
/// let expression = "**/*.txt";
/// let glob = Glob::new(expression).unwrap();
/// for token in glob.captures() {
///     let (start, n) = token.span();
///     println!("capturing sub-expression: {}", &expression[start..][..n]);
/// }
/// ```
#[cfg_attr(docsrs, doc(cfg(feature = "diagnostics-inspect")))]
#[derive(Clone, Copy, Debug)]
pub struct CapturingToken {
    index: usize,
    span: Span,
}

impl CapturingToken {
    /// Gets the index of the capture.
    ///
    /// Captures are one-indexed and the index zero always represents the
    /// implicit capture of the complete match, so the index of
    /// `CapturingToken`s is always one or greater. See [`MatchedText`].
    ///
    /// [`MatchedText`]: crate::MatchedText
    pub fn index(&self) -> usize {
        self.index
    }

    /// Gets the span of the token's sub-expression.
    pub fn span(&self) -> Span {
        self.span
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
#[cfg_attr(docsrs, doc(cfg(feature = "diagnostics-inspect")))]
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum Variance {
    /// A [`Pattern`] is invariant and equivalent to a native path.
    ///
    /// An invariant [`Pattern`] is equivalent to a native path and resolves the
    /// same way as such a native path does when used with the platform's file
    /// system APIs. These APIs may differ, so variance is platform dependent.
    ///
    /// Some non-literal expressions may be invariant, such as in the expression
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
        ///
        /// [`Pattern`]: crate::Pattern
        PathBuf,
    ),
    /// A [`Pattern`] is variant and resolves differently than any native path.
    ///
    /// Variant expressions may be formed from only literals or other seemingly
    /// constant expressions. For example, the variance of literals considers
    /// the case sensitivity of the platform's file system APIs, so the
    /// expression `(?i)path/to/file.txt` is variant on Unix (but not on
    /// Windows). Similarly, the expression `path/[t][o]/file.txt` is variant on
    /// Windows (but not on Unix).
    ///
    /// [`Pattern`]: crate::Pattern
    Variant,
}

impl Variance {
    /// Returns `true` if invariant.
    pub fn is_invariant(&self) -> bool {
        matches!(self, Variance::Invariant(_))
    }

    /// Returns `true` if variant.
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

pub fn captures<'t, I>(tokens: I) -> impl 't + Clone + Iterator<Item = CapturingToken>
where
    I: IntoIterator<Item = &'t Token<'t>>,
    I::IntoIter: 't + Clone,
{
    tokens
        .into_iter()
        .filter(|token| token.is_capturing())
        .enumerate()
        .map(|(index, token)| CapturingToken {
            index: index + 1,
            span: *token.annotation(),
        })
}

// These tests use `Glob` APIs, which wrap functions in this module.
#[cfg(test)]
mod tests {
    use crate::{Glob, Pattern};

    #[test]
    fn inspect_glob_capture_indices() {
        let glob = Glob::new("**/{foo*,bar*}/???").unwrap();
        let indices: Vec<_> = glob.captures().map(|token| token.index()).collect();
        assert_eq!(&indices, &[1, 2, 3, 4, 5]);
    }

    #[test]
    fn inspect_glob_capture_spans() {
        let glob = Glob::new("**/{foo*,bar*}/$").unwrap();
        let spans: Vec<_> = glob.captures().map(|token| token.span()).collect();
        assert_eq!(&spans, &[(0, 3), (3, 11), (15, 1)]);
    }

    #[test]
    fn inspect_glob_variance() {
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
}
