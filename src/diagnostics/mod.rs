#![cfg(any(feature = "diagnostics-inspect", feature = "diagnostics-report"))]

pub mod inspect;
pub mod report;

/// Location and length of a token within a glob expression.
///
/// Spans are encoded as a tuple of `usize`s, where the first element is the
/// location or position and the second element is the length.
///
/// # Examples
///
/// Spans can be used to isolate sub-expressions.
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
pub type Span = (usize, usize);
