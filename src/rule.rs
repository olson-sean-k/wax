//! Rules and limitations for token sequences.
//!
//! This module provides the `check` function, which examines a token sequence
//! and emits an error if the sequence violates rules. Rules are invariants that
//! are difficult or impossible to enforce when parsing text and primarily
//! detect and reject token sequences that produce anomalous, meaningless, or
//! unexpected globs (regular expressions) when compiled.
//!
//! Most rules concern alternatives, which have complex interactions with
//! neighboring tokens.

// TODO: The `check` function fails fast and either report no errors or exactly
//       one error. To better support diagnostics, `check` should probably
//       perform an exhaustive analysis and report zero or more errors.

use itertools::Itertools as _;
#[cfg(feature = "diagnostics-report")]
use miette::{Diagnostic, LabeledSpan, SourceCode, SourceSpan};
use std::borrow::Cow;
#[cfg(feature = "diagnostics-report")]
use std::fmt::Display;
use std::iter::Fuse;
use thiserror::Error;

#[cfg(feature = "diagnostics-report")]
use crate::diagnostics::report::{CompositeSourceSpan, CorrelatedSourceSpan, SourceSpanExt as _};
use crate::token::{InvariantSize, Token, TokenKind, Tokenized};
use crate::{SliceExt as _, Terminals};

/// Maximum invariant size.
///
/// This size is equal to or greater than the maximum size of a path on
/// supported platforms. The primary purpose of this limit is to mitigate
/// malicious or mistaken expressions that encode very large invariant text,
/// namely via repetitions.
///
/// This limit is independent of the back end encoding. This code does not rely
/// on errors in the encoder by design, such as size limitations.
const MAX_INVARIANT_SIZE: InvariantSize = InvariantSize::new(0x10000);

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
                },
                Adjacency::Only { .. } | Adjacency::Last { .. } => None,
            };
            adjacency
        })
    }
}

/// Describes errors concerning rules and patterns in a glob expression.
///
/// Patterns must follow rules described in the [repository
/// documentation](https://github.com/olson-sean-k/wax/blob/master/README.md).
/// These rules are designed to avoid nonsense glob expressions and ambiguity.
/// If a glob expression parses but violates these rules or is otherwise
/// malformed, then this error is returned by some APIs.
///
/// When the `diagnostics-report` feature is enabled, this error implements the
/// [`Diagnostic`] trait and provides more detailed information about the rule
/// violation.
///
/// [`Diagnostic`]: miette::Diagnostic
#[derive(Debug, Error)]
#[error("malformed glob expression: {kind}")]
pub struct RuleError<'t> {
    expression: Cow<'t, str>,
    kind: ErrorKind,
    #[cfg(feature = "diagnostics-report")]
    span: CompositeSourceSpan,
}

impl<'t> RuleError<'t> {
    fn new(
        expression: Cow<'t, str>,
        kind: ErrorKind,
        #[cfg(feature = "diagnostics-report")] span: CompositeSourceSpan,
    ) -> Self {
        RuleError {
            expression,
            kind,
            #[cfg(feature = "diagnostics-report")]
            span,
        }
    }

    /// Clones any borrowed data into an owning instance.
    pub fn into_owned(self) -> RuleError<'static> {
        let RuleError {
            expression,
            kind,
            #[cfg(feature = "diagnostics-report")]
            span,
        } = self;
        RuleError {
            expression: expression.into_owned().into(),
            kind,
            #[cfg(feature = "diagnostics-report")]
            span,
        }
    }

    /// Gets the glob expression that violated pattern rules.
    pub fn expression(&self) -> &str {
        self.expression.as_ref()
    }
}

#[cfg(feature = "diagnostics-report")]
#[cfg_attr(docsrs, doc(cfg(feature = "diagnostics-report")))]
impl Diagnostic for RuleError<'_> {
    fn code<'a>(&'a self) -> Option<Box<dyn 'a + Display>> {
        Some(Box::new(String::from(match self.kind {
            ErrorKind::RootedSubGlob => "wax::glob::rooted_sub_glob",
            ErrorKind::SingularTree => "wax::glob::singular_tree",
            ErrorKind::SingularZeroOrMore => "wax::glob::singular_zero_or_more",
            ErrorKind::AdjacentBoundary => "wax::glob::adjacent_boundary",
            ErrorKind::AdjacentZeroOrMore => "wax::glob::adjacent_zero_or_more",
            ErrorKind::OversizedInvariant => "wax::glob::oversized_invariant",
            ErrorKind::IncompatibleBounds => "wax::glob::incompatible_bounds",
        })))
    }

    fn help<'a>(&'a self) -> Option<Box<dyn 'a + Display>> {
        match self.kind {
            ErrorKind::OversizedInvariant => Some(Box::new(String::from(
                "this error typically occurs when a repetition has a convergent bound that is too \
                 large",
            ))),
            _ => None,
        }
    }

    fn source_code(&self) -> Option<&dyn SourceCode> {
        Some(&self.expression)
    }

    fn labels(&self) -> Option<Box<dyn Iterator<Item = LabeledSpan>>> {
        Some(Box::new(self.span.labels().into_iter()))
    }
}

#[derive(Clone, Debug, Error)]
#[non_exhaustive]
enum ErrorKind {
    #[error("rooted sub-glob in group")]
    RootedSubGlob,
    #[error("singular tree wildcard `**` in group")]
    SingularTree,
    #[error("singular zero-or-more wildcard `*` or `$` in group")]
    SingularZeroOrMore,
    #[error("adjacent component boundaries `/` or `**`")]
    AdjacentBoundary,
    #[error("adjacent zero-or-more wildcards `*` or `$`")]
    AdjacentZeroOrMore,
    #[error("oversized invariant expression")]
    OversizedInvariant,
    #[error("incompatible repetition bounds")]
    IncompatibleBounds,
}

pub fn check<'t>(tokenized: &Tokenized<'t>) -> Result<(), RuleError<'t>> {
    boundary(tokenized)?;
    bounds(tokenized)?;
    group(tokenized)?;
    size(tokenized)?;
    Ok(())
}

fn boundary<'t>(tokenized: &Tokenized<'t>) -> Result<(), RuleError<'t>> {
    #[cfg_attr(not(feature = "diagnostics-report"), allow(unused))]
    if let Some((left, right)) = tokenized
        .walk()
        .group_by(|(position, _)| *position)
        .into_iter()
        .flat_map(|(_, group)| {
            group
                .map(|(_, token)| token)
                .tuple_windows::<(_, _)>()
                .filter(|(left, right)| {
                    left.is_component_boundary() && right.is_component_boundary()
                })
                .map(|(left, right)| (*left.annotation(), *right.annotation()))
        })
        .next()
    {
        Err(RuleError::new(
            tokenized.expression().clone(),
            ErrorKind::AdjacentBoundary,
            #[cfg(feature = "diagnostics-report")]
            CompositeSourceSpan::span(
                Some("here"),
                SourceSpan::from(left).union(&SourceSpan::from(right)),
            ),
        ))
    }
    else {
        Ok(())
    }
}

fn group<'t>(tokenized: &Tokenized<'t>) -> Result<(), RuleError<'t>> {
    use crate::token::TokenKind::{Separator, Wildcard};
    use crate::token::Wildcard::{Tree, ZeroOrMore};
    use crate::Terminals::{Only, StartEnd};

    struct CorrelatedError {
        kind: ErrorKind,
        #[cfg(feature = "diagnostics-report")]
        span: CorrelatedSourceSpan,
    }

    impl CorrelatedError {
        #[cfg_attr(not(feature = "diagnostics-report"), allow(unused))]
        fn new(kind: ErrorKind, outer: Option<&Token>, inner: &Token) -> Self {
            CorrelatedError {
                kind,
                #[cfg(feature = "diagnostics-report")]
                span: CorrelatedSourceSpan::split_some(
                    outer.map(Token::annotation).copied().map(From::from),
                    (*inner.annotation()).into(),
                ),
            }
        }
    }

    #[derive(Clone, Copy, Default)]
    struct Outer<'i, 't> {
        left: Option<&'i Token<'t>>,
        right: Option<&'i Token<'t>>,
    }

    impl<'i, 't> Outer<'i, 't> {
        pub fn push(self, left: Option<&'i Token<'t>>, right: Option<&'i Token<'t>>) -> Self {
            Outer {
                left: left.or(self.left),
                right: right.or(self.right),
            }
        }
    }

    fn has_starting_component_boundary<'t>(token: Option<&'t Token<'t>>) -> bool {
        token.map_or(false, |token| {
            token
                .walk()
                .starting()
                .any(|(_, token)| token.is_component_boundary())
        })
    }

    fn has_ending_component_boundary<'t>(token: Option<&'t Token<'t>>) -> bool {
        token.map_or(false, |token| {
            token
                .walk()
                .ending()
                .any(|(_, token)| token.is_component_boundary())
        })
    }

    fn has_starting_zom_token<'t>(token: Option<&'t Token<'t>>) -> bool {
        token.map_or(false, |token| {
            token
                .walk()
                .starting()
                .any(|(_, token)| matches!(token.kind(), Wildcard(ZeroOrMore(_))))
        })
    }

    fn has_ending_zom_token<'t>(token: Option<&'t Token<'t>>) -> bool {
        token.map_or(false, |token| {
            token
                .walk()
                .ending()
                .any(|(_, token)| matches!(token.kind(), Wildcard(ZeroOrMore(_))))
        })
    }

    fn diagnose<'i, 't>(
        // This is a somewhat unusual API, but it allows the lifetime `'t` of
        // the `Cow` to be properly forwarded to output values (`RuleError`).
        #[allow(clippy::ptr_arg)] expression: &'i Cow<'t, str>,
        #[cfg_attr(not(feature = "diagnostics-report"), allow(unused))] token: &'i Token<'t>,
        #[cfg_attr(not(feature = "diagnostics-report"), allow(unused))] label: &'static str,
    ) -> impl 'i + Copy + Fn(CorrelatedError) -> RuleError<'t>
    where
        't: 'i,
    {
        move |CorrelatedError {
                  kind,
                  #[cfg(feature = "diagnostics-report")]
                  span,
              }| {
            RuleError::new(
                expression.clone(),
                kind,
                #[cfg(feature = "diagnostics-report")]
                CompositeSourceSpan::correlated(
                    Some(label),
                    SourceSpan::from(*token.annotation()),
                    span,
                ),
            )
        }
    }

    fn recurse<'i, 't, I>(
        // This is a somewhat unusual API, but it allows the lifetime `'t` of
        // the `Cow` to be properly forwarded to output values (`RuleError`).
        #[allow(clippy::ptr_arg)] expression: &Cow<'t, str>,
        tokens: I,
        outer: Outer<'i, 't>,
    ) -> Result<(), RuleError<'t>>
    where
        I: IntoIterator<Item = &'i Token<'t>>,
        't: 'i,
    {
        for (left, token, right) in tokens.into_iter().adjacent().map(Adjacency::into_tuple) {
            match token.kind() {
                TokenKind::Alternative(ref alternative) => {
                    let outer = outer.push(left, right);
                    let diagnose = diagnose(expression, token, "in this alternative");
                    for tokens in alternative.branches() {
                        if let Some(terminals) = tokens.terminals() {
                            check_group(terminals, outer).map_err(diagnose)?;
                            check_group_alternative(terminals, outer).map_err(diagnose)?;
                        }
                        recurse(expression, tokens.iter(), outer)?;
                    }
                },
                TokenKind::Repetition(ref repetition) => {
                    let outer = outer.push(left, right);
                    let diagnose = diagnose(expression, token, "in this repetition");
                    let tokens = repetition.tokens();
                    if let Some(terminals) = tokens.terminals() {
                        check_group(terminals, outer).map_err(diagnose)?;
                        check_group_repetition(terminals, outer, repetition.bounds())
                            .map_err(diagnose)?;
                    }
                    recurse(expression, tokens.iter(), outer)?;
                },
                _ => {},
            }
        }
        Ok(())
    }

    fn check_group<'t>(
        terminals: Terminals<&Token>,
        outer: Outer<'t, 't>,
    ) -> Result<(), CorrelatedError> {
        let Outer { left, right } = outer;
        match terminals.map(|token| (token, token.kind())) {
            // The group is preceded by component boundaries; disallow leading
            // separators.
            //
            // For example, `foo/{bar,/}`.
            Only((inner, Separator(_))) | StartEnd((inner, Separator(_)), _)
                if has_ending_component_boundary(left) =>
            {
                Err(CorrelatedError::new(
                    ErrorKind::AdjacentBoundary,
                    left,
                    inner,
                ))
            },
            // The group is followed by component boundaries; disallow trailing
            // separators.
            //
            // For example, `{foo,/}/bar`.
            Only((inner, Separator(_))) | StartEnd(_, (inner, Separator(_)))
                if has_starting_component_boundary(right) =>
            {
                Err(CorrelatedError::new(
                    ErrorKind::AdjacentBoundary,
                    right,
                    inner,
                ))
            },
            // Disallow singular tree tokens.
            //
            // For example, `{foo,bar,**}`.
            Only((inner, Wildcard(Tree { .. }))) => {
                Err(CorrelatedError::new(ErrorKind::SingularTree, None, inner))
            },
            // The group is preceded by component boundaries; disallow leading
            // tree tokens.
            //
            // For example, `foo/{bar,**/baz}`.
            StartEnd((inner, Wildcard(Tree { .. })), _) if has_ending_component_boundary(left) => {
                Err(CorrelatedError::new(
                    ErrorKind::AdjacentBoundary,
                    left,
                    inner,
                ))
            },
            // The group is followed by component boundaries; disallow trailing
            // tree tokens.
            //
            // For example, `{foo,bar/**}/baz`.
            StartEnd(_, (inner, Wildcard(Tree { .. })))
                if has_starting_component_boundary(right) =>
            {
                Err(CorrelatedError::new(
                    ErrorKind::AdjacentBoundary,
                    right,
                    inner,
                ))
            },
            // The group is prefixed by a zero-or-more token; disallow leading
            // zero-or-more tokens.
            //
            // For example, `foo*{bar,*,baz}`.
            Only((inner, Wildcard(ZeroOrMore(_))))
            | StartEnd((inner, Wildcard(ZeroOrMore(_))), _)
                if has_ending_zom_token(left) =>
            {
                Err(CorrelatedError::new(
                    ErrorKind::AdjacentZeroOrMore,
                    left,
                    inner,
                ))
            },
            // The group is followed by a zero-or-more token; disallow trailing
            // zero-or-more tokens.
            //
            // For example, `{foo,*,bar}*baz`.
            Only((inner, Wildcard(ZeroOrMore(_))))
            | StartEnd(_, (inner, Wildcard(ZeroOrMore(_))))
                if has_starting_zom_token(right) =>
            {
                Err(CorrelatedError::new(
                    ErrorKind::AdjacentZeroOrMore,
                    right,
                    inner,
                ))
            },
            _ => Ok(()),
        }
    }

    fn check_group_alternative<'t>(
        terminals: Terminals<&Token>,
        outer: Outer<'t, 't>,
    ) -> Result<(), CorrelatedError> {
        let Outer { left, .. } = outer;
        match terminals.map(|token| (token, token.kind())) {
            // The alternative is preceded by a termination; disallow rooted
            // sub-globs.
            //
            // For example, `{foo,/}` or `{foo,/bar}`.
            Only((inner, Separator(_))) | StartEnd((inner, Separator(_)), _) if left.is_none() => {
                Err(CorrelatedError::new(ErrorKind::RootedSubGlob, left, inner))
            },
            // The alternative is preceded by a termination; disallow rooted
            // sub-globs.
            //
            // For example, `{/**/foo,bar}`.
            Only((inner, Wildcard(Tree { has_root: true })))
            | StartEnd((inner, Wildcard(Tree { has_root: true })), _)
                if left.is_none() =>
            {
                Err(CorrelatedError::new(ErrorKind::RootedSubGlob, left, inner))
            },
            _ => Ok(()),
        }
    }

    fn check_group_repetition<'t>(
        terminals: Terminals<&Token>,
        outer: Outer<'t, 't>,
        bounds: (usize, Option<usize>),
    ) -> Result<(), CorrelatedError> {
        let Outer { left, .. } = outer;
        let (lower, _) = bounds;
        match terminals.map(|token| (token, token.kind())) {
            // The repetition is preceded by a termination; disallow rooted
            // sub-globs with a zero lower bound.
            //
            // For example, `</foo:0,>`.
            Only((inner, Separator(_))) | StartEnd((inner, Separator(_)), _)
                if left.is_none() && lower == 0 =>
            {
                Err(CorrelatedError::new(ErrorKind::RootedSubGlob, left, inner))
            },
            // The repetition is preceded by a termination; disallow rooted
            // sub-globs with a zero lower bound.
            //
            // For example, `</**/foo>`.
            Only((inner, Wildcard(Tree { has_root: true })))
            | StartEnd((inner, Wildcard(Tree { has_root: true })), _)
                if left.is_none() && lower == 0 =>
            {
                Err(CorrelatedError::new(ErrorKind::RootedSubGlob, left, inner))
            },
            // The repetition begins and ends with a separator.
            //
            // For example, `</foo/bar/:1,>`.
            StartEnd((left, _), (right, _))
                if left.is_component_boundary() && right.is_component_boundary() =>
            {
                Err(CorrelatedError::new(
                    ErrorKind::AdjacentBoundary,
                    Some(left),
                    right,
                ))
            },
            // The repetition is a singular separator.
            //
            // For example, `</:1,>`.
            Only((token, Separator(_))) => Err(CorrelatedError::new(
                ErrorKind::AdjacentBoundary,
                None,
                token,
            )),
            // The repetition is a singular zero-or-more wildcard.
            //
            // For example, `<*:1,>`.
            Only((token, Wildcard(ZeroOrMore(_)))) => Err(CorrelatedError::new(
                ErrorKind::SingularZeroOrMore,
                None,
                token,
            )),
            _ => Ok(()),
        }
    }

    recurse(tokenized.expression(), tokenized.tokens(), Outer::default())
}

fn bounds<'t>(tokenized: &Tokenized<'t>) -> Result<(), RuleError<'t>> {
    #[cfg_attr(not(feature = "diagnostics-report"), allow(unused))]
    if let Some((_, token)) = tokenized.walk().find(|(_, token)| match token.kind() {
        TokenKind::Repetition(ref repetition) => {
            let (lower, upper) = repetition.bounds();
            upper.map_or(false, |upper| upper < lower || upper == 0)
        },
        _ => false,
    }) {
        Err(RuleError::new(
            tokenized.expression().clone(),
            ErrorKind::IncompatibleBounds,
            #[cfg(feature = "diagnostics-report")]
            CompositeSourceSpan::span(Some("here"), (*token.annotation()).into()),
        ))
    }
    else {
        Ok(())
    }
}

fn size<'t>(tokenized: &Tokenized<'t>) -> Result<(), RuleError<'t>> {
    #[cfg_attr(not(feature = "diagnostics-report"), allow(unused))]
    if let Some((_, token)) = tokenized
        .walk()
        // TODO: This is expensive. For each token tree encountered, the
        //       tree is traversed to determine its variance. If variant,
        //       the tree is traversed and queried again, revisiting the
        //       same tokens to recompute their local variance.
        .find(|(_, token)| {
            token
                .variance::<InvariantSize>()
                .as_invariance()
                .map_or(false, |size| *size >= MAX_INVARIANT_SIZE)
        })
    {
        Err(RuleError::new(
            tokenized.expression().clone(),
            ErrorKind::OversizedInvariant,
            #[cfg(feature = "diagnostics-report")]
            CompositeSourceSpan::span(Some("here"), (*token.annotation()).into()),
        ))
    }
    else {
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::rule::{Adjacency, IteratorExt as _};

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
}
