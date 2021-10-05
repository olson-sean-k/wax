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

use itertools::Itertools as _;
#[cfg(feature = "diagnostics")]
use miette::{Diagnostic, LabeledSpan, SourceCode, SourceSpan};
use std::borrow::Cow;
#[cfg(feature = "diagnostics")]
use std::fmt::Display;
use thiserror::Error;

use crate::token::{Annotation, Token};
#[cfg(feature = "diagnostics")]
use crate::SourceSpanExt as _;
use crate::{IteratorExt as _, SliceExt as _, Terminals};

#[cfg(feature = "diagnostics")]
type AlternativeAnnotation = AlternativeSpan;
#[cfg(not(feature = "diagnostics"))]
type AlternativeAnnotation = ();

#[cfg(feature = "diagnostics")]
type BoundaryAnnotation = SourceSpan;
#[cfg(not(feature = "diagnostics"))]
type BoundaryAnnotation = ();

#[derive(Debug, Error)]
#[error("invalid glob expression: {kind}")]
pub struct RuleError<'t> {
    expression: Cow<'t, str>,
    kind: ErrorKind,
}

impl<'t> RuleError<'t> {
    fn new(expression: &'t str, kind: ErrorKind) -> Self {
        RuleError {
            expression: expression.into(),
            kind,
        }
    }

    pub fn into_owned(self) -> RuleError<'static> {
        let RuleError { expression, kind } = self;
        RuleError {
            expression: expression.into_owned().into(),
            kind,
        }
    }

    pub fn expression(&self) -> &str {
        self.expression.as_ref()
    }
}

#[cfg(feature = "diagnostics")]
impl<'t> Diagnostic for RuleError<'t> {
    fn code<'a>(&'a self) -> Option<Box<dyn 'a + Display>> {
        Some(Box::new(String::from("glob::rule")))
    }

    fn source_code(&self) -> Option<&dyn SourceCode> {
        Some(&self.expression)
    }

    fn labels(&self) -> Option<Box<dyn Iterator<Item = LabeledSpan>>> {
        use crate::rule::ErrorKind::{
            AlternativeBoundary, AlternativeSingularTree, AlternativeZeroOrMore, BoundaryAdjacent,
        };

        let here = Some(String::from("here"));
        Some(Box::new(
            match self.kind {
                AlternativeBoundary(ref annotation)
                | AlternativeSingularTree(ref annotation)
                | AlternativeZeroOrMore(ref annotation) => {
                    let alternative = LabeledSpan::new_with_span(
                        Some(String::from("in this alternative")),
                        annotation.alternative.clone(),
                    );
                    match annotation.conflicts {
                        SpanGroup::Contiguous(ref contiguous) => {
                            vec![
                                alternative,
                                LabeledSpan::new_with_span(here, contiguous.clone()),
                            ]
                        }
                        SpanGroup::Split(ref left, ref right) => vec![
                            alternative,
                            LabeledSpan::new_with_span(here.clone(), left.clone()),
                            LabeledSpan::new_with_span(here, right.clone()),
                        ],
                    }
                }
                BoundaryAdjacent(ref annotation) => {
                    vec![LabeledSpan::new_with_span(here, annotation.clone())]
                }
            }
            .into_iter(),
        ))
    }
}

#[derive(Clone, Debug, Error)]
#[non_exhaustive]
enum ErrorKind {
    #[error("rooted sub-glob or adjacent component boundaries `/` or `**` in alternative")]
    AlternativeBoundary(AlternativeAnnotation),
    #[error("singular tree wildcard `**` in alternative")]
    AlternativeSingularTree(AlternativeAnnotation),
    #[error("adjacent zero-or-more wildcards `*` or `$` in alternative")]
    AlternativeZeroOrMore(AlternativeAnnotation),
    #[error("adjacent component boundaries `/` or `**`")]
    BoundaryAdjacent(BoundaryAnnotation),
}

#[cfg(feature = "diagnostics")]
#[derive(Clone, Debug)]
struct AlternativeSpan {
    alternative: SourceSpan,
    conflicts: SpanGroup,
}

#[cfg(feature = "diagnostics")]
#[derive(Clone, Debug)]
enum SpanGroup {
    Contiguous(SourceSpan),
    Split(SourceSpan, SourceSpan),
}

#[cfg(feature = "diagnostics")]
impl SpanGroup {
    pub fn split_some(left: Option<SourceSpan>, right: SourceSpan) -> Self {
        if let Some(left) = left {
            SpanGroup::Split(left, right)
        }
        else {
            SpanGroup::Contiguous(right)
        }
    }
}

#[cfg(feature = "diagnostics")]
impl From<SourceSpan> for SpanGroup {
    fn from(span: SourceSpan) -> Self {
        SpanGroup::Contiguous(span)
    }
}

pub fn check<'t, 'i, I>(expression: &'t str, tokens: I) -> Result<(), RuleError<'t>>
where
    I: IntoIterator<Item = &'i Token<'t, Annotation>>,
    I::IntoIter: Clone,
    't: 'i,
{
    let tokens = tokens.into_iter();
    alternative(expression, tokens.clone())?;
    boundary(expression, tokens)?;
    Ok(())
}

fn alternative<'t, 'i, I>(expression: &'t str, tokens: I) -> Result<(), RuleError<'t>>
where
    I: IntoIterator<Item = &'i Token<'t, Annotation>>,
    't: 'i,
{
    use crate::token::TokenKind::{Alternative, Separator, Wildcard};
    use crate::token::Wildcard::{Tree, ZeroOrMore};
    use crate::Terminals::{Only, StartEnd};

    #[derive(Clone, Copy, Default)]
    struct Outer<'t, 'i> {
        left: Option<&'i Token<'t, Annotation>>,
        right: Option<&'i Token<'t, Annotation>>,
    }

    fn is_component_boundary<'t>(adjacent: Option<&'t Token<'t, Annotation>>) -> bool {
        adjacent
            .map(|token| token.is_component_boundary())
            .unwrap_or(false)
    }

    fn is_component_boundary_or_terminal<'t>(adjacent: Option<&'t Token<'t, Annotation>>) -> bool {
        adjacent
            .map(|token| token.is_component_boundary())
            .unwrap_or(true)
    }

    fn recurse<'t, 'i, I>(
        expression: &'t str,
        tokens: I,
        outer: Outer<'t, 'i>,
    ) -> Result<(), RuleError<'t>>
    where
        I: IntoIterator<Item = &'i Token<'t, Annotation>>,
        't: 'i,
    {
        #[cfg_attr(not(feature = "diagnostics"), allow(unused))]
        for (token, alternative, left, right) in
            tokens.into_iter().adjacent().filter_map(|adjacency| {
                let (left, token, right) = adjacency.into_tuple();
                match token.kind() {
                    Alternative(alternative) => Some((token, alternative, left, right)),
                    _ => None,
                }
            })
        {
            let outer = Outer {
                left: left.or(outer.left),
                right: right.or(outer.right),
            };
            for tokens in alternative.branches() {
                if let Some(terminals) = tokens.terminals() {
                    // Check branch terminals against the tokens adjacent to
                    // their corresponding alternative token.
                    check(terminals, outer, token.annotation())
                        .map_err(|kind| RuleError::new(expression, kind))?;
                }
                recurse(expression, tokens.iter(), outer)?;
            }
        }
        Ok(())
    }

    fn check<'t, 'i>(
        terminals: Terminals<&'i Token<'t, Annotation>>,
        outer: Outer<'t, 'i>,
        #[cfg_attr(not(feature = "diagnostics"), allow(unused))] annotation: &Annotation,
    ) -> Result<(), ErrorKind> {
        #[cfg(feature = "diagnostics")]
        let annotate = |outer: Option<_>, inner: &Token<Annotation>| AlternativeSpan {
            alternative: annotation.clone(),
            conflicts: SpanGroup::split_some(
                outer.map(Token::annotation).cloned(),
                inner.annotation().clone(),
            ),
        };
        #[cfg(not(feature = "diagnostics"))]
        let annotate = |_: Option<_>, _: &Token<Annotation>| {};

        let Outer { left, right } = outer;
        #[cfg_attr(not(feature = "diagnostics"), allow(clippy::unit_arg))]
        match terminals.map(|token| (token, token.kind())) {
            Only((inner, Separator)) if is_component_boundary_or_terminal(left) => {
                // The alternative is preceded by component boundaries or
                // terminations; disallow singular separators and rooted
                // sub-globs.
                //
                // For example, `foo/{bar,/}` or `{/,foo}`.
                Err(ErrorKind::AlternativeBoundary(annotate(left, inner)))
            }
            Only((inner, Separator)) if is_component_boundary(right) => {
                // The alternative is followed by component boundaries; disallow
                // singular separators and rooted sub-globs.
                //
                // For example, `foo/{bar,/}` or `{/,foo}`.
                Err(ErrorKind::AlternativeBoundary(annotate(right, inner)))
            }
            StartEnd((inner, Separator), _) if is_component_boundary_or_terminal(left) => {
                // The alternative is preceded by component boundaries or
                // terminations; disallow leading separators and rooted
                // sub-globs.
                //
                // For example, `foo/{bar,/baz}` or `{bar,/baz}`.
                Err(ErrorKind::AlternativeBoundary(annotate(left, inner)))
            }
            StartEnd(_, (inner, Separator)) if is_component_boundary(right) => {
                // The alternative is followed by component boundaries; disallow
                // trailing separators.
                //
                // For example, `{foo,bar/}/baz`.
                Err(ErrorKind::AlternativeBoundary(annotate(right, inner)))
            }
            Only((inner, Wildcard(Tree { .. }))) => {
                // NOTE: Supporting singular tree tokens is possible, but
                //       presents subtle edge cases that may be misleading or
                //       confusing. Rather than optimize or otherwise allow
                //       singular tree tokens, they are forbidden for
                //       simplicity.
                // Disallow singular tree tokens.
                //
                // For example, `{foo,bar,**}`.
                Err(ErrorKind::AlternativeSingularTree(annotate(None, inner)))
            }
            StartEnd((inner, Wildcard(Tree { is_rooted: true })), _) if left.is_none() => {
                // NOTE: `is_rooted` is not considered when the alternative is
                //       prefixed.
                // Disallow rooted sub-globs.
                //
                // For example, `{/**/foo,bar}`.
                Err(ErrorKind::AlternativeBoundary(annotate(None, inner)))
            }
            StartEnd((inner, Wildcard(Tree { .. })), _) if is_component_boundary(left) => {
                // The alternative is preceded by component boundaries; disallow
                // leading tree tokens.
                //
                // For example, `foo/{bar,**/baz}`.
                Err(ErrorKind::AlternativeBoundary(annotate(left, inner)))
            }
            StartEnd(_, (inner, Wildcard(Tree { .. }))) if is_component_boundary(right) => {
                // The alternative is followed by component boundaries; disallow
                // trailing tree tokens.
                //
                // For example, `{foo,bar/**}/baz`.
                Err(ErrorKind::AlternativeBoundary(annotate(right, inner)))
            }
            Only((inner, Wildcard(ZeroOrMore(_))))
                if matches!(left.map(Token::kind), Some(Wildcard(ZeroOrMore(_)))) =>
            {
                // The alternative is prefixed by a zero-or-more token; disallow
                // singular zero-or-more tokens.
                //
                // For example, `foo*{bar,*,baz}`.
                Err(ErrorKind::AlternativeZeroOrMore(annotate(left, inner)))
            }
            Only((inner, Wildcard(ZeroOrMore(_))))
                if matches!(right.map(Token::kind), Some(Wildcard(ZeroOrMore(_)))) =>
            {
                // The alternative is followed by a zero-or-more token; disallow
                // singular zero-or-more tokens.
                //
                // For example, `foo*{bar,*,baz}`.
                Err(ErrorKind::AlternativeZeroOrMore(annotate(right, inner)))
            }
            StartEnd((inner, Wildcard(ZeroOrMore(_))), _)
                if matches!(left.map(Token::kind), Some(Wildcard(ZeroOrMore(_)))) =>
            {
                // The alternative is prefixed by a zero-or-more token; disallow
                // leading zero-or-more tokens.
                //
                // For example, `foo*{bar,*baz}`.
                Err(ErrorKind::AlternativeZeroOrMore(annotate(left, inner)))
            }
            StartEnd(_, (inner, Wildcard(ZeroOrMore(_))))
                if matches!(right.map(Token::kind), Some(Wildcard(ZeroOrMore(_)))) =>
            {
                // The alternative is postfixed by a zero-or-more token;
                // disallow trailing zero-or-more tokens.
                //
                // For example, `{foo,bar*}*baz`.
                Err(ErrorKind::AlternativeZeroOrMore(annotate(right, inner)))
            }
            _ => Ok(()),
        }
    }

    recurse(expression, tokens, Default::default())
}

fn boundary<'t, 'i, I>(expression: &'t str, tokens: I) -> Result<(), RuleError<'t>>
where
    I: IntoIterator<Item = &'i Token<'t, Annotation>>,
    't: 'i,
{
    #[cfg(feature = "diagnostics")]
    let annotate = |(left, right): (&SourceSpan, _)| left.union(right);
    #[cfg(not(feature = "diagnostics"))]
    let annotate = |_| {};

    if let Some(annotations) = tokens
        .into_iter()
        .tuple_windows::<(_, _)>()
        .find(|(left, right)| left.is_component_boundary() && right.is_component_boundary())
        .map(|(left, right)| (left.annotation(), right.annotation()))
    {
        Err(RuleError::new(
            expression,
            #[cfg_attr(not(feature = "diagnostics"), allow(clippy::unit_arg))]
            ErrorKind::BoundaryAdjacent(annotate(annotations)),
        ))
    }
    else {
        Ok(())
    }
}
