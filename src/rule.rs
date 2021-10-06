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
use miette::{Diagnostic, LabeledSpan, SourceCode};
use std::borrow::Cow;
#[cfg(feature = "diagnostics")]
use std::fmt::Display;
use thiserror::Error;

#[cfg(feature = "diagnostics")]
use crate::span::{CompositeSourceSpan, CorrelatedSourceSpan, SourceSpanExt as _};
use crate::token::{Annotation, Token};
use crate::{IteratorExt as _, SliceExt as _, Terminals};

#[derive(Debug, Error)]
#[error("invalid glob expression: {kind}")]
pub struct RuleError<'t> {
    expression: Cow<'t, str>,
    kind: ErrorKind,
    #[cfg(feature = "diagnostics")]
    span: CompositeSourceSpan,
}

impl<'t> RuleError<'t> {
    fn new(
        expression: &'t str,
        kind: ErrorKind,
        #[cfg(feature = "diagnostics")] span: CompositeSourceSpan,
    ) -> Self {
        RuleError {
            expression: expression.into(),
            kind,
            #[cfg(feature = "diagnostics")]
            span,
        }
    }

    pub fn into_owned(self) -> RuleError<'static> {
        let RuleError {
            expression,
            kind,
            #[cfg(feature = "diagnostics")]
            span,
        } = self;
        RuleError {
            expression: expression.into_owned().into(),
            kind,
            #[cfg(feature = "diagnostics")]
            span,
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
        Some(Box::new(self.span.labels().into_iter()))
    }
}

#[derive(Clone, Debug, Error)]
#[non_exhaustive]
enum ErrorKind {
    #[error("rooted sub-glob or adjacent component boundaries `/` or `**` in alternative")]
    AlternativeBoundary,
    #[error("singular tree wildcard `**` in alternative")]
    AlternativeSingularTree,
    #[error("adjacent zero-or-more wildcards `*` or `$` in alternative")]
    AlternativeZeroOrMore,
    #[error("adjacent component boundaries `/` or `**`")]
    BoundaryAdjacent,
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

    #[derive(Clone)]
    struct CheckError {
        kind: ErrorKind,
        #[cfg(feature = "diagnostics")]
        span: CorrelatedSourceSpan,
    }

    impl CheckError {
        #[cfg_attr(not(feature = "diagnostics"), allow(unused))]
        fn new(
            kind: ErrorKind,
            outer: Option<&Token<Annotation>>,
            inner: &Token<Annotation>,
        ) -> Self {
            CheckError {
                kind,
                #[cfg(feature = "diagnostics")]
                span: CorrelatedSourceSpan::split_some(
                    outer.map(Token::annotation).cloned(),
                    inner.annotation().clone(),
                ),
            }
        }
    }

    #[derive(Clone, Copy, Default)]
    struct Outer<'t, 'i> {
        left: Option<&'i Token<'t, Annotation>>,
        right: Option<&'i Token<'t, Annotation>>,
    }

    fn has_preceding_component_boundary<'t>(token: Option<&'t Token<'t, Annotation>>) -> bool {
        token
            .map(|token| token.has_preceding_token_with(&mut |token| token.is_component_boundary()))
            .unwrap_or(false)
    }

    fn has_terminating_component_boundary<'t>(token: Option<&'t Token<'t, Annotation>>) -> bool {
        token
            .map(|token| {
                token.has_terminating_token_with(&mut |token| token.is_component_boundary())
            })
            .unwrap_or(false)
    }

    fn has_terminating_component_boundary_or_terminal<'t>(
        token: Option<&'t Token<'t, Annotation>>,
    ) -> bool {
        token
            .map(|token| {
                token.has_terminating_token_with(&mut |token| token.is_component_boundary())
            })
            .unwrap_or(true)
    }

    fn has_preceding_zom_token<'t>(token: Option<&'t Token<'t, Annotation>>) -> bool {
        token
            .map(|token| {
                token.has_preceding_token_with(&mut |token| {
                    matches!(token.kind(), Wildcard(ZeroOrMore(_)))
                })
            })
            .unwrap_or(false)
    }

    fn has_terminating_zom_token<'t>(token: Option<&'t Token<'t, Annotation>>) -> bool {
        token
            .map(|token| {
                token.has_terminating_token_with(&mut |token| {
                    matches!(token.kind(), Wildcard(ZeroOrMore(_)))
                })
            })
            .unwrap_or(false)
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
                    check(terminals, outer).map_err(
                        |CheckError {
                             kind,
                             #[cfg(feature = "diagnostics")]
                             span,
                         }| {
                            RuleError::new(
                                expression,
                                kind,
                                #[cfg(feature = "diagnostics")]
                                CompositeSourceSpan::correlated(
                                    Some("in this alternative"),
                                    token.annotation().clone(),
                                    span,
                                ),
                            )
                        },
                    )?;
                }
                recurse(expression, tokens.iter(), outer)?;
            }
        }
        Ok(())
    }

    fn check<'t, 'i>(
        terminals: Terminals<&'i Token<'t, Annotation>>,
        outer: Outer<'t, 'i>,
    ) -> Result<(), CheckError> {
        use ErrorKind::{AlternativeBoundary, AlternativeSingularTree, AlternativeZeroOrMore};

        let Outer { left, right } = outer;
        match terminals.map(|token| (token, token.kind())) {
            Only((inner, Separator)) if has_terminating_component_boundary_or_terminal(left) => {
                // The alternative is preceded by component boundaries or
                // terminations; disallow singular separators and rooted
                // sub-globs.
                //
                // For example, `foo/{bar,/}` or `{/,foo}`.
                Err(CheckError::new(AlternativeBoundary, left, inner))
            }
            Only((inner, Separator)) if has_preceding_component_boundary(right) => {
                // The alternative is followed by component boundaries; disallow
                // singular separators and rooted sub-globs.
                //
                // For example, `foo/{bar,/}` or `{/,foo}`.
                Err(CheckError::new(AlternativeBoundary, right, inner))
            }
            StartEnd((inner, Separator), _)
                if has_terminating_component_boundary_or_terminal(left) =>
            {
                // The alternative is preceded by component boundaries or
                // terminations; disallow leading separators and rooted
                // sub-globs.
                //
                // For example, `foo/{bar,/baz}` or `{bar,/baz}`.
                Err(CheckError::new(AlternativeBoundary, left, inner))
            }
            StartEnd(_, (inner, Separator)) if has_preceding_component_boundary(right) => {
                // The alternative is followed by component boundaries; disallow
                // trailing separators.
                //
                // For example, `{foo,bar/}/baz`.
                Err(CheckError::new(AlternativeBoundary, right, inner))
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
                Err(CheckError::new(AlternativeSingularTree, None, inner))
            }
            StartEnd((inner, Wildcard(Tree { is_rooted: true })), _) if left.is_none() => {
                // NOTE: `is_rooted` is not considered when the alternative is
                //       prefixed.
                // Disallow rooted sub-globs.
                //
                // For example, `{/**/foo,bar}`.
                Err(CheckError::new(AlternativeBoundary, None, inner))
            }
            StartEnd((inner, Wildcard(Tree { .. })), _)
                if has_terminating_component_boundary(left) =>
            {
                // The alternative is preceded by component boundaries; disallow
                // leading tree tokens.
                //
                // For example, `foo/{bar,**/baz}`.
                Err(CheckError::new(AlternativeBoundary, left, inner))
            }
            StartEnd(_, (inner, Wildcard(Tree { .. })))
                if has_preceding_component_boundary(right) =>
            {
                // The alternative is followed by component boundaries; disallow
                // trailing tree tokens.
                //
                // For example, `{foo,bar/**}/baz`.
                Err(CheckError::new(AlternativeBoundary, right, inner))
            }
            Only((inner, Wildcard(ZeroOrMore(_)))) if has_terminating_zom_token(left) => {
                // The alternative is prefixed by a zero-or-more token; disallow
                // singular zero-or-more tokens.
                //
                // For example, `foo*{bar,*,baz}`.
                Err(CheckError::new(AlternativeZeroOrMore, left, inner))
            }
            Only((inner, Wildcard(ZeroOrMore(_)))) if has_preceding_zom_token(right) => {
                // The alternative is followed by a zero-or-more token; disallow
                // singular zero-or-more tokens.
                //
                // For example, `foo*{bar,*,baz}`.
                Err(CheckError::new(AlternativeZeroOrMore, right, inner))
            }
            StartEnd((inner, Wildcard(ZeroOrMore(_))), _) if has_terminating_zom_token(left) => {
                // The alternative is prefixed by a zero-or-more token; disallow
                // leading zero-or-more tokens.
                //
                // For example, `foo*{bar,*baz}`.
                Err(CheckError::new(AlternativeZeroOrMore, left, inner))
            }
            StartEnd(_, (inner, Wildcard(ZeroOrMore(_)))) if has_preceding_zom_token(right) => {
                // The alternative is postfixed by a zero-or-more token;
                // disallow trailing zero-or-more tokens.
                //
                // For example, `{foo,bar*}*baz`.
                Err(CheckError::new(AlternativeZeroOrMore, right, inner))
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
    #[cfg_attr(not(feature = "diagnostics"), allow(unused))]
    if let Some((left, right)) = tokens
        .into_iter()
        .tuple_windows::<(_, _)>()
        .find(|(left, right)| left.is_component_boundary() && right.is_component_boundary())
        .map(|(left, right)| (left.annotation(), right.annotation()))
    {
        Err(RuleError::new(
            expression,
            ErrorKind::BoundaryAdjacent,
            #[cfg(feature = "diagnostics")]
            CompositeSourceSpan::span(Some("here"), left.union(right)),
        ))
    }
    else {
        Ok(())
    }
}
