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
use thiserror::Error;

use crate::token::Token;
use crate::{IteratorExt as _, SliceExt as _, Terminals};

#[derive(Debug, Error)]
#[non_exhaustive]
pub enum RuleError {
    #[error("rooted sub-glob or adjacent component boundaries `/` or `**` in alternative")]
    AlternativeBoundary,
    #[error("adjacent zero-or-more wildcards `*` or `$` in alternative")]
    AlternativeZeroOrMore,
    #[error("adjacent component boundaries `/` or `**`")]
    BoundaryAdjacent,
}

pub fn check<'t, I>(tokens: I) -> Result<(), RuleError>
where
    I: IntoIterator<Item = &'t Token<'t>>,
    I::IntoIter: Clone,
{
    let tokens = tokens.into_iter();
    alternative(tokens.clone())?;
    boundary(tokens)?;
    Ok(())
}

fn alternative<'t, I>(tokens: I) -> Result<(), RuleError>
where
    I: IntoIterator<Item = &'t Token<'t>>,
    I::IntoIter: Clone,
{
    use crate::token::Token::{Alternative, Separator, Wildcard};
    use crate::token::Wildcard::{Tree, ZeroOrMore};
    use crate::Terminals::{Only, StartEnd};

    fn is_component_boundary<'t>(adjacent: Option<&'t Token<'t>>) -> bool {
        adjacent
            .map(|token| token.is_component_boundary())
            .unwrap_or(false)
    }

    fn is_component_boundary_or_terminal<'t>(adjacent: Option<&'t Token<'t>>) -> bool {
        adjacent
            .map(|token| token.is_component_boundary())
            .unwrap_or(true)
    }

    fn recurse<'t>(
        tokens: impl Iterator<Item = &'t Token<'t>>,
        left: Option<&'t Token<'t>>,
        right: Option<&'t Token<'t>>,
    ) -> Result<(), RuleError> {
        for (local_left, alternative, local_right) in
            tokens
                .adjacent()
                .filter_map(|adjacency| match adjacency.into_tuple() {
                    (left, Alternative(alternative), right) => Some((left, alternative, right)),
                    _ => None,
                })
        {
            let left = local_left.or(left);
            let right = local_right.or(right);
            for tokens in alternative.branches() {
                if let Some(terminals) = tokens.terminals() {
                    // Check branch terminals against the tokens adjacent to
                    // their corresponding alternative token.
                    check(terminals, left, right)?;
                }
                recurse(tokens.iter(), left, right)?;
            }
        }
        Ok(())
    }

    fn check<'t>(
        terminals: Terminals<&Token<'t>>,
        left: Option<&Token<'t>>,
        right: Option<&Token<'t>>,
    ) -> Result<(), RuleError> {
        match terminals {
            Only(Separator)
                if is_component_boundary_or_terminal(left) || is_component_boundary(right) =>
            {
                // The alternative is adjacent to component boundaries or
                // terminations; disallow singular separators and rooted
                // sub-globs.
                //
                // For example, `foo/{bar,/}` or `{/,foo}`.
                Err(RuleError::AlternativeBoundary)
            }
            StartEnd(Separator, _) if is_component_boundary_or_terminal(left) => {
                // The alternative is preceded by component boundaries or
                // terminations; disallow leading separators and rooted
                // sub-globs.
                //
                // For example, `foo/{bar,/baz}` or `{bar,/baz}`.
                Err(RuleError::AlternativeBoundary)
            }
            StartEnd(_, Separator) if is_component_boundary(right) => {
                // The alternative is followed by component boundaries; disallow
                // trailing separators.
                //
                // For example, `{foo,bar/}/baz`.
                Err(RuleError::AlternativeBoundary)
            }
            Only(Wildcard(Tree { .. })) => {
                // NOTE: Supporting singular tree tokens is possible, but
                //       presents subtle edge cases that may be misleading or
                //       confusing. Rather than optimize or otherwise allow
                //       singular tree tokens, they are forbidden for
                //       simplicity.
                // Disallow singular tree tokens.
                //
                // For example, `{foo,bar,**}`.
                Err(RuleError::AlternativeBoundary)
            }
            StartEnd(Wildcard(Tree { is_rooted: true }), _) if left.is_none() => {
                // NOTE: `is_rooted` is not considered when the alternative is
                //       prefixed.
                // Disallow rooted sub-globs.
                //
                // For example, `{/**/foo,bar}`.
                Err(RuleError::AlternativeBoundary)
            }
            StartEnd(Wildcard(Tree { .. }), _) if is_component_boundary(left) => {
                // The alternative is preceded by component boundaries; disallow
                // leading tree tokens.
                //
                // For example, `foo/{bar,**/baz}`.
                Err(RuleError::AlternativeBoundary)
            }
            StartEnd(_, Wildcard(Tree { .. })) if is_component_boundary(right) => {
                // The alternative is followed by component boundaries; disallow
                // trailing tree tokens.
                //
                // For example, `{foo,bar/**}baz`.
                Err(RuleError::AlternativeBoundary)
            }
            Only(Wildcard(ZeroOrMore(_)))
                if matches!(
                    (left, right),
                    (Some(Wildcard(ZeroOrMore(_))), _) | (_, Some(Wildcard(ZeroOrMore(_))))
                ) =>
            {
                // The alternative is adjacent to a zero-or-more token; disallow
                // singular zero-or-more tokens.
                //
                // For example, `foo*{bar,*,baz}`.
                Err(RuleError::AlternativeZeroOrMore)
            }
            StartEnd(Wildcard(ZeroOrMore(_)), _)
                if matches!(left, Some(Wildcard(ZeroOrMore(_)))) =>
            {
                // The alternative is prefixed by a zero-or-more token; disallow
                // leading zero-or-more tokens.
                //
                // For example, `foo*{bar,*baz}`.
                Err(RuleError::AlternativeZeroOrMore)
            }
            StartEnd(_, Wildcard(ZeroOrMore(_)))
                if matches!(right, Some(Wildcard(ZeroOrMore(_)))) =>
            {
                // The alternative is postfixed by a zero-or-more token;
                // disallow trailing zero-or-more tokens.
                //
                // For example, `{foo,bar*}*baz`.
                Err(RuleError::AlternativeZeroOrMore)
            }
            _ => Ok(()),
        }
    }

    recurse(tokens.into_iter(), None, None)
}

fn boundary<'t, I>(tokens: I) -> Result<(), RuleError>
where
    I: IntoIterator<Item = &'t Token<'t>>,
    I::IntoIter: Clone,
{
    if tokens
        .into_iter()
        .tuple_windows::<(_, _)>()
        .any(|(left, right)| left.is_component_boundary() && right.is_component_boundary())
    {
        Err(RuleError::BoundaryAdjacent)
    } else {
        Ok(())
    }
}
