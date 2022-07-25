#![cfg(feature = "diagnostics")]

use miette::{Diagnostic, LabeledSpan, SourceSpan};
use std::borrow::Cow;
use std::cmp;
use tardar::BoxedDiagnostic;
use thiserror::Error;

use crate::token::{self, TokenKind, Tokenized};
use crate::Span;

pub trait SpanExt {
    fn union(&self, other: &Self) -> Self;
}

impl SpanExt for Span {
    fn union(&self, other: &Self) -> Self {
        let start = cmp::min(self.0, other.0);
        let end = cmp::max(self.0 + self.1, other.0 + other.1);
        (start, end - start)
    }
}

#[derive(Clone, Copy, Debug)]
pub struct CompositeSpan {
    label: Option<&'static str>,
    kind: CompositeKind,
}

impl CompositeSpan {
    pub fn span(label: Option<&'static str>, span: Span) -> Self {
        CompositeSpan {
            label,
            kind: CompositeKind::Span(span),
        }
    }

    pub fn correlated(label: Option<&'static str>, span: Span, correlated: CorrelatedSpan) -> Self {
        CompositeSpan {
            label,
            kind: CompositeKind::Correlated { span, correlated },
        }
    }

    pub fn labels(&self) -> Vec<LabeledSpan> {
        let label = self.label.map(str::to_string);
        match self.kind {
            CompositeKind::Span(ref span) => vec![LabeledSpan::new_with_span(label, *span)],
            CompositeKind::Correlated {
                ref span,
                ref correlated,
            } => {
                let mut labels = vec![LabeledSpan::new_with_span(label, *span)];
                labels.extend(correlated.labels());
                labels
            },
        }
    }
}

#[derive(Clone, Copy, Debug)]
enum CompositeKind {
    Span(Span),
    Correlated {
        span: Span,
        correlated: CorrelatedSpan,
    },
}

#[derive(Clone, Copy, Debug)]
pub enum CorrelatedSpan {
    Contiguous(Span),
    Split(Span, Span),
}

impl CorrelatedSpan {
    pub fn split_some(left: Option<Span>, right: Span) -> Self {
        if let Some(left) = left {
            CorrelatedSpan::Split(left, right)
        }
        else {
            CorrelatedSpan::Contiguous(right)
        }
    }

    pub fn labels(&self) -> Vec<LabeledSpan> {
        let label = Some("here".to_string());
        match self {
            CorrelatedSpan::Contiguous(ref span) => {
                vec![LabeledSpan::new_with_span(label, *span)]
            },
            CorrelatedSpan::Split(ref left, ref right) => vec![
                LabeledSpan::new_with_span(label.clone(), *left),
                LabeledSpan::new_with_span(label, *right),
            ],
        }
    }
}

impl From<Span> for CorrelatedSpan {
    fn from(span: Span) -> Self {
        CorrelatedSpan::Contiguous(span)
    }
}

#[derive(Clone, Debug, Diagnostic, Error)]
#[diagnostic(code(wax::glob::semantic_literal), severity(warning))]
#[error("`{literal}` has been interpreted as a literal with no semantics")]
pub struct SemanticLiteralWarning<'t> {
    #[source_code]
    expression: Cow<'t, str>,
    literal: Cow<'t, str>,
    #[label("here")]
    span: SourceSpan,
}

#[derive(Clone, Debug, Diagnostic, Error)]
#[diagnostic(code(wax::glob::terminating_separator), severity(warning))]
#[error("terminating separator may discard matches")]
pub struct TerminatingSeparatorWarning<'t> {
    #[source_code]
    expression: Cow<'t, str>,
    #[label("here")]
    span: SourceSpan,
}

pub fn diagnose<'i, 't>(
    tokenized: &'i Tokenized<'t>,
) -> impl 'i + Iterator<Item = BoxedDiagnostic<'t>> {
    None.into_iter()
        .chain(
            token::literals(tokenized.tokens())
                .filter(|(_, literal)| literal.is_semantic_literal())
                .map(|(component, literal)| {
                    Box::new(SemanticLiteralWarning {
                        expression: tokenized.expression().clone(),
                        literal: literal.text().clone(),
                        span: component
                            .tokens()
                            .iter()
                            .map(|token| *token.annotation())
                            .reduce(|left, right| left.union(&right))
                            .map(SourceSpan::from)
                            .expect("no tokens in component"),
                    }) as BoxedDiagnostic
                }),
        )
        .chain(tokenized.tokens().last().into_iter().filter_map(|token| {
            matches!(token.kind(), TokenKind::Separator(_)).then(|| {
                Box::new(TerminatingSeparatorWarning {
                    expression: tokenized.expression().clone(),
                    span: (*token.annotation()).into(),
                }) as BoxedDiagnostic
            })
        }))
}

// These tests exercise `Glob` APIs, which wrap functions in this module.
#[cfg(test)]
mod tests {
    use crate::Glob;

    // It is non-trivial to downcast `&dyn Diagnostic`, so diagnostics are
    // identified in tests by their code.
    const CODE_SEMANTIC_LITERAL: &str = "wax::glob::semantic_literal";
    const CODE_TERMINATING_SEPARATOR: &str = "wax::glob::terminating_separator";

    #[cfg(any(unix, windows))]
    #[test]
    fn diagnose_glob_semantic_literal_warning() {
        let glob = Glob::new("../foo").unwrap();
        let diagnostics: Vec<_> = glob.diagnose().collect();

        assert!(diagnostics.iter().any(|diagnostic| diagnostic
            .code()
            .map_or(false, |code| code.to_string() == CODE_SEMANTIC_LITERAL)));
    }

    #[test]
    fn diagnose_glob_terminating_separator_warning() {
        let glob = Glob::new("**/foo/").unwrap();
        let diagnostics: Vec<_> = glob.diagnose().collect();

        assert!(diagnostics.iter().any(|diagnostic| diagnostic
            .code()
            .map_or(false, |code| code.to_string() == CODE_TERMINATING_SEPARATOR)));
    }
}
