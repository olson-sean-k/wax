#![cfg(feature = "diagnostics")]

use miette::{Diagnostic, LabeledSpan, SourceSpan};
use std::borrow::Cow;
use std::cmp;
use tardar::BoxedDiagnostic;
use thiserror::Error;

use crate::token::{self, TokenKind, Tokenized};

pub trait SourceSpanExt {
    fn union(&self, other: &SourceSpan) -> SourceSpan;
}

impl SourceSpanExt for SourceSpan {
    fn union(&self, other: &SourceSpan) -> SourceSpan {
        let start = cmp::min(self.offset(), other.offset());
        let end = cmp::max(self.offset() + self.len(), other.offset() + other.len());
        (start, end - start).into()
    }
}

#[derive(Clone, Debug)]
pub struct CompositeSourceSpan {
    label: Option<&'static str>,
    kind: CompositeKind,
}

impl CompositeSourceSpan {
    pub fn span(label: Option<&'static str>, span: SourceSpan) -> Self {
        CompositeSourceSpan {
            label,
            kind: CompositeKind::Span(span),
        }
    }

    pub fn correlated(
        label: Option<&'static str>,
        span: SourceSpan,
        correlated: CorrelatedSourceSpan,
    ) -> Self {
        CompositeSourceSpan {
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

#[derive(Clone, Debug)]
enum CompositeKind {
    Span(SourceSpan),
    Correlated {
        span: SourceSpan,
        correlated: CorrelatedSourceSpan,
    },
}

#[derive(Clone, Debug)]
pub enum CorrelatedSourceSpan {
    Contiguous(SourceSpan),
    Split(SourceSpan, SourceSpan),
}

impl CorrelatedSourceSpan {
    pub fn split_some(left: Option<SourceSpan>, right: SourceSpan) -> Self {
        if let Some(left) = left {
            CorrelatedSourceSpan::Split(left, right)
        }
        else {
            CorrelatedSourceSpan::Contiguous(right)
        }
    }

    pub fn labels(&self) -> Vec<LabeledSpan> {
        let label = Some("here".to_string());
        match self {
            CorrelatedSourceSpan::Contiguous(ref span) => {
                vec![LabeledSpan::new_with_span(label, *span)]
            },
            CorrelatedSourceSpan::Split(ref left, ref right) => vec![
                LabeledSpan::new_with_span(label.clone(), *left),
                LabeledSpan::new_with_span(label, *right),
            ],
        }
    }
}

impl From<SourceSpan> for CorrelatedSourceSpan {
    fn from(span: SourceSpan) -> Self {
        CorrelatedSourceSpan::Contiguous(span)
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
                            .map(|token| SourceSpan::from(*token.annotation()))
                            .reduce(|left, right| left.union(&right))
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
