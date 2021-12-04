#![cfg(feature = "diagnostics-report")]

use miette::{Diagnostic, LabeledSpan, SourceSpan};
use std::borrow::Cow;
use std::cmp;
use std::path::PathBuf;
use thiserror::Error;
use vec1::Vec1;

use crate::token::{self, TokenKind, Tokenized};

pub type BoxedDiagnostic<'t> = Box<dyn Diagnostic + 't>;
#[cfg_attr(docsrs, doc(cfg(feature = "diagnostics-report")))]
pub type DiagnosticResult<'t, T> = Result<(T, Vec<BoxedDiagnostic<'t>>), Vec1<BoxedDiagnostic<'t>>>;

#[cfg_attr(docsrs, doc(cfg(feature = "diagnostics-report")))]
pub trait DiagnosticResultExt<'t, T> {
    fn diagnostics(&self) -> &[BoxedDiagnostic<'t>];
}

impl<'t, T> DiagnosticResultExt<'t, T> for DiagnosticResult<'t, T> {
    fn diagnostics(&self) -> &[BoxedDiagnostic<'t>] {
        match self {
            Ok((_, ref diagnostics)) => diagnostics,
            Err(ref diagnostics) => diagnostics,
        }
    }
}

#[cfg_attr(docsrs, doc(cfg(feature = "diagnostics-report")))]
pub trait DiagnosticGlob<'t>: Sized {
    fn new(expression: &'t str) -> DiagnosticResult<'t, Self>;

    fn partitioned(expression: &'t str) -> DiagnosticResult<'t, (PathBuf, Self)>;
}

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
        let label = self.label.map(|label| label.to_string());
        match self.kind {
            CompositeKind::Span(ref span) => vec![LabeledSpan::new_with_span(label, span.clone())],
            CompositeKind::Correlated {
                ref span,
                ref correlated,
            } => {
                let mut labels = vec![LabeledSpan::new_with_span(label, span.clone())];
                labels.extend(correlated.labels());
                labels
            }
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
                vec![LabeledSpan::new_with_span(label, span.clone())]
            }
            CorrelatedSourceSpan::Split(ref left, ref right) => vec![
                LabeledSpan::new_with_span(label.clone(), left.clone()),
                LabeledSpan::new_with_span(label, right.clone()),
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

pub fn diagnostics<'i, 't>(
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
        .chain(tokenized.tokens().last().into_iter().flat_map(|token| {
            matches!(token.kind(), TokenKind::Separator).then(|| {
                Box::new(TerminatingSeparatorWarning {
                    expression: tokenized.expression().clone(),
                    span: (*token.annotation()).into(),
                }) as BoxedDiagnostic
            })
        }))
}

// These tests use `Glob` APIs, which simply wrap functions in this module.
#[cfg(test)]
mod tests {
    use crate::Glob;

    // It is non-trivial to downcast `&dyn Diagnostic`, so diagnostics are
    // identified in tests by code.
    const CODE_SEMANTIC_LITERAL: &str = "wax::glob::semantic_literal";
    const CODE_TERMINATING_SEPARATOR: &str = "wax::glob::terminating_separator";

    #[cfg(any(unix, windows))]
    #[test]
    fn report_semantic_literal_warning() {
        let glob = Glob::new("../foo").unwrap();
        let diagnostics: Vec<_> = glob.diagnostics().collect();

        assert!(diagnostics.iter().any(|diagnostic| diagnostic
            .code()
            .map(|code| code.to_string() == CODE_SEMANTIC_LITERAL)
            .unwrap_or(false)));
    }

    #[test]
    fn report_terminating_separator_warning() {
        let glob = Glob::new("**/foo/").unwrap();
        let diagnostics: Vec<_> = glob.diagnostics().collect();

        assert!(diagnostics.iter().any(|diagnostic| diagnostic
            .code()
            .map(|code| code.to_string() == CODE_TERMINATING_SEPARATOR)
            .unwrap_or(false)));
    }
}
