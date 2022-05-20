#![cfg(feature = "diagnostics-report")]

use miette::{Diagnostic, LabeledSpan, SourceSpan};
use std::borrow::Cow;
use std::cmp;
use thiserror::Error;
use vec1::{vec1, Vec1};

use crate::token::{self, TokenKind, Tokenized};

pub type BoxedDiagnostic<'t> = Box<dyn Diagnostic + 't>;

/// `Result` that includes diagnostics on both success and failure.
///
/// On success, the `Ok` variant contains zero or more diagnostics. On failure,
/// the `Err` variant contains one or more diagnostics, where at least one of
/// the diagnostics is an error.
#[cfg_attr(docsrs, doc(cfg(feature = "diagnostics-report")))]
pub type DiagnosticResult<'t, T> = Result<(T, Vec<BoxedDiagnostic<'t>>), Vec1<BoxedDiagnostic<'t>>>;

pub trait IteratorExt<'t>: Iterator + Sized {
    fn into_non_error_diagnostic(self) -> DiagnosticResult<'t, ()>;
}

impl<'t, I> IteratorExt<'t> for I
where
    I: Iterator<Item = BoxedDiagnostic<'t>>,
{
    fn into_non_error_diagnostic(self) -> DiagnosticResult<'t, ()> {
        Ok(((), self.collect()))
    }
}

pub trait ResultExt<'t, T, E> {
    fn into_error_diagnostic(self) -> DiagnosticResult<'t, T>
    where
        E: 't + Diagnostic;
}

impl<'t, T, E> ResultExt<'t, T, E> for Result<T, E> {
    fn into_error_diagnostic(self) -> DiagnosticResult<'t, T>
    where
        E: 't + Diagnostic,
    {
        match self {
            Ok(value) => Ok((value, vec![])),
            Err(error) => Err(vec1![Box::new(error) as Box<dyn Diagnostic + 't>]),
        }
    }
}

/// Extension traits for `Result`s with diagnostics.
#[cfg_attr(docsrs, doc(cfg(feature = "diagnostics-report")))]
pub trait DiagnosticResultExt<'t, T> {
    fn ok_value(self) -> Option<T>;

    fn diagnostics(&self) -> &[BoxedDiagnostic<'t>];

    fn map_value<U, F>(self, f: F) -> DiagnosticResult<'t, U>
    where
        F: FnOnce(T) -> U;

    fn and_then_diagnose<U, F>(self, f: F) -> DiagnosticResult<'t, U>
    where
        F: FnOnce(T) -> DiagnosticResult<'t, U>;
}

impl<'t, T> DiagnosticResultExt<'t, T> for DiagnosticResult<'t, T> {
    fn ok_value(self) -> Option<T> {
        match self {
            Ok((value, _)) => Some(value),
            _ => None,
        }
    }

    /// Gets the diagnostics associated with the `Result`.
    fn diagnostics(&self) -> &[BoxedDiagnostic<'t>] {
        match self {
            Ok((_, ref diagnostics)) => diagnostics,
            Err(ref diagnostics) => diagnostics,
        }
    }

    fn map_value<U, F>(self, f: F) -> DiagnosticResult<'t, U>
    where
        F: FnOnce(T) -> U,
    {
        match self {
            Ok((value, diagnostics)) => Ok((f(value), diagnostics)),
            Err(diagnostics) => Err(diagnostics),
        }
    }

    fn and_then_diagnose<U, F>(self, f: F) -> DiagnosticResult<'t, U>
    where
        F: FnOnce(T) -> DiagnosticResult<'t, U>,
    {
        match self {
            Ok((value, mut diagnostics)) => match f(value) {
                Ok((value, tail)) => {
                    diagnostics.extend(tail);
                    Ok((value, diagnostics))
                },
                Err(tail) => {
                    diagnostics.extend(tail);
                    Err(diagnostics
                        .try_into()
                        .expect("diagnostic failure with no errors"))
                },
            },
            Err(diagnostics) => Err(diagnostics),
        }
    }
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
        .chain(tokenized.tokens().last().into_iter().filter_map(|token| {
            matches!(token.kind(), TokenKind::Separator(_)).then(|| {
                Box::new(TerminatingSeparatorWarning {
                    expression: tokenized.expression().clone(),
                    span: (*token.annotation()).into(),
                }) as BoxedDiagnostic
            })
        }))
}

// These tests use `Glob` APIs, which wrap functions in this module.
#[cfg(test)]
mod tests {
    use crate::Glob;

    // It is non-trivial to downcast `&dyn Diagnostic`, so diagnostics are
    // identified in tests by their code.
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
