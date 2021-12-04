#![cfg(feature = "diagnostics-inspect")]

use crate::diagnostics::Span;
use crate::token::Token;

#[cfg_attr(docsrs, doc(cfg(feature = "diagnostics-inspect")))]
#[derive(Clone, Copy, Debug)]
pub struct CapturingToken {
    index: usize,
    span: Span,
}

impl CapturingToken {
    pub fn index(&self) -> usize {
        self.index
    }

    pub fn span(&self) -> Span {
        self.span
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

// These tests use `Glob` APIs, which simply wrap functions in this module.
#[cfg(test)]
mod tests {
    use crate::Glob;

    #[test]
    fn inspect_capture_indices() {
        let glob = Glob::new("**/{foo*,bar*}/???").unwrap();
        let indices: Vec<_> = glob.captures().map(|token| token.index()).collect();
        assert_eq!(&indices, &[1, 2, 3, 4, 5]);
    }

    #[test]
    fn inspect_capture_spans() {
        let glob = Glob::new("**/{foo*,bar*}/$").unwrap();
        let spans: Vec<_> = glob.captures().map(|token| token.span()).collect();
        assert_eq!(&spans, &[(0, 3), (3, 11), (15, 1)]);
    }
}
