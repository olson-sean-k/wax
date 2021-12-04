#![cfg(any(feature = "diagnostics-inspect", feature = "diagnostics-report"))]

pub mod inspect;
pub mod report;

#[cfg_attr(docsrs, doc(cfg(feature = "diagnostics-inspect")))]
pub type Span = (usize, usize);
