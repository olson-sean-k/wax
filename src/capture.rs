use regex::Captures as BorrowedText;
use std::str;

#[derive(Clone, Debug)]
struct OwnedText {
    matched: String,
    ranges: Vec<Option<(usize, usize)>>,
}

impl OwnedText {
    pub fn get(&self, index: usize) -> Option<&str> {
        if index == 0 {
            Some(self.matched.as_ref())
        }
        else {
            self.ranges
                .get(index - 1)
                .map(|range| range.map(|range| &self.matched[range.0..range.1]))
                .flatten()
        }
    }
}

impl<'t> From<BorrowedText<'t>> for OwnedText {
    fn from(captures: BorrowedText<'t>) -> Self {
        From::from(&captures)
    }
}

impl<'m, 't> From<&'m BorrowedText<'t>> for OwnedText {
    fn from(captures: &'m BorrowedText<'t>) -> Self {
        let matched = captures.get(0).unwrap().as_str().into();
        let ranges = captures
            .iter()
            .skip(1)
            .map(|capture| capture.map(|capture| (capture.start(), capture.end())))
            .collect();
        OwnedText { matched, ranges }
    }
}

#[derive(Debug)]
enum MaybeOwnedText<'t> {
    Borrowed(BorrowedText<'t>),
    Owned(OwnedText),
}

impl<'t> MaybeOwnedText<'t> {
    fn into_owned(self) -> MaybeOwnedText<'static> {
        match self {
            MaybeOwnedText::Borrowed(borrowed) => OwnedText::from(borrowed).into(),
            MaybeOwnedText::Owned(owned) => owned.into(),
        }
    }

    fn to_owned(&self) -> MaybeOwnedText<'static> {
        match self {
            MaybeOwnedText::Borrowed(ref borrowed) => OwnedText::from(borrowed).into(),
            MaybeOwnedText::Owned(ref owned) => owned.clone().into(),
        }
    }
}

impl<'t> From<BorrowedText<'t>> for MaybeOwnedText<'t> {
    fn from(captures: BorrowedText<'t>) -> Self {
        MaybeOwnedText::Borrowed(captures)
    }
}

impl From<OwnedText> for MaybeOwnedText<'static> {
    fn from(captures: OwnedText) -> Self {
        MaybeOwnedText::Owned(captures)
    }
}

#[derive(Debug)]
pub struct MatchedText<'t> {
    inner: MaybeOwnedText<'t>,
}

impl<'t> MatchedText<'t> {
    pub fn into_owned(self) -> MatchedText<'static> {
        let MatchedText { inner } = self;
        MatchedText {
            inner: inner.into_owned(),
        }
    }

    pub fn to_owned(&self) -> MatchedText<'static> {
        MatchedText {
            inner: self.inner.to_owned(),
        }
    }

    pub fn complete(&self) -> &str {
        self.get(0).unwrap()
    }

    pub fn get(&self, index: usize) -> Option<&str> {
        match self.inner {
            MaybeOwnedText::Borrowed(ref captures) => {
                captures.get(index).map(|capture| capture.as_str())
            }
            MaybeOwnedText::Owned(ref captures) => captures.get(index),
        }
    }
}

// TODO: This probably shouldn't be part of the public API.
impl<'t> From<BorrowedText<'t>> for MatchedText<'t> {
    fn from(captures: BorrowedText<'t>) -> Self {
        MatchedText {
            inner: captures.into(),
        }
    }
}

impl From<OwnedText> for MatchedText<'static> {
    fn from(captures: OwnedText) -> Self {
        MatchedText {
            inner: captures.into(),
        }
    }
}
