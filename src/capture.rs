use regex::Captures as BorrowedCaptures;
use std::str;

#[derive(Debug)]
enum MaybeOwnedCaptures<'t> {
    Borrowed(BorrowedCaptures<'t>),
    Owned(OwnedCaptures),
}

impl<'t> MaybeOwnedCaptures<'t> {
    fn into_owned(self) -> MaybeOwnedCaptures<'static> {
        match self {
            MaybeOwnedCaptures::Borrowed(borrowed) => OwnedCaptures::from(borrowed).into(),
            MaybeOwnedCaptures::Owned(owned) => owned.into(),
        }
    }

    fn to_owned(&self) -> MaybeOwnedCaptures<'static> {
        match self {
            MaybeOwnedCaptures::Borrowed(ref borrowed) => OwnedCaptures::from(borrowed).into(),
            MaybeOwnedCaptures::Owned(ref owned) => owned.clone().into(),
        }
    }
}

impl<'t> From<BorrowedCaptures<'t>> for MaybeOwnedCaptures<'t> {
    fn from(captures: BorrowedCaptures<'t>) -> Self {
        MaybeOwnedCaptures::Borrowed(captures)
    }
}

impl From<OwnedCaptures> for MaybeOwnedCaptures<'static> {
    fn from(captures: OwnedCaptures) -> Self {
        MaybeOwnedCaptures::Owned(captures)
    }
}

#[derive(Clone, Debug)]
struct OwnedCaptures {
    matched: String,
    ranges: Vec<Option<(usize, usize)>>,
}

impl OwnedCaptures {
    pub fn get(&self, index: usize) -> Option<&str> {
        if index == 0 {
            Some(self.matched.as_ref())
        } else {
            self.ranges
                .get(index - 1)
                .map(|range| range.map(|range| &self.matched[range.0..range.1]))
                .flatten()
        }
    }
}

impl<'t> From<BorrowedCaptures<'t>> for OwnedCaptures {
    fn from(captures: BorrowedCaptures<'t>) -> Self {
        From::from(&captures)
    }
}

impl<'c, 't> From<&'c BorrowedCaptures<'t>> for OwnedCaptures {
    fn from(captures: &'c BorrowedCaptures<'t>) -> Self {
        let matched = captures.get(0).unwrap().as_str().into();
        let ranges = captures
            .iter()
            .skip(1)
            .map(|capture| capture.map(|capture| (capture.start(), capture.end())))
            .collect();
        OwnedCaptures { matched, ranges }
    }
}

#[derive(Debug)]
pub struct Captures<'t> {
    inner: MaybeOwnedCaptures<'t>,
}

impl<'t> Captures<'t> {
    pub fn into_owned(self) -> Captures<'static> {
        let Captures { inner } = self;
        Captures {
            inner: inner.into_owned(),
        }
    }

    pub fn to_owned(&self) -> Captures<'static> {
        Captures {
            inner: self.inner.to_owned(),
        }
    }

    pub fn matched(&self) -> &str {
        self.get(0).unwrap()
    }

    pub fn get(&self, index: usize) -> Option<&str> {
        match self.inner {
            MaybeOwnedCaptures::Borrowed(ref captures) => {
                captures.get(index).map(|capture| capture.as_str())
            }
            MaybeOwnedCaptures::Owned(ref captures) => captures.get(index),
        }
    }
}

// TODO: This probably shouldn't be part of the public API.
impl<'t> From<BorrowedCaptures<'t>> for Captures<'t> {
    fn from(captures: BorrowedCaptures<'t>) -> Self {
        Captures {
            inner: captures.into(),
        }
    }
}

impl From<OwnedCaptures> for Captures<'static> {
    fn from(captures: OwnedCaptures) -> Self {
        Captures {
            inner: captures.into(),
        }
    }
}
