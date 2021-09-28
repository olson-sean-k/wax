use os_str_bytes::OsStrBytes as _;
use regex::bytes::Captures as BorrowedCaptures;
use std::borrow::Cow;
use std::ops::Deref;
use std::path::Path;
use std::str;

use crate::ResultExt as _;

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
    matched: Vec<u8>,
    ranges: Vec<Option<(usize, usize)>>,
}

impl OwnedCaptures {
    pub fn get(&self, index: usize) -> Option<&[u8]> {
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
        let matched = captures.get(0).unwrap().as_bytes().into();
        let ranges = captures
            .iter()
            .skip(1)
            .map(|capture| capture.map(|capture| (capture.start(), capture.end())))
            .collect();
        OwnedCaptures { matched, ranges }
    }
}

#[derive(Clone, Copy, Debug)]
pub struct Capture<'t> {
    bytes: &'t [u8],
}

impl<'t> Capture<'t> {
    pub fn into_bytes(self) -> &'t [u8] {
        self.bytes
    }

    pub fn as_str(&self) -> Option<&'t str> {
        str::from_utf8(self.bytes).ok()
    }

    pub fn to_string_lossy(&self) -> Cow<'t, str> {
        String::from_utf8_lossy(self.bytes)
    }

    pub fn to_path(&self) -> Cow<'t, Path> {
        Path::from_raw_bytes(self.bytes).expect_os_str_bytes()
    }
}

impl<'t> AsRef<[u8]> for Capture<'t> {
    fn as_ref(&self) -> &[u8] {
        self.bytes
    }
}

impl<'t> Deref for Capture<'t> {
    type Target = [u8];

    fn deref(&self) -> &Self::Target {
        self.bytes
    }
}

#[derive(Debug)]
pub struct CaptureBuffer<'t> {
    inner: MaybeOwnedCaptures<'t>,
}

impl<'t> CaptureBuffer<'t> {
    pub fn into_owned(self) -> CaptureBuffer<'static> {
        let CaptureBuffer { inner } = self;
        CaptureBuffer {
            inner: inner.into_owned(),
        }
    }

    pub fn to_owned(&self) -> CaptureBuffer<'static> {
        CaptureBuffer {
            inner: self.inner.to_owned(),
        }
    }

    pub fn matched(&self) -> Capture {
        self.get(0).unwrap()
    }

    pub fn get(&self, index: usize) -> Option<Capture> {
        match self.inner {
            MaybeOwnedCaptures::Borrowed(ref captures) => {
                captures.get(index).map(|capture| capture.as_bytes())
            }
            MaybeOwnedCaptures::Owned(ref captures) => captures.get(index),
        }
        .map(|bytes| Capture { bytes })
    }
}

// TODO: Maybe this shouldn't be part of the public API.
impl<'t> From<BorrowedCaptures<'t>> for CaptureBuffer<'t> {
    fn from(captures: BorrowedCaptures<'t>) -> Self {
        CaptureBuffer {
            inner: captures.into(),
        }
    }
}

impl From<OwnedCaptures> for CaptureBuffer<'static> {
    fn from(captures: OwnedCaptures) -> Self {
        CaptureBuffer {
            inner: captures.into(),
        }
    }
}
