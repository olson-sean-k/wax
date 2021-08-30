use nom::error::{ErrorKind, ParseError};
use nom::{
    AsBytes, Compare, CompareResult, Err as NomError, ExtendInto, IResult, InputIter, InputLength,
    InputTake, InputTakeAtPosition, Needed, Offset, Parser, Slice,
};
use std::borrow::{Cow, ToOwned};
use std::ops::{Deref, RangeFrom, RangeTo};

// TODO: Move this into its own crate.

#[derive(Debug, Eq, Hash, PartialEq)]
pub struct Fragment<'i, T>
where
    T: ?Sized,
{
    offset: usize,
    data: &'i T,
}

impl<'i, T> Fragment<'i, T>
where
    T: ?Sized,
{
    pub fn into_data(self) -> &'i T {
        self.data
    }

    pub fn offset(&self) -> usize {
        self.offset
    }
}

impl<'i, T> AsBytes for Fragment<'i, T>
where
    T: ?Sized,
    &'i T: AsBytes,
{
    fn as_bytes(&self) -> &[u8] {
        self.data.as_bytes()
    }
}

impl<'i, T> AsRef<T> for Fragment<'i, T>
where
    T: ?Sized,
{
    fn as_ref(&self) -> &T {
        self.data
    }
}

impl<'i, T> Clone for Fragment<'i, T>
where
    T: ?Sized,
{
    fn clone(&self) -> Self {
        Fragment {
            offset: self.offset,
            data: self.data,
        }
    }
}

impl<'i, T, U> Compare<&'i U> for Fragment<'i, T>
where
    T: ?Sized,
    U: ?Sized,
    &'i T: Compare<&'i U>,
    &'i U: Into<Fragment<'i, U>>,
{
    fn compare(&self, other: &'i U) -> CompareResult {
        self.data.compare(other.into().data)
    }

    fn compare_no_case(&self, other: &'i U) -> CompareResult {
        self.data.compare_no_case(other.into().data)
    }
}

impl<'i, T> Copy for Fragment<'i, T> where T: ?Sized {}

impl<'i, T> Deref for Fragment<'i, T>
where
    T: ?Sized,
{
    type Target = T;

    fn deref(&self) -> &Self::Target {
        self.as_ref()
    }
}

impl<'i, T> ExtendInto for Fragment<'i, T>
where
    T: ?Sized,
    &'i T: ExtendInto,
{
    type Item = <&'i T as ExtendInto>::Item;
    type Extender = <&'i T as ExtendInto>::Extender;

    fn new_builder(&self) -> Self::Extender {
        self.data.new_builder()
    }

    fn extend_into(&self, extender: &mut Self::Extender) {
        self.data.extend_into(extender)
    }
}

impl<'i, T> From<Fragment<'i, T>> for Cow<'i, T>
where
    T: ?Sized + ToOwned,
{
    fn from(fragment: Fragment<'i, T>) -> Self {
        Cow::Borrowed(fragment.data)
    }
}

impl<'i, T> From<&'i T> for Fragment<'i, T>
where
    T: ?Sized,
{
    fn from(data: &'i T) -> Self {
        Fragment { offset: 0, data }
    }
}

impl<'i, T> InputIter for Fragment<'i, T>
where
    T: ?Sized,
    &'i T: InputIter,
{
    type Item = <&'i T as InputIter>::Item;
    type Iter = <&'i T as InputIter>::Iter;
    type IterElem = <&'i T as InputIter>::IterElem;

    fn iter_indices(&self) -> Self::Iter {
        self.data.iter_indices()
    }

    fn iter_elements(&self) -> Self::IterElem {
        self.data.iter_elements()
    }

    fn position<P>(&self, predicate: P) -> Option<usize>
    where
        P: Fn(Self::Item) -> bool,
    {
        self.data.position(predicate)
    }

    fn slice_index(&self, count: usize) -> Result<usize, Needed> {
        self.data.slice_index(count)
    }
}

impl<'i, T> InputLength for Fragment<'i, T>
where
    T: ?Sized,
    &'i T: InputLength,
{
    fn input_len(&self) -> usize {
        self.data.input_len()
    }
}

impl<'i, T> InputTake for Fragment<'i, T>
where
    T: ?Sized,
    Self: Slice<RangeFrom<usize>> + Slice<RangeTo<usize>>,
{
    fn take(&self, count: usize) -> Self {
        self.slice(..count)
    }

    fn take_split(&self, count: usize) -> (Self, Self) {
        (self.slice(count..), self.slice(..count))
    }
}

impl<'i, T> InputTakeAtPosition for Fragment<'i, T>
where
    T: ?Sized,
    &'i T: InputIter + InputLength + InputTakeAtPosition,
    Self: Slice<RangeFrom<usize>> + Slice<RangeTo<usize>>,
{
    type Item = <&'i T as InputIter>::Item;

    fn split_at_position_complete<P, E>(&self, predicate: P) -> IResult<Self, Self, E>
    where
        P: Fn(Self::Item) -> bool,
        E: ParseError<Self>,
    {
        match self.split_at_position(predicate) {
            Err(NomError::Incomplete(_)) => Ok(self.take_split(self.input_len())),
            result => result,
        }
    }

    fn split_at_position<P, E>(&self, predicate: P) -> IResult<Self, Self, E>
    where
        P: Fn(Self::Item) -> bool,
        E: ParseError<Self>,
    {
        match self.data.position(predicate) {
            Some(n) => Ok(self.take_split(n)),
            None => Err(NomError::Incomplete(Needed::new(1))),
        }
    }

    fn split_at_position1<P, E>(&self, predicate: P, kind: ErrorKind) -> IResult<Self, Self, E>
    where
        P: Fn(Self::Item) -> bool,
        E: ParseError<Self>,
    {
        match self.data.position(predicate) {
            Some(0) => Err(NomError::Error(E::from_error_kind(*self, kind))),
            Some(n) => Ok(self.take_split(n)),
            None => Err(NomError::Incomplete(Needed::new(1))),
        }
    }

    fn split_at_position1_complete<P, E>(
        &self,
        predicate: P,
        kind: ErrorKind,
    ) -> IResult<Self, Self, E>
    where
        P: Fn(Self::Item) -> bool,
        E: ParseError<Self>,
    {
        match self.data.position(predicate) {
            Some(0) => Err(NomError::Error(E::from_error_kind(*self, kind))),
            Some(n) => Ok(self.take_split(n)),
            None => {
                if self.data.input_len() == 0 {
                    Err(NomError::Error(E::from_error_kind(*self, kind)))
                } else {
                    Ok(self.take_split(self.input_len()))
                }
            }
        }
    }
}

impl<'i, T> Offset for Fragment<'i, T>
where
    T: ?Sized,
{
    fn offset(&self, other: &Self) -> usize {
        assert!(other.offset >= self.offset);
        other.offset - self.offset
    }
}

impl<'i, T, R> Slice<R> for Fragment<'i, T>
where
    T: ?Sized,
    &'i T: AsBytes + Offset + Slice<R> + Slice<RangeTo<usize>>,
{
    fn slice(&self, range: R) -> Self {
        let sliced = self.data.slice(range);
        let offset = self.data.offset(&sliced);
        Fragment {
            offset: self.offset + offset,
            data: sliced,
        }
    }
}

pub fn span<'i, T, O, E, F>(
    mut parser: F,
) -> impl FnMut(Fragment<'i, T>) -> IResult<Fragment<'i, T>, ((usize, usize), O), E>
where
    T: 'i + ?Sized,
    E: ParseError<Fragment<'i, T>>,
    F: Parser<Fragment<'i, T>, O, E>,
{
    move |input: Fragment<'i, T>| {
        let start = input.offset();
        parser.parse(input).map(move |(remaining, output)| {
            let n = Offset::offset(&input, &remaining);
            (remaining, ((start, n), output))
        })
    }
}
