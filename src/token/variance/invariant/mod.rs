mod natural;
mod text;

use std::num::NonZeroUsize;

use crate::token::variance::bound::{BoundedVariantRange, Boundedness, OpenedUpperBound};
use crate::token::variance::ops::{Conjunction, Disjunction, Product};

pub use crate::token::variance::invariant::natural::{Depth, Size};
pub use crate::token::variance::invariant::text::{IntoNominalText, IntoStructuralText, Text};

pub trait Identity {
    fn zero() -> Self;
}

pub trait Invariant: Sized + Identity {
    type Bound;

    fn once() -> Self {
        Self::zero()
    }

    fn bound(lhs: Self, rhs: Self) -> Boundedness<Self::Bound>;

    fn into_lower_bound(self) -> Boundedness<Self::Bound>;
}

// Breadth is the maximum size (UTF-8 bytes) of component text in a glob expression. For example,
// the breadth of `{a/,a/b/}<c/d:2>` is two (bytes).
//
// Composition is not implemented for breadth and it is only queried from leaf tokens. No values
// are associated with its invariant nor bounds. Breadth is probably the least interesting and yet
// most difficult quantity to compute. Determining correct breadth values likely involves:
//
// - Complex terms that support both running sums and running maximums across boundaries.
// - Searches from the start and end of sub-trees in repetitions, where terminals may interact.
//   Consider `<a/b:2>` vs. `<a/b/:2>`, which have breadths of two and one, respectively.
// - Potentially large sets for bounds. Ranges lose too much information, in particular information
//   about boundaries when composing terms.
//
// There are likely other difficult composition problems. As such, breadth is only implemented as
// much as needed. Any requirements on more complete breadth computations ought to be considered
// carefully.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Breadth;

impl Breadth {
    pub const fn new() -> Self {
        Breadth
    }
}

impl Identity for Breadth {
    fn zero() -> Self {
        Breadth
    }
}

impl Invariant for Breadth {
    type Bound = ();

    fn bound(_: Self, _: Self) -> Boundedness<Self::Bound> {
        ().into()
    }

    fn into_lower_bound(self) -> Boundedness<Self::Bound> {
        ().into()
    }
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct UnitBound;

impl<T> Conjunction<T> for UnitBound {
    type Output = Self;

    fn conjunction(self, _: T) -> Self::Output {
        self
    }
}

impl Disjunction for UnitBound {
    type Output = Boundedness<Self>;

    fn disjunction(self, _: Self) -> Self::Output {
        self.into()
    }
}

impl From<()> for UnitBound {
    fn from(_: ()) -> Self {
        UnitBound
    }
}

impl From<BoundedVariantRange> for UnitBound {
    fn from(_: BoundedVariantRange) -> Self {
        UnitBound
    }
}

impl OpenedUpperBound for UnitBound {
    fn opened_upper_bound(self) -> Boundedness<Self> {
        UnitBound.into()
    }
}

impl Product<BoundedVariantRange> for UnitBound {
    type Output = Boundedness<Self>;

    fn product(self, _: BoundedVariantRange) -> Self::Output {
        self.into()
    }
}

impl Product<NonZeroUsize> for Boundedness<UnitBound> {
    type Output = Self;

    fn product(self, _: NonZeroUsize) -> Self::Output {
        self
    }
}
