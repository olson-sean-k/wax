use std::num::NonZeroUsize;

use crate::token::variance::bound::{
    Bounded, BoundedVariantRange, Boundedness, Unbounded, VariantRange,
};
use crate::token::variance::invariant::{GlobVariance, Identity, Invariant};
use crate::token::variance::ops::{self, Conjunction, Disjunction, Product};
use crate::token::variance::Variance;

macro_rules! impl_invariant_natural {
    ($name:ident $(,)?) => {
        impl_invariant_natural!($name, once => 0);
    };
    ($name:ident, once => $once:expr $(,)?) => {
        #[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
        #[repr(transparent)]
        pub struct $name(usize);

        impl $name {
            pub const ZERO: Self = $name(0);
            pub const ONE: Self = $name(1);

            pub const fn new(n: usize) -> Self {
                $name(n)
            }

            pub fn map<F>(self, f: F) -> Self
            where
                F: FnOnce(usize) -> usize,
            {
                $name(f(self.0))
            }

            pub fn zip_map<F>(self, rhs: Self, f: F) -> Self
            where
                F: FnOnce(usize, usize) -> usize,
            {
                $name(f(self.0, rhs.0))
            }
        }

        impl AsRef<usize> for $name {
            fn as_ref(&self) -> &usize {
                &self.0
            }
        }

        impl Conjunction for $name {
            type Output = Self;

            fn conjunction(self, rhs: Self) -> Self::Output {
                self.zip_map(rhs, ops::conjunction)
            }
        }

        impl From<usize> for $name {
            fn from(n: usize) -> $name {
                $name(n)
            }
        }

        impl From<$name> for usize {
            fn from(size: $name) -> usize {
                size.0
            }
        }

        impl Identity for $name {
            fn zero() -> Self {
                $name(0)
            }
        }

        impl Invariant for $name {
            type Bound = BoundedVariantRange;

            fn once() -> Self {
                $name($once)
            }

            fn bound(lhs: Self, rhs: Self) -> Boundedness<Self::Bound> {
                let [lower, upper] = crate::minmax(lhs, rhs);
                BoundedVariantRange::try_from_lower_and_upper(lower.0, upper.0)
                    .map_or(Unbounded, Bounded)
            }

            fn into_lower_bound(self) -> Boundedness<Self::Bound> {
                NonZeroUsize::new(self.0)
                    .map(BoundedVariantRange::Lower)
                    .map(From::from)
                    .unwrap_or(Unbounded)
            }
        }

        impl PartialEq<usize> for $name {
            fn eq(&self, rhs: &usize) -> bool {
                self.0 == *rhs
            }
        }

        impl Product<usize> for $name {
            type Output = Self;

            fn product(self, rhs: usize) -> Self::Output {
                self.map(|lhs| ops::product(lhs, rhs))
            }
        }

        impl Product<VariantRange> for $name {
            type Output = GlobVariance<Self>;

            fn product(self, rhs: VariantRange) -> Self::Output {
                NonZeroUsize::new(self.0)
                    .map_or_else(
                        GlobVariance::<Self>::zero,
                        |lhs| Variance::Variant(rhs.map_bounded(|rhs| ops::product(rhs, lhs))),
                    )
            }
        }

        impl Conjunction<$name> for BoundedVariantRange {
            type Output = Self;

            fn conjunction(self, rhs: $name) -> Self::Output {
                self.translation(rhs.0)
            }
        }

        impl Disjunction<$name> for BoundedVariantRange {
            type Output = VariantRange;

            fn disjunction(self, rhs: $name) -> Self::Output {
                self.union(rhs.0)
            }
        }
    };
}
impl_invariant_natural!(Depth, once => 1);
impl_invariant_natural!(Size);

impl GlobVariance<Depth> {
    pub fn is_exhaustive(&self) -> bool {
        !self.has_upper_bound()
    }
}
