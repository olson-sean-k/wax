use std::num::NonZeroUsize;

use crate::token::variance::bound::{
    Bounded, BoundedVariantRange, Boundedness, Unbounded, VariantRange,
};
use crate::token::variance::invariant::term::{BoundaryTerm, SeparatedTerm, Termination};
use crate::token::variance::invariant::{Finalize, Invariant, One, Zero};
use crate::token::variance::ops::{self, Conjunction, Disjunction, Product};
use crate::token::variance::{TokenVariance, Variance};

macro_rules! impl_natural_invariant_term {
    ($name:ident, $term:ident $(,)?) => {
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
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

        impl Invariant for $name {
            type Term = $term<$name>;
            type Bound = BoundedVariantRange;

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

        impl One for $name {
            fn one() -> Self {
                $name(1)
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
            type Output = TokenVariance<Self>;

            fn product(self, rhs: VariantRange) -> Self::Output {
                NonZeroUsize::new(self.0).map_or_else(TokenVariance::<Self>::zero, |lhs| {
                    Variance::Variant(rhs.map_bounded(|rhs| ops::product(rhs, lhs)))
                })
            }
        }

        impl Zero for $name {
            fn zero() -> Self {
                $name(0)
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
impl_natural_invariant_term!(Depth, BoundaryTerm);
impl_natural_invariant_term!(Size, TokenVariance);

impl TokenVariance<Depth> {
    pub fn is_exhaustive(&self) -> bool {
        !self.has_upper_bound()
    }
}

impl Finalize for SeparatedTerm<TokenVariance<Depth>> {
    type Output = TokenVariance<Depth>;

    fn finalize(self) -> Self::Output {
        use Termination::{Closed, Open};

        let SeparatedTerm(termination, term) = self;
        match termination {
            Open => ops::conjunction(term, One::one()),
            Closed => term.map_invariant(|term| term.map(|term| term.saturating_sub(1))),
            _ => term,
        }
    }
}

impl BoundaryTerm<Depth> {
    pub fn is_exhaustive(&self) -> bool {
        self.clone().finalize().is_exhaustive()
    }
}
