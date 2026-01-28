use crate::query::When;
use crate::token::variance::invariant::{
    BoundaryTerm, Coalescence, DisjunctiveTerm, Finalize, One, SeparatedTerm, Termination, Zero,
};
use crate::token::variance::natural::define_natural_invariant;
use crate::token::variance::ops::{self, Conjunction, Disjunction, Product};
use crate::token::variance::TokenVariance;
use crate::token::Composition;

//type Term = BoundaryTerm<TokenVariance<Depth>>;

define_natural_invariant!(
    /// Depth of a glob expression.
    Depth => BoundaryTerm<TokenVariance<Depth>>,
);

impl TokenVariance<Depth> {
    pub fn is_exhaustive(&self) -> bool {
        !self.has_upper_bound()
    }
}

impl BoundaryTerm<TokenVariance<Depth>> {
    pub fn is_exhaustive(&self) -> When {
        match self {
            BoundaryTerm::Conjunctive(SeparatedTerm(_, ref term)) => term.is_exhaustive().into(),
            BoundaryTerm::Disjunctive(ref term) => term
                .branches()
                .map(AsRef::as_ref)
                .map(TokenVariance::<Depth>::is_exhaustive)
                .map(When::from)
                .reduce(When::certainty)
                .unwrap_or(When::Never),
        }
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

impl Conjunction for BoundaryTerm<TokenVariance<Depth>> {
    type Output = Self;

    fn conjunction(self, rhs: Self) -> Self::Output {
        use Composition::{Conjunctive, Disjunctive};

        match (self, rhs) {
            (Conjunctive(lhs), Conjunctive(rhs)) => Conjunctive(ops::conjunction(lhs, rhs)),
            (Conjunctive(lhs), Disjunctive(rhs)) => Disjunctive(ops::conjunction(lhs, rhs)),
            (Disjunctive(lhs), Conjunctive(rhs)) => Disjunctive(ops::conjunction(lhs, rhs)),
            (Disjunctive(lhs), Disjunctive(rhs)) => Disjunctive(ops::conjunction(lhs, rhs)),
        }
    }
}

impl Disjunction for BoundaryTerm<TokenVariance<Depth>> {
    type Output = Self;

    fn disjunction(self, rhs: Self) -> Self::Output {
        use Composition::{Conjunctive, Disjunctive};

        Disjunctive(match (self, rhs) {
            (Conjunctive(lhs), Conjunctive(rhs)) => ops::disjunction(lhs, rhs),
            (Conjunctive(lhs), Disjunctive(rhs)) => ops::disjunction(lhs, rhs),
            (Disjunctive(lhs), Conjunctive(rhs)) => ops::disjunction(lhs, rhs),
            (Disjunctive(lhs), Disjunctive(rhs)) => ops::disjunction(lhs, rhs),
        })
    }
}

impl<T> Product<T> for BoundaryTerm<TokenVariance<Depth>>
where
    TokenVariance<Depth>: Product<T, Output = TokenVariance<Depth>>,
    T: Clone,
{
    type Output = Self;

    fn product(self, rhs: T) -> Self::Output {
        match self {
            BoundaryTerm::Conjunctive(lhs) => BoundaryTerm::Conjunctive(ops::product(lhs, rhs)),
            BoundaryTerm::Disjunctive(lhs) => BoundaryTerm::Disjunctive(ops::product(lhs, rhs)),
        }
    }
}

impl Conjunction for SeparatedTerm<TokenVariance<Depth>> {
    type Output = Self;

    fn conjunction(self, rhs: Self) -> Self::Output {
        use Coalescence::{Left, Neither, Right};

        let lhs = self;
        let (termination, lhs, rhs) = match ops::conjunction(lhs.0, rhs.0) {
            Left(termination) => (termination, lhs.finalize(), rhs.1),
            Right(termination) => (termination, lhs.1, rhs.finalize()),
            Neither(termination) => (termination, lhs.1, rhs.1),
        };
        SeparatedTerm(termination, ops::conjunction(lhs, rhs))
    }
}

impl Disjunction for SeparatedTerm<TokenVariance<Depth>> {
    type Output = DisjunctiveTerm<Self>;

    fn disjunction(self, rhs: Self) -> Self::Output {
        DisjunctiveTerm::from_branches([self, rhs])
    }
}

impl One for SeparatedTerm<TokenVariance<Depth>> {
    fn one() -> Self {
        SeparatedTerm(Termination::Closed, One::one())
    }
}

impl<T> Product<T> for SeparatedTerm<TokenVariance<Depth>>
where
    TokenVariance<Depth>: Product<T, Output = TokenVariance<Depth>>,
{
    type Output = Self;

    fn product(self, rhs: T) -> Self::Output {
        SeparatedTerm(self.0, ops::product(self.1, rhs))
    }
}

impl Zero for SeparatedTerm<TokenVariance<Depth>> {
    fn zero() -> Self {
        SeparatedTerm(Termination::Open, Zero::zero())
    }
}
