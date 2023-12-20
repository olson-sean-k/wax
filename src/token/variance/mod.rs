pub mod bound;
pub mod invariant;
pub mod ops;

use itertools::Itertools;
use std::marker::PhantomData;
use std::num::NonZeroUsize;

use crate::token::variance::bound::{
    Bounded, Boundedness, NaturalRange, OpenedUpperBound, Unbounded, VariantRange,
};
use crate::token::variance::invariant::{
    Breadth, Depth, GlobVariance, Identity, Invariant, Text, UnitBound,
};
use crate::token::variance::ops::{Conjunction, Disjunction, Product};
use crate::token::walk::{ChildToken, Fold, Forward, ParentToken, Sequencer};
use crate::token::{Boundary, BranchKind, LeafKind};

use self::bound::BoundedVariantRange;

pub trait VarianceTerm<T>
where
    T: Invariant,
{
    fn term(&self) -> GlobVariance<T>;
}

pub trait VarianceFold<T>
where
    T: Invariant,
{
    fn fold(&self, terms: Vec<GlobVariance<T>>) -> Option<GlobVariance<T>>;

    fn finalize(&self, term: GlobVariance<T>) -> GlobVariance<T> {
        term
    }
}

#[derive(Clone, Copy, Debug, Eq)]
pub enum Variance<T, B = Boundedness<UnitBound>> {
    Invariant(T),
    Variant(B),
}

impl<T, B> Variance<T, B> {
    pub fn zero() -> Self
    where
        T: Identity,
    {
        Variance::Invariant(T::zero())
    }

    pub fn once() -> Self
    where
        T: Invariant,
    {
        Variance::Invariant(T::once())
    }

    pub fn map_invariant<U, F>(self, f: F) -> Variance<U, B>
    where
        F: FnOnce(T) -> U,
    {
        match self {
            Variance::Invariant(invariant) => Variance::Invariant(f(invariant)),
            Variance::Variant(bound) => Variance::Variant(bound),
        }
    }

    pub fn map_variant<U, F>(self, f: F) -> Variance<T, U>
    where
        F: FnOnce(B) -> U,
    {
        match self {
            Variance::Invariant(invariant) => Variance::Invariant(invariant),
            Variance::Variant(bound) => Variance::Variant(f(bound)),
        }
    }

    pub fn invariant(self) -> Option<T> {
        match self {
            Variance::Invariant(invariant) => Some(invariant),
            _ => None,
        }
    }

    pub fn variant(self) -> Option<B> {
        match self {
            Variance::Variant(bound) => Some(bound),
            _ => None,
        }
    }

    pub fn as_ref(&self) -> Variance<&T, &B> {
        match self {
            Variance::Invariant(ref invariant) => Variance::Invariant(invariant),
            Variance::Variant(ref bound) => Variance::Variant(bound),
        }
    }

    pub fn is_invariant(&self) -> bool {
        matches!(self, Variance::Invariant(_))
    }

    pub fn is_variant(&self) -> bool {
        matches!(self, Variance::Variant(_))
    }
}

impl<T, B> Variance<T, Boundedness<B>> {
    pub const fn unbounded() -> Self {
        Variance::Variant(Unbounded)
    }

    pub fn is_bounded(&self) -> bool {
        !self.is_unbounded()
    }

    pub fn is_unbounded(&self) -> bool {
        self.as_ref()
            .variant()
            .map_or(false, Boundedness::is_unbounded)
    }
}

impl<T> Variance<T, VariantRange> {
    pub fn has_upper_bound(&self) -> bool {
        self.as_ref()
            .variant()
            .map_or(true, |range| range.upper().into_bound().is_bounded())
    }
}

impl<T> Conjunction for GlobVariance<T>
where
    T: Conjunction<Output = T> + Invariant,
    T::Bound: Conjunction<Output = T::Bound> + Conjunction<T, Output = T::Bound> + OpenedUpperBound,
{
    type Output = Self;

    fn conjunction(self, rhs: Self) -> Self::Output {
        use Variance::{Invariant, Variant};

        let lhs = self;
        match (lhs, rhs) {
            // Both terms are invariant. Conjunction is invariant over the sum of the invariants.
            (Invariant(lhs), Invariant(rhs)) => Invariant(ops::conjunction(lhs, rhs)),
            // Both terms are bounded. Conjunction is bounded over the sum of the bounds.
            (Variant(Bounded(lhs)), Variant(Bounded(rhs))) => {
                Variant(Bounded(ops::conjunction(lhs, rhs)))
            },
            // Both terms are unbounded. Conjunction is unbounded.
            (Variant(Unbounded), Variant(Unbounded)) => Variant(Unbounded),
            // One term is bounded and the other is invariant. Conjunction is bounded over the sum
            // of the bound and the invariant.
            (Variant(Bounded(bound)), Invariant(invariant))
            | (Invariant(invariant), Variant(Bounded(bound))) => {
                Variant(Bounded(ops::conjunction(bound, invariant)))
            },
            // One term is unbounded and the other is invariant. Conjunction is variant over the
            // bound of the invariant.
            (Variant(Unbounded), Invariant(invariant))
            | (Invariant(invariant), Variant(Unbounded)) => Variant(invariant.into_lower_bound()),
            // One term is unbounded and the other is bounded. Conjunction is variant over the
            // bounded term without its upper bound.
            (Variant(Unbounded), Variant(Bounded(bound)))
            | (Variant(Bounded(bound)), Variant(Unbounded)) => Variant(bound.opened_upper_bound()),
        }
    }
}

impl<T> Disjunction for GlobVariance<T>
where
    Self: PartialEq,
    T: Invariant,
    T::Bound: Disjunction<Output = Boundedness<T::Bound>>
        + Disjunction<T, Output = Boundedness<T::Bound>>,
{
    type Output = Self;

    fn disjunction(self, rhs: Self) -> Self::Output {
        use Variance::{Invariant, Variant};

        let lhs = self;
        match (lhs, rhs) {
            // The terms are equal. Disjunction is one of the terms (any term may be used).
            (lhs, rhs) if lhs == rhs => lhs,
            // The terms are invariant (and inequal). Disjunction is variant over the bound of the
            // invariants.
            (Invariant(lhs), Invariant(rhs)) => Variant(T::bound(lhs, rhs)),
            // A term is unbounded. Disjunction is unbounded.
            (Variant(Unbounded), _) | (_, Variant(Unbounded)) => Variant(Unbounded),
            // Both terms are bounded. Disjunction is variant over the sum of the bounds.
            (Variant(Bounded(lhs)), Variant(Bounded(rhs))) => Variant(ops::disjunction(lhs, rhs)),
            // One term is bounded and the other is invariant. Disjunction is variant over the sum
            // (and bound) of the bound and the invariant.
            (Variant(Bounded(bound)), Invariant(invariant))
            | (Invariant(invariant), Variant(Bounded(bound))) => {
                Variant(ops::disjunction(bound, invariant))
            },
        }
    }
}

impl<T, B> PartialEq for Variance<T, B>
where
    T: PartialEq<T>,
    B: PartialEq<B>,
{
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Variance::Invariant(ref left), Variance::Invariant(ref right)) => left == right,
            (Variance::Variant(ref left), Variance::Variant(ref right)) => left == right,
            _ => false,
        }
    }
}

impl<T> Product<NaturalRange> for GlobVariance<T>
where
    Boundedness<T::Bound>: Product<NonZeroUsize, Output = Boundedness<T::Bound>>,
    T: Invariant + Product<VariantRange, Output = GlobVariance<T>> + Product<usize, Output = T>,
    T::Bound: Product<BoundedVariantRange, Output = Boundedness<T::Bound>>,
{
    type Output = Self;

    fn product(self, rhs: NaturalRange) -> Self::Output {
        use Variance::{Invariant, Variant};

        let lhs = self;
        match (lhs, rhs) {
            (Variant(Unbounded), Variant(Unbounded))
            | (Variant(Unbounded), Variant(Bounded(_)))
            | (Variant(Bounded(_)), Variant(Unbounded)) => Variant(Unbounded),
            // This inner product is incomplete (and cannot be complete). Ideally, the bound would
            // implement the product over `usize` with variance as the output, but it is impossible
            // to implement `Product` this way. Instead, a zero invariant is mapped to the zero
            // variance or else the product with the bound is computed.
            (Variant(lhs), Invariant(rhs)) => NonZeroUsize::new(rhs)
                .map_or_else(Variance::zero, |rhs| Variant(ops::product(lhs, rhs))),
            (Variant(Bounded(lhs)), Variant(Bounded(rhs))) => Variant(ops::product(lhs, rhs)),
            (Invariant(lhs), Variant(rhs)) => ops::product(lhs, rhs),
            (Invariant(lhs), Invariant(rhs)) => Invariant(ops::product(lhs, rhs)),
        }
    }
}

pub struct TreeVariance<T>(PhantomData<fn() -> T>);

impl<T> Default for TreeVariance<T> {
    fn default() -> Self {
        TreeVariance(PhantomData)
    }
}

impl<'t, A, T> Fold<'t, A> for TreeVariance<T>
where
    BranchKind<'t, A>: VarianceFold<T>,
    LeafKind<'t>: VarianceTerm<T>,
    T: Invariant,
{
    type Sequencer = Forward;
    type Term = GlobVariance<T>;

    fn sequencer() -> Self::Sequencer {
        Forward
    }

    fn fold(&mut self, branch: &BranchKind<'t, A>, terms: Vec<Self::Term>) -> Option<Self::Term> {
        branch.fold(terms)
    }

    fn finalize(&mut self, branch: &BranchKind<'t, A>, term: Self::Term) -> Self::Term {
        branch.finalize(term)
    }

    fn term(&mut self, leaf: &LeafKind<'t>) -> Self::Term {
        leaf.term()
    }
}

#[derive(Debug, Default)]
pub struct TreeExhaustiveness;

impl Sequencer for TreeExhaustiveness {
    fn enqueue<'i, 't, A>(
        &mut self,
        parent: ParentToken<'i, 't, A>,
    ) -> impl Iterator<Item = ChildToken<'i, 't, A>> {
        parent.into_tokens().rev().take_while(|token| {
            token.as_ref().as_leaf().map_or(true, |leaf| {
                if let Some(Boundary::Separator) = leaf.boundary() {
                    true
                }
                else {
                    let breadth: GlobVariance<Breadth> = leaf.term();
                    let text: GlobVariance<Text> = leaf.term();
                    breadth.is_unbounded() && text.is_unbounded()
                }
            })
        })
    }
}

impl<'t, A> Fold<'t, A> for TreeExhaustiveness {
    type Sequencer = Self;
    type Term = GlobVariance<Depth>;

    fn sequencer() -> Self::Sequencer {
        Self
    }

    fn fold(&mut self, branch: &BranchKind<'t, A>, terms: Vec<Self::Term>) -> Option<Self::Term> {
        // TODO: Detect generalizations in alternation branches. This may be possible in an
        //       optimization step that fold maps token trees and discards unnecessary branches.
        // When folding terms into an alternation, if some but not all branches are exhaustive,
        // then do not sum the terms and instead return the bounded depth [0,1]. This is necessary
        // to prevent false positives when the sum of exhaustiveness terms for branches is
        // exhaustive but a **non-overlapping** branch is non-exhaustive. Consider `{a/**,**/b}`.
        // This pattern is nonexhaustive, because matches in `**/b` are not exhaustive and are not
        // necessarily sub-trees of an exhaustive branch (in this example, the only such branch
        // being `a/**`). Despite this, the terms exhaustiveness terms for the alternation are
        // unbounded and zero. These terms sum to unbounded, which is a false positive.
        //
        // Note that this heuristic is also applied when all non-exhaustive branches overlap with
        // an exhaustive branch (that is, all non-exhaustive branches are generalized by exhaustive
        // branches), which causes false negatives. Consider `{/**,/**/a}`. The branch `/**`
        // generalizes the remaining branches, so this pattern is exhaustive, but this heuristic
        // rejects this. However, this false negative is far more acceptable than a false positive,
        // which causes errant behavior.
        if let BranchKind::Alternation(_) = branch {
            let (all, any) = terms
                .iter()
                .fold_while((true, false), |sum, term| {
                    use itertools::FoldWhile::{Continue, Done};

                    let term = term.is_exhaustive();
                    match (sum.0 && term, sum.1 || term) {
                        sum @ (false, true) => Done(sum),
                        sum => Continue(sum),
                    }
                })
                .into_inner();
            if !all && any {
                return Some(GlobVariance::<Depth>::Variant(Bounded(
                    BoundedVariantRange::Upper(unsafe { NonZeroUsize::new_unchecked(1) }),
                )));
            }
        }

        let n = terms.len();
        let sum = VarianceFold::fold(branch, terms);
        if branch.tokens().into_inner().len() == n {
            // No terms were discarded. Yield the sum.
            sum
        }
        else {
            // Terms were discarded, meaning some non-depth quantity was bounded. Yield any sum
            // only if the depth is exhaustive, otherwise zero.
            if sum.as_ref().map_or(false, Variance::is_exhaustive) {
                sum
            }
            else {
                Some(Variance::zero())
            }
        }
    }

    fn finalize(&mut self, branch: &BranchKind<'t, A>, term: Self::Term) -> Self::Term {
        use Variance::{Invariant, Variant};

        match branch {
            branch @ BranchKind::Repetition(_) => match term {
                // When folding terms into a repetition, only finalize variant terms and the
                // multiplicative identity and annihilator (one and zero). This is necessary,
                // because natural bounds do not express the subset nor relationship of matched
                // values within the range. Consider `<*/*/>`. This pattern is unbounded w.r.t.
                // depth, but only matches paths with a depth that is a multiple of two and so is
                // nonexhaustive. However, the similar pattern `<*/>` is exhaustive and matches any
                // sub-tree of a match.
                Invariant(Depth::ZERO) | Invariant(Depth::ONE) | Variant(_) => {
                    VarianceFold::finalize(branch, term)
                },
                _ => term,
            },
            branch => VarianceFold::finalize(branch, term),
        }
    }

    fn term(&mut self, leaf: &LeafKind<'t>) -> Self::Term {
        VarianceTerm::term(leaf)
    }
}

#[cfg(test)]
mod tests {
    use std::path::{Path, PathBuf};

    use crate::token::variance::bound::Unbounded;
    use crate::token::variance::invariant::{GlobVariance, Size};
    use crate::token::variance::{NaturalRange, Variance};
    use crate::token::{self, TokenTree};

    // TODO: Move this test into the `token` module.
    #[test]
    fn invariant_text_prefix() {
        fn invariant_path_prefix(expression: &str) -> PathBuf {
            let (_, text) = token::parse(expression)
                .unwrap()
                .into_token()
                .invariant_text_prefix();
            text.into()
        }

        assert_eq!(invariant_path_prefix("/a/b"), Path::new("/a/b"));
        assert_eq!(invariant_path_prefix("a/b"), Path::new("a/b"));
        assert_eq!(invariant_path_prefix("a/*"), Path::new("a"));
        assert_eq!(invariant_path_prefix("a/*b"), Path::new("a"));
        assert_eq!(invariant_path_prefix("a/b*"), Path::new("a"));
        assert_eq!(invariant_path_prefix("a/b/*/c"), Path::new("a/b"));

        #[cfg(any(unix, windows))]
        let prefix = invariant_path_prefix("../foo/(?i)bar/(?-i)baz");
        #[cfg(unix)]
        assert_eq!(prefix, Path::new("../foo"));
        #[cfg(windows)]
        assert_eq!(prefix, Path::new("../foo/bar"));

        assert_eq!(invariant_path_prefix("**"), Path::new(""));
        assert_eq!(invariant_path_prefix("a*"), Path::new(""));
        assert_eq!(invariant_path_prefix("*/b"), Path::new(""));
        assert_eq!(invariant_path_prefix("a?/b"), Path::new(""));
    }

    // TODO: Rename and expand upon this test. Query other invariants.
    #[test]
    fn tree_expression_variance() {
        use Variance::Variant;

        fn range(lower: usize, upper: Option<usize>) -> GlobVariance<Size> {
            NaturalRange::from_closed_and_open(lower, upper).map_invariant(From::from)
        }

        let token = token::parse("**").unwrap().into_token();
        assert_eq!(token.variance::<Size>(), Variant(Unbounded));
        let token = token::parse("<*/>*").unwrap().into_token();
        assert_eq!(token.variance::<Size>(), Variant(Unbounded));
        let token = token::parse("<<?>/>*").unwrap().into_token();
        assert_eq!(token.variance::<Size>(), Variant(Unbounded));
        let token = token::parse("<foo*/>*").unwrap().into_token();
        assert_eq!(token.variance::<Size>(), Variant(Unbounded));

        let token = token::parse("foo/**").unwrap().into_token();
        assert_eq!(token.variance::<Size>(), range(3, None));
        let token = token::parse("<foo*/:1,>*").unwrap().into_token();
        assert_eq!(token.variance::<Size>(), range(4, None));
    }

    // TODO: Document the expressions in this important test, especially non-exhaustive
    //       expressions. False positives are bad news.
    #[test]
    fn exhaustiveness() {
        // This function does not check token trees against rules. This allows the test to examine
        // interesting trees, including some that may not occur in `Glob` but may occur elsewhere
        // like `Any`. For example, initial alternations with roots are rejected by `rule::check`
        // but not `Checked::any`. Expressions given to this function require extra scrutiny.
        fn is_exhaustive(expression: &str) -> bool {
            token::parse(expression)
                .unwrap()
                .into_token()
                .is_exhaustive()
        }

        assert!(is_exhaustive("**"));
        assert!(is_exhaustive("a/**"));
        assert!(is_exhaustive("<a/**>"));
        assert!(is_exhaustive("<a/**:1,2>"));
        assert!(is_exhaustive("<a/<*/:3,>>"));
        assert!(is_exhaustive("<*/:1,>"));
        assert!(is_exhaustive("<*/>"));
        assert!(is_exhaustive("<a/<*/>>"));
        assert!(is_exhaustive("a/<*/>"));
        assert!(is_exhaustive("a/<*/>*"));
        assert!(is_exhaustive("a/<<?>/>*"));
        assert!(is_exhaustive("{a/**,b/**}"));
        assert!(is_exhaustive("{{a/**,b/**},c/**}"));
        assert!(is_exhaustive("<{{a/**,b/**},c/**}:2,4>"));
        assert!(is_exhaustive("{a/**,b/**,[xyz]<*/>}"));
        assert!(is_exhaustive("<<?>/>"));
        assert!(is_exhaustive("<<?>/>*"));
        assert!(is_exhaustive("<*{/}>"));
        assert!(is_exhaustive("<*{/,/}>"));
        assert!(is_exhaustive("<*{/,/**}>"));
        assert!(is_exhaustive("<{<<{{a/b}}{{/**}}>>}>"));

        assert!(!is_exhaustive(""));
        assert!(!is_exhaustive("**/a"));
        assert!(!is_exhaustive("a/**/b"));
        assert!(!is_exhaustive("a/*"));
        assert!(!is_exhaustive("<a/*>"));
        assert!(!is_exhaustive("<*/a>"));
        assert!(!is_exhaustive("<a/*>/*"));
        // This pattern only matches components in groups of two.
        assert!(!is_exhaustive("<*/*/>"));
        // This pattern only matches at most four components.
        assert!(!is_exhaustive("<*/:0,4>"));
        assert!(!is_exhaustive("a/<?>"));
        assert!(!is_exhaustive("a</**/b>"));
        assert!(!is_exhaustive("<?>"));
        assert!(!is_exhaustive("<?/>"));
        // This pattern may match a nonexhaustive branch that does **not** overlap with any
        // exhaustive branch.
        //
        // To understand why this is not exhaustive, consider the match `foo/bar/b`. This matches
        // the second branch of the alternation, but not the first. This pattern does not match any
        // sub-tree of this match other than more `b` components (the first branch will never be
        // matched).
        assert!(!is_exhaustive("{a/**,**/b}"));
        assert!(!is_exhaustive("<{a/**,**/b}:1>"));
        assert!(!is_exhaustive("{{<a:1,>{/**},**/b},c/**}"));

        // TODO: This expression is exhaustive. The `/**` branch generalizes the `/**/a` branch.
        //       However, exhaustiveness applies a heuristic that rejects this (but importantly
        //       rejects nonexhaustive patterns like `{a/**,**/b}`). Remove generalized branches in
        //       an optimization step or remove their terms when determining exhaustiveness.
        //assert!(is_exhaustive("{/**,/**/a}"));
    }
}
