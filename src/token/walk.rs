use std::cmp;
use std::collections::VecDeque;

use crate::filter::{
    CancelWalk, HierarchicalIterator, Isomeric, SeparatingFilterInput, Separation, TreeResidue,
};
use crate::token::variance::natural::NaturalRange;
use crate::token::{
    Alternation, BranchKind, Composition, Concatenation, LeafKind, Repetition, Token,
    TokenTopology, TokenTree,
};
use crate::{IteratorExt as _, SliceExt as _, SliceProjection};

type TokenFeed<'i, 't, A> = (TokenEntry<'i, 't, A>, TreeResidue<TokenEntry<'i, 't, A>>);

impl<'i, 't, A> Isomeric for TokenFeed<'i, 't, A> {
    type Substituent<'a> = &'a TokenEntry<'i, 't, A>
    where
        Self: 'a;

    fn substituent(separation: &Separation<Self>) -> Self::Substituent<'_> {
        match separation {
            Separation::Filtrate(ref filtrate) => filtrate.get(),
            Separation::Residue(ref residue) => residue.get().get(),
        }
    }
}

pub trait ParentToken<'i, 't, A> {
    type Child: 'i + ChildToken<'t, A>;

    fn as_ref(&self) -> &BranchKind<'t, A>;

    fn into_tokens(self) -> impl DoubleEndedIterator<Item = Self::Child>;
}

impl<'i, 't, A> ParentToken<'i, 't, A> for &'i BranchKind<'t, A> {
    type Child = &'i Token<'t, A>;

    fn as_ref(&self) -> &BranchKind<'t, A> {
        self
    }

    fn into_tokens(self) -> impl DoubleEndedIterator<Item = Self::Child> {
        self.tokens().into_inner().iter()
    }
}

pub trait ChildToken<'t, A> {
    fn as_ref(&self) -> &Token<'t, A>;
}

impl<'i, 't, A, T> ChildToken<'t, A> for &'i T
where
    T: ChildToken<'t, A>,
{
    fn as_ref(&self) -> &Token<'t, A> {
        T::as_ref(*self)
    }
}

impl<'t, A> ChildToken<'t, A> for Token<'t, A> {
    fn as_ref(&self) -> &Token<'t, A> {
        self
    }
}

#[derive(Debug)]
pub struct Adjacency<'i, 't, A> {
    pub left: Option<&'i Token<'t, A>>,
    pub right: Option<&'i Token<'t, A>>,
}

impl<'i, 't, A> Adjacency<'i, 't, A> {
    // This may appear to operate in place.
    #[must_use]
    pub fn or(self, left: Option<&'i Token<'t, A>>, right: Option<&'i Token<'t, A>>) -> Self {
        Adjacency {
            left: left.or(self.left),
            right: right.or(self.right),
        }
    }

    pub fn is_open(&self) -> bool {
        self.left.is_none() && self.right.is_none()
    }

    pub fn is_closed(&self) -> bool {
        self.left.is_some() && self.right.is_some()
    }

    pub fn is_closed_boundary(&self) -> bool {
        let is_boundary =
            |token: Option<&Token<'_, _>>| token.map_or(false, |token| token.boundary().is_some());
        is_boundary(self.left) && is_boundary(self.right)
    }
}

impl<'i, 't, A> Clone for Adjacency<'i, 't, A> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<'i, 't, A> Copy for Adjacency<'i, 't, A> {}

impl<'i, 't, A> Default for Adjacency<'i, 't, A> {
    fn default() -> Self {
        Adjacency {
            left: None,
            right: None,
        }
    }
}

impl<'i, 't, A> From<Adjacency<'i, 't, A>>
    for (Option<&'i Token<'t, A>>, Option<&'i Token<'t, A>>)
{
    fn from(adjacency: Adjacency<'i, 't, A>) -> Self {
        let Adjacency { left, right } = adjacency;
        (left, right)
    }
}

pub trait FoldPosition<'t, A> {
    type Path: SliceProjection<Item = BranchKind<'t, A>>;

    fn adjacency(&self) -> &Adjacency<'_, 't, A>;

    fn path(&self) -> &Self::Path;
}

// Fold APIs are batched: folds operate against a complete and ordered sequence of terms rather
// than an accumulator and a single subsequent term. This incurs a performance penalty, but
// supports aggregations that must consider the complete sequence of terms without the need for
// additional state in `Fold` implementers or `Term`s.
pub trait Fold<'t, A> {
    type Sequencer: Sequencer;
    type Term;

    fn sequencer() -> Self::Sequencer;

    fn initialize(&mut self, _branch: &BranchKind<'t, A>) -> Option<Self::Term> {
        None
    }

    fn penult_or_root(&mut self, term: Self::Term) -> Self::Term {
        term
    }

    fn fold(
        &mut self,
        position: impl FoldPosition<'t, A>,
        branch: &BranchKind<'t, A>,
        terms: Vec<Self::Term>,
    ) -> Option<Self::Term>;

    fn finalize(&mut self, _branch: &BranchKind<'t, A>, term: Self::Term) -> Self::Term {
        term
    }

    fn term(&mut self, position: impl FoldPosition<'t, A>, leaf: &LeafKind<'t>) -> Self::Term;
}

impl<'f, 't, A, F> Fold<'t, A> for &'f mut F
where
    F: Fold<'t, A>,
{
    type Sequencer = F::Sequencer;
    type Term = F::Term;

    fn sequencer() -> Self::Sequencer {
        F::sequencer()
    }

    fn initialize(&mut self, branch: &BranchKind<'t, A>) -> Option<Self::Term> {
        F::initialize(self, branch)
    }

    fn penult_or_root(&mut self, term: Self::Term) -> Self::Term {
        F::penult_or_root(self, term)
    }

    fn fold(
        &mut self,
        position: impl FoldPosition<'t, A>,
        branch: &BranchKind<'t, A>,
        terms: Vec<Self::Term>,
    ) -> Option<Self::Term> {
        F::fold(self, position, branch, terms)
    }

    fn finalize(&mut self, branch: &BranchKind<'t, A>, term: Self::Term) -> Self::Term {
        F::finalize(self, branch, term)
    }

    fn term(&mut self, position: impl FoldPosition<'t, A>, leaf: &LeafKind<'t>) -> Self::Term {
        F::term(self, position, leaf)
    }
}

pub trait FoldMap<'t, 'o, A> {
    type Annotation;

    fn fold(
        &mut self,
        annotation: A,
        branch: BranchFold,
        tokens: Vec<Token<'o, Self::Annotation>>,
    ) -> Option<Token<'o, Self::Annotation>>;

    fn map(&mut self, annotation: A, leaf: LeafKind<'t>) -> Token<'o, Self::Annotation>;
}

impl<'t, A, B, F> FoldMap<'t, 't, A> for F
where
    F: FnMut(A) -> B,
{
    type Annotation = B;

    fn fold(
        &mut self,
        annotation: A,
        branch: BranchFold,
        tokens: Vec<Token<'t, Self::Annotation>>,
    ) -> Option<Token<'t, Self::Annotation>> {
        branch
            .fold(tokens)
            .ok()
            .map(|branch| Token::new(branch, (self)(annotation)))
    }

    fn map(&mut self, annotation: A, leaf: LeafKind<'t>) -> Token<'t, Self::Annotation> {
        Token::new(leaf, (self)(annotation))
    }
}

// The data in each variant must be the same as the associated `BranchComposition::BranchData` type
// for each branch type. However, there is no way to reference this type indepenently of the input
// type parameter `A`. These types must not depend on `A`, but there is no way to enforce this in
// `BranchComposition` as written. `BranchFold` expresses these types with no explicit relationship
// to `BranchComposition`. See `BranchComposition`.
#[derive(Debug)]
pub enum BranchFold {
    Alternation(()),
    Concatenation(()),
    Repetition(NaturalRange),
}

impl BranchFold {
    pub fn fold<'t, A>(self, tokens: Vec<Token<'t, A>>) -> Result<BranchKind<'t, A>, ()> {
        match self {
            BranchFold::Alternation(data) => {
                BranchKind::compose::<Alternation<'t, A>>(data, tokens)
            },
            BranchFold::Concatenation(data) => {
                BranchKind::compose::<Concatenation<'t, A>>(data, tokens)
            },
            BranchFold::Repetition(data) => BranchKind::compose::<Repetition<'t, A>>(data, tokens),
        }
    }
}

impl<'i, 't, A> crate::Adjacency<&'i Token<'t, A>> {
    pub fn fold_with_adjacent<F>(&self, f: F) -> Option<F::Term>
    where
        F: Fold<'t, A>,
    {
        let (left, token, right) = self.into_tuple();
        token.fold_at_position(Adjacency { left, right }, f)
    }
}

impl<'t, A> Token<'t, A> {
    pub fn fold<F>(&self, f: F) -> Option<F::Term>
    where
        F: Fold<'t, A>,
    {
        self.fold_at_position(Default::default(), f)
    }

    fn fold_at_position<F>(&self, adjacency: Adjacency<'_, 't, A>, f: F) -> Option<F::Term>
    where
        F: Fold<'t, A>,
    {
        #[derive(Clone, Copy, Debug)]
        struct Parent<'i, 't, A, I> {
            branch: &'i BranchKind<'t, A>,
            tokens: I,
        }

        impl<'i, 't, A, I> ParentToken<'i, 't, A> for Parent<'i, 't, A, I>
        where
            I: DoubleEndedIterator<Item = Child<'i, 't, A>>,
        {
            type Child = Child<'i, 't, A>;

            fn as_ref(&self) -> &BranchKind<'t, A> {
                self.branch
            }

            fn into_tokens(self) -> impl DoubleEndedIterator<Item = Self::Child> {
                self.tokens
            }
        }

        #[derive(Clone, Copy, Debug)]
        struct Child<'i, 't, A> {
            token: &'i Token<'t, A>,
            adjacency: Adjacency<'i, 't, A>,
        }

        impl<'i, 't, A> ChildToken<'t, A> for Child<'i, 't, A> {
            fn as_ref(&self) -> &Token<'t, A> {
                self.token
            }
        }

        #[derive(Clone, Copy, Debug)]
        pub struct Position<'i, 't, A, P> {
            adjacency: Adjacency<'i, 't, A>,
            path: P,
        }

        impl<'i, 't, A, P> FoldPosition<'t, A> for Position<'i, 't, A, P>
        where
            P: SliceProjection<Item = BranchKind<'t, A>>,
        {
            type Path = P;

            fn adjacency(&self) -> &Adjacency<'_, 't, A> {
                &self.adjacency
            }

            fn path(&self) -> &Self::Path {
                &self.path
            }
        }

        struct TokenPath<'i, 't, A, F>
        where
            F: Fold<'t, A>,
        {
            branches: Vec<TokenBranch<'i, 't, A, F>>,
            f: F,
        }

        impl<'i, 't, A, F> TokenPath<'i, 't, A, F>
        where
            F: Fold<'t, A>,
        {
            pub fn push(&mut self, branch: &'i BranchKind<'t, A>, adjacency: Adjacency<'i, 't, A>) {
                let mut terms = VecDeque::with_capacity(branch.tokens().into_inner().len() + 1);
                if let Some(term) = self.f.initialize(branch) {
                    terms.push_front(term);
                }
                self.branches.push(TokenBranch {
                    branch,
                    adjacency,
                    terms,
                });
            }

            pub fn pop(&mut self, depth: usize) {
                if let Some(n) = self.branches.len().checked_sub(depth) {
                    self.fold(n);
                }
            }

            pub fn accumulate(
                &mut self,
                leaf: &'i LeafKind<'t>,
                adjacency: Adjacency<'i, 't, A>,
            ) -> Result<(), F::Term> {
                let (f, path) = self.as_fold_and_path_slice();
                let term = f.term(Position { adjacency, path }, leaf);
                match self.branches.last_mut() {
                    Some(branch) => {
                        branch.push(term);
                        Ok(())
                    },
                    None => Err(term),
                }
            }

            pub fn as_fold_and_path_slice(
                &mut self,
            ) -> (&mut F, impl '_ + SliceProjection<Item = BranchKind<'t, A>>) {
                (
                    &mut self.f,
                    self.branches.as_slice().project(|branch| branch.branch),
                )
            }

            pub fn last(mut self) -> Option<F::Term> {
                self.fold(usize::MAX);
                self.branches.pop().and_then(|branch| {
                    let (f, path) = self.as_fold_and_path_slice();
                    branch.last(path, f)
                })
            }

            pub fn only(mut self, term: F::Term) -> F::Term {
                self.f.penult_or_root(term)
            }

            fn fold(&mut self, n: usize) {
                for _ in 0..cmp::min(n, self.branches.len().saturating_sub(1)) {
                    let branch = self.branches.pop().unwrap();
                    let (f, path) = self.as_fold_and_path_slice();
                    if let Some(term) = branch.fold(path, f) {
                        self.branches.last_mut().unwrap().push(term);
                    }
                }
            }
        }

        struct TokenBranch<'i, 't, A, F>
        where
            F: Fold<'t, A>,
        {
            branch: &'i BranchKind<'t, A>,
            adjacency: Adjacency<'i, 't, A>,
            // A queue is used to preserve the order of terms w.r.t. to the token tree and, more
            // subtly, any initializer terms.
            terms: VecDeque<F::Term>,
        }

        impl<'i, 't, A, F> TokenBranch<'i, 't, A, F>
        where
            F: Fold<'t, A>,
        {
            pub fn push(&mut self, term: F::Term) {
                self.terms.push_front(term)
            }

            pub fn fold(
                self,
                path: impl SliceProjection<Item = BranchKind<'t, A>>,
                f: &mut F,
            ) -> Option<F::Term> {
                self.fold_map(path, |terms| (terms.into(), f))
            }

            pub fn last(
                self,
                path: impl SliceProjection<Item = BranchKind<'t, A>>,
                f: &mut F,
            ) -> Option<F::Term> {
                self.fold_map(path, |terms| {
                    (
                        terms
                            .into_iter()
                            .map(|term| f.penult_or_root(term))
                            .collect(),
                        f,
                    )
                })
            }

            fn fold_map<'m, M>(
                self,
                path: impl SliceProjection<Item = BranchKind<'t, A>>,
                map_terms_and_get_fold: M,
            ) -> Option<F::Term>
            where
                F: 'm,
                M: 'm + FnOnce(VecDeque<F::Term>) -> (Vec<F::Term>, &'m mut F),
            {
                let TokenBranch {
                    branch,
                    adjacency,
                    terms,
                } = self;
                let (terms, f) = (map_terms_and_get_fold)(terms);
                f.fold(Position { adjacency, path }, branch, terms)
                    .map(|term| f.finalize(branch, term))
            }
        }

        let mut sequencer = F::sequencer();
        let mut path = TokenPath {
            branches: vec![],
            f,
        };
        let mut tokens = vec![(self, adjacency, 0usize)];
        while let Some((token, adjacency, depth)) = tokens.pop() {
            path.pop(depth);
            match token.topology() {
                TokenTopology::Branch(ref branch) => {
                    // `Adjacent` does not implement `DoubleEndedIterator`, so it is moved into
                    // `Map` and advanced in lockstep. This avoids collecting into an intermediate
                    // buffer.
                    let mut adjacencies = branch
                        .tokens()
                        .into_inner()
                        .iter()
                        .adjacent()
                        .map(crate::Adjacency::into_tuple)
                        .map(|(left, _, right)| adjacency.or(left, right));
                    tokens.extend(
                        sequencer
                            .enqueue(Parent {
                                branch,
                                tokens: branch.tokens().into_inner().iter().map(|token| Child {
                                    token,
                                    adjacency: adjacencies.next().expect("no adjacency for token"),
                                }),
                            })
                            .map(|Child { token, adjacency }| (token, adjacency, depth + 1)),
                    );
                    path.push(branch, adjacency);
                },
                TokenTopology::Leaf(ref leaf) => {
                    if let Err(term) = path.accumulate(leaf, adjacency) {
                        return Some(path.only(term));
                    }
                },
            }
        }
        path.last()
    }

    pub fn fold_map<'o, F>(self, f: F) -> Token<'o, F::Annotation>
    where
        F: FoldMap<'t, 'o, A>,
    {
        struct TokenPath<'t, 'o, A, F>
        where
            F: FoldMap<'t, 'o, A>,
        {
            branches: Vec<TokenBranch<'t, 'o, A, F>>,
            f: F,
        }

        impl<'t, 'o, A, F> TokenPath<'t, 'o, A, F>
        where
            F: FoldMap<'t, 'o, A>,
        {
            pub fn push(&mut self, annotation: A, branch: BranchFold, hint: Option<usize>) {
                self.branches.push(TokenBranch {
                    annotation,
                    branch,
                    tokens: match hint {
                        Some(hint) => Vec::with_capacity(hint),
                        _ => vec![],
                    },
                });
            }

            pub fn pop(&mut self, depth: usize) {
                if let Some(n) = self.branches.len().checked_sub(depth) {
                    self.fold_n(n);
                }
            }

            pub fn fold(mut self) -> Option<Token<'o, F::Annotation>> {
                self.fold_n(usize::MAX);
                self.branches
                    .pop()
                    .and_then(|branch| branch.fold(&mut self.f))
            }

            pub fn map(
                &mut self,
                annotation: A,
                leaf: LeafKind<'t>,
            ) -> Result<(), Token<'o, F::Annotation>> {
                let token = self.f.map(annotation, leaf);
                match self.branches.last_mut() {
                    Some(branch) => {
                        branch.push(token);
                        Ok(())
                    },
                    None => Err(token),
                }
            }

            fn fold_n(&mut self, n: usize) {
                for _ in 0..cmp::min(n, self.branches.len().saturating_sub(1)) {
                    if let Some(token) = self.branches.pop().unwrap().fold(&mut self.f) {
                        self.branches.last_mut().unwrap().push(token);
                    }
                }
            }
        }

        struct TokenBranch<'t, 'o, A, F>
        where
            F: FoldMap<'t, 'o, A>,
        {
            annotation: A,
            branch: BranchFold,
            tokens: Vec<Token<'o, F::Annotation>>,
        }

        impl<'t, 'o, A, F> TokenBranch<'t, 'o, A, F>
        where
            F: FoldMap<'t, 'o, A>,
        {
            fn push(&mut self, token: Token<'o, F::Annotation>) {
                self.tokens.push(token)
            }

            fn fold(self, f: &mut F) -> Option<Token<'o, F::Annotation>> {
                let TokenBranch {
                    annotation,
                    branch,
                    tokens,
                } = self;
                f.fold(annotation, branch, tokens)
            }
        }

        let mut path = TokenPath {
            branches: vec![],
            f,
        };
        let mut tokens = vec![(self, 0usize)];
        while let Some((token, depth)) = tokens.pop() {
            path.pop(depth);
            match token.topology {
                TokenTopology::Branch(branch) => {
                    let (branch, children) = branch.decompose();
                    let n = children.len();
                    tokens.extend(children.into_iter().rev().map(|token| (token, depth + 1)));
                    path.push(token.annotation, branch, Some(n));
                },
                TokenTopology::Leaf(leaf) => {
                    if let Err(token) = path.map(token.annotation, leaf) {
                        return token;
                    }
                },
            }
        }
        path.fold().expect("no tokens in non-empty tree path")
    }
}

pub trait Sequencer {
    fn enqueue<'i, 't, A, T>(&mut self, parent: T) -> impl Iterator<Item = T::Child>
    where
        T: ParentToken<'i, 't, A>;
}

#[derive(Default)]
pub struct Forward;

impl Sequencer for Forward {
    fn enqueue<'i, 't, A, T>(&mut self, parent: T) -> impl Iterator<Item = T::Child>
    where
        T: ParentToken<'i, 't, A>,
    {
        parent.into_tokens()
    }
}

#[derive(Default)]
pub struct Starting;

impl Sequencer for Starting {
    fn enqueue<'i, 't, A, T>(&mut self, parent: T) -> impl Iterator<Item = T::Child>
    where
        T: ParentToken<'i, 't, A>,
    {
        let n = match parent.as_ref().tokens() {
            Composition::Conjunctive(_) => 1,
            Composition::Disjunctive(tokens) => tokens.len(),
        };
        parent.into_tokens().take(n)
    }
}

#[derive(Default)]
pub struct Ending;

impl Sequencer for Ending {
    fn enqueue<'i, 't, A, T>(&mut self, parent: T) -> impl Iterator<Item = T::Child>
    where
        T: ParentToken<'i, 't, A>,
    {
        let n = match parent.as_ref().tokens() {
            Composition::Conjunctive(tokens) => tokens.len().saturating_sub(1),
            Composition::Disjunctive(_) => 0,
        };
        parent.into_tokens().skip(n)
    }
}

#[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
pub struct WalkDepth {
    pub conjunctive: usize,
    pub disjunctive: usize,
}

#[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
pub struct WalkPosition {
    pub depth: WalkDepth,
    pub branch: usize,
}

impl WalkPosition {
    // This may appear to operate in place.
    #[must_use]
    fn conjunction(self) -> Self {
        let WalkPosition {
            depth:
                WalkDepth {
                    conjunctive,
                    disjunctive,
                },
            branch,
        } = self;
        WalkPosition {
            depth: WalkDepth {
                conjunctive: conjunctive + 1,
                disjunctive,
            },
            branch,
        }
    }

    // This may appear to operate in place.
    #[must_use]
    fn disjunction(self, branch: usize) -> Self {
        let WalkPosition {
            depth:
                WalkDepth {
                    conjunctive,
                    disjunctive,
                },
            ..
        } = self;
        WalkPosition {
            depth: WalkDepth {
                conjunctive,
                disjunctive: disjunctive + 1,
            },
            branch,
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub struct WalkEntry<T> {
    pub position: WalkPosition,
    pub token: T,
}

impl<T> WalkEntry<T> {
    pub fn into_token(self) -> T {
        self.token
    }

    fn map<U, F>(self, f: F) -> WalkEntry<U>
    where
        F: FnOnce(T) -> U,
    {
        let WalkEntry { position, token } = self;
        WalkEntry {
            position,
            token: f(token),
        }
    }

    pub fn position(&self) -> WalkPosition {
        self.position
    }
}

type BranchEntry<'i, 't, A> = WalkEntry<&'i BranchKind<'t, A>>;

pub type TokenEntry<'i, 't, A> = WalkEntry<&'i Token<'t, A>>;

#[derive(Clone, Debug)]
struct Walk<'i, 't, A, S> {
    branch: Option<BranchEntry<'i, 't, A>>,
    tokens: VecDeque<TokenEntry<'i, 't, A>>,
    sequencer: S,
}

impl<'i, 't, A, S> CancelWalk for Walk<'i, 't, A, S> {
    fn cancel_walk_tree(&mut self) {
        self.branch.take();
    }
}

impl<'i, 't, A, S> Iterator for Walk<'i, 't, A, S>
where
    S: Sequencer,
{
    type Item = TokenEntry<'i, 't, A>;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(BranchEntry { position, token }) = self.branch.take() {
            match token.composition().map(|_| self.sequencer.enqueue(token)) {
                Composition::Conjunctive(tokens) => {
                    self.tokens.extend(tokens.map(|token| TokenEntry {
                        position: position.conjunction(),
                        token,
                    }))
                },
                Composition::Disjunctive(tokens) => {
                    self.tokens
                        .extend(tokens.enumerate().map(|(branch, token)| TokenEntry {
                            position: position.disjunction(branch),
                            token,
                        }))
                },
            };
        }
        if let Some(entry) = self.tokens.pop_front() {
            if let Some(branch) = entry.token.as_branch() {
                self.branch = Some(entry.map(|_| branch));
            }
            Some(entry)
        }
        else {
            None
        }
    }
}

impl<'i, 't, A, S> SeparatingFilterInput for Walk<'i, 't, A, S>
where
    S: Sequencer,
{
    type Feed = TokenFeed<'i, 't, A>;
}

// NOTE: Tokens discarded by `sequencer` are **not** present in the feed of the output.
pub fn with_sequence<'i, 't, T, S>(
    tree: &'i T,
    sequencer: S,
) -> impl 'i + HierarchicalIterator<Feed = TokenFeed<'i, 't, T::Annotation>>
where
    't: 'i,
    T: TokenTree<'t>,
    S: 'i + Sequencer,
{
    Walk {
        branch: None,
        tokens: Some(TokenEntry {
            position: WalkPosition::default(),
            token: tree.as_token(),
        })
        .into_iter()
        .collect(),
        sequencer,
    }
}

pub fn forward<'i, 't, T>(
    tree: &'i T,
) -> impl 'i + HierarchicalIterator<Feed = TokenFeed<'i, 't, T::Annotation>>
where
    't: 'i,
    T: TokenTree<'t>,
{
    self::with_sequence(tree, Forward)
}

pub fn starting<'i, 't, T>(
    tree: &'i T,
) -> impl 'i + HierarchicalIterator<Feed = TokenFeed<'i, 't, T::Annotation>>
where
    't: 'i,
    T: 't + TokenTree<'t>,
{
    self::with_sequence(tree, Starting)
}

pub fn ending<'i, 't, T>(
    tree: &'i T,
) -> impl 'i + HierarchicalIterator<Feed = TokenFeed<'i, 't, T::Annotation>>
where
    't: 'i,
    T: 't + TokenTree<'t>,
{
    self::with_sequence(tree, Ending)
}
