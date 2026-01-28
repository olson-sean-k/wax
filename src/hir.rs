#[cfg(feature = "miette")]
use miette::Diagnostic;
use regex_syntax::hir;
use std::borrow::Borrow;
use std::collections::VecDeque;
#[cfg(feature = "miette")]
use std::fmt::Display;
use thiserror::Error;

pub use regex_automata::meta::Regex;

use crate::token::walk::{Fold, FoldPosition, Forward};
use crate::token::{
    self, ops, Archetype, BoundaryTerm, BranchKind, Composition, ConcatenationTree, Conjunction,
    Finalize, LeafKind, SeparatedTerm, Termination, TreeTerm,
};
use crate::IteratorExt as _;

impl Conjunction for hir::Hir {
    type Output = Self;

    fn conjunction(self, rhs: Self) -> Self::Output {
        hir::Hir::concat(vec![self, rhs])
    }
}

trait IntoHir {
    fn into_hir(self) -> hir::Hir;
}

impl IntoHir for hir::ClassUnicode {
    fn into_hir(self) -> hir::Hir {
        hir::Hir::class(hir::Class::Unicode(self))
    }
}

trait Negated {
    fn negated(self) -> Self;
}

impl Negated for hir::ClassUnicode {
    fn negated(mut self) -> Self {
        self.negate();
        self
    }
}

/// Describes errors that occur when compiling a glob expression.
///
/// **This error only occurs when the size of the compiled program is too large.** All other
/// compilation errors are considered internal bugs and will panic.
#[derive(Clone, Debug, Error)]
#[error("failed to compile glob: {kind}")]
pub struct CompileError {
    kind: CompileErrorKind,
}

#[derive(Clone, Copy, Debug, Error)]
#[non_exhaustive]
enum CompileErrorKind {
    #[error("oversized program")]
    OversizedProgram,
}

#[cfg(feature = "miette")]
#[cfg_attr(docsrs, doc(cfg(feature = "miette")))]
impl Diagnostic for CompileError {
    fn code<'a>(&'a self) -> Option<Box<dyn 'a + Display>> {
        Some(Box::new(String::from(match self.kind {
            CompileErrorKind::OversizedProgram => "wax::glob::oversized_program",
        })))
    }
}

#[cfg(unix)]
fn separator() -> hir::ClassUnicode {
    hir::ClassUnicode::new([hir::ClassUnicodeRange::new('/', '/')])
}

#[cfg(windows)]
fn separator() -> hir::ClassUnicode {
    hir::ClassUnicode::new([
        hir::ClassUnicodeRange::new('/', '/'),
        hir::ClassUnicodeRange::new('\\', '\\'),
    ])
}

// This pattern only matches the platform's **main** separator, so any additional separators behave
// nominally rather than structurally. It may be better to have explicit platform support and
// invoke `compile_error!` on unsupported platforms, as this could cause very aberrant behavior.
// Then again, it seems that platforms using more than one separator are rare. GS/OS, OS/2, and
// Windows are likely the best known examples, and of those only Windows is a supported Rust target
// at time of writing.
#[cfg(not(any(unix, windows)))]
fn separator() -> hir::ClassUnicode {
    use std::path::MAIN_SEPARATOR;

    hir::ClassUnicode::new([hir::ClassUnicodeRange::new(MAIN_SEPARATOR, MAIN_SEPARATOR)])
}

fn case_folded_literal(text: impl AsRef<str>) -> hir::Hir {
    hir::Hir::concat(
        text.as_ref()
            .chars()
            .map(|point| hir::ClassUnicode::new([hir::ClassUnicodeRange::new(point, point)]))
            .map(|mut hir| {
                let _ = hir.try_case_fold_simple();
                hir
            })
            .map(hir::Class::Unicode)
            .map(hir::Hir::class)
            .collect(),
    )
}

pub fn case_folded_eq(lhs: impl AsRef<str>, rhs: impl AsRef<str>) -> bool {
    let lhs = self::case_folded_literal(lhs);
    let rhs = rhs.as_ref();
    let regex = Regex::builder()
        .build_from_hir(&lhs)
        .expect("failed to compile case folding regular expression");
    regex.find(rhs).map_or(false, |matched| {
        matched.start() == 0 && matched.end() == rhs.len()
    })
}

// <*/> => Last(ZeroOrMore)
// x<*/> => [Open(Hir(x)), Last(ZeroOrMore(*/))]
//          {Open(Hir(x)), Last(Hir(x*/))}
// <*/>* => [Last(ZeroOrMore), Open(Many(None,None))]
//          {Open(Many(None,None)), Open(Many(Hir,None))}
// x<*/>* => [{Open(Hir(x)), Last(Hir(x*/))}, Open(Many(None,Hir(*),None))]
//           {Open(Hir(x*)), Open(Many(Hir(x*/),Hir(*),None))}
// {a/,b} => {Last(Hir(a/)), Open(Hir(b))}
// {a/,b}* => [{Last(Hir(a/)), Open(Hir(b))}, Open(Many(None,Hir(*),None))]
//            {Open(Many(Hir(a/),Hir(*),None)), Open(Hir(b*))}
// x<*/>* => [Open(Hir(x)),{Open(Hir(@)),Last(Hir(<*/:1,>))},Open(ZeroOrOne(Only([*])))]
//           [{Open(Hir(x)),Last(Hir(x<*/:1,>))},Open(ZeroOrOne(Only([*])))]
//           {Open(Hir(x<?:0,>)),Open(ZeroOrOne(Left(Hir(x<*/:1,>),[*])))}
//        F= Hir({x<?:0,>,x<*/:1,><?:1,>})
// <a:0,5>* => [Open(ZeroOrOne(Only([a]))),Open(ZeroOrOne(Only([*])))]
//             Open(ZeroOrOne(Only([a,*])))
//          F= Hir({<a:1,5><?:0,>,<a:0,5><?:1,>})
// $<a>b => [Open(ZeroOrOne(Only([$]))),Open(ZeroOrOne(Only([a]))),Open(Hir(b))]
//          [Open(ZeroOrOne(Only([$,a]))),Open(Hir(b))]
//          Open(Hir(<#:0,><a:0,>b))
// */a => [Open(ZeroOrOne(Only([*]))),Closed(Hir(/)),Open(Hir(a))]
//        [Last(ZeroOrOne(Right([*],Hir(/)))),Open(Hir(a))]
//        Open(ZeroOrOne(Right([*],Hir(/a))))
// {a/,b}* => [{Last(Hir(a/)),Open(Hir(b))},Open(ZeroOrOne(Only[*]))]
//            {Open(ZeroOrOne(Left(Hir(a/),[*]))),Open(Hir(b<?:0,>))}
pub fn compile<'t, T>(tree: impl Borrow<T>) -> Result<Regex, CompileError>
where
    T: ConcatenationTree<'t>,
{
    impl Conjunction for BoundaryTerm<Deferred> {
        type Output = Self;

        fn conjunction(self, rhs: Self) -> Self::Output {
            use Composition::{Conjunctive, Disjunctive};

            //match (self, rhs) {
            //    (Conjunctive(lhs), Conjunctive(rhs)) => ops::conjunction(lhs, rhs),
            //    (Conjunctive(lhs), Disjunctive(rhs)) => ops::conjunction(lhs, rhs),
            //    (Disjunctive(lhs), Conjunctive(rhs)) => ops::conjunction(lhs, rhs),
            //    (Disjunctive(lhs), Disjunctive(rhs)) => ops::conjunction(lhs, rhs),
            //}
            todo!()
        }
    }

    impl Conjunction for SeparatedTerm<Deferred> {
        type Output = BoundaryTerm<Deferred>;

        fn conjunction(self, rhs: Self) -> Self::Output {
            todo!()
        }
    }

    trait Capture {
        fn capture(self, index: u32) -> Self;
    }

    trait IntoRepetition {
        fn zero_or_more(self) -> hir::Hir;

        fn at_least_one(self) -> hir::Hir;
    }

    #[derive(Clone, Debug)]
    struct MaybeZero {
        hir: hir::Hir,
        max: Option<u32>,
        is_greedy: bool,
    }

    impl MaybeZero {
        fn into_repetition(self, min: u32) -> hir::Repetition {
            let MaybeZero {
                hir,
                max,
                is_greedy,
            } = self;
            hir::Repetition {
                min,
                max,
                greedy: self.is_greedy,
                sub: Box::new(hir),
            }
        }
    }

    impl Capture for MaybeZero {
        fn capture(mut self, index: u32) -> Self {
            self.hir = hir::Hir::capture(hir::Capture {
                index,
                name: None,
                sub: Box::new(self.hir),
            });
            self
        }
    }

    impl Finalize for MaybeZero {
        type Output = hir::Hir;

        fn finalize(self) -> Self::Output {
            self.at_least_one()
        }
    }

    impl IntoRepetition for MaybeZero {
        fn zero_or_more(self) -> hir::Hir {
            hir::Hir::repetition(self.into_repetition(0))
        }

        fn at_least_one(self) -> hir::Hir {
            hir::Hir::repetition(self.into_repetition(1))
        }
    }

    impl IntoRepetition for VecDeque<MaybeZero> {
        fn zero_or_more(self) -> hir::Hir {
            hir::Hir::concat(self.into_iter().map(MaybeZero::zero_or_more).collect())
        }

        fn at_least_one(self) -> hir::Hir {
            // TODO: What about captures? How does `regex` handle identical capture indices, in
            //       particular when they are composed into alternatives?
            hir::Hir::alternation(
                (0..self.len())
                    .map(|at_least_one_index| {
                        hir::Hir::concat(
                            self.iter()
                                .cloned()
                                .enumerate()
                                .map(|(index, repetition)| {
                                    if at_least_one_index == index {
                                        repetition.at_least_one()
                                    }
                                    else {
                                        repetition.zero_or_more()
                                    }
                                })
                                .collect(),
                        )
                    })
                    .collect(),
            )
        }
    }

    #[derive(Debug)]
    struct ZeroOrOneLeft(pub Box<Deferred<ZeroOrOneRight>>, pub MaybeZero);

    impl Finalize for ZeroOrOneLeft {
        type Output = hir::Hir;

        fn finalize(self) -> Self::Output {
            let ZeroOrOneLeft(left, repetition) = self;
            hir::Hir::concat(vec![
                left.finalize(),
                repetition.finalize(),
            ])
        }
    }

    #[derive(Debug)]
    struct ZeroOrOneRight(pub MaybeZero, pub Box<Deferred<ZeroOrOneLeft>>);

    impl<N> Conjunction<Deferred<N>> for ZeroOrOneRight {
        type Output = TreeTerm<Self>;

        fn conjunction(self, rhs: Deferred<N>) -> Self::Output {
            todo!()
        }
    }

    impl Finalize for ZeroOrOneRight {
        type Output = hir::Hir;

        fn finalize(self) -> Self::Output {
            let ZeroOrOneRight(repetition, right) = self;
            hir::Hir::concat(vec![
                repetition.finalize(),
                right.finalize(),
            ])
        }
    }

    // TODO: It looks like this would need an ordered vector of `MaybeZero`s for when the
    //       repetition components of `ZeroOrOne`s are conjoined. In that case, there is no way to
    //       encode the repetitions into a `Hir` until the lower bound is determined. Moreover, the
    //       pattern may get nasty: it looks like it may require an alternation with N branches
    //       wherein one of the repetitions has a lower bound of one.
    #[derive(Debug)]
    enum ZeroOrOne {
        Only(MaybeZero),
        Left(ZeroOrOneLeft),
        Right(ZeroOrOneRight),
    }

    impl Finalize for ZeroOrOne {
        type Output = hir::Hir;

        fn finalize(self) -> Self::Output {
            match self {
                ZeroOrOne::Left(left) => left.finalize(),
                ZeroOrOne::Only(only) => only.finalize(),
                ZeroOrOne::Right(right) => right.finalize(),
            }
        }
    }

    //#[derive(Debug)]
    //struct ZeroAndMaybeOne(pub MaybeZero);

    //impl Finalize for ZeroAndMaybeOne {
    //    type Output = hir::Hir;

    //    fn finalize(self) -> Self::Output {
    //        self.zero_or_more()
    //    }
    //}

    #[derive(Debug)]
    enum Deferred<N = ZeroOrOne> {
        Ready(hir::Hir),
        ZeroOrOne(N),
        // TODO: This variant is not necessary. A couple observations:
        //
        //       1. Any token/term representing some kind of repetition falls into this category if
        //          it (or its composition) has a termination. Today, this is only possible with
        //          repetition tokens. For example, `<a/>` but NOT `<a>` NOR `<a/b>`.
        //       2. When this happens, the token can be IMMEDIATELY rendered as a disjunctive term!
        //          For example, `<a/>` is correctly represented by the term
        //          `{Open(Hir(@)),Last(Hir(<a/:1,>))}`, where `@` means "empty". This combines
        //          properly with subsequent terms.
        //ZeroAndMaybeOne(ZeroAndMaybeOne),
    }

    impl<N> Capture for Deferred<N>
    where
        N: Capture,
    {
        fn capture(self, index: u32) -> Self {
            match self {
                Deferred::Ready(hir) => Deferred::Ready(hir.capture(index)),
                Deferred::ZeroOrOne(repetition) => Deferred::ZeroOrOne(repetition.capture(index)),
            }
        }
    }

    impl<N> Finalize for Deferred<N>
    where
        N: Finalize<Output = hir::Hir>,
    {
        type Output = hir::Hir;

        fn finalize(self) -> Self::Output {
            match self {
                Deferred::Ready(hir) => hir,
                Deferred::ZeroOrOne(repetition) => repetition.finalize(),
            }
        }
    }

    #[derive(Debug, Default)]
    struct Compile;

    impl<'t, A> Fold<'t, A> for Compile {
        type Sequencer = Forward;
        type Term = hir::Hir;

        fn sequencer() -> Self::Sequencer {
            Forward
        }

        fn fold(
            &mut self,
            _: impl FoldPosition<'t, A>,
            branch: &BranchKind<'t, A>,
            terms: Vec<Self::Term>,
        ) -> Option<Self::Term> {
            use BranchKind::{Alternation, Concatenation, Repetition};

            Some(match branch {
                Alternation(_) => hir::Hir::alternation(terms),
                Concatenation(_) => hir::Hir::concat(terms),
                Repetition(ref repetition) => {
                    let (min, max) = repetition.bound_specification();
                    hir::Hir::repetition(hir::Repetition {
                        min: u32::try_from(min).unwrap_or(u32::MAX),
                        max: max.map(u32::try_from).transpose().unwrap_or(Some(u32::MAX)),
                        greedy: true,
                        sub: Box::new(hir::Hir::concat(terms)),
                    })
                },
            })
        }

        fn term(&mut self, position: impl FoldPosition<'t, A>, leaf: &LeafKind<'t>) -> Self::Term {
            use token::Wildcard::{One, Tree, ZeroOrMore};
            use Archetype::{Character, Range};
            use LeafKind::{Class, Literal, Separator, Wildcard};

            let adjacency = position.adjacency();
            match leaf {
                Class(ref class) => {
                    let is_negated = class.is_negated();
                    let mut class =
                        hir::ClassUnicode::new(class.archetypes().iter().map(|archetype| {
                            let (start, end) = match archetype {
                                Character(ref point) => (*point, *point),
                                Range(ref start, ref end) => (*start, *end),
                            };
                            hir::ClassUnicodeRange::new(start, end)
                        }));
                    if is_negated {
                        class.union(&self::separator());
                        class.negate();
                    }
                    else {
                        class.difference(&self::separator());
                    }
                    class.into_hir()
                },
                Literal(ref literal) => {
                    if literal.is_case_insensitive() {
                        self::case_folded_literal(literal.text())
                    }
                    else {
                        hir::Hir::literal(literal.text().as_bytes())
                    }
                },
                Separator(_) => {
                    if adjacency.right.is_some() {
                        self::separator().into_hir()
                    }
                    else {
                        hir::Hir::alternation(vec![
                            self::separator().into_hir(),
                            hir::Hir::look(hir::Look::End),
                        ])
                    }
                },
                Wildcard(ref wildcard) => match wildcard {
                    One => hir::Hir::class(hir::Class::Unicode(self::separator().negated())),
                    Tree { ref has_root } => hir::Hir::alternation(vec![
                        hir::Hir::concat(vec![
                            if *has_root {
                                self::separator().into_hir()
                            }
                            else {
                                hir::Hir::empty()
                            },
                            hir::Hir::repetition(hir::Repetition {
                                min: 0,
                                max: None,
                                greedy: true,
                                sub: Box::new(hir::Hir::dot(hir::Dot::AnyChar)),
                            }),
                            hir::Hir::alternation(vec![
                                self::separator().into_hir(),
                                hir::Hir::look(hir::Look::End),
                            ]),
                        ]),
                        self::separator().into_hir(),
                        hir::Hir::empty(),
                    ]),
                    // TODO: Adjacency and simple `Hir` terms are insufficient for any tokens that
                    //       represent some kind of repetition like this. Likely, some kind of
                    //       `BoundaryTerm` with `DisjunctiveTerm`s for alternations are necessary.
                    //
                    //       Consider `{a/,b}*`. The `*` must be redistributed in the conjunction,
                    //       because it must encode two different programs for each branch. Notice
                    //       that this always occurs when a zero-or-more repetition token (of any
                    //       kind) forms a component wherein a boundary occurs `Sometimes`. In this
                    //       case, the equivalent glob expression must be `{a/<?:1,>,b<?>}`. Note
                    //       too that the end of the expression behaves like a boundary in this
                    //       context: the distributed equivalent of `{a/,b}*c` is `{a/<?>,b<?>}c`
                    //       wherein `*` is `<?>` in both branches of the alternation.
                    //
                    //       This of course applies to repetition tokens too. `a/<x>/b` must become
                    //       `a/<x:1,>/b`. Similarly, `{a/,b}<x>` must be equivalent to
                    //       `{a/<x:1,>,b<x>}`. However, this is only the case for repetitions with
                    //       open sub-globs (no separators at terminations). This is important not
                    //       only for correctness, but also for avoiding the need for indirection
                    //       in term types to prevent infinitely sized types (because an
                    //       intermediate `ZeroOrMore` may need to contain itself).
                    //
                    //       Moreover, it may not be possible to encode this in the HIR with only
                    //       additional HIR nodes. There is no notion of "this node, but never
                    //       empty", for example. Instead, the `hir::Repetition` likely needs to be
                    //       constructed in `fold` with an appropriate bound. However, it may be
                    //       possible to do so by always using a minimum bound of one and nesting
                    //       in a repetition with a minimum bound of zero, but this requires most
                    //       of the information needed to construct the necessary repetition alone
                    //       anyway.
                    //
                    //       Tree wildcards need no special attention. They cannot be adjacent to
                    //       other boundary tokens (even `Sometimes`), so their lower bound can
                    //       always remain zero. Even if adjacent boundary tokens were allowed,
                    //       then they would also need to coalesce, and patterns like `{a/,b}**/`
                    //       would be equivalent to `{a,b}/**/` and `{a/**/,b/**/}`.
                    ZeroOrMore { ref is_greedy } => hir::Hir::repetition(hir::Repetition {
                        min: if adjacency.is_component() { 1 } else { 0 },
                        max: None,
                        greedy: *is_greedy,
                        sub: Box::new(self::separator().negated().into_hir()),
                    }),
                },
            }
        }
    }

    let mut capture_group_index = 0u32;
    let hir = hir::Hir::concat(
        Some(hir::Hir::look(hir::Look::Start))
            .into_iter()
            .chain(
                tree.borrow()
                    .concatenation()
                    .iter()
                    .adjacent()
                    .map(|token| {
                        // TODO: Regarding TODOs above: this approach to captures should continue
                        //       to work, but just requires a conjunction of terms and finalization
                        //       here, outside of the `Fold` implementation.
                        //
                        //       This is ideal, because it allows `Token`s to cleanly abstract what
                        //       captures (i.e., `Token::is_capturing` is both meaningful and
                        //       authoritative).
                        let hir = token
                            .fold_with_adjacent(Compile)
                            .unwrap_or_else(hir::Hir::empty);
                        if token.into_item().is_capturing() {
                            capture_group_index = capture_group_index
                                .checked_add(1)
                                .expect("overflow in capture group index");
                            hir::Hir::capture(hir::Capture {
                                index: capture_group_index,
                                name: None,
                                sub: Box::new(hir),
                            })
                        }
                        else {
                            hir
                        }
                    }),
            )
            .chain(Some(hir::Hir::look(hir::Look::End)))
            .collect(),
    );
    // TODO: Remove this.
    //eprintln!("TREE\n{:#?}", hir);
    Regex::builder()
        .build_from_hir(&hir)
        .map_err(|error| match error.size_limit() {
            Some(_) => CompileError {
                kind: CompileErrorKind::OversizedProgram,
            },
            _ => panic!("failed to compile glob"),
        })
}

#[cfg(test)]
pub mod harness {
    use crate::encode;

    pub fn assert_case_folded_eq_eq(lhs: &str, rhs: &str, expected: bool) -> bool {
        let eq = encode::case_folded_eq(lhs, rhs);
        assert!(
            eq == expected,
            "`encode::case_folded_eq` is `{}`, but expected `{}`",
            eq,
            expected,
        );
        eq
    }
}

#[cfg(test)]
mod tests {
    use rstest::rstest;

    use crate::encode::harness;

    #[rstest]
    #[case::ascii_with_no_casing("", "")]
    #[case::ascii_with_no_casing("0", "0")]
    #[case::ascii_with_no_casing("_", "_")]
    #[case::ascii_with_casing("a", "a")]
    #[case::ascii_with_casing("a", "A")]
    #[case::ascii_with_casing("aa", "aa")]
    #[case::ascii_with_casing("aa", "aA")]
    #[case::ascii_with_casing("aa", "Aa")]
    #[case::ascii_with_casing("aa", "AA")]
    #[case::ascii_with_casing("z", "z")]
    #[case::ascii_with_casing("z", "Z")]
    #[case::cjk("愛", "愛")]
    #[case::cjk("グロブ", "グロブ")]
    fn case_folded_eq_eq(#[case] lhs: &str, #[case] rhs: &str) {
        harness::assert_case_folded_eq_eq(lhs, rhs, true);
    }

    #[rstest]
    #[case::whitespace("", " ")]
    #[case::whitespace(" ", "\t")]
    #[case::whitespace(" ", "  ")]
    #[case::length("a", "aa")]
    #[case::ascii_with_no_casing("0", "1")]
    #[case::ascii_with_casing("a", "b")]
    #[case::ascii_with_casing("a", "B")]
    #[case::cjk("金", "銀")]
    #[case::cjk("もー", "もぉ")]
    fn case_folded_eq_not_eq(#[case] lhs: &str, #[case] rhs: &str) {
        harness::assert_case_folded_eq_eq(lhs, rhs, false);
    }
}
