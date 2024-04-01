#[cfg(feature = "miette")]
use miette::Diagnostic;
use regex_syntax::hir::{self, Hir};
use std::borrow::Borrow;
#[cfg(feature = "miette")]
use std::fmt::Display;
use thiserror::Error;

pub use regex_automata::meta::Regex;

use crate::token::walk::{Fold, FoldPosition, Forward};
use crate::token::{self, Archetype, BranchKind, ConcatenationTree, LeafKind};
use crate::IteratorExt as _;

trait IntoHir {
    fn into_hir(self) -> Hir;
}

impl IntoHir for hir::ClassUnicode {
    fn into_hir(self) -> Hir {
        Hir::class(hir::Class::Unicode(self))
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

fn case_folded_literal(text: impl AsRef<str>) -> Hir {
    Hir::concat(
        text.as_ref()
            .chars()
            .map(|point| hir::ClassUnicode::new([hir::ClassUnicodeRange::new(point, point)]))
            .map(|mut hir| {
                let _ = hir.try_case_fold_simple();
                hir
            })
            .map(hir::Class::Unicode)
            .map(Hir::class)
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

pub fn compile<'t, T>(tree: impl Borrow<T>) -> Result<Regex, CompileError>
where
    T: ConcatenationTree<'t>,
{
    #[derive(Debug, Default)]
    struct Compile;

    impl<'t, A> Fold<'t, A> for Compile {
        type Sequencer = Forward;
        type Term = Hir;

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
                Alternation(_) => Hir::alternation(terms),
                Concatenation(_) => Hir::concat(terms),
                Repetition(ref repetition) => {
                    let (min, max) = repetition.bound_specification();
                    Hir::repetition(hir::Repetition {
                        min: u32::try_from(min).unwrap_or(u32::MAX),
                        max: max.map(u32::try_from).transpose().unwrap_or(Some(u32::MAX)),
                        greedy: true,
                        sub: Box::new(Hir::concat(terms)),
                    })
                },
            })
        }

        fn finalize(&mut self, _branch: &BranchKind<'t, A>, term: Self::Term) -> Self::Term {
            term
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
                        Hir::literal(literal.text().as_bytes())
                    }
                },
                Separator(_) => {
                    if adjacency.right.is_some() {
                        self::separator().into_hir()
                    }
                    else {
                        Hir::alternation(vec![
                            self::separator().into_hir(),
                            Hir::look(hir::Look::End),
                        ])
                    }
                },
                Wildcard(ref wildcard) => match wildcard {
                    One => Hir::class(hir::Class::Unicode(self::separator().negated())),
                    Tree { ref has_root } => Hir::alternation(vec![
                        Hir::concat(vec![
                            if *has_root {
                                self::separator().into_hir()
                            }
                            else {
                                Hir::empty()
                            },
                            Hir::repetition(hir::Repetition {
                                min: 0,
                                max: None,
                                greedy: true,
                                sub: Box::new(Hir::dot(hir::Dot::AnyChar)),
                            }),
                            Hir::alternation(vec![
                                self::separator().into_hir(),
                                Hir::look(hir::Look::End),
                            ]),
                        ]),
                        self::separator().into_hir(),
                        Hir::empty(),
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
                    //       `{a/<x:1,>,b<x>}`.
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
                    ZeroOrMore { ref is_greedy } => Hir::repetition(hir::Repetition {
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
    let hir = Hir::concat(
        Some(Hir::look(hir::Look::Start))
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
                        let hir = token.fold_with_adjacent(Compile).unwrap_or_else(Hir::empty);
                        if token.into_item().is_capturing() {
                            capture_group_index = capture_group_index
                                .checked_add(1)
                                .expect("overflow in capture group index");
                            Hir::capture(hir::Capture {
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
            .chain(Some(Hir::look(hir::Look::End)))
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
