#[cfg(feature = "miette")]
use miette::Diagnostic;
use regex_syntax::hir::{self, Hir};
use std::borrow::Borrow;
#[cfg(feature = "miette")]
use std::fmt::Display;
use thiserror::Error;

pub use regex_automata::meta::Regex;

use crate::token::walk::{Fold, Forward};
use crate::token::{self, Archetype, BranchKind, ConcatenationTree, LeafKind};

trait IntoHir {
    fn into_hir(self) -> Hir;
}

impl IntoHir for hir::ClassUnicode {
    fn into_hir(self) -> Hir {
        Hir::class(hir::Class::Unicode(self))
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

// TODO: The implementation of this function depends on platform/OS.
fn separator() -> hir::ClassUnicode {
    hir::ClassUnicode::new([hir::ClassUnicodeRange::new('/', '/')])
}

fn not_separator() -> hir::ClassUnicode {
    let mut hir = separator();
    hir.negate();
    hir
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

        fn term(&mut self, leaf: &LeafKind<'t>) -> Self::Term {
            use token::Wildcard::{One, Tree, ZeroOrMore};
            use Archetype::{Character, Range};
            use LeafKind::{Class, Literal, Separator, Wildcard};

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
                // TODO: Separators should probably also match the end of text when they are at the
                //       end of a glob expression. This may not be possible in a fold with simple
                //       terms though, since that positional information isn't available until
                //       reaching the root of the token tree.
                Separator(_) => self::separator().into_hir(),
                Wildcard(ref wildcard) => match wildcard {
                    One => Hir::class(hir::Class::Unicode(self::not_separator())),
                    Tree { has_root } => Hir::alternation(vec![
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
                    // TODO: Zero or more wildcards should match **one** or more if they comprise
                    //       the entirety of a component, such as in `a/*/b`. This may not be
                    //       possible in a fold with simple terms though, since adjacency
                    //       information isn't available until reaching the root of the token tree.
                    ZeroOrMore(ref evaluation) => Hir::repetition(hir::Repetition {
                        min: 0,
                        max: None,
                        greedy: evaluation.is_eager(),
                        sub: Box::new(self::not_separator().into_hir()),
                    }),
                },
            }
        }
    }

    let mut capture_group_index = 1u32;
    let hir = Hir::concat(
        Some(Hir::look(hir::Look::Start))
            .into_iter()
            .chain(tree.borrow().concatenation().iter().map(|token| {
                let hir = token.fold(Compile::default()).unwrap_or_else(Hir::empty);
                if token.is_capturing() {
                    let index = capture_group_index;
                    capture_group_index = capture_group_index
                        .checked_add(1)
                        .expect("overflow determining capture group index");
                    // TODO: Some tokens require different capture topology depending on their
                    //       position in the concatenation. Position information is trivially
                    //       available here, but a more complex term (likely a closure of some
                    //       kind) is needed to integrate the capture HIR into its tree. This
                    //       namely applies to tree wildcards, which should not always capture the
                    //       entirety of the text that they match.
                    Hir::capture(hir::Capture {
                        index,
                        name: None,
                        sub: Box::new(hir),
                    })
                }
                else {
                    hir
                }
            }))
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
