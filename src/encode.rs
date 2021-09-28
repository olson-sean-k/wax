use const_format::formatcp;
use itertools::{Itertools as _, Position};
use regex::bytes::Regex;
use std::borrow::{Borrow, Cow};

use crate::token::Token;
use crate::PositionExt as _;

#[cfg(windows)]
const SEPARATOR_EXPRESSION: &str = "(?:/|\\\\)";
// NOTE: Not only is this specific to Unix, but each supported platform must
//       specify its separator expression, especially when more than one
//       separator is supported. It is not possible to use `MAIN_SEPARATOR` here
//       for platforms with only one separator, as it is not possible to
//       properly escape the separator; at the time of writing, `const_format`
//       does not support hexadecimal formatting with a fixed width and it is
//       possible that the separator is a control character.
#[cfg(not(windows))]
const SEPARATOR_EXPRESSION: &str = "/";

macro_rules! sepexpr {
    ($fmt: expr) => {
        formatcp!($fmt, SEPARATOR_EXPRESSION)
    };
}

#[derive(Clone, Copy, Debug)]
enum Grouping {
    Capture,
    NonCapture,
}

impl Grouping {
    pub fn push_str(&self, pattern: &mut String, encoding: &str) {
        self.push_with(pattern, || encoding.into());
    }

    pub fn push_with<'p, F>(&self, pattern: &mut String, f: F)
    where
        F: Fn() -> Cow<'p, str>,
    {
        match self {
            Grouping::Capture => pattern.push('('),
            Grouping::NonCapture => pattern.push_str("(?:"),
        }
        pattern.push_str(f().as_ref());
        pattern.push(')');
    }
}

pub fn compile<'t, T>(tokens: impl IntoIterator<Item = T>) -> Regex
where
    T: Borrow<Token<'t>>,
{
    let mut pattern = String::new();
    pattern.push_str("(?-u)^");
    encode(Grouping::Capture, None, &mut pattern, tokens);
    pattern.push('$');
    Regex::new(&pattern).expect("glob compilation failed")
}

fn encode<'t, T>(
    grouping: Grouping,
    subposition: Option<Position<()>>,
    pattern: &mut String,
    tokens: impl IntoIterator<Item = T>,
) where
    T: Borrow<Token<'t>>,
{
    use itertools::Position::{First, Last, Middle, Only};

    use crate::token::Archetype::{Character, Range};
    use crate::token::Evaluation::{Eager, Lazy};
    use crate::token::TokenKind::{Alternative, Class, Literal, Separator, Wildcard};
    use crate::token::Wildcard::{One, Tree, ZeroOrMore};

    fn encode_intermediate_tree(grouping: Grouping, pattern: &mut String) {
        pattern.push_str(sepexpr!("(?:{0}|{0}"));
        grouping.push_str(pattern, sepexpr!(".*{0}"));
        pattern.push(')');
    }

    // TODO: Use `Grouping` everywhere a group is encoded. For invariant groups
    //       that ignore `grouping`, construct a local `Grouping` instead.
    for token in tokens.into_iter().with_position() {
        match token.interior_borrow().map(Token::kind).as_tuple() {
            (_, Literal(literal)) => {
                // TODO: Only encode changes to casing flags.
                // TODO: Should Unicode support also be toggled by casing flags?
                if literal.is_case_insensitive() {
                    pattern.push_str("(?iu)");
                } else {
                    pattern.push_str("(?-iu)");
                }
                for &byte in literal.text().as_bytes() {
                    pattern.push_str(&escape(byte));
                }
            }
            (_, Separator) => pattern.push_str(SEPARATOR_EXPRESSION),
            (position, Alternative(alternative)) => {
                let encodings: Vec<_> = alternative
                    .branches()
                    .iter()
                    .map(|tokens| {
                        let mut pattern = String::new();
                        pattern.push_str("(?:");
                        encode(
                            Grouping::NonCapture,
                            subposition.or(Some(position)),
                            &mut pattern,
                            tokens.iter(),
                        );
                        pattern.push(')');
                        pattern
                    })
                    .collect();
                grouping.push_str(pattern, &encodings.join("|"));
            }
            (
                _,
                Class {
                    is_negated,
                    archetypes,
                },
            ) => {
                grouping.push_with(pattern, || {
                    let mut pattern = String::new();
                    pattern.push('[');
                    if *is_negated {
                        pattern.push('^');
                    }
                    for archetype in archetypes {
                        match archetype {
                            Character(literal) => {
                                let mut bytes = [0u8; 4];
                                literal.encode_utf8(&mut bytes);
                                for &byte in &bytes {
                                    pattern.push_str(&escape(byte))
                                }
                            }
                            Range(left, right) => {
                                pattern.push(*left);
                                pattern.push('-');
                                pattern.push(*right);
                            }
                        }
                    }
                    pattern.push_str(sepexpr!("&&[^{0}]]"));
                    pattern.into()
                });
            }
            (_, Wildcard(One)) => grouping.push_str(pattern, sepexpr!("[^{0}]")),
            (_, Wildcard(ZeroOrMore(Eager))) => grouping.push_str(pattern, sepexpr!("[^{0}]*")),
            (_, Wildcard(ZeroOrMore(Lazy))) => grouping.push_str(pattern, sepexpr!("[^{0}]*?")),
            (First(_), Wildcard(Tree { is_rooted })) => match subposition {
                Some(Middle(_)) | Some(Last(_)) => {
                    encode_intermediate_tree(grouping, pattern);
                }
                _ => {
                    if *is_rooted {
                        grouping.push_str(pattern, sepexpr!("{0}.*{0}?"));
                    } else {
                        pattern.push_str(sepexpr!("(?:{0}?|"));
                        grouping.push_str(pattern, sepexpr!(".*{0}"));
                        pattern.push(')');
                    }
                }
            },
            (Middle(_), Wildcard(Tree { .. })) => {
                encode_intermediate_tree(grouping, pattern);
            }
            (Last(_), Wildcard(Tree { .. })) => match subposition {
                Some(First(_)) | Some(Middle(_)) => {
                    encode_intermediate_tree(grouping, pattern);
                }
                _ => {
                    pattern.push_str(sepexpr!("(?:{0}?|{0}"));
                    grouping.push_str(pattern, ".*");
                    pattern.push(')');
                }
            },
            (Only(_), Wildcard(Tree { .. })) => grouping.push_str(pattern, ".*"),
        }
    }
}

fn escape(byte: u8) -> String {
    const ASCII_TERMINATOR: u8 = 0x7F;

    if byte <= ASCII_TERMINATOR {
        regex::escape(&(byte as char).to_string())
    } else {
        format!("\\x{:02x}", byte)
    }
}
