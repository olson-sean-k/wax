use const_format::formatcp;
use itertools::{Itertools as _, Position};
use regex::Regex;
use std::borrow::{Borrow, Cow};

use crate::token::Token;
use crate::PositionExt as _;

#[cfg(windows)]
const SEPARATOR_CLASS_EXPRESSION: &str = "/\\\\";
#[cfg(unix)]
const SEPARATOR_CLASS_EXPRESSION: &str = "/";

// This only encodes the platform's main separator, so any additional separators
// will be missed. It may be better to have explicit platform support and invoke
// `compile_error!` on unsupported platforms, as this could cause very aberrant
// behavior. Then again, it seems that platforms using more than one separator
// are rare. GS/OS, OS/2, and Windows are likely the best known examples and of
// those only Windows is a supported Rust target at the time of writing (and is
// already supported by Wax).
#[cfg(not(any(windows, unix)))]
const SEPARATOR_CLASS_EXPRESSION: &str = main_separator_class_expression();

#[cfg(not(any(windows, unix)))]
const fn main_separator_class_expression() -> &'static str {
    use std::path::MAIN_SEPARATOR;

    // TODO: This is based upon `regex_syntax::is_meta_character`, but that
    //       function is not `const`. Perhaps that can be changed upstream.
    const fn escape(x: char) -> &'static str {
        match x {
            '\\' | '.' | '+' | '*' | '?' | '(' | ')' | '|' | '[' | ']' | '{' | '}' | '^' | '$'
            | '#' | '&' | '-' | '~' => "\\",
            _ => "",
        }
    }

    formatcp!("{0}{1}", escape(MAIN_SEPARATOR), MAIN_SEPARATOR)
}

macro_rules! sepexpr {
    ($fmt: expr) => {
        formatcp!($fmt, formatcp!("[{0}]", SEPARATOR_CLASS_EXPRESSION))
    };
}

macro_rules! nsepexpr {
    ($fmt: expr) => {
        formatcp!($fmt, formatcp!("[^{0}]", SEPARATOR_CLASS_EXPRESSION))
    };
}

trait Escaped {
    fn escaped(&self) -> String;
}

impl Escaped for char {
    fn escaped(&self) -> String {
        regex::escape(&self.to_string())
    }
}

impl Escaped for str {
    fn escaped(&self) -> String {
        regex::escape(self)
    }
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
    pattern.push('^');
    encode(Grouping::Capture, None, &mut pattern, tokens);
    pattern.push('$');
    Regex::new(&pattern).expect("glob compilation failed")
}

fn encode<'t, T>(
    grouping: Grouping,
    superposition: Option<Position<()>>,
    pattern: &mut String,
    tokens: impl IntoIterator<Item = T>,
) where
    T: Borrow<Token<'t>>,
{
    use itertools::Position::{First, Last, Middle, Only};

    use crate::token::Archetype::{Character, Range};
    use crate::token::Evaluation::{Eager, Lazy};
    use crate::token::TokenKind::{Alternative, Class, Literal, Repetition, Separator, Wildcard};
    use crate::token::Wildcard::{One, Tree, ZeroOrMore};

    // This assumes that `NUL` is not allowed in paths and matches nothing.
    const NULL_CHARACTER_CLASS: &str = nsepexpr!("[\\x00&&{0}]");

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
                    pattern.push_str("(?i)");
                }
                else {
                    pattern.push_str("(?-i)");
                }
                pattern.push_str(&literal.text().escaped());
            }
            (_, Separator) => pattern.push_str(sepexpr!("{0}")),
            (position, Alternative(alternative)) => {
                let encodings: Vec<_> = alternative
                    .branches()
                    .iter()
                    .map(|tokens| {
                        let mut pattern = String::new();
                        pattern.push_str("(?:");
                        encode(
                            Grouping::NonCapture,
                            superposition.or(Some(position)),
                            &mut pattern,
                            tokens.iter(),
                        );
                        pattern.push(')');
                        pattern
                    })
                    .collect();
                grouping.push_str(pattern, &encodings.join("|"));
            }
            (position, Repetition(repetition)) => {
                let encoding = {
                    let (lower, upper) = repetition.bounds();
                    let mut pattern = String::new();
                    pattern.push_str("(?:");
                    encode(
                        Grouping::NonCapture,
                        superposition.or(Some(position)),
                        &mut pattern,
                        repetition.tokens().iter(),
                    );
                    pattern.push_str(&if let Some(upper) = upper {
                        format!("){{{},{}}}", lower, upper)
                    }
                    else {
                        format!("){{{},}}", lower)
                    });
                    pattern
                };
                grouping.push_str(pattern, &encoding);
            }
            (_, Class(class)) => {
                grouping.push_with(pattern, || {
                    let mut pattern = String::new();
                    pattern.push('[');
                    if class.is_negated() {
                        pattern.push('^');
                    }
                    for archetype in class.archetypes() {
                        match archetype {
                            Character(literal) => pattern.push_str(&literal.escaped()),
                            Range(left, right) => {
                                pattern.push_str(&left.escaped());
                                pattern.push('-');
                                pattern.push_str(&right.escaped());
                            }
                        }
                    }
                    pattern.push_str(nsepexpr!("&&{0}]"));
                    // Compile the character class sub-expression. This may fail
                    // if the subtraction of the separator pattern yields an
                    // empty character class (meaning that the glob expression
                    // matches only separator characters on the target
                    // platform). If compilation fails, then use the null
                    // character class, which matches nothing on supported
                    // platforms.
                    if Regex::new(&pattern).is_ok() {
                        pattern.into()
                    }
                    else {
                        NULL_CHARACTER_CLASS.into()
                    }
                });
            }
            (_, Wildcard(One)) => grouping.push_str(pattern, nsepexpr!("{0}")),
            (_, Wildcard(ZeroOrMore(Eager))) => grouping.push_str(pattern, nsepexpr!("{0}*")),
            (_, Wildcard(ZeroOrMore(Lazy))) => grouping.push_str(pattern, nsepexpr!("{0}*?")),
            (First(_), Wildcard(Tree { is_rooted })) => match superposition {
                Some(Middle(_)) | Some(Last(_)) => {
                    encode_intermediate_tree(grouping, pattern);
                }
                _ => {
                    if *is_rooted {
                        grouping.push_str(pattern, sepexpr!("{0}.*{0}?"));
                    }
                    else {
                        pattern.push_str(sepexpr!("(?:{0}?|"));
                        grouping.push_str(pattern, sepexpr!(".*{0}"));
                        pattern.push(')');
                    }
                }
            },
            (Middle(_), Wildcard(Tree { .. })) => {
                encode_intermediate_tree(grouping, pattern);
            }
            (Last(_), Wildcard(Tree { .. })) => match superposition {
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