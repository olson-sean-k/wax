use itertools::Itertools as _;
use smallvec::{smallvec, SmallVec};
use std::borrow::Cow;
use std::path::{PathBuf, MAIN_SEPARATOR};

use crate::rule;
use crate::GlobError;

#[derive(Clone, Debug)]
pub struct Alternative<'t>(pub Vec<Vec<Token<'t>>>);

impl<'t> Alternative<'t> {
    pub fn into_owned(self) -> Alternative<'static> {
        Alternative(
            self.0
                .into_iter()
                .map(|tokens| tokens.into_iter().map(|token| token.into_owned()).collect())
                .collect(),
        )
    }

    pub fn branches(&self) -> &Vec<Vec<Token<'t>>> {
        &self.0
    }

    pub fn has_component_boundary(&self) -> bool {
        self.0.iter().any(|tokens| {
            tokens.iter().any(|token| match token {
                Token::Alternative(ref alternative) => alternative.has_component_boundary(),
                _ => token.is_component_boundary(),
            })
        })
    }
}

impl<'t> From<Vec<Vec<Token<'t>>>> for Alternative<'t> {
    fn from(alternatives: Vec<Vec<Token<'t>>>) -> Self {
        Alternative(alternatives)
    }
}

#[derive(Clone, Copy, Debug)]
pub enum Archetype {
    Character(char),
    Range(char, char),
}

impl From<char> for Archetype {
    fn from(literal: char) -> Archetype {
        Archetype::Character(literal)
    }
}

impl From<(char, char)> for Archetype {
    fn from(range: (char, char)) -> Archetype {
        Archetype::Range(range.0, range.1)
    }
}

#[derive(Clone, Copy, Debug)]
pub enum Evaluation {
    Eager,
    Lazy,
}

#[derive(Clone, Debug)]
pub enum Wildcard {
    One,
    ZeroOrMore(Evaluation),
    Tree { is_rooted: bool },
}

#[derive(Clone, Debug)]
pub enum Token<'t> {
    Alternative(Alternative<'t>),
    Class {
        is_negated: bool,
        archetypes: Vec<Archetype>,
    },
    Literal(Cow<'t, str>),
    Separator,
    Wildcard(Wildcard),
}

impl<'t> Token<'t> {
    pub fn into_owned(self) -> Token<'static> {
        match self {
            Token::Alternative(alternative) => alternative.into_owned().into(),
            Token::Class {
                is_negated,
                archetypes,
            } => Token::Class {
                is_negated,
                archetypes,
            },
            Token::Literal(literal) => literal.into_owned().into(),
            Token::Separator => Token::Separator,
            Token::Wildcard(wildcard) => Token::Wildcard(wildcard),
        }
    }

    pub fn is_component_boundary(&self) -> bool {
        matches!(
            self,
            Token::Separator | Token::Wildcard(Wildcard::Tree { .. })
        )
    }
}

impl<'t> From<Alternative<'t>> for Token<'t> {
    fn from(alternative: Alternative<'t>) -> Self {
        Token::Alternative(alternative)
    }
}

impl<'t> From<&'t str> for Token<'t> {
    fn from(literal: &'t str) -> Self {
        Token::Literal(literal.into())
    }
}

impl From<String> for Token<'static> {
    fn from(literal: String) -> Self {
        Token::Literal(literal.into())
    }
}

impl From<Wildcard> for Token<'static> {
    fn from(wildcard: Wildcard) -> Self {
        Token::Wildcard(wildcard)
    }
}

#[derive(Clone, Debug)]
pub struct Component<'t>(SmallVec<[&'t Token<'t>; 4]>);

impl<'t> Component<'t> {
    pub fn tokens(&self) -> &[&'t Token<'t>] {
        self.0.as_ref()
    }

    pub fn literal(&self) -> Option<Cow<'t, str>> {
        // This predicate is more easily expressed with `all`, but `any` is used
        // here, because it returns `false` for empty iterators and in that case
        // this function should return `None`.
        (!self
            .tokens()
            .iter()
            .any(|token| !matches!(token, Token::Literal(_))))
        .then(|| {
            if self.tokens().len() == 1 {
                match self.tokens().first().unwrap() {
                    Token::Literal(ref literal) => literal.clone(),
                    _ => unreachable!(), // See predicate above.
                }
            } else {
                self.tokens()
                    .iter()
                    .map(|token| match token {
                        Token::Literal(ref literal) => literal,
                        _ => unreachable!(), // See predicate above.
                    })
                    .join("")
                    .into()
            }
        })
    }
}

pub fn components<'t, I>(tokens: I) -> impl Iterator<Item = Component<'t>>
where
    I: IntoIterator<Item = &'t Token<'t>>,
    I::IntoIter: Clone,
{
    tokens.into_iter().batching(|tokens| {
        let mut first = tokens.next();
        while matches!(first, Some(Token::Separator)) {
            first = tokens.next();
        }
        first.map(|first| match first {
            Token::Wildcard(Wildcard::Tree { .. }) => Component(smallvec![first]),
            _ => Component(
                Some(first)
                    .into_iter()
                    .chain(tokens.take_while_ref(|token| !token.is_component_boundary()))
                    .collect(),
            ),
        })
    })
}

pub fn literal_path_prefix<'t, I>(tokens: I) -> Option<PathBuf>
where
    I: IntoIterator<Item = &'t Token<'t>>,
    I::IntoIter: Clone,
{
    use crate::token::Token::{Separator, Wildcard};
    use crate::token::Wildcard::Tree;

    let mut tokens = tokens.into_iter().peekable();
    let mut prefix = String::new();
    if let Some(Separator | Wildcard(Tree { is_rooted: true })) = tokens.peek() {
        // Include any rooting component boundary at the beginning of the token
        // sequence.
        prefix.push(MAIN_SEPARATOR);
    }
    // TODO: Replace `map`, `take_while`, and `flatten` with `map_while`
    //       when it stabilizes.
    prefix.push_str(
        &components(tokens)
            .map(|component| component.literal())
            .take_while(|literal| literal.is_some())
            .flatten()
            .join(&MAIN_SEPARATOR.to_string()),
    );
    if prefix.is_empty() {
        None
    } else {
        Some(prefix.into())
    }
}

// NOTE: Both forward and back slashes are disallowed in non-separator tokens
//       like literals and character classes. This means escaping back slashes
//       is not possible (despite common conventions). This avoids non-separator
//       tokens parsing over directory boundaries (in particular on Windows).
pub fn parse(text: &str) -> Result<Vec<Token<'_>>, GlobError> {
    use nom::bytes::complete as bytes;
    use nom::character::complete as character;
    use nom::error::ParseError;
    use nom::{branch, combinator, multi, sequence, IResult, Parser};

    fn no_adjacent_tree<'i, O, E, F>(parser: F) -> impl FnMut(&'i str) -> IResult<&'i str, O, E>
    where
        E: ParseError<&'i str>,
        F: Parser<&'i str, O, E>,
    {
        sequence::delimited(
            combinator::peek(combinator::not(bytes::tag("**"))),
            parser,
            combinator::peek(combinator::not(bytes::tag("**"))),
        )
    }

    fn literal<'i, E>(input: &'i str) -> IResult<&'i str, Token, E>
    where
        E: ParseError<&'i str>,
    {
        combinator::map(
            combinator::verify(
                // NOTE: Character classes, which accept arbitrary characters,
                //       can be used to escape metacharacters like `*`, `?`,
                //       etc. For example, to escape `*`, either `\*` or `[*]`
                //       can be used.
                bytes::escaped_transform(
                    no_adjacent_tree(bytes::is_not("/?*$[]{},\\")),
                    '\\',
                    branch::alt((
                        combinator::value("?", bytes::tag("?")),
                        combinator::value("*", bytes::tag("*")),
                        combinator::value("$", bytes::tag("$")),
                        combinator::value("[", bytes::tag("[")),
                        combinator::value("]", bytes::tag("]")),
                        combinator::value("{", bytes::tag("{")),
                        combinator::value("}", bytes::tag("}")),
                        combinator::value(",", bytes::tag(",")),
                    )),
                ),
                |text: &str| !text.is_empty(),
            ),
            Token::from,
        )(input)
    }

    fn separator<'i, E>(input: &'i str) -> IResult<&'i str, Token, E>
    where
        E: ParseError<&'i str>,
    {
        combinator::value(Token::Separator, bytes::tag("/"))(input)
    }

    fn wildcard<'i, E>(input: &'i str) -> IResult<&'i str, Token, E>
    where
        E: ParseError<&'i str>,
    {
        branch::alt((
            combinator::map(no_adjacent_tree(bytes::tag("?")), |_| {
                Token::from(Wildcard::One)
            }),
            combinator::map(
                sequence::tuple((
                    branch::alt((bytes::tag("/"), bytes::tag(""))),
                    sequence::terminated(
                        bytes::tag("**"),
                        branch::alt((
                            bytes::tag("/"),
                            combinator::eof,
                            // In alternatives, tree tokens may be terminated by
                            // commas `,` or closing curly braces `}`. These
                            // delimiting tags must be consumed by their respective
                            // parsers, so they are peeked.
                            combinator::peek(branch::alt((bytes::tag(","), bytes::tag("}")))),
                        )),
                    ),
                )),
                |(root, _): (&str, _)| {
                    Wildcard::Tree {
                        is_rooted: !root.is_empty(),
                    }
                    .into()
                },
            ),
            combinator::map(
                sequence::terminated(
                    bytes::tag("*"),
                    branch::alt((combinator::peek(bytes::is_not("*$")), combinator::eof)),
                ),
                |_| Wildcard::ZeroOrMore(Evaluation::Eager).into(),
            ),
            combinator::map(
                sequence::terminated(
                    bytes::tag("$"),
                    branch::alt((combinator::peek(bytes::is_not("*$")), combinator::eof)),
                ),
                |_| Wildcard::ZeroOrMore(Evaluation::Lazy).into(),
            ),
        ))(input)
    }

    fn class<'i, E>(input: &'i str) -> IResult<&'i str, Token, E>
    where
        E: ParseError<&'i str>,
    {
        fn archetypes<'i, E>(input: &'i str) -> IResult<&'i str, Vec<Archetype>, E>
        where
            E: ParseError<&'i str>,
        {
            let escaped_character = |input| {
                branch::alt((
                    character::none_of("[]-\\"),
                    branch::alt((
                        combinator::value('[', bytes::tag("\\[")),
                        combinator::value(']', bytes::tag("\\]")),
                        combinator::value('-', bytes::tag("\\-")),
                    )),
                ))(input)
            };

            multi::many1(branch::alt((
                combinator::map(
                    sequence::separated_pair(escaped_character, bytes::tag("-"), escaped_character),
                    Archetype::from,
                ),
                combinator::map(escaped_character, Archetype::from),
            )))(input)
        }

        combinator::map(
            sequence::delimited(
                bytes::tag("["),
                sequence::tuple((combinator::opt(bytes::tag("!")), archetypes)),
                bytes::tag("]"),
            ),
            |(negation, archetypes)| Token::Class {
                is_negated: negation.is_some(),
                archetypes,
            },
        )(input)
    }

    fn alternative<'i, E>(input: &'i str) -> IResult<&'i str, Token, E>
    where
        E: ParseError<&'i str>,
    {
        sequence::delimited(
            bytes::tag("{"),
            combinator::map(
                multi::separated_list1(bytes::tag(","), glob),
                |alternatives| Alternative::from(alternatives).into(),
            ),
            bytes::tag("}"),
        )(input)
    }

    fn glob<'i, E>(input: &'i str) -> IResult<&'i str, Vec<Token>, E>
    where
        E: ParseError<&'i str>,
    {
        multi::many1(branch::alt((
            literal,
            alternative,
            wildcard,
            class,
            separator,
        )))(input)
    }

    let tokens = combinator::all_consuming(glob)(text)
        .map(|(_, tokens)| tokens)
        .map_err(GlobError::from)?;
    rule::check(tokens.iter())?;
    Ok(tokens)
}

// NOTE: Some optimization cases cannot occur using `token::parse` alone, but
//       all optimizations assume that the token sequence is accepted by
//       `rule::check`; there are no optimizations for sequences that are
//       rejected by `rule::check`.
pub fn optimize<'t>(
    tokens: impl IntoIterator<Item = Token<'t>>,
) -> impl Iterator<Item = Token<'t>> {
    tokens
        .into_iter()
        // Discard empty literal tokens.
        .filter(|token| match &token {
            Token::Literal(ref literal) => !literal.is_empty(),
            _ => true,
        })
        // Coalesce adjacent literal tokens into a single concatenated literal
        // token.
        .coalesce(|left, right| match (&left, &right) {
            (Token::Literal(ref left), Token::Literal(ref right)) => {
                Ok(Token::Literal(format!("{}{}", left, right).into()))
            }
            _ => Err((left, right)),
        })
}

#[cfg(test)]
mod tests {
    use std::path::Path;

    use crate::token;

    #[test]
    fn literal_path_prefix() {
        assert_eq!(
            token::literal_path_prefix(token::parse("/a/b").unwrap().iter()).unwrap(),
            Path::new("/a/b"),
        );
        assert_eq!(
            token::literal_path_prefix(token::parse("a/b").unwrap().iter()).unwrap(),
            Path::new("a/b"),
        );
        assert_eq!(
            token::literal_path_prefix(token::parse("a/*").unwrap().iter()).unwrap(),
            Path::new("a/"),
        );
        assert_eq!(
            token::literal_path_prefix(token::parse("a/*b").unwrap().iter()).unwrap(),
            Path::new("a/"),
        );
        assert_eq!(
            token::literal_path_prefix(token::parse("a/b*").unwrap().iter()).unwrap(),
            Path::new("a/"),
        );
        assert_eq!(
            token::literal_path_prefix(token::parse("a/b/*/c").unwrap().iter()).unwrap(),
            Path::new("a/b/"),
        );

        assert!(token::literal_path_prefix(token::parse("**").unwrap().iter()).is_none());
        assert!(token::literal_path_prefix(token::parse("a*").unwrap().iter()).is_none());
        assert!(token::literal_path_prefix(token::parse("*/b").unwrap().iter()).is_none());
        assert!(token::literal_path_prefix(token::parse("a?/b").unwrap().iter()).is_none());
    }
}
