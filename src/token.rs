use itertools::Itertools as _;
#[cfg(feature = "diagnostics")]
use miette::{self, Diagnostic, SourceSpan};
use nom::error::ErrorKind;
use smallvec::{smallvec, SmallVec};
use std::borrow::Cow;
use std::mem;
use std::ops::Deref;
use std::path::{PathBuf, MAIN_SEPARATOR};
use thiserror::Error;

use crate::fragment::Stateful;
#[cfg(feature = "diagnostics")]
use crate::fragment::{self, Locate};
use crate::rule;
use crate::{GlobError, StrExt as _, PATHS_ARE_CASE_INSENSITIVE};

#[cfg(feature = "diagnostics")]
pub type Annotation = SourceSpan;
#[cfg(not(feature = "diagnostics"))]
pub type Annotation = ();

#[cfg(feature = "diagnostics")]
type Fragment<'i> = Locate<'i, str>;
#[cfg(not(feature = "diagnostics"))]
type Fragment<'i> = &'i str;

type ParserInput<'i> = Stateful<Fragment<'i>, FlagState>;

type NomError<'t> = nom::Err<nom::error::Error<ParserInput<'t>>>;

#[derive(Debug, Error)]
#[error("failed to parse glob expression: {kind:?}")]
#[cfg_attr(feature = "diagnostics", derive(Diagnostic))]
#[cfg_attr(feature = "diagnostics", diagnostic(code = "glob::parse"))]
pub struct ParseError<'t> {
    expression: Cow<'t, str>,
    kind: ErrorKind,
    #[cfg(feature = "diagnostics")]
    #[snippet(expression, message("in this expression"))]
    snippet: SourceSpan,
    #[cfg(feature = "diagnostics")]
    #[highlight(snippet, label("here"))]
    error: SourceSpan,
}

impl<'t> ParseError<'t> {
    fn new(expression: &'t str, error: NomError<'t>) -> Self {
        match error {
            NomError::Incomplete(_) => {
                panic!("unexpected parse error: incomplete input")
            }
            #[cfg(feature = "diagnostics")]
            NomError::Error(error) | NomError::Failure(error) => {
                use nom::Offset;

                let input = error.input.as_ref().as_ref();
                ParseError {
                    expression: expression.into(),
                    kind: error.code,
                    snippet: (0, expression.len()).into(),
                    error: (Offset::offset(&expression, &input), 0).into(),
                }
            }
            #[cfg(not(feature = "diagnostics"))]
            NomError::Error(error) | NomError::Failure(error) => ParseError {
                expression: expression.into(),
                kind: error.code,
            },
        }
    }

    pub fn into_owned(self) -> ParseError<'static> {
        let ParseError {
            expression,
            kind,
            #[cfg(feature = "diagnostics")]
            snippet,
            #[cfg(feature = "diagnostics")]
            error,
        } = self;
        ParseError {
            expression: expression.into_owned().into(),
            kind,
            #[cfg(feature = "diagnostics")]
            snippet,
            #[cfg(feature = "diagnostics")]
            error,
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct FlagState {
    is_case_insensitive: bool,
}

impl Default for FlagState {
    fn default() -> Self {
        FlagState {
            is_case_insensitive: PATHS_ARE_CASE_INSENSITIVE,
        }
    }
}

#[derive(Clone, Copy, Debug)]
enum FlagToggle {
    CaseInsensitive(bool),
}

#[derive(Clone, Debug)]
pub struct Alternative<'t, A = ()>(Vec<Vec<Token<'t, A>>>);

impl<'t, A> Alternative<'t, A> {
    pub fn into_owned(self) -> Alternative<'static, A> {
        Alternative(
            self.0
                .into_iter()
                .map(|tokens| tokens.into_iter().map(Token::into_owned).collect())
                .collect(),
        )
    }

    #[cfg(feature = "diagnostics")]
    pub fn unannotate(self) -> Alternative<'t, ()> {
        Alternative(
            self.0
                .into_iter()
                .map(|tokens| tokens.into_iter().map(Token::unannotate).collect())
                .collect(),
        )
    }

    pub fn branches(&self) -> &Vec<Vec<Token<'t, A>>> {
        &self.0
    }

    pub fn has_component_boundary(&self) -> bool {
        self.0.iter().any(|tokens| {
            tokens.iter().any(|token| match token.kind() {
                TokenKind::Alternative(ref alternative) => alternative.has_component_boundary(),
                _ => token.is_component_boundary(),
            })
        })
    }
}

impl<'t, A> From<Vec<Vec<Token<'t, A>>>> for Alternative<'t, A> {
    fn from(alternatives: Vec<Vec<Token<'t, A>>>) -> Self {
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

#[derive(Clone, Debug)]
pub struct Literal<'t> {
    text: Cow<'t, str>,
    is_case_insensitive: bool,
}

impl<'t> Literal<'t> {
    pub fn text(&self) -> &str {
        self.text.as_ref()
    }

    pub fn is_case_insensitive(&self) -> bool {
        self.is_case_insensitive
    }

    pub fn has_variant_casing(&self) -> bool {
        // If path case sensitivity agrees with the literal case sensitivity,
        // then the literal is not variant. Otherwise, the literal is variant if
        // it contains characters with casing.
        (PATHS_ARE_CASE_INSENSITIVE != self.is_case_insensitive) && self.text.has_casing()
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
pub struct Token<'t, A = ()> {
    kind: TokenKind<'t, A>,
    annotation: A,
}

impl<'t, A> Token<'t, A> {
    fn new(kind: TokenKind<'t, A>, annotation: A) -> Self {
        Token { kind, annotation }
    }

    pub fn into_owned(self) -> Token<'static, A> {
        let Token { kind, annotation } = self;
        Token {
            kind: kind.into_owned(),
            annotation,
        }
    }

    #[cfg(feature = "diagnostics")]
    pub fn unannotate(self) -> Token<'t, ()> {
        let Token { kind, .. } = self;
        Token {
            kind: kind.unannotate(),
            annotation: (),
        }
    }

    pub fn unroot(&mut self) -> bool {
        self.kind.unroot()
    }

    pub fn kind(&self) -> &TokenKind<'t, A> {
        self.as_ref()
    }

    pub fn annotation(&self) -> &A {
        self.as_ref()
    }
}

impl<'t, A> AsRef<TokenKind<'t, A>> for Token<'t, A> {
    fn as_ref(&self) -> &TokenKind<'t, A> {
        &self.kind
    }
}

impl<'t, A> AsRef<A> for Token<'t, A> {
    fn as_ref(&self) -> &A {
        &self.annotation
    }
}

impl<'t, A> Deref for Token<'t, A> {
    type Target = TokenKind<'t, A>;

    fn deref(&self) -> &Self::Target {
        self.as_ref()
    }
}

impl<'t> From<TokenKind<'t, ()>> for Token<'t, ()> {
    fn from(kind: TokenKind<'t, ()>) -> Self {
        Token {
            kind,
            annotation: (),
        }
    }
}

#[derive(Clone, Debug)]
pub enum TokenKind<'t, A = ()> {
    Alternative(Alternative<'t, A>),
    Class {
        is_negated: bool,
        archetypes: Vec<Archetype>,
    },
    Literal(Literal<'t>),
    Separator,
    Wildcard(Wildcard),
}

impl<'t, A> TokenKind<'t, A> {
    pub fn into_owned(self) -> TokenKind<'static, A> {
        match self {
            TokenKind::Alternative(alternative) => alternative.into_owned().into(),
            TokenKind::Class {
                is_negated,
                archetypes,
            } => TokenKind::Class {
                is_negated,
                archetypes,
            },
            TokenKind::Literal(Literal {
                text,
                is_case_insensitive,
            }) => TokenKind::Literal(Literal {
                text: text.into_owned().into(),
                is_case_insensitive,
            }),
            TokenKind::Separator => TokenKind::Separator,
            TokenKind::Wildcard(wildcard) => TokenKind::Wildcard(wildcard),
        }
    }

    #[cfg(feature = "diagnostics")]
    pub fn unannotate(self) -> TokenKind<'t, ()> {
        match self {
            TokenKind::Alternative(alternative) => alternative.unannotate().into(),
            TokenKind::Class {
                is_negated,
                archetypes,
            } => TokenKind::Class {
                is_negated,
                archetypes,
            },
            TokenKind::Literal(Literal {
                text,
                is_case_insensitive,
            }) => TokenKind::Literal(Literal {
                text,
                is_case_insensitive,
            }),
            TokenKind::Separator => TokenKind::Separator,
            TokenKind::Wildcard(wildcard) => TokenKind::Wildcard(wildcard),
        }
    }

    pub fn unroot(&mut self) -> bool {
        match self {
            TokenKind::Wildcard(Wildcard::Tree { ref mut is_rooted }) => {
                mem::replace(is_rooted, false)
            }
            _ => false,
        }
    }

    pub fn is_component_boundary(&self) -> bool {
        matches!(
            self,
            TokenKind::Separator | TokenKind::Wildcard(Wildcard::Tree { .. })
        )
    }
}

impl<'t, A> From<Alternative<'t, A>> for TokenKind<'t, A> {
    fn from(alternative: Alternative<'t, A>) -> Self {
        TokenKind::Alternative(alternative)
    }
}

impl<A> From<Wildcard> for TokenKind<'static, A> {
    fn from(wildcard: Wildcard) -> Self {
        TokenKind::Wildcard(wildcard)
    }
}

#[derive(Clone, Debug)]
pub struct LiteralSequence<'t>(SmallVec<[&'t Literal<'t>; 4]>);

impl<'t> LiteralSequence<'t> {
    pub fn literals(&self) -> &[&'t Literal<'t>] {
        self.0.as_ref()
    }

    pub fn text(&self) -> Cow<'t, str> {
        if self.literals().len() == 1 {
            self.literals().first().unwrap().text.clone()
        } else {
            self.literals()
                .iter()
                .map(|literal| &literal.text)
                .join("")
                .into()
        }
    }

    pub fn has_variant_casing(&self) -> bool {
        self.literals()
            .iter()
            .any(|literal| literal.has_variant_casing())
    }
}

#[derive(Clone, Debug)]
pub struct Component<'t, A = ()>(SmallVec<[&'t Token<'t, A>; 4]>);

impl<'t, A> Component<'t, A> {
    pub fn tokens(&self) -> &[&'t Token<'t, A>] {
        self.0.as_ref()
    }

    pub fn literal(&self) -> Option<LiteralSequence<'t>> {
        // This predicate is more easily expressed with `all`, but `any` is used
        // here, because it returns `false` for empty iterators and in that case
        // this function should return `None`.
        (!self
            .tokens()
            .iter()
            .any(|token| !matches!(token.kind(), TokenKind::Literal(_))))
        .then(|| {
            LiteralSequence(
                self.tokens()
                    .iter()
                    .map(|token| match token.kind() {
                        TokenKind::Literal(ref literal) => literal,
                        _ => unreachable!(), // See predicate above.
                    })
                    .collect(),
            )
        })
    }
}

pub fn components<'t, A, I>(tokens: I) -> impl Iterator<Item = Component<'t, A>>
where
    A: 't,
    I: IntoIterator<Item = &'t Token<'t, A>>,
    I::IntoIter: Clone,
{
    tokens.into_iter().batching(|tokens| {
        let mut first = tokens.next();
        while matches!(first.map(Token::kind), Some(TokenKind::Separator)) {
            first = tokens.next();
        }
        first.map(|first| match first.kind() {
            TokenKind::Wildcard(Wildcard::Tree { .. }) => Component(smallvec![first]),
            _ => Component(
                Some(first)
                    .into_iter()
                    .chain(tokens.take_while_ref(|token| !token.is_component_boundary()))
                    .collect(),
            ),
        })
    })
}

pub fn literal_path_prefix<'t, A, I>(tokens: I) -> Option<PathBuf>
where
    A: 't,
    I: IntoIterator<Item = &'t Token<'t, A>>,
    I::IntoIter: Clone,
{
    use crate::token::TokenKind::{Separator, Wildcard};
    use crate::token::Wildcard::Tree;

    let mut tokens = tokens.into_iter().peekable();
    let mut prefix = String::new();
    if let Some(Separator | Wildcard(Tree { is_rooted: true })) =
        tokens.peek().map(|token| token.kind())
    {
        // Include any rooting component boundary at the beginning of the token
        // sequence.
        prefix.push(MAIN_SEPARATOR);
    }
    // TODO: Replace `map`, `take_while`, and `flatten` with `map_while`
    //       when it stabilizes.
    prefix.push_str(
        &components(tokens)
            .map(|component| {
                component
                    .literal()
                    .filter(|literal| !literal.has_variant_casing())
            })
            .take_while(|literal| literal.is_some())
            .flatten()
            .map(|literal| literal.text())
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
pub fn parse(expression: &str) -> Result<Vec<Token>, GlobError> {
    use nom::bytes::complete as bytes;
    use nom::character::complete as character;
    use nom::error::ParseError;
    use nom::{branch, combinator, multi, sequence, IResult, Parser};

    use crate::token::FlagToggle::CaseInsensitive;

    fn flags<'i, E, T, F>(
        mut toggle: T,
    ) -> impl FnMut(ParserInput<'i>) -> IResult<ParserInput<'i>, (), E>
    where
        E: ParseError<ParserInput<'i>>,
        T: FnMut(FlagToggle) -> F,
        F: Parser<ParserInput<'i>, (), E>,
    {
        move |input| {
            let (input, _) = multi::many0(sequence::delimited(
                bytes::tag("(?"),
                multi::many1(branch::alt((
                    sequence::tuple((bytes::tag("i"), toggle(CaseInsensitive(true)))),
                    sequence::tuple((bytes::tag("-i"), toggle(CaseInsensitive(false)))),
                ))),
                bytes::tag(")"),
            ))(input)?;
            Ok((input, ()))
        }
    }

    fn flags_with_state<'i, E>(input: ParserInput<'i>) -> IResult<ParserInput<'i>, (), E>
    where
        E: ParseError<ParserInput<'i>>,
    {
        flags(move |toggle| {
            move |mut input: ParserInput<'i>| {
                match toggle {
                    CaseInsensitive(toggle) => {
                        input.state.is_case_insensitive = toggle;
                    }
                }
                Ok((input, ()))
            }
        })(input)
    }

    fn flags_without_state<'i, E>(input: ParserInput<'i>) -> IResult<ParserInput<'i>, (), E>
    where
        E: ParseError<ParserInput<'i>>,
    {
        flags(move |_| move |input: ParserInput<'i>| Ok((input, ())))(input)
    }

    fn no_adjacent_tree<'i, O, E, F>(
        parser: F,
    ) -> impl FnMut(ParserInput<'i>) -> IResult<ParserInput<'i>, O, E>
    where
        E: ParseError<ParserInput<'i>>,
        F: Parser<ParserInput<'i>, O, E>,
    {
        sequence::delimited(
            combinator::peek(sequence::tuple((
                combinator::not(bytes::tag("**")),
                flags_without_state,
            ))),
            parser,
            combinator::peek(sequence::tuple((
                flags_without_state,
                combinator::not(bytes::tag("**")),
            ))),
        )
    }

    fn literal(input: ParserInput) -> IResult<ParserInput, TokenKind<Annotation>> {
        combinator::map(
            combinator::verify(
                // NOTE: Character classes, which accept arbitrary characters,
                //       can be used to escape metacharacters like `*`, `?`,
                //       etc. For example, to escape `*`, either `\*` or `[*]`
                //       can be used.
                bytes::escaped_transform(
                    no_adjacent_tree(bytes::is_not("/?*$()[]{},\\")),
                    '\\',
                    branch::alt((
                        combinator::value("?", bytes::tag("?")),
                        combinator::value("*", bytes::tag("*")),
                        combinator::value("$", bytes::tag("$")),
                        combinator::value("(", bytes::tag("(")),
                        combinator::value(")", bytes::tag(")")),
                        combinator::value("[", bytes::tag("[")),
                        combinator::value("]", bytes::tag("]")),
                        combinator::value("{", bytes::tag("{")),
                        combinator::value("}", bytes::tag("}")),
                        combinator::value(",", bytes::tag(",")),
                    )),
                ),
                |text: &str| !text.is_empty(),
            ),
            |text| {
                TokenKind::Literal(Literal {
                    text: text.into(),
                    is_case_insensitive: input.state.is_case_insensitive,
                })
            },
        )(input)
    }

    fn separator(input: ParserInput) -> IResult<ParserInput, TokenKind<Annotation>> {
        combinator::value(TokenKind::Separator, bytes::tag("/"))(input)
    }

    fn wildcard(input: ParserInput) -> IResult<ParserInput, TokenKind<Annotation>> {
        branch::alt((
            combinator::map(no_adjacent_tree(bytes::tag("?")), |_| {
                TokenKind::from(Wildcard::One)
            }),
            combinator::map(
                sequence::tuple((
                    branch::alt((
                        combinator::map(
                            sequence::tuple((bytes::tag("/"), flags_with_state)),
                            |(left, _)| left,
                        ),
                        bytes::tag(""),
                    )),
                    sequence::terminated(
                        bytes::tag("**"),
                        branch::alt((
                            combinator::map(
                                sequence::tuple((flags_with_state, bytes::tag("/"))),
                                |(_, right)| right,
                            ),
                            combinator::eof,
                            // In alternatives, tree tokens may be terminated by
                            // commas `,` or closing curly braces `}`. These
                            // delimiting tags must be consumed by their respective
                            // parsers, so they are peeked.
                            combinator::peek(branch::alt((bytes::tag(","), bytes::tag("}")))),
                        )),
                    ),
                )),
                |(root, _): (ParserInput, _)| {
                    Wildcard::Tree {
                        is_rooted: !root.is_empty(),
                    }
                    .into()
                },
            ),
            combinator::map(
                sequence::terminated(
                    bytes::tag("*"),
                    branch::alt((
                        combinator::map(
                            combinator::peek(sequence::tuple((
                                flags_without_state,
                                bytes::is_not("*$"),
                            ))),
                            |(_, right)| right,
                        ),
                        combinator::eof,
                    )),
                ),
                |_| Wildcard::ZeroOrMore(Evaluation::Eager).into(),
            ),
            combinator::map(
                sequence::terminated(
                    bytes::tag("$"),
                    branch::alt((
                        combinator::map(
                            combinator::peek(sequence::tuple((
                                flags_without_state,
                                bytes::is_not("*$"),
                            ))),
                            |(_, right)| right,
                        ),
                        combinator::eof,
                    )),
                ),
                |_| Wildcard::ZeroOrMore(Evaluation::Lazy).into(),
            ),
        ))(input)
    }

    fn class(input: ParserInput) -> IResult<ParserInput, TokenKind<Annotation>> {
        fn archetypes(input: ParserInput) -> IResult<ParserInput, Vec<Archetype>> {
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
            |(negation, archetypes)| TokenKind::Class {
                is_negated: negation.is_some(),
                archetypes,
            },
        )(input)
    }

    fn alternative(input: ParserInput) -> IResult<ParserInput, TokenKind<Annotation>> {
        sequence::delimited(
            bytes::tag("{"),
            combinator::map(
                multi::separated_list1(bytes::tag(","), glob),
                |alternatives| Alternative::from(alternatives).into(),
            ),
            bytes::tag("}"),
        )(input)
    }

    fn glob(input: ParserInput) -> IResult<ParserInput, Vec<Token<Annotation>>> {
        #[cfg(feature = "diagnostics")]
        fn annotate<'i, E, F>(
            parser: F,
        ) -> impl FnMut(ParserInput<'i>) -> IResult<ParserInput<'i>, Token<'i, Annotation>, E>
        where
            E: ParseError<ParserInput<'i>>,
            F: Parser<ParserInput<'i>, TokenKind<'i, Annotation>, E>,
        {
            combinator::map(fragment::span(parser), |(span, kind)| {
                Token::new(kind, span.into())
            })
        }

        #[cfg(not(feature = "diagnostics"))]
        fn annotate<'i, E, F>(
            parser: F,
        ) -> impl FnMut(ParserInput<'i>) -> IResult<ParserInput<'i>, Token<'i, Annotation>, E>
        where
            E: ParseError<ParserInput<'i>>,
            F: Parser<ParserInput<'i>, TokenKind<'i, Annotation>, E>,
        {
            combinator::map(parser, |kind| Token::new(kind, ()))
        }

        multi::many1(branch::alt((
            annotate(sequence::preceded(flags_with_state, literal)),
            annotate(sequence::preceded(flags_with_state, alternative)),
            annotate(sequence::preceded(flags_with_state, wildcard)),
            annotate(sequence::preceded(flags_with_state, class)),
            annotate(sequence::preceded(flags_with_state, separator)),
        )))(input)
    }

    #[cfg_attr(not(feature = "diagnostics"), allow(clippy::useless_conversion))]
    let input = ParserInput::new(Fragment::from(expression), FlagState::default());
    let tokens = combinator::all_consuming(glob)(input)
        .map(|(_, tokens)| tokens)
        .map_err(|error| crate::token::ParseError::new(expression, error))
        .map_err(GlobError::from)?;
    rule::check(expression, tokens.iter())?;
    #[cfg(feature = "diagnostics")]
    {
        // TODO: Token sequences tend to be small (tens of tokens). It may not
        //       be worth the additional allocation and moves to drop
        //       annotations.
        Ok(tokens.into_iter().map(Token::unannotate).collect())
    }
    #[cfg(not(feature = "diagnostics"))]
    {
        Ok(tokens)
    }
}

#[cfg(test)]
mod tests {
    use std::path::Path;

    use crate::token::{self, TokenKind};

    #[test]
    fn literal_case_insensitivity() {
        let tokens = token::parse("(?-i)../foo/(?i)**/bar/**(?-i)/baz/*(?i)qux").unwrap();
        let literals: Vec<_> = tokens
            .into_iter()
            .flat_map(|token| match token.kind {
                TokenKind::Literal(literal) => Some(literal),
                _ => None,
            })
            .collect();

        assert!(!literals[0].is_case_insensitive); // `..`
        assert!(!literals[1].is_case_insensitive); // `foo`
        assert!(literals[2].is_case_insensitive); // `bar`
        assert!(!literals[3].is_case_insensitive); // `baz`
        assert!(literals[4].is_case_insensitive); // `qux`
    }

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
        let prefix =
            token::literal_path_prefix(token::parse("../foo/(?i)bar/(?-i)baz").unwrap().iter())
                .unwrap();
        #[cfg(windows)]
        assert_eq!(prefix, Path::new("../foo/bar"));
        #[cfg(not(windows))]
        assert_eq!(prefix, Path::new("../foo"));

        assert!(token::literal_path_prefix(token::parse("**").unwrap().iter()).is_none());
        assert!(token::literal_path_prefix(token::parse("a*").unwrap().iter()).is_none());
        assert!(token::literal_path_prefix(token::parse("*/b").unwrap().iter()).is_none());
        assert!(token::literal_path_prefix(token::parse("a?/b").unwrap().iter()).is_none());
    }
}
