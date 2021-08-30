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

use crate::rule;
use crate::GlobError;

#[cfg(feature = "diagnostics")]
pub type Fragment<'i> = crate::fragment::Fragment<'i, str>;
#[cfg(not(feature = "diagnostics"))]
pub type Fragment<'i> = &'i str;

#[cfg(feature = "diagnostics")]
pub type Annotation = SourceSpan;
#[cfg(not(feature = "diagnostics"))]
pub type Annotation = ();

type NomError<'t> = nom::Err<nom::error::Error<Fragment<'t>>>;

#[derive(Debug, Error)]
#[error("failed to parse glob expression: {kind:?}")]
#[cfg_attr(feature = "diagnostics", derive(Diagnostic))]
#[cfg_attr(feature = "diagnostics", diagnostic(code = "glob::parse"))]
pub struct ParseError<'t> {
    text: Cow<'t, str>,
    kind: ErrorKind,
    #[cfg(feature = "diagnostics")]
    #[snippet(text, message("in this expression"))]
    expression: SourceSpan,
    #[cfg(feature = "diagnostics")]
    #[highlight(expression, label("here"))]
    error: SourceSpan,
}

impl<'t> ParseError<'t> {
    fn new(text: Fragment<'t>, error: NomError<'t>) -> Self {
        match error {
            NomError::Incomplete(_) => {
                panic!("unexpected parse error: incomplete input")
            }
            #[cfg(feature = "diagnostics")]
            NomError::Error(error) | NomError::Failure(error) => {
                use nom::Offset;

                ParseError {
                    text: text.into(),
                    kind: error.code,
                    expression: (0, text.len()).into(),
                    error: (Offset::offset(&text, &error.input), 0).into(),
                }
            }
            #[cfg(not(feature = "diagnostics"))]
            NomError::Error(error) | NomError::Failure(error) => ParseError {
                text: text.into(),
                kind: error.code,
            },
        }
    }

    pub fn into_owned(self) -> ParseError<'static> {
        let ParseError {
            text,
            kind,
            #[cfg(feature = "diagnostics")]
            expression,
            #[cfg(feature = "diagnostics")]
            error,
        } = self;
        ParseError {
            text: text.into_owned().into(),
            kind,
            #[cfg(feature = "diagnostics")]
            expression,
            #[cfg(feature = "diagnostics")]
            error,
        }
    }
}

#[derive(Clone, Debug)]
pub struct Alternative<'t, A = ()>(pub Vec<Vec<Token<'t, A>>>);

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
    Literal(Cow<'t, str>),
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
            TokenKind::Literal(literal) => literal.into_owned().into(),
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
            TokenKind::Literal(literal) => TokenKind::Literal(literal),
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

impl<'t, A> From<&'t str> for TokenKind<'t, A> {
    fn from(literal: &'t str) -> Self {
        TokenKind::Literal(literal.into())
    }
}

impl<A> From<String> for TokenKind<'static, A> {
    fn from(literal: String) -> Self {
        TokenKind::Literal(literal.into())
    }
}

impl<A> From<Wildcard> for TokenKind<'static, A> {
    fn from(wildcard: Wildcard) -> Self {
        TokenKind::Wildcard(wildcard)
    }
}

#[derive(Clone, Debug)]
pub struct Component<'t, A = ()>(SmallVec<[&'t Token<'t, A>; 4]>);

impl<'t, A> Component<'t, A> {
    pub fn tokens(&self) -> &[&'t Token<'t, A>] {
        self.0.as_ref()
    }

    pub fn literal(&self) -> Option<Cow<'t, str>> {
        // This predicate is more easily expressed with `all`, but `any` is used
        // here, because it returns `false` for empty iterators and in that case
        // this function should return `None`.
        (!self
            .tokens()
            .iter()
            .any(|token| !matches!(token.kind(), TokenKind::Literal(_))))
        .then(|| {
            if self.tokens().len() == 1 {
                match self.tokens().first().unwrap().kind() {
                    TokenKind::Literal(ref literal) => literal.clone(),
                    _ => unreachable!(), // See predicate above.
                }
            } else {
                self.tokens()
                    .iter()
                    .map(|token| match token.kind() {
                        TokenKind::Literal(ref literal) => literal,
                        _ => unreachable!(), // See predicate above.
                    })
                    .join("")
                    .into()
            }
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
pub fn parse(text: &str) -> Result<Vec<Token>, GlobError> {
    use nom::bytes::complete as bytes;
    use nom::character::complete as character;
    use nom::error::ParseError;
    use nom::{branch, combinator, multi, sequence, IResult, Parser};

    fn no_adjacent_tree<'i, O, E, F>(
        parser: F,
    ) -> impl FnMut(Fragment<'i>) -> IResult<Fragment<'i>, O, E>
    where
        E: ParseError<Fragment<'i>>,
        F: Parser<Fragment<'i>, O, E>,
    {
        sequence::delimited(
            combinator::peek(combinator::not(bytes::tag("**"))),
            parser,
            combinator::peek(combinator::not(bytes::tag("**"))),
        )
    }

    fn literal(input: Fragment) -> IResult<Fragment, TokenKind<Annotation>> {
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
            TokenKind::from,
        )(input)
    }

    fn separator(input: Fragment) -> IResult<Fragment, TokenKind<Annotation>> {
        combinator::value(TokenKind::Separator, bytes::tag("/"))(input)
    }

    fn wildcard(input: Fragment) -> IResult<Fragment, TokenKind<Annotation>> {
        branch::alt((
            combinator::map(no_adjacent_tree(bytes::tag("?")), |_| {
                TokenKind::from(Wildcard::One)
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
                |(root, _): (Fragment, _)| {
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

    fn class(input: Fragment) -> IResult<Fragment, TokenKind<Annotation>> {
        fn archetypes(input: Fragment) -> IResult<Fragment, Vec<Archetype>> {
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

    fn alternative(input: Fragment) -> IResult<Fragment, TokenKind<Annotation>> {
        sequence::delimited(
            bytes::tag("{"),
            combinator::map(
                multi::separated_list1(bytes::tag(","), glob),
                |alternatives| Alternative::from(alternatives).into(),
            ),
            bytes::tag("}"),
        )(input)
    }

    fn glob(input: Fragment) -> IResult<Fragment, Vec<Token<Annotation>>> {
        #[cfg(feature = "diagnostics")]
        fn annotate<'i, E, F>(
            parser: F,
        ) -> impl FnMut(Fragment<'i>) -> IResult<Fragment<'i>, Token<'i, Annotation>, E>
        where
            E: ParseError<Fragment<'i>>,
            F: Parser<Fragment<'i>, TokenKind<'i, Annotation>, E>,
        {
            use crate::fragment;

            combinator::map(fragment::span(parser), |(span, kind)| {
                Token::new(kind, span.into())
            })
        }

        #[cfg(not(feature = "diagnostics"))]
        fn annotate<'i, E, F>(
            parser: F,
        ) -> impl FnMut(Fragment<'i>) -> IResult<Fragment<'i>, Token<'i, Annotation>, E>
        where
            E: ParseError<Fragment<'i>>,
            F: Parser<Fragment<'i>, TokenKind<'i, Annotation>, E>,
        {
            combinator::map(parser, |kind| Token::new(kind, ()))
        }

        multi::many1(branch::alt((
            annotate(literal),
            annotate(alternative),
            annotate(wildcard),
            annotate(class),
            annotate(separator),
        )))(input)
    }

    #[cfg_attr(not(feature = "diagnostics"), allow(clippy::useless_conversion))]
    let text = Fragment::from(text);
    let tokens = combinator::all_consuming(glob)(text)
        .map(|(_, tokens)| tokens)
        .map_err(|error| crate::token::ParseError::new(text, error))
        .map_err(GlobError::from)?;
    rule::check(text, tokens.iter())?;
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
