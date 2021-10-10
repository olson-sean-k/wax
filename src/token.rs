use itertools::Itertools as _;
#[cfg(feature = "diagnostics")]
use miette::{self, Diagnostic, SourceSpan};
use nom::error::ErrorKind;
use smallvec::{smallvec, SmallVec};
use std::borrow::Cow;
use std::cmp;
use std::mem;
use std::ops::{Bound, Deref, RangeBounds};
use std::path::{PathBuf, MAIN_SEPARATOR};
use std::str::FromStr;
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
type Expression<'i> = Locate<'i, str>;
#[cfg(not(feature = "diagnostics"))]
type Expression<'i> = &'i str;

type ParserInput<'i> = Stateful<Expression<'i>, FlagState>;

type NomError<'t> = nom::Err<nom::error::Error<ParserInput<'t>>>;

#[derive(Debug, Error)]
#[error("failed to parse glob expression: {kind:?}")]
#[cfg_attr(feature = "diagnostics", derive(Diagnostic))]
#[cfg_attr(feature = "diagnostics", diagnostic(code = "glob::parse"))]
pub struct ParseError<'t> {
    #[cfg_attr(feature = "diagnostics", source_code)]
    expression: Cow<'t, str>,
    kind: ErrorKind,
    #[cfg(feature = "diagnostics")]
    #[label("starting here")]
    span: SourceSpan,
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
                    span: (Offset::offset(&expression, &input), 0).into(),
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
            span,
        } = self;
        ParseError {
            expression: expression.into_owned().into(),
            kind,
            #[cfg(feature = "diagnostics")]
            span,
        }
    }

    pub fn expression(&self) -> &str {
        self.expression.as_ref()
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

    pub fn is_rooted(&self) -> bool {
        self.has_preceding_token_with(&mut |token| {
            matches!(
                token.kind(),
                TokenKind::Separator | TokenKind::Wildcard(Wildcard::Tree { is_rooted: true })
            )
        })
    }

    pub fn has_component_boundary(&self) -> bool {
        self.has_token_with(&mut |token| token.is_component_boundary())
    }

    pub fn has_token_with(&self, f: &mut impl FnMut(&Token<'t, A>) -> bool) -> bool {
        match self.kind() {
            TokenKind::Alternative(ref alternative) => alternative.has_token_with(f),
            TokenKind::Repetition(ref repetition) => repetition.has_token_with(f),
            _ => f(self),
        }
    }

    pub fn has_preceding_token_with(&self, f: &mut impl FnMut(&Token<'t, A>) -> bool) -> bool {
        match self.kind() {
            TokenKind::Alternative(ref alternative) => alternative.has_preceding_token_with(f),
            TokenKind::Repetition(ref repetition) => repetition.has_preceding_token_with(f),
            _ => f(self),
        }
    }

    pub fn has_terminating_token_with(&self, f: &mut impl FnMut(&Token<'t, A>) -> bool) -> bool {
        match self.kind() {
            TokenKind::Alternative(ref alternative) => alternative.has_terminating_token_with(f),
            TokenKind::Repetition(ref repetition) => repetition.has_terminating_token_with(f),
            _ => f(self),
        }
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
    Repetition(Repetition<'t, A>),
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
            TokenKind::Repetition(repetition) => repetition.into_owned().into(),
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
            TokenKind::Repetition(repetition) => repetition.unannotate().into(),
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

impl<'t, A> From<Repetition<'t, A>> for TokenKind<'t, A> {
    fn from(repetition: Repetition<'t, A>) -> Self {
        TokenKind::Repetition(repetition)
    }
}

impl<A> From<Wildcard> for TokenKind<'static, A> {
    fn from(wildcard: Wildcard) -> Self {
        TokenKind::Wildcard(wildcard)
    }
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

    pub fn has_token_with(&self, f: &mut impl FnMut(&Token<'t, A>) -> bool) -> bool {
        self.0
            .iter()
            .any(|tokens| tokens.iter().any(|token| token.has_token_with(f)))
    }

    pub fn has_preceding_token_with(&self, f: &mut impl FnMut(&Token<'t, A>) -> bool) -> bool {
        self.0.iter().any(|tokens| {
            tokens
                .first()
                .map(|token| token.has_preceding_token_with(f))
                .unwrap_or(false)
        })
    }

    pub fn has_terminating_token_with(&self, f: &mut impl FnMut(&Token<'t, A>) -> bool) -> bool {
        self.0.iter().any(|tokens| {
            tokens
                .last()
                .map(|token| token.has_terminating_token_with(f))
                .unwrap_or(false)
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

#[derive(Clone, Debug)]
pub struct Repetition<'t, A = ()> {
    tokens: Vec<Token<'t, A>>,
    lower: usize,
    step: Option<usize>,
}

impl<'t, A> Repetition<'t, A> {
    fn new(tokens: Vec<Token<'t, A>>, bounds: impl RangeBounds<usize>) -> Option<Self> {
        let lower = match bounds.start_bound() {
            Bound::Included(lower) => *lower,
            Bound::Excluded(lower) => *lower + 1,
            Bound::Unbounded => 0,
        };
        let upper = match bounds.end_bound() {
            Bound::Included(upper) => Some(*upper),
            Bound::Excluded(upper) => Some(cmp::max(*upper, 1) - 1),
            Bound::Unbounded => None,
        };
        match upper {
            Some(upper) => (upper >= lower).then(|| Repetition {
                tokens,
                lower,
                step: Some(upper - lower),
            }),
            None => Some(Repetition {
                tokens,
                lower,
                step: None,
            }),
        }
    }

    pub fn into_owned(self) -> Repetition<'static, A> {
        let Repetition {
            tokens,
            lower,
            step,
        } = self;
        Repetition {
            tokens: tokens.into_iter().map(Token::into_owned).collect(),
            lower,
            step,
        }
    }

    #[cfg(feature = "diagnostics")]
    pub fn unannotate(self) -> Repetition<'t, ()> {
        let Repetition {
            tokens,
            lower,
            step,
        } = self;
        Repetition {
            tokens: tokens.into_iter().map(Token::unannotate).collect(),
            lower,
            step,
        }
    }

    pub fn tokens(&self) -> &Vec<Token<'t, A>> {
        &self.tokens
    }

    pub fn bounds(&self) -> (usize, Option<usize>) {
        (self.lower, self.step.map(|step| self.lower + step))
    }

    pub fn has_token_with(&self, f: &mut impl FnMut(&Token<'t, A>) -> bool) -> bool {
        self.tokens.iter().any(|token| token.has_token_with(f))
    }

    pub fn has_preceding_token_with(&self, f: &mut impl FnMut(&Token<'t, A>) -> bool) -> bool {
        self.tokens
            .first()
            .map(|token| token.has_preceding_token_with(f))
            .unwrap_or(false)
    }

    pub fn has_terminating_token_with(&self, f: &mut impl FnMut(&Token<'t, A>) -> bool) -> bool {
        self.tokens
            .last()
            .map(|token| token.has_terminating_token_with(f))
            .unwrap_or(false)
    }
}

#[derive(Clone, Debug)]
pub enum Wildcard {
    One,
    ZeroOrMore(Evaluation),
    // NOTE: Repetitions can represent tree wildcards as they are more general
    //       and are allowed to cross component boundaries. However,
    //       transforming tree wildcards into repetitions would move complex
    //       logic into the parser and require additional state that is easier
    //       (and likely less expensive) to manage in compilation (see
    //       `encode::compile`).
    Tree { is_rooted: bool },
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
        }
        else {
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

// TODO: Repetition tokens are invariant if they have constant bounds (`step` is
//       zero) and their sub-glob consists of invariant tokens. This should be
//       considered here.
pub fn invariant_prefix_path<'t, A, I>(tokens: I) -> Option<PathBuf>
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
    }
    else {
        Some(prefix.into())
    }
}

pub fn invariant_prefix_upper_bound(tokens: &[Token]) -> usize {
    use crate::token::TokenKind::{Literal, Separator, Wildcard};
    use crate::token::Wildcard::Tree;

    let mut separator = None;
    for (n, token) in tokens.iter().map(Token::kind).enumerate() {
        match token {
            Separator => {
                separator = Some(n);
            }
            Literal(literal) if !literal.has_variant_casing() => {
                continue;
            }
            Wildcard(Tree { .. }) => {
                return n;
            }
            _ => {
                return match separator {
                    Some(n) => n + 1,
                    None => 0,
                };
            }
        }
    }
    tokens.len()
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
                    no_adjacent_tree(bytes::is_not("/?*$:<>()[]{},\\")),
                    '\\',
                    branch::alt((
                        combinator::value("?", bytes::tag("?")),
                        combinator::value("*", bytes::tag("*")),
                        combinator::value("$", bytes::tag("$")),
                        combinator::value(":", bytes::tag(":")),
                        combinator::value("<", bytes::tag("<")),
                        combinator::value(">", bytes::tag(">")),
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
                            // In alternatives and repetitions, tree tokens may
                            // be terminated by additional tags. These
                            // delimiting tags must be consumed by their
                            // respective parsers, so they are peeked.
                            combinator::peek(branch::alt((
                                bytes::tag(","),
                                bytes::tag(":"),
                                bytes::tag("}"),
                                bytes::tag(">"),
                            ))),
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

    fn repetition(input: ParserInput) -> IResult<ParserInput, TokenKind<Annotation>> {
        type NParseResult<T> = Result<T, <usize as FromStr>::Err>;

        fn bounds(input: ParserInput) -> IResult<ParserInput, (usize, Option<usize>)> {
            branch::alt((
                sequence::preceded(
                    bytes::tag(":"),
                    branch::alt((
                        combinator::map_res(
                            sequence::separated_pair(
                                character::digit1,
                                bytes::tag(","),
                                combinator::opt(character::digit1),
                            ),
                            |(lower, upper): (ParserInput, Option<_>)| -> NParseResult<_> {
                                let lower = lower.parse::<usize>()?;
                                let upper =
                                    upper.map(|upper| upper.parse::<usize>()).transpose()?;
                                Ok((lower, upper))
                            },
                        ),
                        combinator::map_res(
                            character::digit1,
                            |n: ParserInput| -> NParseResult<_> {
                                let n = n.parse::<usize>()?;
                                Ok((n, Some(n)))
                            },
                        ),
                        combinator::value((1, None), bytes::tag("")),
                    )),
                ),
                combinator::value((0, None), bytes::tag("")),
            ))(input)
        }

        combinator::map_opt(
            no_adjacent_tree(sequence::delimited(
                bytes::tag("<"),
                sequence::tuple((glob, bounds)),
                bytes::tag(">"),
            )),
            |(tokens, (lower, upper))| match upper {
                Some(upper) => Repetition::new(tokens, lower..=upper).map(From::from),
                None => Repetition::new(tokens, lower..).map(From::from),
            },
        )(input)
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
            no_adjacent_tree(sequence::delimited(
                bytes::tag("["),
                sequence::tuple((combinator::opt(bytes::tag("!")), archetypes)),
                bytes::tag("]"),
            )),
            |(negation, archetypes)| TokenKind::Class {
                is_negated: negation.is_some(),
                archetypes,
            },
        )(input)
    }

    fn alternative(input: ParserInput) -> IResult<ParserInput, TokenKind<Annotation>> {
        no_adjacent_tree(sequence::delimited(
            bytes::tag("{"),
            combinator::map(
                multi::separated_list1(bytes::tag(","), glob),
                |alternatives| Alternative::from(alternatives).into(),
            ),
            bytes::tag("}"),
        ))(input)
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
            annotate(sequence::preceded(flags_with_state, repetition)),
            annotate(sequence::preceded(flags_with_state, alternative)),
            annotate(sequence::preceded(flags_with_state, wildcard)),
            annotate(sequence::preceded(flags_with_state, class)),
            annotate(sequence::preceded(flags_with_state, separator)),
        )))(input)
    }

    #[cfg_attr(not(feature = "diagnostics"), allow(clippy::useless_conversion))]
    let input = ParserInput::new(Expression::from(expression), FlagState::default());
    let mut tokens = combinator::all_consuming(glob)(input)
        .map(|(_, tokens)| tokens)
        .map_err(|error| crate::token::ParseError::new(expression, error))
        .map_err(GlobError::from)?;
    rule::check(expression, tokens.iter())?;
    // Remove any trailing separator tokens. Such separators are meaningless and
    // are typically normalized in paths by removing them or ignoring them in
    // nominal comparisons.
    while let Some(TokenKind::Separator) = tokens.last().map(Token::kind) {
        tokens.pop();
    }
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
    use std::path::{Path, PathBuf};

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
    fn invariant_prefix_path() {
        fn invariant_prefix_path(expression: &str) -> Option<PathBuf> {
            token::invariant_prefix_path(token::parse(expression).unwrap().iter())
        }

        assert_eq!(invariant_prefix_path("/a/b").unwrap(), Path::new("/a/b"));
        assert_eq!(invariant_prefix_path("a/b").unwrap(), Path::new("a/b"));
        assert_eq!(invariant_prefix_path("a/*").unwrap(), Path::new("a/"));
        assert_eq!(invariant_prefix_path("a/*b").unwrap(), Path::new("a/"));
        assert_eq!(invariant_prefix_path("a/b*").unwrap(), Path::new("a/"));
        assert_eq!(invariant_prefix_path("a/b/*/c").unwrap(), Path::new("a/b/"));

        #[cfg_attr(not(any(unix, windows)), allow(unused))]
        let prefix = invariant_prefix_path("../foo/(?i)bar/(?-i)baz").unwrap();
        #[cfg(unix)]
        assert_eq!(prefix, Path::new("../foo"));
        #[cfg(windows)]
        assert_eq!(prefix, Path::new("../foo/bar"));

        assert!(invariant_prefix_path("**").is_none());
        assert!(invariant_prefix_path("a*").is_none());
        assert!(invariant_prefix_path("*/b").is_none());
        assert!(invariant_prefix_path("a?/b").is_none());
    }
}
