mod supreme {
    //! Re-exported items from `nom_supreme`.
    //!
    //! This module collapses `nom_supreme` and exposes its items using similar
    //! names to `nom`. Parsers are used via this module such that they resemble
    //! the use of `nom` parsers. See the `parse` function.

    pub use nom_supreme::error::{BaseErrorKind, ErrorTree, Expectation, StackContext};
    pub use nom_supreme::multi::{
        collect_separated_terminated as many1, parse_separated_terminated as fold1,
    };
    pub use nom_supreme::parser_ext::ParserExt;
    pub use nom_supreme::tag::complete::tag;
}

#[cfg(feature = "diagnostics-report")]
use miette::{self, Diagnostic, LabeledSpan, SourceCode};
use pori::{Located, Location, Stateful};
use std::borrow::Cow;
use std::fmt::{self, Display, Formatter};
use std::str::FromStr;
use thiserror::Error;

#[cfg(any(feature = "diagnostics-inspect", feature = "diagnostics-report"))]
use crate::diagnostics::Span;
use crate::token::{
    Alternative, Archetype, Class, Evaluation, Literal, Repetition, Separator, Token, TokenKind,
    Tokenized, Wildcard,
};
use crate::PATHS_ARE_CASE_INSENSITIVE;

#[cfg(any(feature = "diagnostics-inspect", feature = "diagnostics-report"))]
pub type Annotation = Span;
#[cfg(all(
    not(feature = "diagnostics-inspect"),
    not(feature = "diagnostics-report"),
))]
pub type Annotation = ();

type BaseErrorKind =
    supreme::BaseErrorKind<&'static str, Box<dyn std::error::Error + Send + Sync + 'static>>;
type StackContext = supreme::StackContext<&'static str>;

type Expression<'i> = Located<'i, str>;
type Input<'i> = Stateful<Expression<'i>, ParserState>;
type ErrorTree<'i> = supreme::ErrorTree<Input<'i>>;
type ErrorMode<'t> = nom::Err<ErrorTree<'t>>;

#[derive(Clone, Debug)]
struct ErrorLocation {
    location: usize,
    context: String,
}

impl<'e, 'i> From<ErrorEntry<'e, Input<'i>>> for ErrorLocation {
    fn from(entry: ErrorEntry<'e, Input<'i>>) -> Self {
        ErrorLocation {
            location: entry.input.location(),
            context: entry.context.to_string(),
        }
    }
}

#[cfg(feature = "diagnostics-report")]
impl From<ErrorLocation> for LabeledSpan {
    fn from(location: ErrorLocation) -> Self {
        let ErrorLocation { location, context } = location;
        LabeledSpan::new(Some(context), location, 1)
    }
}

impl Display for ErrorLocation {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "at offset {}: {}", self.location, self.context)
    }
}

#[derive(Clone, Debug)]
struct ErrorEntry<'e, I> {
    depth: usize,
    input: &'e I,
    context: ErrorContext<'e>,
}

#[derive(Clone, Debug)]
enum ErrorContext<'e> {
    Kind(&'e BaseErrorKind),
    Stack(&'e StackContext),
}

impl Display for ErrorContext<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            ErrorContext::Kind(kind) => match kind {
                BaseErrorKind::Expected(_) | BaseErrorKind::Kind(_) => write!(f, "{}", kind),
                // Omit any "external error" prefix as seen in the `Display`
                // implementation of `BaseErrorKind`.
                BaseErrorKind::External(error) => write!(f, "{}", error),
            },
            ErrorContext::Stack(stack) => write!(f, "{}", stack),
        }
    }
}

trait ErrorTreeExt<I> {
    fn for_each<F>(&self, f: F)
    where
        F: FnMut(ErrorEntry<I>);

    fn bounding_error_locations(&self) -> (Vec<ErrorLocation>, Vec<ErrorLocation>);
}

impl<'i> ErrorTreeExt<Input<'i>> for ErrorTree<'i> {
    fn for_each<F>(&self, mut f: F)
    where
        F: FnMut(ErrorEntry<Input<'i>>),
    {
        fn recurse<'i, F>(tree: &'_ ErrorTree<'i>, depth: usize, f: &mut F)
        where
            F: FnMut(ErrorEntry<Input<'i>>),
        {
            match tree {
                ErrorTree::Base {
                    ref location,
                    ref kind,
                } => f(ErrorEntry {
                    depth,
                    input: location,
                    context: ErrorContext::Kind(kind),
                }),
                ErrorTree::Stack {
                    ref base,
                    ref contexts,
                } => {
                    for (location, context) in contexts {
                        f(ErrorEntry {
                            depth: depth + 1,
                            input: location,
                            context: ErrorContext::Stack(context),
                        });
                    }
                    recurse(base, depth + 1, f);
                },
                ErrorTree::Alt(ref trees) => {
                    for tree in trees {
                        recurse(tree, depth + 1, f);
                    }
                },
            }
        }
        recurse(self, 0, &mut f);
    }

    fn bounding_error_locations(&self) -> (Vec<ErrorLocation>, Vec<ErrorLocation>) {
        let mut min: Option<(usize, Vec<ErrorLocation>)> = None;
        let mut max: Option<(usize, Vec<ErrorLocation>)> = None;
        self.for_each(|entry| {
            let write_if =
                |locations: &mut Option<(_, _)>, push: fn(&_, &_) -> _, reset: fn(&_, &_) -> _| {
                    let locations = locations.get_or_insert_with(|| (entry.depth, vec![]));
                    if reset(&entry.depth, &locations.0) {
                        *locations = (entry.depth, vec![]);
                    }
                    if push(&entry.depth, &locations.0) {
                        locations.1.push(entry.clone().into());
                    }
                };
            write_if(&mut min, usize::eq, |&depth, &min| depth < min);
            write_if(&mut max, usize::eq, |&depth, &max| depth > max);
        });
        (
            min.map(|(_, locations)| locations).unwrap_or_default(),
            max.map(|(_, locations)| locations).unwrap_or_default(),
        )
    }
}

/// Describes errors that occur when parsing a glob expression.
///
/// Common examples of glob expressions that cannot be parsed are alternative
/// and repetition patterns with missing delimiters and ambiguous patterns, such
/// as `src/***/*.rs` or `{.local,.config/**/*.toml`.
///
/// When the `diagnostics-report` feature is enabled, this error implements the
/// [`Diagnostic`] trait and provides more detailed information about the parse
/// failure.
///
/// [`Diagnostic`]: miette::Diagnostic
#[derive(Clone, Debug, Error)]
#[error("failed to parse glob expression")]
pub struct ParseError<'t> {
    expression: Cow<'t, str>,
    start: ErrorLocation,
    ends: Vec<ErrorLocation>,
}

impl<'t> ParseError<'t> {
    fn new(expression: &'t str, error: ErrorMode<'t>) -> Self {
        match error {
            ErrorMode::Incomplete(_) => {
                panic!("unexpected parse error: incomplete input")
            },
            ErrorMode::Error(error) | ErrorMode::Failure(error) => {
                let (starts, ends) = error.bounding_error_locations();
                ParseError {
                    expression: expression.into(),
                    start: starts
                        .into_iter()
                        .next()
                        .expect("expected lower bound error location"),
                    ends,
                }
            },
        }
    }

    /// Clones any borrowed data into an owning instance.
    pub fn into_owned(self) -> ParseError<'static> {
        let ParseError {
            expression,
            start,
            ends,
        } = self;
        ParseError {
            expression: expression.into_owned().into(),
            start,
            ends,
        }
    }

    /// Gets the glob expression that failed to parse.
    pub fn expression(&self) -> &str {
        self.expression.as_ref()
    }
}

#[cfg(feature = "diagnostics-report")]
#[cfg_attr(docsrs, doc(cfg(feature = "diagnostics-report")))]
impl Diagnostic for ParseError<'_> {
    fn code<'a>(&'a self) -> Option<Box<dyn Display + 'a>> {
        Some(Box::new("wax::glob::parse"))
    }

    fn source_code(&self) -> Option<&dyn SourceCode> {
        Some(&self.expression)
    }

    // Surfacing useful parsing errors is difficult. This code replaces any
    // lower bound errors with a simple label noting the beginning of the
    // parsing error. Details are discarded, because these are typically
    // top-level alternative errors that do not provide any useful insight.
    // Upper bound errors are labeled as-is, though they only sometimes provide
    // useful context.
    fn labels(&self) -> Option<Box<dyn Iterator<Item = LabeledSpan> + '_>> {
        Some(Box::new(
            Some(LabeledSpan::new(
                Some(String::from("starting here")),
                self.start.location,
                1,
            ))
            .into_iter()
            .chain(self.ends.iter().cloned().map(|end| {
                LabeledSpan::new(
                    Some(end.context),
                    self.start.location,
                    end.location.saturating_sub(self.start.location) + 1,
                )
            })),
        ))
    }
}

#[derive(Clone, Copy, Debug, Default)]
struct ParserState {
    flags: FlagState,
    subexpression: usize,
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

pub fn parse(expression: &str) -> Result<Tokenized, ParseError> {
    use nom::bytes::complete as bytes;
    use nom::character::complete as character;
    use nom::{branch, combinator, multi, sequence, IResult, Parser};
    use supreme::ParserExt;

    use crate::token::parse::FlagToggle::CaseInsensitive;

    #[derive(Clone, Copy, Debug, Error)]
    #[error("expected {subject}")]
    struct Expectation {
        subject: &'static str,
    }

    type ParseResult<'i, O> = IResult<Input<'i>, O, ErrorTree<'i>>;

    fn boe(input: Input) -> ParseResult<Input> {
        if input.state.subexpression == input.location() {
            Ok((input, input))
        }
        else {
            Err(ErrorMode::Error(ErrorTree::Base {
                location: input,
                kind: BaseErrorKind::External(Box::new(Expectation {
                    subject: "beginning of expression",
                })),
            }))
        }
    }

    fn identity(input: Input) -> ParseResult<Input> {
        Ok((input, input))
    }

    fn flags<'i, F>(
        mut toggle: impl FnMut(FlagToggle) -> F,
    ) -> impl FnMut(Input<'i>) -> ParseResult<'i, ()>
    where
        F: Parser<Input<'i>, (), ErrorTree<'i>>,
    {
        move |input| {
            let (input, _) = multi::many0(sequence::delimited(
                supreme::tag("(?"),
                multi::many1(branch::alt((
                    sequence::tuple((supreme::tag("i"), toggle(CaseInsensitive(true)))),
                    sequence::tuple((supreme::tag("-i"), toggle(CaseInsensitive(false)))),
                ))),
                supreme::tag(")"),
            ))(input)?;
            Ok((input, ()))
        }
    }

    // Explicit lifetimes prevent inference errors.
    #[allow(clippy::needless_lifetimes)]
    fn flags_with_state<'i>(input: Input<'i>) -> ParseResult<'i, ()> {
        flags(move |toggle| {
            move |mut input: Input<'i>| {
                match toggle {
                    CaseInsensitive(toggle) => {
                        input.state.flags.is_case_insensitive = toggle;
                    },
                }
                Ok((input, ()))
            }
        })(input)
    }

    // Explicit lifetimes prevent inference errors.
    #[allow(clippy::needless_lifetimes)]
    fn flags_without_state<'i>(input: Input<'i>) -> ParseResult<'i, ()> {
        flags(move |_| move |input: Input<'i>| Ok((input, ())))(input)
    }

    fn literal(input: Input) -> ParseResult<TokenKind<Annotation>> {
        combinator::map(
            combinator::verify(
                bytes::escaped_transform(
                    bytes::is_not("/?*$:<>()[]{},\\"),
                    '\\',
                    branch::alt((
                        combinator::value("?", supreme::tag("?")),
                        combinator::value("*", supreme::tag("*")),
                        combinator::value("$", supreme::tag("$")),
                        combinator::value(":", supreme::tag(":")),
                        combinator::value("<", supreme::tag("<")),
                        combinator::value(">", supreme::tag(">")),
                        combinator::value("(", supreme::tag("(")),
                        combinator::value(")", supreme::tag(")")),
                        combinator::value("[", supreme::tag("[")),
                        combinator::value("]", supreme::tag("]")),
                        combinator::value("{", supreme::tag("{")),
                        combinator::value("}", supreme::tag("}")),
                        combinator::value(",", supreme::tag(",")),
                    )),
                ),
                |text: &str| !text.is_empty(),
            ),
            move |text| {
                TokenKind::Literal(Literal {
                    text: text.into(),
                    is_case_insensitive: input.state.flags.is_case_insensitive,
                })
            },
        )(input)
    }

    fn separator(input: Input) -> ParseResult<TokenKind<Annotation>> {
        combinator::value(TokenKind::Separator(Separator), supreme::tag("/"))(input)
    }

    fn wildcard<'i>(
        terminator: impl Clone + Parser<Input<'i>, Input<'i>, ErrorTree<'i>>,
    ) -> impl FnMut(Input<'i>) -> ParseResult<'i, TokenKind<'i, Annotation>> {
        branch::alt((
            combinator::map(supreme::tag("?"), |_| TokenKind::from(Wildcard::One))
                .context("exactly-one"),
            combinator::map(
                sequence::tuple((
                    combinator::map(
                        branch::alt((
                            sequence::tuple((
                                combinator::value(true, supreme::tag("/")),
                                flags_with_state,
                            )),
                            sequence::tuple((combinator::value(false, boe), flags_with_state)),
                        )),
                        |(prefix, _)| prefix,
                    )
                    .context("prefix"),
                    sequence::terminated(
                        supreme::tag("**"),
                        branch::alt((
                            combinator::map(
                                sequence::tuple((flags_with_state, supreme::tag("/"))),
                                |(_, postfix)| postfix,
                            ),
                            terminator.clone(),
                        ))
                        .context("postfix"),
                    ),
                )),
                |(has_root, _)| Wildcard::Tree { has_root }.into(),
            )
            .context("tree"),
            combinator::map(
                sequence::terminated(
                    supreme::tag("*"),
                    branch::alt((
                        combinator::map(
                            combinator::peek(sequence::tuple((
                                flags_without_state,
                                bytes::is_not("*$").context("no terminating wildcard"),
                            ))),
                            |(_, right)| right,
                        ),
                        terminator.clone(),
                    )),
                ),
                |_| Wildcard::ZeroOrMore(Evaluation::Eager).into(),
            )
            .context("zero-or-more"),
            combinator::map(
                sequence::terminated(
                    supreme::tag("$"),
                    branch::alt((
                        combinator::map(
                            combinator::peek(sequence::tuple((
                                flags_without_state,
                                bytes::is_not("*$").context("no terminating wildcard"),
                            ))),
                            |(_, right)| right,
                        ),
                        terminator,
                    )),
                ),
                |_| Wildcard::ZeroOrMore(Evaluation::Lazy).into(),
            )
            .context("zero-or-more"),
        ))
    }

    fn repetition(input: Input) -> ParseResult<TokenKind<Annotation>> {
        fn bounds(input: Input) -> ParseResult<(usize, Option<usize>)> {
            type BoundResult<T> = Result<T, <usize as FromStr>::Err>;

            branch::alt((
                sequence::preceded(
                    supreme::tag(":"),
                    branch::alt((
                        combinator::map_res(
                            sequence::separated_pair(
                                character::digit1,
                                supreme::tag(","),
                                combinator::opt(character::digit1),
                            ),
                            |(lower, upper): (Input, Option<_>)| -> BoundResult<_> {
                                let lower = lower.parse::<usize>()?;
                                let upper =
                                    upper.map(|upper| upper.parse::<usize>()).transpose()?;
                                Ok((lower, upper))
                            },
                        )
                        .context("range"),
                        combinator::map_res(character::digit1, |n: Input| -> BoundResult<_> {
                            let n = n.parse::<usize>()?;
                            Ok((n, Some(n)))
                        })
                        .context("converged"),
                        combinator::success((1, None)),
                    )),
                ),
                combinator::success((0, None)),
            ))(input)
        }

        combinator::map(
            sequence::delimited(
                supreme::tag("<"),
                sequence::tuple((
                    glob(move |input| {
                        combinator::peek(branch::alt((supreme::tag(":"), supreme::tag(">"))))(input)
                    })
                    .context("sub-glob"),
                    bounds.context("bounds"),
                )),
                supreme::tag(">"),
            ),
            |(tokens, (lower, upper))| {
                Repetition {
                    tokens,
                    lower,
                    upper,
                }
                .into()
            },
        )(input)
    }

    fn class(input: Input) -> ParseResult<TokenKind<Annotation>> {
        fn archetypes(input: Input) -> ParseResult<Vec<Archetype>> {
            let escaped_character = |input| {
                branch::alt((
                    character::none_of("[]-\\"),
                    branch::alt((
                        combinator::value('[', supreme::tag("\\[")),
                        combinator::value(']', supreme::tag("\\]")),
                        combinator::value('-', supreme::tag("\\-")),
                    )),
                ))(input)
            };

            multi::many1(branch::alt((
                combinator::map(
                    sequence::separated_pair(
                        escaped_character,
                        supreme::tag("-"),
                        escaped_character,
                    ),
                    Archetype::from,
                ),
                combinator::map(escaped_character, Archetype::from),
            )))(input)
        }

        combinator::map(
            sequence::delimited(
                supreme::tag("["),
                sequence::tuple((combinator::opt(supreme::tag("!")), archetypes)),
                supreme::tag("]"),
            ),
            |(negation, archetypes)| {
                Class {
                    is_negated: negation.is_some(),
                    archetypes,
                }
                .into()
            },
        )(input)
    }

    fn alternative(input: Input) -> ParseResult<TokenKind<Annotation>> {
        sequence::preceded(
            supreme::tag("{"),
            combinator::map(
                supreme::many1(
                    glob(move |input| {
                        combinator::peek(branch::alt((supreme::tag(","), supreme::tag("}"))))(input)
                    })
                    .context("sub-glob"),
                    supreme::tag(","),
                    supreme::tag("}"),
                ),
                |alternatives: Vec<Vec<_>>| Alternative::from(alternatives).into(),
            ),
        )(input)
    }

    fn glob<'i>(
        terminator: impl 'i + Clone + Parser<Input<'i>, Input<'i>, ErrorTree<'i>>,
    ) -> impl Parser<Input<'i>, Vec<Token<'i, Annotation>>, ErrorTree<'i>> {
        #[cfg(any(feature = "diagnostics-inspect", feature = "diagnostics-report"))]
        fn annotate<'i, F>(
            parser: F,
        ) -> impl FnMut(Input<'i>) -> ParseResult<'i, Token<'i, Annotation>>
        where
            F: 'i + Parser<Input<'i>, TokenKind<'i, Annotation>, ErrorTree<'i>>,
        {
            combinator::map(pori::span(parser), |(span, kind)| Token::new(kind, span))
        }

        #[cfg(all(
            not(feature = "diagnostics-inspect"),
            not(feature = "diagnostics-report"),
        ))]
        fn annotate<'i, F>(
            parser: F,
        ) -> impl FnMut(Input<'i>) -> ParseResult<'i, Token<'i, Annotation>>
        where
            F: 'i + Parser<Input<'i>, TokenKind<'i, Annotation>, ErrorTree<'i>>,
        {
            combinator::map(parser, |kind| Token::new(kind, ()))
        }

        move |mut input: Input<'i>| {
            input.state.subexpression = input.location();
            supreme::many1(
                branch::alt((
                    annotate(sequence::preceded(flags_with_state, literal)).context("literal"),
                    annotate(sequence::preceded(flags_with_state, repetition))
                        .context("repetition"),
                    annotate(sequence::preceded(flags_with_state, alternative))
                        .context("alternative"),
                    annotate(sequence::preceded(
                        flags_with_state,
                        wildcard(terminator.clone()),
                    ))
                    .context("wildcard"),
                    annotate(sequence::preceded(flags_with_state, class)).context("class"),
                    annotate(sequence::preceded(flags_with_state, separator)).context("separator"),
                )),
                identity,
                terminator.clone(),
            )
            .parse(input)
        }
    }

    if expression.is_empty() {
        Ok(Tokenized {
            expression: expression.into(),
            tokens: vec![],
        })
    }
    else {
        let input = Input::new(Expression::from(expression), ParserState::default());
        let tokens = combinator::all_consuming(glob(combinator::eof))(input)
            .map(|(_, tokens)| tokens)
            .map_err(|error| ParseError::new(expression, error))?;
        Ok(Tokenized {
            expression: expression.into(),
            tokens,
        })
    }
}
