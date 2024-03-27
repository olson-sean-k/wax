use regex_automata::meta::Regex;
use regex_automata::util::captures::Captures;
use std::borrow::Cow;
use std::str;

use crate::CandidatePath;

pub trait RegexExt {
    fn matched<'t>(&self, text: impl Into<Cow<'t, str>>) -> Option<MatchedText<'t>>;
}

impl RegexExt for Regex {
    fn matched<'t>(&self, text: impl Into<Cow<'t, str>>) -> Option<MatchedText<'t>> {
        let text = text.into();
        let mut captures = self.create_captures();
        self.captures(text.as_ref(), &mut captures);
        if captures.is_match() {
            Some(MatchedText { text, captures })
        }
        else {
            None
        }
    }
}

/// Text that has been matched by a [`Program`] and its captures.
///
/// To match a [`Glob`] or other [`Program`] against a [`CandidatePath`] and get the matched text,
/// use the [`Program::matched`] function.
///
/// All [`Program`]s provide an implicit capture of the complete text of a match. This implicit
/// capture has index zero, and is exposed via the [`complete`] function as well as the [`get`]
/// function using index zero. Capturing tokens are indexed starting at one, and can be used to
/// isolate more specific sub-text.
///
/// # Examples
///
/// Capturing tokens and matched text can be used to isolate sub-text in a match. For example, the
/// file name of a match can be extracted using an alternation to group patterns.
///
/// ```rust
/// use wax::{CandidatePath, Glob, Program};
///
/// let glob = Glob::new("src/**/{*.{go,rs}}").unwrap();
/// let candidate = CandidatePath::from("src/graph/link.rs");
/// let matched = glob.matched(&candidate).unwrap();
///
/// assert_eq!("link.rs", matched.get(2).unwrap());
/// ```
///
/// [`CandidatePath`]: crate::CandidatePath
/// [`complete`]: crate::MatchedText::complete
/// [`get`]: crate::MatchedText::get
/// [`Glob`]: crate::Glob
/// [`Program`]: crate::Program
/// [`Program::matched`]: crate::Program::matched
#[derive(Clone, Debug)]
pub struct MatchedText<'t> {
    text: Cow<'t, str>,
    captures: Captures,
}

impl<'t> MatchedText<'t> {
    /// Clones any borrowed data into an owning instance.
    pub fn into_owned(self) -> MatchedText<'static> {
        let MatchedText { text, captures } = self;
        MatchedText {
            text: text.into_owned().into(),
            captures,
        }
    }

    /// Gets the complete text of a match.
    ///
    /// All [`Program`]s have an implicit capture of the complete text at index zero. This function
    /// is therefore equivalent to unwrapping the output of the [`get`] function with index zero.
    ///
    /// [`get`]: crate::MatchedText::get
    /// [`Program`]: crate::Program
    pub fn complete(&self) -> &str {
        self.get(0).expect("match has no complete text")
    }

    /// Gets the matched text of a capture at the given index.
    ///
    /// All [`Program`]s have an implicit capture of the complete text at index zero. Capturing
    /// tokens are indexed from one, so any capturing sub-expression will be indexed after the
    /// implicit complete text. For example, the sub-expression `*` in the glob expression `*.txt`
    /// is at index one and will exclude the suffix `.txt` in its matched text.
    ///
    /// Alternation and repetition patterns group their sub-globs into a single capture, so it is
    /// not possible to isolate matched text from their sub-globs. This can be used to explicitly
    /// group matched text, such as isolating an entire matched file name using an expression like
    /// `{*.{go,rs}}`.
    ///
    /// [`Program`]: crate::Program
    pub fn get(&self, index: usize) -> Option<&str> {
        self.captures.get_group(index).map(|span| {
            self.text
                .as_ref()
                .get(span.start..span.end)
                .expect("match span not in text")
        })
    }

    pub fn to_candidate_path(&self) -> CandidatePath {
        CandidatePath::from(self.complete())
    }
}
