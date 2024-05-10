//! Zero-dependency library for writing parsers in a concise functional style & with exhaustive
//! error-reporting.
//!
//! Kinds of errors are distinguished via a user-defined `Expectation` type, which signals what did
//! a parser expect.
//! A [`ParsingError`] can also have no expectation, which will mean that the error is recoverable.
//! Some built-in parsers can have `Infallible` as their expectation, which means that any error
//! the parser may ever return is recoverable.
//! The distinction between recoverable & fatal errors is important for parsers that need to try
//! multiple options.
//!
//! Error reporting with precise location in the source is facilitated by methods such as
//! [`Parser::parse_with_err_loc`], [`ParsingError::with_src_loc`]

pub mod tuple;

use core::{fmt::{Display, Formatter}, num::NonZeroU32};
use core::{convert::Infallible, fmt::Debug};
use std::{error::Error, path::Path};

use tuple::{first, map_second, rev, second, tuple, Tuple};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Location {
    line: NonZeroU32,
    col: u32,
}

impl Default for Location {
    fn default() -> Self {
        Self {
            line: unsafe { NonZeroU32::new(1).unwrap_unchecked() },
            col: 0
        }
    }
}

impl Display for Location {
    fn fmt(&self, f: &mut Formatter) -> core::fmt::Result {
        write!(f, "{}:{}", self.line, self.col)
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct ParsingError<'rest, Expectation> {
    rest: &'rest str,
    /// `None` means that the error is recoverable
    expected: Option<Expectation>,
}

#[derive(Debug)]
pub struct FullParsingError<'path, Expectation> {
    at: Location,
    path: &'path Path,
    expected: Option<Expectation>,
}

impl<Expectation: Display> Display for FullParsingError<'_, Expectation> {
    fn fmt(&self, f: &mut Formatter) -> core::fmt::Result {
        write!(f, "parsing error at {}:{}", self.path.display(), self.at)?;
        if let Some(expected) = &self.expected {
            write!(f, ": {expected}")?;
        }
        Ok(())
    }
}

impl<Expectation: Error> Error for FullParsingError<'_, Expectation> {}

impl<'rest, Expectation> ParsingError<'rest, Expectation> {
    pub const fn new(rest: &'rest str, expected: Expectation) -> Self {
        Self { rest, expected: Some(expected) }
    }

    pub const fn new_recoverable(rest: &'rest str) -> Self {
        Self { rest, expected: None }
    }

    pub const fn is_recoverable(&self) -> bool {
        self.expected.is_none()
    }

    pub fn expectation<NewExpectation>(self, expected: NewExpectation)
        -> ParsingError<'rest, NewExpectation>
    {
        ParsingError { expected: Some(expected), rest: self.rest }
    }

    pub fn narrow_expectation<NewExpectation>(self, expected: NewExpectation)
        -> ParsingError<'rest, NewExpectation>
    {
        ParsingError { expected: self.expected.map(|_| expected), rest: self.rest }
    }

    pub fn with_src_loc<'path>(self, path: &'path Path, src: &str)
        -> FullParsingError<'path, Expectation>
    {
        let Some(progress) = src.len().checked_sub(self.rest.len()) else {
            return FullParsingError { at: Location::default(), expected: self.expected, path }
        };

        FullParsingError {
            at: src.bytes().take(progress).fold(Location::default(), |loc, b| match b {
                b'\n' => Location { line: loc.line.saturating_add(1), col: 0 },
                _ => Location { col: loc.col.saturating_add(1), ..loc },
            }),
            expected: self.expected,
            path,
        }
    }
}

/// The result of a parser.
pub type ParsingResult<'src, T = (), Expectation = Infallible> = core::result::Result<
    (&'src str, T),
    ParsingError<'src, Expectation>,
>;

/// The core of the crate, a trait representing a function that takes some string as input and
/// returns either a tuple of (the rest of the input, the output) or a [`ParsingError`].
pub trait Parser<'input, T = (), Expectation = Infallible>:
    Sized + FnOnce(&'input str) -> ParsingResult<'input, T, Expectation>
{
    /// Turns output into a recoverable error if the output doesn't meet a condition.
    fn filter(self, f: impl FnOnce(&T) -> bool)
        -> impl FnOnce(&'input str)
        -> ParsingResult<'input, T, Expectation>
    {
        move |input| match self(input) {
            Ok((rest, res)) if f(&res) => Ok((rest, res)),
            Ok(_) => Err(ParsingError::new_recoverable(input)),
            Err(err) => Err(err),
        }
    }

    /// Transforms the first output of the parser, if present.
    fn map<U>(self, f: impl FnOnce(T) -> U)
        -> impl FnOnce(&'input str)
        -> ParsingResult<'input, U, Expectation>
    {
        move |input| self(input).map(map_second(f))
    }

    /// Replaces a recoverable error with the result of `parser`.
    fn or(self, parser: impl FnOnce(&'input str) -> ParsingResult<'input, T, Expectation>)
        -> impl FnOnce(&'input str)
        -> ParsingResult<'input, T, Expectation>
    {
        move |input| match self(input) {
            Ok(res) => Ok(res),
            Err(err) if err.is_recoverable() => parser(input),
            Err(err) => Err(err),
        }
    }

    /// Replaces a recoverable error with the transformed remains of the input.
    /// The returned remains of the input are an empty string.
    fn or_map_rest(self, f: impl FnOnce(&'input str) -> T)
        -> impl FnOnce(&'input str)
        -> ParsingResult<'input, T, Expectation>
    {
        move |input| match self(input) {
            Ok(res) => Ok(res),
            Err(err) if err.is_recoverable() => Ok(("", f(err.rest))),
            Err(err) => Err(err),
        }
    }

    /// Replaces a recoverable error with `value` & the rest of the input in the recoverable error.
    fn or_value(self, value: T)
        -> impl FnOnce(&'input str)
        -> ParsingResult<'input, T, Expectation>
    {
        move |input| match self(input) {
            Ok(res) => Ok(res),
            Err(err) if err.is_recoverable() => Ok((err.rest, value)),
            Err(err) => Err(err),
        }
    }

    /// Parses the rest of the input after the first parser, returning both outputs
    /// & short-circuiting on an error.
    /// See also [`Parser::add`].
    fn and<U>(self, parser: impl FnOnce(&'input str) -> ParsingResult<'input, U, Expectation>)
        -> impl FnOnce(&'input str)
        -> ParsingResult<'input, (T, U), Expectation>
    {
        move |input| {
            let (rest, out) = self(input)?;
            let (rest, new_out) = parser(rest)?;
            Ok((rest, (out, new_out)))
        }
    }

    /// Like [`Parser::and`], but specific to parsers that output a tuple:
    /// the new output is appended to the tuple of other tuples using the [`Tuple`] trait.
    fn add<U>(self, parser: impl FnOnce(&'input str) -> ParsingResult<'input, U, Expectation>)
        -> impl FnOnce(&'input str)
        -> ParsingResult<'input, T::Appended<U>, Expectation>
    where
        T: Tuple,
    {
        move |input| {
            let (rest, out) = self(input)?;
            let (rest, new_out) = parser(rest)?;
            Ok((rest, out.append(new_out)))
        }
    }

    /// Like [`Parser::and`], but discards the output of the first parser.
    fn then<U>(self, parser: impl FnOnce(&'input str) -> ParsingResult<'input, U, Expectation>)
        -> impl FnOnce(&'input str)
        -> ParsingResult<'input, U, Expectation>
    {
        move |input| {
            let rest = self(input)?.0;
            let (rest, out) = parser(rest)?;
            Ok((rest, out))
        }
    }

    /// Same as [`Parser::and`] but discards the output of the second parser
    fn skip<U>(self, parser: impl FnOnce(&'input str) -> ParsingResult<'input, U, Expectation>)
        -> impl FnOnce(&'input str)
        -> ParsingResult<'input, T, Expectation>
    {
        move |input| {
            let (rest, out) = self(input)?;
            let rest = parser(rest)?.0;
            Ok((rest, out))
        }
    }

    /// Same as [`Parser::skip`] but discards the error of the second parser as well.
    /// Effectively, all this function does is advance the input to right after the second parser,
    /// if it succeeds, otherwise the input stays as if only the first parser was called.
    fn maybe_skip<U>(self, parser: impl FnOnce(&'input str) -> ParsingResult<'input, U, Expectation>)
        -> impl FnOnce(&'input str)
        -> ParsingResult<'input, T, Expectation>
    {
        move |input| {
            let (rest, out) = self(input)?;
            let rest = parser(rest).map_or(rest, first);
            Ok((rest, out))
        }
    }

    /// Sets the expectation from the parser, making all errors unrecoverable.
    fn expect<NewExpectation>(self, expected: NewExpectation)
        -> impl FnOnce(&'input str)
        -> ParsingResult<'input, T, NewExpectation>
    {
        move |input| self(input).map_err(|e| e.expectation(expected))
    }

    /// Changes the expectation from the parser, unless the error is recoverable.
    fn narrow_expectation<NewExpectation>(self, expected: NewExpectation)
        -> impl FnOnce(&'input str)
        -> ParsingResult<'input, T, NewExpectation>
    {
        move |input| self(input).map_err(|e| e.narrow_expectation(expected))
    }

    /// Adds the part of the input that was consumed by the parser to the outputs.
    /// If the input increased in length after the parser (which should not happen), an empty
    /// string is added.
    /// See also [`Parser::add_span`], which adds the span to the tuple of other outputs.
    fn get_span(self)
        -> impl FnOnce(&'input str)
        -> ParsingResult<'input, (T, &'input str), Expectation>
    {
        self.map(tuple).add_span()
    }

    /// Like [`Parser::get_span`], but adds the output to the tuple of other outputs using the
    /// [`Tuple`] trait.
    fn add_span(self)
        -> impl FnOnce(&'input str)
        -> ParsingResult<'input, T::Appended<&'input str>, Expectation>
    where
        T: Tuple,
    {
        move |input| {
            let (rest, out) = self(input)?;
            let consumed = unsafe {
                input.get_unchecked(.. input.len().saturating_sub(rest.len())) 
            };
            Ok((rest, out.append(consumed)))
        }
    }

    /// Repeats the parser until a recoverable error is met, discarding all the output.
    /// Beware parsers with non-trivially cloneable captured variables: the parser is called
    /// repeatedly by being cloned.
    fn repeat(self) -> impl FnOnce(&'input str) -> ParsingResult<'input, (), Expectation>
    where
        Self: Clone
    {
        move |input| loop {
            match self.clone()(input) {
                Ok(_) => (),
                Err(err) if err.is_recoverable() => return Ok((err.rest, ())),
                Err(err) => return Err(err),
            }
        }
    }

    /// Calls the parser and augments the parsing error, if present, with location in the input.
    /// `path` is the reported path to the file where the error occured.
    fn parse_with_err_loc<'path>(self, path: &'path Path, input: &'input str)
        -> Result<T, FullParsingError<'path, Expectation>>
    {
        self(input).map_err(|e| e.with_src_loc(path, input)).map(second)
    }
}

impl<'input, T, Expectation, F> Parser<'input, T, Expectation> for F
where
    F: FnOnce(&'input str) -> ParsingResult<'input, T, Expectation>,
{}

/// Strips any 1 character from the input.
/// Returns the parsed character or a recoverable error.
/// See also [`parse_char`]
pub fn parse_any_char(input: &str) -> ParsingResult<char> {
    let mut iter = input.chars();
    iter.next().map(|ch| (iter.as_str(), ch)).ok_or(ParsingError::new_recoverable(input))
}

/// Strips exactly 1 character `ch` from the input.
/// Returns `ch` or a recoverable error.
/// See also [`parse_any_char`]
pub fn parse_char<'input>(ch: char) -> impl Parser<'input, char> {
    parse_any_char.filter(move |x| *x == ch)
}

/// Strips exactly 1 string `prefix` from the input.
/// Returns `prefix` or a recoverable error.
pub fn parse_exact(prefix: &str) -> impl Parser<&str> {
    move |input| prefix.strip_prefix(prefix)
        .map(|rest| (rest, prefix))
        .ok_or(ParsingError::new_recoverable(input))
}

/// Strips characters from the input until `pred` returns `true`, i.e. while it returns `false`.
/// Returns the consumed string slice or a recoverable error.
/// See also [`parse_while`]
pub fn parse_until<'input>(pred: impl Fn(&char) -> bool) -> impl Parser<'input, &'input str> {
    move |input| input.find(|c| pred(&c))
        .map(|id| input.split_at(id).rev())
        .ok_or(ParsingError::new_recoverable(input))
}

/// Strips characters from the input until `delimiter` is met.
/// The `delimiter` is omitted from both the output and the rest of the input.
/// Returns the string consumed before the `delimiter` or a recoverable error.
pub fn parse_until_exact(delimiter: &str) -> impl Parser<&str> {
    move |input| input.split_once(delimiter)
        .map(rev)
        .ok_or(ParsingError::new_recoverable(input))
}

/// The output is a string up to the point where `pred` returned `true`
/// any returned error is recoverable
pub fn parse_while<'input>(pred: impl Fn(&char) -> bool) -> impl Parser<'input, &'input str> {
    parse_until(move |c| !pred(c))
}

/// Parse a balanced group of `open` & `close` characters.
/// Returns the group without the initial `open` & the final `close`, or:
/// - If no initial `open` was found, a recoverable error is returned.
/// - If the end was reached before a matching `close` character, a fatal error is returned.
/// An example use of this is parsing balanced parentheses:
/// ```rust
/// # fn main() {
/// use shrimple_parsing::{parse_group, ParsingError};
/// let input = "(foo) bar";
/// assert_eq!(parse_group('(', ')')(input), Ok((" bar", "foo")));
/// let input = "(oops";
/// assert_eq!(parse_group('(', ')')(input), Err(ParsingError::new("(oops", ())));
/// # }
/// ```
pub fn parse_group<'input>(open: char, close: char) -> impl Parser<'input, &'input str, ()> {
    move |original_input| {
        let (input, _) = parse_char(open).expect(())(original_input)?;
        let mut depth = 0usize;
        for (at, ch) in input.char_indices() {
            if ch == close {
                if depth == 0 {
                    let (res, src) = input.split_at(at);
                    return Ok((&src[1..], res));
                }
                depth -= 1
            } else if ch == open {
                depth += 1
            }
        }
        Err(ParsingError::new(original_input, ()))
    }
}
