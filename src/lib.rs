//! Zero-dependency library for writing parsers in a concise functional style & with exhaustive
//! error-reporting.
//!
//! Kinds of errors are distinguished via a user-defined `Reason` type, which signals what did
//! a parser expect.
//! A [`ParsingError`] can also have no reason, which will mean that the error is recoverable.
//! Some built-in parsers can have [`std::convert::Infallible`] as their error reason,
//! which means that any error the parser may ever return is recoverable.
//! The distinction between recoverable & fatal errors is important for parsers that need to try
//! multiple options.
//!
//! Error reporting with precise location in the source is facilitated by
//! constructing a [`FullParsingError`] with methods such as
//! [`Parser::with_full_error`], [`ParsingError::with_src_loc`]

#![cfg_attr(feature = "nightly", feature(unboxed_closures, tuple_trait, doc_cfg))]

pub mod tuple;
pub mod utils;

use core::{fmt::{Debug, Display, Formatter}, cmp::min, convert::Infallible};
use std::{error::Error, path::Path};
use tuple::{first, map_second, rev, tuple, Tuple};
use utils::{locate_saturating, FullLocation, WithSourceLine};

/// Error returned by a parser.
///
/// A parsing error may be either recoverable or fatal, parser methods such as [`Parser::or`] allow
/// trying different paths if a recoverable error occurs, whereas a fatal error is not intended to
/// be recovered from and should just be propagated.
///
/// This error isn't an error per Rust's definition, it doesn't implement [`std::error::Error`],
/// the reason being that it lacks any information that'd make it actually useful, to make the
/// error more useful, consider the following options:
/// - [`ParsingError::with_src_loc`]
/// - [`Parser::with_full_error`]
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct ParsingError<'rest, Reason> {
    /// The rest of the input that could not be processed.
    pub rest: &'rest str,
    /// What the parser expected, the reason for the error.
    /// `None` means that the error is recoverable.
    pub reason: Option<Reason>,
}

/// A final error with information about where in the source did the error occur.
///
/// This should be constructed at the top-level of a parser as the final action before returning
/// the result. Main ways to construct this are [`ParsingError::with_src_loc`] and
/// [`Parser::with_full_error`]
///
/// To print the source line of the error along with the reason & location, wrap the error in
/// [`WithSourceLine`], this will alter its [`Display`] implementation.
#[derive(Debug, Clone, Copy)]
pub struct FullParsingError<'path, Reason> {
    /// Where the error occured.
    pub loc: FullLocation<'path>,
    /// What the parser expected to see at the location of the error.
    /// If `None`, then the error was recoverable and the parser didn't have any particular
    /// reason.
    pub reason: Option<Reason>,
}

impl<Reason: Display> Display for FullParsingError<'_, Reason> {
    fn fmt(&self, f: &mut Formatter) -> core::fmt::Result {
        if let Some(reason) = &self.reason {
            writeln!(f, "{reason}")?;
        }
        write!(f, "--> {}", self.loc)?;
        Ok(())
    }
}

impl<Reason: Display> Display for WithSourceLine<FullParsingError<'_, Reason>> {
    fn fmt(&self, f: &mut Formatter) -> core::fmt::Result {
        if let Some(reason) = &self.0.reason {
            writeln!(f, "{reason}")?;
        }
        write!(f, "--> {}", WithSourceLine(self.0.loc))?;
        Ok(())
    }
}

impl<Reason: Error> Error for FullParsingError<'_, Reason> {}

impl<'rest, Reason> ParsingError<'rest, Reason> {
    /// Create a new fatal parsing error.
    pub const fn new(rest: &'rest str, expected: Reason) -> Self {
        Self { rest, reason: Some(expected) }
    }

    /// Create a new recoverable parsing error.
    pub const fn new_recoverable(rest: &'rest str) -> Self {
        Self { rest, reason: None }
    }

    /// Returns a boolean indicating whether the error is recoverable.
    pub const fn is_recoverable(&self) -> bool {
        self.reason.is_none()
    }

    /// Changes the reason associated with the error, making the error fatal.
    pub fn reason<NewReason>(self, expected: NewReason)
        -> ParsingError<'rest, NewReason>
    {
        ParsingError { reason: Some(expected), rest: self.rest }
    }

    /// Transforms the reason by calling `f`, except if it's a recoverable error,
    /// in which case it remains recoverable.
    pub fn map_reason<NewReason>(self, f: impl FnOnce(Reason) -> NewReason)
        -> ParsingError<'rest, NewReason>
    {
        ParsingError { reason: self.reason.map(f), rest: self.rest }
    }

    /// Changes the reason associated with error, except if it's a recoverable error,
    /// in which case it remains recoverable.
    pub fn narrow_reason<NewReason>(self, expected: NewReason)
        -> ParsingError<'rest, NewReason>
    {
        ParsingError { reason: self.reason.map(|_| expected), rest: self.rest }
    }

    /// Turns this error into a [`FullParsingError`] for more informative error report.
    pub fn with_src_loc<'path>(self, path: &'path Path, src: &str)
        -> FullParsingError<'path, Reason>
    {
        FullParsingError {
            loc: locate_saturating(self.rest.as_ptr(), src).with_path(path),
            reason: self.reason,
        }
    }
}

/// The result of a parser.
pub type ParsingResult<'src, T = (), Reason = Infallible> = core::result::Result<
    (&'src str, T),
    ParsingError<'src, Reason>,
>;

/// The core of the crate, a trait representing a function that takes some string as input and
/// returns either a tuple of (the rest of the input, the output) or a [`ParsingError`].
#[allow(clippy::missing_errors_doc, /* reason="it only propagates them, nothing to document" */)]
pub trait Parser<'input, T = (), Reason = Infallible>:
    Sized + FnOnce(&'input str) -> ParsingResult<'input, T, Reason>
{
    /// Turns output into a recoverable error if the output doesn't meet a condition.
    fn filter(self, f: impl FnOnce(&T) -> bool) -> impl Parser<'input, T, Reason> {
        move |input| match self(input) {
            Ok((rest, res)) if f(&res) => Ok((rest, res)),
            Ok(_) => Err(ParsingError::new_recoverable(input)),
            Err(err) => Err(err),
        }
    }

    /// Transforms the output of the parser, if present.
    fn map<U>(self, f: impl FnOnce(T) -> U) -> impl Parser<'input, U, Reason> {
        move |input| self(input).map(map_second(f))
    }

    /// Like [`Parser::map`], but calls the provdied function using the Nightly [`FnOnce::call_once`]
    /// method, effectively spreading the output as the arguments of the function.
    /// The following nIghtly Rust code:
    /// ```rs
    /// use shrimple_parser::Parser;
    /// parser.call(u32::pow)
    /// ```
    /// is equivalent to the following stable Rust code:
    /// ```rs
    /// use shrimple_parser::{Parser, call};
    /// parser.map(call!(u32::pow(x, y)))
    /// ```
    #[cfg(feature = "nightly")]
    #[doc(cfg(feature = "nightly"))]
    fn call<F>(self, f: F) -> impl Parser<'input, F::Output, Reason>
    where
        F: FnOnce<T>,
        T: core::marker::Tuple,
    {
        move |input| self(input).map(map_second(move |x| f.call(x)))
    }

    /// Replaces a recoverable error with the result of `parser`.
    /// The reason for the first parser is adapted to the one of the second parser.
    fn or<NewReason>(self, parser: impl Parser<'input, T, NewReason>)
        -> impl Parser<'input, T, NewReason>
    where
        Reason: Into<NewReason>,
    {
        move |input| match self(input) {
            Ok(res) => Ok(res),
            Err(err) if err.is_recoverable() => parser(input),
            Err(err) => Err(err.map_reason(Into::into)),
        }
    }

    /// Replaces a recoverable error with the transformed remains of the input.
    /// The returned remains of the input are an empty string.
    fn or_map_rest(self, f: impl FnOnce(&'input str) -> T) -> impl Parser<'input, T, Reason> {
        move |input| match self(input) {
            Ok(res) => Ok(res),
            Err(err) if err.is_recoverable() => Ok(("", f(err.rest))),
            Err(err) => Err(err),
        }
    }

    /// Replaces a recoverable error with `value` & the rest of the input in the recoverable error.
    fn or_value(self, value: T) -> impl Parser<'input, T, Reason> {
        move |input| match self(input) {
            Ok(res) => Ok(res),
            Err(err) if err.is_recoverable() => Ok((err.rest, value)),
            Err(err) => Err(err),
        }
    }

    /// Parses the rest of the input after the first parser, returning both outputs
    /// & short-circuiting on an error.
    /// The reason for the errors of the first parser is adapted to the one of the second parser.
    /// See also [`Parser::add`].
    fn and<U, NewReason>(self, parser: impl Parser<'input, U, NewReason>)
        -> impl Parser<'input, (T, U), NewReason>
    where
        Reason: Into<NewReason>,
    {
        move |input| {
            let (rest, out) = self(input).map_err(|e| e.map_reason(Into::into))?;
            let (rest, new_out) = parser(rest)?;
            Ok((rest, (out, new_out)))
        }
    }

    /// Like [`Parser::and`], but specific to parsers that output a tuple:
    /// the new output is appended to the tuple of other tuples using the [`Tuple`] trait.
    /// The reason for the errors of the first parser is adapted to the one of the second parser.
    fn add<U, NewReason>(self, parser: impl Parser<'input, U, NewReason>)
        -> impl Parser<'input, T::Appended<U>, NewReason>
    where
        T: Tuple,
        Reason: Into<NewReason>,
    {
        move |input| {
            let (rest, out) = self(input).map_err(|e| e.map_reason(Into::into))?;
            let (rest, new_out) = parser(rest)?;
            Ok((rest, out.append(new_out)))
        }
    }

    /// Like [`Parser::and`], but discards the output of the first parser.
    /// The reason for the errors of the first parser is adapted to the one of the second parser.
    fn then<U, NewReason>(self, parser: impl Parser<'input, U, NewReason>)
        -> impl Parser<'input, U, NewReason>
    where
        Reason: Into<NewReason>,
    {
        move |input| {
            let rest = self(input).map_err(|e| e.map_reason(Into::into))?.0;
            let (rest, out) = parser(rest)?;
            Ok((rest, out))
        }
    }

    /// Same as [`Parser::and`] but discards the output of the second parser
    /// The reason for the errors the first parser is adapted to the one of the second parser.
    fn skip<U, NewReason>(self, parser: impl Parser<'input, U, NewReason>)
        -> impl Parser<'input, T, NewReason>
    where
        Reason: Into<NewReason>,
    {
        move |input| {
            let (rest, out) = self(input).map_err(|e| e.map_reason(Into::into))?;
            let rest = parser(rest)?.0;
            Ok((rest, out))
        }
    }

    /// Same as [`Parser::skip`] but discards the error of the second parser as well.
    /// Effectively, all this function does is advance the input to right after the second parser,
    /// if it succeeds, otherwise the input stays as if only the first parser was called.
    fn maybe_skip<U, OtherReason>(self, parser: impl Parser<'input, U, OtherReason>)
        -> impl Parser<'input, T, Reason>
    {
        move |input| {
            let (rest, out) = self(input)?;
            let rest = parser(rest).map_or(rest, first);
            Ok((rest, out))
        }
    }

    /// Sets the reason for errors returned from the parser, making all errors fatal.
    fn expect<NewReason>(self, expected: NewReason)
        -> impl Parser<'input, T, NewReason>
    {
        move |input| self(input).map_err(|e| e.reason(expected))
    }

    /// Changes the reason from the parser, unless the error is recoverable.
    fn narrow_reason<NewReason>(self, expected: NewReason)
        -> impl Parser<'input, T, NewReason>
    {
        move |input| self(input).map_err(|e| e.narrow_reason(expected))
    }

    /// Adds the part of the input that was consumed by the parser to the outputs.
    /// If the input increased in length after the parser (which should not happen), an empty
    /// string is added.
    /// See also [`Parser::add_span`], which adds the span to the tuple of other outputs.
    fn get_span(self) -> impl Parser<'input, (T, &'input str), Reason>
    {
        self.map(tuple).add_span()
    }

    /// Like [`Parser::get_span`], but adds the output to the tuple of other outputs using the
    /// [`Tuple`] trait.
    fn add_span(self) -> impl Parser<'input, T::Appended<&'input str>, Reason>
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
    fn repeat(self)  -> impl Parser<'input, (), Reason>
    where
        Self: Clone
    {
        move |mut input| loop {
            match self.clone()(input) {
                Ok((rest, _)) => input = rest,
                Err(err) if err.is_recoverable() => return Ok((err.rest, ())),
                Err(err) => return Err(err),
            }
        }
    }

    /// Prints the output using its `Debug` implementation & the first 16 bytes of the rest of the
    /// input, all along with a custom provided message.
    fn dbg(self, label: impl Display) -> impl Parser<'input, T, Reason> where T: Debug {
        move |input| {
            let (rest, out) = self(input)?;
            println!("{label}: {out:?} : {}...", &rest[.. min(rest.len(), 16)].escape_debug());
            Ok((rest, out))
        }
    }

    /// Aaugments the parsing error, if present, with location in the `input`.
    /// `path` is the reported path to the file where the error occured.
    /// Note that the `input` passed here is only used for error reporting, not as the input to the
    /// parser.
    fn with_full_error<'path>(self, path: &'path Path, full_input: &'input str)
        -> impl FnOnce(&'input str)
        -> Result<(&'input str, T), FullParsingError<'path, Reason>>
    {
        move |input| self(input).map_err(|e| e.with_src_loc(path, full_input))
    }
}

impl<'input, T, Reason, F> Parser<'input, T, Reason> for F
where
    F: FnOnce(&'input str) -> ParsingResult<'input, T, Reason>,
{}

fn str_split_first(input: &str) -> Option<(&str, char)> {
    let mut iter = input.chars();
    iter.next().map(|ch| (iter.as_str(), ch))
}

/// Parses any 1 character from the input.
/// See also [`parse_char`]
/// # Errors
/// Returns a recoverable error if the input is empty.
pub fn parse_any_char(input: &str) -> ParsingResult<char> {
    str_split_first(input).ok_or_else(|| ParsingError::new_recoverable(input))
}

/// Parses exactly 1 character `ch` from the input.
/// See also [`parse_any_char`]
/// # Errors
/// The returned parser returns a recoverable error if the input is empty
/// or the 1st character isn't `ch`.
pub fn parse_char<'input>(ch: char) -> impl Parser<'input, char> {
    parse_any_char.filter(move |x| *x == ch)
}

/// Parses exactly 1 string `prefix` from the input.
/// # Errors
/// The returned parser returns a recoverable error if the input doesn't start with `prefix`.
pub fn parse_exact(prefix: &str) -> impl Parser<&str> {
    move |input| input.strip_prefix(prefix)
        .map(|rest| (rest, prefix))
        .ok_or_else(|| ParsingError::new_recoverable(input))
}

/// Strips characters from the input until `pred` returns `true`, i.e. while it returns `false`,
/// returns the string spanning the stripped characters.
///
/// The rest of the input, will still have the character on which `pred` returned `true`.
/// See also [`parse_while`], [`parse_until_ex`]
/// This parser never returns an error, if `pred` returns `false` for all the characters in the
/// input, then the output is the entire input, and the rest of the input is an empty string.
pub fn parse_until<'input>(pred: impl Fn(&char) -> bool) -> impl Parser<'input, &'input str> {
    move |input| Ok(input.find(|c| pred(&c)).map_or(("", input), |id| input.split_at(id).rev()))
}

/// Like [`parse_until`], but also removes the character on which `pred` returned `true` from the
/// rest of the input.
/// # Errors
/// Unlike [`parse_until`], this parser returns a recoverable error if `pred` returned `false` for
/// all the characters in the input.
pub fn parse_until_ex<'input>(pred: impl Fn(&char) -> bool) -> impl Parser<'input, &'input str> {
    move |input| input.find(|c| pred(&c))
        .map(|id| input.split_at(id).rev().map_first(|rest| unsafe {
            str_split_first(rest).unwrap_unchecked().0
        }))
        .ok_or_else(|| ParsingError::new_recoverable(input))
}

/// Strips characters from the input until `delimiter` is met, returns the string before it.
/// The `delimiter` is omitted from both the output and the rest of the input.
/// # Errors
/// The returned parser returns a recoverable error if `delimiter` isn't found in the input.
// TODO: make more generic with patterns
pub fn parse_until_exact(delimiter: &str) -> impl Parser<&str> {
    move |input| input.split_once(delimiter)
        .map(rev)
        .ok_or_else(|| ParsingError::new_recoverable(input))
}

/// Strips characters from the input until `pred` returned `false`, i.e. while it returns
/// `true`, returns the string spanning the stripped characters.
///
/// This parser never returns an error, if `pred` returns `true` for all the characters in the
/// input, then the output is the entire input, and the rest of the input is an empty string.
pub fn parse_while<'input>(pred: impl Fn(&char) -> bool) -> impl Parser<'input, &'input str> {
    parse_until(move |c| !pred(c))
}

/// Like [`parse_while`], but also removes the character on which `pred` returned `false` from the
/// rest of the input.
/// # Errors
/// Unlike [`parse_while`], this parser returns a recoverable error if `pred` returned `true` for
/// all the characters in the input.
pub fn parse_while_ex<'input>(pred: impl Fn(&char) -> bool) -> impl Parser<'input, &'input str> {
    parse_until_ex(move |c| !pred(c))
}

/// Parse a balanced group of `open` & `close` characters.
/// # Errors
/// - If no initial `open` was found, a recoverable error is returned.
/// - If the end was reached before a matching `close` character, a fatal error is returned.
///
/// An example use of this is parsing balanced parentheses:
/// ```rust
/// # fn main() {
/// use shrimple_parser::{parse_group, ParsingError};
/// let input = "(foo) bar";
/// assert_eq!(parse_group('(', ')')(input), Ok((" bar", "foo")));
/// let input = "(oops";
/// assert_eq!(parse_group('(', ')')(input), Err(ParsingError::new("(oops", ())));
/// # }
/// ```
pub fn parse_group<'input>(open: char, close: char) -> impl Parser<'input, &'input str, ()> {
    move |original_input| {
        let (input, _) = parse_char(open).narrow_reason(())(original_input)?;
        let mut depth = 0usize;
        for (at, ch) in input.char_indices() {
            if ch == close {
                if depth == 0 {
                    let (res, src) = input.split_at(at);
                    return Ok((&src[1..], res));
                }
                depth -= 1;
            } else if ch == open {
                depth += 1;
            }
        }
        Err(ParsingError::new(original_input, ()))
    }
}
