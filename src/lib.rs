//! Zero-dependency library with no-std support for writing parsers in a concise functional style
//! & with rich error-reporting.
//!
//! Kinds of errors are distinguished via a user-defined `Reason` type, which signals what did
//! a parser expect.
//! A [`ParsingError`] can also have no reason, which will mean that the error is recoverable.
//!
//! Some built-in parsers can have [`core::convert::Infallible`] as their error reason,
//! which means that any error the parser may ever return is recoverable.
//!
//! The distinction between recoverable & fatal errors is important for parsers that need to try
//! multiple options.
//!
//! Error reporting with precise location in the source is facilitated by
//! constructing a [`FullParsingError`] with methods such as
//! [`Parser::with_full_error`], [`ParsingError::with_src_loc`]

#![cfg_attr(feature = "nightly", feature(unboxed_closures, fn_traits, tuple_trait, doc_auto_cfg))]

pub mod tuple;
pub mod utils;
pub mod pattern;
mod input;
pub use input::Input;

use core::{
    cmp::min,
    convert::Infallible,
    error::Error,
    fmt::{Debug, Display, Formatter},
    iter::FusedIterator,
    marker::PhantomData,
    ops::Not,
    mem::take,
};
use tuple::{first, map_second, tuple, Tuple};
use utils::{locate_saturating, FullLocation, PathLike};
#[cfg(feature = "std")]
use utils::WithSourceLine;

/// Error returned by a parser.
///
/// A parsing error may be either recoverable or fatal, parser methods such as [`Parser::or`] allow
/// trying different paths if a recoverable error occurs, whereas a fatal error is not intended to
/// be recovered from and should just be propagated.
///
/// To make the error more useful, consider the following options:
/// - [`ParsingError::with_src_loc`]
/// - [`Parser::with_full_error`]
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct ParsingError<In, Reason = Infallible> {
    /// The rest of the input that could not be processed.
    pub rest: In,
    /// What the parser expected, the reason for the error.
    /// `None` means that the error is recoverable.
    pub reason: Option<Reason>,
}

impl<In: Input, Reason: Display> Display for ParsingError<In, Reason> {
    fn fmt(&self, f: &mut Formatter) -> core::fmt::Result {
        if let Some(reason) = &self.reason {
            writeln!(f, "{reason}")?;
        }
        write!(f, "error source: {}{}",
            self.rest[.. self.rest.len().min(16)].escape_debug(),
            if self.rest.len() > 16 {"..."} else {""})?;
        Ok(())
    }
}

impl<In: Input, Reason: Error> Error for ParsingError<In, Reason> {}

impl<In, Reason> ParsingError<In, Reason> {
    /// Create a new fatal parsing error.
    pub const fn new(rest: In, reason: Reason) -> Self {
        Self { rest, reason: Some(reason) }
    }

    /// Create a new recoverable parsing error.
    pub const fn new_recoverable(rest: In) -> Self {
        Self { rest, reason: None }
    }

    /// Returns a boolean indicating whether the error is recoverable.
    pub const fn is_recoverable(&self) -> bool {
        self.reason.is_none()
    }

    /// Changes the reason associated with the error, making the error fatal.
    pub fn reason<NewReason>(self, reason: NewReason)
        -> ParsingError<In, NewReason>
    {
        ParsingError { reason: Some(reason), rest: self.rest }
    }

    /// Makes a recoverable error fatal by giving it a reason, if it's already fatal, does nothing
    #[must_use]
    pub fn or_reason(self, reason: Reason) -> Self {
        Self { reason: self.reason.or(Some(reason)), rest: self.rest }
    }

    /// Like [`ParsingError::or_reason`] but does nothing if the rest of the input is empty
    #[must_use]
    pub fn or_reason_if_nonempty(self, reason: Reason) -> Self
    where
        In: Input,
    {
        Self {
            reason: self.reason.or_else(|| self.rest.is_empty().not().then_some(reason)),
            rest: self.rest
        }
    }

    /// Transforms the reason by calling `f`, except if it's a recoverable error,
    /// in which case it remains recoverable.
    pub fn map_reason<NewReason>(self, f: impl FnOnce(Reason) -> NewReason)
        -> ParsingError<In, NewReason>
    {
        ParsingError { reason: self.reason.map(f), rest: self.rest }
    }

    /// Changes the reason associated with error, except if it's a recoverable error,
    /// in which case it remains recoverable.
    pub fn narrow_reason<NewReason>(self, expected: NewReason)
        -> ParsingError<In, NewReason>
    {
        ParsingError { reason: self.reason.map(|_| expected), rest: self.rest }
    }

    /// Turns this error into a [`FullParsingError`] for more informative error report.
    pub fn with_src_loc<'path>(self, path: impl PathLike<'path>, input: &str)
        -> FullParsingError<'path, Reason>
    where
        In: Input,
    {
        FullParsingError {
            loc: locate_saturating(self.rest.as_ptr(), input).with_path(path),
            reason: self.reason,
        }
    }
}

/// A final error with information about where in the source did the error occur.
///
/// This should be constructed at the top-level of a parser as the final action before returning
/// the result. Main ways to construct this are [`ParsingError::with_src_loc`] and
/// [`Parser::with_full_error`]
///
/// To print the source line of the error along with the reason & location, wrap the error in
/// [`WithSourceLine`], this will alter its [`Display`] implementation.
#[derive(Debug, Clone)]
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

#[cfg(feature = "std")]
impl<Reason: Display> Display for WithSourceLine<FullParsingError<'_, Reason>> {
    fn fmt(&self, f: &mut Formatter) -> core::fmt::Result {
        if let Some(reason) = &self.0.reason {
            writeln!(f, "{reason}")?;
        }
        write!(f, "--> {}", WithSourceLine(&self.0.loc))?;
        Ok(())
    }
}

impl<Reason: Display + Debug> Error for WithSourceLine<FullParsingError<'_, Reason>> {}

impl<Reason: Error> Error for FullParsingError<'_, Reason> {}

impl<Reason> FullParsingError<'_, Reason> {
    /// Unbind the error from the lifetimes by allocating the file path if it hasn't been already.
    pub fn own(self) -> FullParsingError<'static, Reason> {
        FullParsingError { loc: self.loc.own(), ..self }
    }
}

/// The result of a parser.
pub type ParsingResult<In, T, Reason = Infallible> = core::result::Result<
    (In, T),
    ParsingError<In, Reason>,
>;

/// The core of the crate, a trait representing a function that takes some input and
/// returns either a tuple of (the rest of the input, the output) or a [`ParsingError`].
pub trait Parser<In: Input, Out, Reason = Infallible>:
    Sized + FnMut(In) -> ParsingResult<In, Out, Reason>
{
    /// Use the parser to produce the output.
    #[expect(clippy::missing_errors_doc)]
    fn parse(&mut self, input: In) -> ParsingResult<In, Out, Reason> {
        self(input)
    }

    /// Turns output into a recoverable error if the output doesn't meet a condition.
    fn filter(mut self, mut f: impl FnMut(&Out) -> bool) -> impl Parser<In, Out, Reason> {
        move |src| match self(src.clone()) {
            Ok((rest, res)) if f(&res) => Ok((rest, res)),
            Ok(_) => Err(ParsingError::new_recoverable(src)),
            Err(err) => Err(err),
        }
    }

    /// Like [`Parser::filter`], but the possible error is instead fatal, with `reason`
    // TODO: better name maybe?
    fn filter_fatal(mut self, reason: Reason, mut f: impl FnMut(&Out) -> bool)
        -> impl Parser<In, Out, Reason>
    where
        Reason: Clone,
    {
        move |src| match self(src.clone()) {
            Ok((rest, res)) if f(&res) => Ok((rest, res)),
            Ok(_) => Err(ParsingError::new(src, reason.clone())),
            Err(err) => Err(err),
        }
    }

    /// Transforms the output of the parser, if present.
    fn map<NewOut>(mut self, mut f: impl FnMut(Out) -> NewOut) -> impl Parser<In, NewOut, Reason> {
        move |src| self(src).map(map_second(&mut f))
    }

    /// Tranforms the output of the parser, if present, or try parsing the next value.
    fn maybe_map<NewOut>(mut self, mut f: impl FnMut(Out) -> Option<NewOut>)
        -> impl Parser<In, NewOut, Reason>
    {
        move |mut src| loop {
            let (rest, value) = self(take(&mut src)).map(map_second(&mut f))?;
            src = rest;
            let Some(value) = value else {
                continue;
            };
            return Ok((src, value));
        }
    }

    /// Like [`Parser::map`], but calls the provdied function using the Nightly [`FnMut::call_mut`]
    /// method, effectively spreading the output as the arguments of the function.
    ///
    /// The following nIghtly Rust code:
    /// ```ignore
    /// use shrimple_parser::Parser;
    /// parser.call(u32::pow)
    /// ```
    /// is equivalent to the following stable Rust code:
    /// ```ignore
    /// use shrimple_parser::Parser;
    /// parser.map(|(x, y)| u32::pow(x, y))
    /// ```
    /// `T` for this method is constrained not by the [`crate::Tuple`] trait, but by the unstable
    /// standard trait [`core::marker::Tuple`], which means that `T` can be a tuple of absolutely
    /// any length.
    ///
    /// See also: [`crate::call`], a macro for a stable alternative to this method.
    #[cfg(feature = "nightly")]
    fn call<F>(mut self, mut f: F) -> impl Parser<In, F::Output, Reason>
    where
        F: FnMut<Out>,
        Out: core::marker::Tuple,
    {
        move |src| self(src).map(map_second(|x| f.call_mut(x)))
    }

    /// Replaces a recoverable error with the result of `parser`.
    ///
    /// The input fed into the second parser is the rest of the input returned by the first parser.
    ///
    /// # Warning
    /// Do not use this in combination with [`Parser::iter`]; Use [`Parser::or_nonempty`]
    fn or(mut self, mut parser: impl Parser<In, Out, Reason>) -> impl Parser<In, Out, Reason> {
        move |src| match self(src) {
            Ok(res) => Ok(res),
            Err(err) if err.is_recoverable() => parser(err.rest),
            Err(err) => Err(err),
        }
    }


    /// Like [`Parser::or`], but keeps the error if the rest of the input is empty.
    /// 
    /// This allows to avoid slipping into an infinite loop, e.g. when using [`Parser::iter`]
    /// somewhere down the line.
    fn or_nonempty(mut self, mut parser: impl Parser<In, Out, Reason>)
        -> impl Parser<In, Out, Reason>
    {
        move |input| match self(input) {
            Ok(res) => Ok(res),
            Err(err) if err.is_recoverable() && !err.rest.is_empty() => parser(err.rest),
            Err(err) => Err(err),
        }
    }

    /// Replaces a recoverable error with the transformed remains of the input.
    /// If the rest of the input in the recoverable error is already empty, does nothing.
    /// The returned remains of the input are an empty string.
    fn or_map_rest(mut self, mut f: impl FnMut(In) -> Out) -> impl Parser<In, Out, Reason> {
        move |src| match self(src) {
            Ok(res) => Ok(res),
            Err(err) if err.is_recoverable() && !err.rest.is_empty() => {
                Ok((In::default(), f(err.rest)))
            }
            Err(err) => Err(err),
        }
    }

    /// Replaces a recoverable error with `value` & the rest of the input in the recoverable error.
    ///
    /// Be aware that `value` will be cloned every time it's to be returned.
    ///
    /// See [`Parser::or`], [`Parser::or_nonempty`], [`Parser::or_map_rest`].
    fn or_value(mut self, value: Out) -> impl Parser<In, Out, Reason> where Out: Clone {
        move |src| match self(src) {
            Ok(res) => Ok(res),
            Err(err) if err.is_recoverable() => Ok((err.rest, value.clone())),
            Err(err) => Err(err),
        }
    }

    /// Parses the rest of the input after the first parser, returning both outputs
    /// & short-circuiting on an error.
    ///
    /// The reason for the errors of the first parser is adapted to the one of the second parser.
    ///
    /// See also [`Parser::add`], [`Parser::and_value`].
    fn and<Other>(mut self, mut parser: impl Parser<In, Other, Reason>)
        -> impl Parser<In, (Out, Other), Reason>
    {
        move |src| {
            let (rest, out) = self(src)?;
            let (rest, new_out) = parser(rest)?;
            Ok((rest, (out, new_out)))
        }
    }

    /// Adds a value to the output of the parser
    ///
    /// Be aware that `value` will be cloned every time it's to be returned.
    ///
    /// See [`Parser::and`].
    fn and_value<Other: Clone>(mut self, value: Other) -> impl Parser<In, (Out, Other), Reason> {
        move |src| {
            let (rest, out) = self(src)?;
            Ok((rest, (out, value.clone())))
        }
    }

    /// Like [`Parser::and`], but specific to parsers that output a tuple:
    /// the new output is appended to the tuple of other tuples using the [`Tuple`] trait.
    fn add<New>(mut self, mut parser: impl Parser<In, New, Reason>)
        -> impl Parser<In, Out::Appended<New>, Reason>
    where
        Out: Tuple,
    {
        move |src| {
            let (rest, out) = self(src)?;
            let (rest, new_out) = parser(rest)?;
            Ok((rest, out.append(new_out)))
        }
    }

    /// Like [`Parser::and_value`], but specific to parsers that output a tuple:
    /// the new output is appended to the tuple of other tuples using the [`Tuple`] trait.
    fn add_value<Other: Clone>(mut self, value: Other)
        -> impl Parser<In, Out::Appended<Other>, Reason>
    where
        Out: Tuple,
    {
        move |src| {
            let (rest, out) = self(src)?;
            Ok((rest, out.append(value.clone())))
        }
    }

    /// Like [`Parser::and`], but discards the output of the first parser.
    /// The reason for the errors of the first parser is adapted to the one of the second parser.
    fn then<NewOut>(mut self, mut parser: impl Parser<In, NewOut, Reason>)
        -> impl Parser<In, NewOut, Reason>
    {
        move |src| {
            let rest = self(src)?.0;
            let (rest, out) = parser(rest)?;
            Ok((rest, out))
        }
    }

    /// Same as [`Parser::and`] but discards the output of the second parser
    /// The reason for the errors the first parser is adapted to the one of the second parser.
    fn skip<Skipped>(mut self, mut parser: impl Parser<In, Skipped, Reason>)
        -> impl Parser<In, Out, Reason>
    {
        move |src| {
            let (rest, out) = self(src)?;
            let rest = parser(rest)?.0;
            Ok((rest, out))
        }
    }

    /// Same as [`Parser::skip`] but discards the error of the second parser as well.
    ///
    /// Effectively, all this function does is advance the input to right after the second parser,
    /// if it succeeds, otherwise the input stays as if only the first parser was called.
    fn maybe_skip<Skipped, OtherReason>(mut self, mut parser: impl Parser<In, Skipped, OtherReason>)
        -> impl Parser<In, Out, Reason>
    {
        move |src| {
            let (rest, out) = self(src)?;
            let rest = parser(rest).map_or_else(|err| err.rest, first);
            Ok((rest, out))
        }
    }

    /// Sets the reason for errors returned from the parser, making all errors fatal.
    fn expect<NewReason: Clone>(mut self, expected: NewReason)
        -> impl Parser<In, Out, NewReason>
    {
        move |src| self(src).map_err(|e| e.reason(expected.clone()))
    }

    /// Makes a recoverable error fatal by giving it a reason. If the error is already fatal,
    /// nothing is changed
    fn or_reason(mut self, reason: Reason) -> impl Parser<In, Out, Reason>
    where
        Reason: Clone,
    {
        move |src| self(src).map_err(|e| e.or_reason(reason.clone()))
    }

    /// Like [`Parser::or_reason`] but does nothing if the rest of the input is empty.
    ///
    /// Be aware that `reason` is cloned every time it's to be returned.
    fn or_reason_if_nonempty(mut self, reason: Reason) -> impl Parser<In, Out, Reason>
    where
        Reason: Clone,
    {
        move |src| self(src).map_err(|e| e.or_reason_if_nonempty(reason.clone()))
    }

    /// Changes the reason from the parser, unless the error is recoverable.
    fn narrow_reason<NewReason: Clone>(mut self, expected: NewReason)
        -> impl Parser<In, Out, NewReason>
    {
        move |src| self(src).map_err(|e| e.narrow_reason(expected.clone()))
    }

    /// Adds the part of the input that was consumed by the parser to the outputs.
    ///
    /// If the input increased in length after the parser (which should not happen), an empty
    /// string is added.
    /// See also [`Parser::add_span`], which adds the span to the tuple of other outputs.
    fn get_span(self) -> impl Parser<In, (Out, In), Reason> where In: Input {
        self.map(tuple).add_span()
    }

    /// Like [`Parser::get_span`], but adds the output to the tuple of other outputs using the
    /// [`Tuple`] trait.
    fn add_span(mut self) -> impl Parser<In, Out::Appended<In>, Reason> where Out: Tuple {
        move |src| {
            let (rest, out) = self(src.clone())?;
            let end = src.len().saturating_sub(rest.len());
            let consumed = src.before(end);
            Ok((rest, out.append(consumed)))
        }
    }

    /// Adds a copy of rest of the input to the output.
    fn get_rest(self) -> impl Parser<In, (Out, In), Reason> {
        self.map(tuple).add_rest()
    }

    /// Like [`Parser::get_rest`], but adds the input to the tuple of other outputs using the
    /// [`Tuple`] trait.
    fn add_rest(mut self) -> impl Parser<In, Out::Appended<In>, Reason> where Out: Tuple {
        move |src| self(src).map(|(rest, out)| (rest.clone(), out.append(rest)))
    }

    /// Replaces a recoverable error with `None`, making the output optional.
    fn maybe(mut self) -> impl Parser<In, Option<Out>, Reason> {
        move |src| match self(src) {
            Ok((rest, out)) => Ok((rest, Some(out))),
            Err(err) if err.is_recoverable() => Ok((err.rest, None)),
            Err(err) => Err(err),
        }
    }

    /// Replaces the output with `true` and a recoverable error with `false`
    fn ok(mut self) -> impl Parser<In, bool, Reason> {
        move |src| match self(src) {
            Ok((rest, _)) => Ok((rest, true)),
            Err(err) if err.is_recoverable() => Ok((err.rest, false)),
            Err(err) => Err(err),
        }
    }

    /// Repeats the parser until a recoverable error is met, discarding all the output.
    fn repeat(mut self)  -> impl Parser<In, (), Reason> {
        move |mut src| loop {
            match self(src) {
                Ok((rest, _)) => src = rest,
                Err(err) if err.is_recoverable() => return Ok((err.rest, ())),
                Err(err) => return Err(err),
            }
        }
    }

    /// Prints the output using its `Debug` implementation & the first 16 bytes of the rest of the
    /// input, all along with a custom provided message.
    fn dbg(mut self, label: impl Display) -> impl Parser<In, Out, Reason>
    where
        In: Input,
        Out: Debug,
    {
        move |src| {
            let (rest, out) = self(src)?;
            println!("{label}: {out:?} : {}...", &rest[.. min(rest.len(), 16)].escape_debug());
            Ok((rest, out))
        }
    }

    /// Turns the parser into an iterator that yields output until the first recoverable error.
    /// If an error is yielded from the iterator, it's guaranteed to be fatal.
    fn iter(self, input: In) -> Iter<In, Out, Reason, Self> {
        Iter { input: Some(input), parser: self, _params: PhantomData }
    }

    /// Aaugments the parsing error, if present, with location in the `input`.
    /// `path` is the reported path to the file where the error occured.
    /// Note that the `input` passed here is only used for error reporting, not as the input to the
    /// parser.
    fn with_full_error<'path>(mut self, path: impl PathLike<'path>, full_src: &str)
        -> impl FnOnce(In)
        -> Result<(In, Out), FullParsingError<'path, Reason>>
    where
        In: Input
    {
        move |src| self(src).map_err(|e| e.with_src_loc(path, full_src))
    }
}

impl<In, Out, Reason, F> Parser<In, Out, Reason> for F
where
    In: Input,
    F: FnMut(In) -> ParsingResult<In, Out, Reason>,
{}

/// Iterator returned by [`Parser::iter`]
pub struct Iter<In, Out, Reason, P> {
    input: Option<In>,
    parser: P,
    _params: PhantomData<(Out, Reason)>
}

impl<In, Out, Reason, P> Iterator for Iter<In, Out, Reason, P>
where
    In: Input,
    P: Parser<In, Out, Reason>,
{
    type Item = Result<Out, ParsingError<In, Reason>>;

    fn next(&mut self) -> Option<Self::Item> {
        let input = self.input.take()?;
        match (self.parser)(input) {
            Ok((rest, res)) => {
                self.input = Some(rest);
                Some(Ok(res))
            }
            Err(err) if err.is_recoverable() => None,
            Err(err) => Some(Err(err)),
        }
    }
}

impl<In, Out, Reason, P> FusedIterator for Iter<In, Out, Reason, P>
where
    In: Input,
    P: Parser<In, Out, Reason>,
{}

impl<In, Out, Reason, P> Iter<In, Out, Reason, P>
where
    In: Input,
    P: Parser<In, Out, Reason>,
{
    /// Returned the part of the input that hasn't been processed by the parser yet.
    pub const fn remainder(&self) -> Option<&In> {
        self.input.as_ref()
    }
}

/// Parses any 1 character from the input.
///
/// # Errors
/// Returns a recoverable error if the input is empty.
pub fn parse_char<In: Input, Reason>(input: In) -> ParsingResult<In, char, Reason> {
    match input.chars().next() {
        Some(ch) => Ok((input.before(ch.len_utf8()), ch)),
        None => Err(ParsingError::new_recoverable(input)),
    }
}
