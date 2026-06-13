//! A collection of fundamental parsers to build out your own.

use {
    crate::{
        error::{FullParsingError, ParsingError, ParsingResult},
        input::Input,
        pattern::{IntoPattern, Pattern},
        tuple::{Tuple, first, map_second, tuple},
        utils::PathLike,
    },
    std::{
        convert::Infallible,
        fmt::{Debug, Display},
        iter::FusedIterator,
        marker::PhantomData,
        mem::replace,
    },
};

/// A trait alias for a function that maps from the input & intermediate output to the rest of the
/// input & a different output.
///
/// Used in [`Parser::map`].
///
/// See [`match_out`] for a convenient way to create such a mapper.
pub trait MappingParser<In, Out, NewOut, Reason = Infallible>:
    Sized + FnMut(In, Out) -> ParsingResult<In, NewOut, Reason>
{
}

impl<In, Out, NewOut, Reason, F> MappingParser<In, Out, NewOut, Reason> for F where
    F: Sized + FnMut(In, Out) -> ParsingResult<In, NewOut, Reason>
{
}

/// A trait representing a function that takes some string-like input and
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
    fn filter_fatal(
        mut self,
        reason: Reason,
        mut f: impl FnMut(&Out) -> bool,
    ) -> impl Parser<In, Out, Reason>
    where
        Reason: Clone,
    {
        move |src| match self(src.clone()) {
            Ok((rest, res)) if f(&res) => Ok((rest, res)),
            Ok(_) => Err(ParsingError::new(src, reason.clone())),
            Err(err) => Err(err),
        }
    }

    /// Changes the error reason by passing it through `f`.
    fn map_reason<NewReason>(
        mut self,
        mut f: impl FnMut(Reason) -> NewReason,
    ) -> impl Parser<In, Out, NewReason> {
        move |src| self(src).map_err(|e| e.map_reason(&mut f))
    }

    /// Converts the reason, if present, to another type using the [`From`] trait.
    fn adapt_reason<NewReason>(mut self) -> impl Parser<In, Out, NewReason>
    where
        Infallible: From<Reason>,
    {
        move |i| self(i).map_err(ParsingError::adapt_reason)
    }

    /// Transforms the input & the output of the parser, if present.
    ///
    /// The argument is a function that maps the input & the current output of the parser to the
    /// rest of the input & the new output.
    ///
    /// See [`crate::match_out`]
    fn map<NewOut>(
        mut self,
        mut parser: impl MappingParser<In, Out, NewOut, Reason>,
    ) -> impl Parser<In, NewOut, Reason> {
        move |src| self(src).and_then(|(i, o)| parser(i, o))
    }

    /// Like [`Parser::map`], but only maps the current output, if present.
    fn map_out<NewOut>(
        mut self,
        mut f: impl FnMut(Out) -> NewOut,
    ) -> impl Parser<In, NewOut, Reason> {
        move |src| self(src).map(map_second(&mut f))
    }

    /// Tranforms the output of the parser, if present, or try parsing the next value.
    fn map_until<NewOut>(
        mut self,
        mut f: impl FnMut(Out) -> Option<NewOut>,
    ) -> impl Parser<In, NewOut, Reason> {
        move |mut src| {
            let end = src.clone().end();
            loop {
                let (rest, value) = self(replace(&mut src, end.clone())).map(map_second(&mut f))?;
                src = rest;
                let Some(value) = value else {
                    continue;
                };
                return Ok((src, value));
            }
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
        move |src| {
            let fallback = src.clone();
            match self(src) {
                Ok(res) => Ok(res),
                Err(err) if err.is_recoverable() => parser(fallback),
                Err(err) => Err(err),
            }
        }
    }

    /// Like [`Parser::or`], but keeps the error if the rest of the input is empty.
    ///
    /// This allows to avoid slipping into an infinite loop, e.g. when using [`Parser::iter`]
    /// somewhere down the line.
    fn or_nonempty(
        mut self,
        mut parser: impl Parser<In, Out, Reason>,
    ) -> impl Parser<In, Out, Reason> {
        move |src| {
            let fallback = src.clone();
            match self(src) {
                Ok(res) => Ok(res),
                Err(err) if err.is_recoverable() && !err.rest.is_empty() => parser(fallback),
                Err(err) => Err(err),
            }
        }
    }

    /// Replaces a recoverable error with the transformed remains of the input.
    /// If the rest of the input in the recoverable error is already empty, does nothing.
    /// The returned remains of the input are is an empty string that points to the end of the
    /// input.
    fn or_map_rest(mut self, mut f: impl FnMut(In) -> Out) -> impl Parser<In, Out, Reason> {
        move |src| {
            let fallback = src.clone();
            match self(src) {
                Ok(res) => Ok(res),
                Err(err) if err.is_recoverable() && !err.rest.is_empty() => {
                    Ok((fallback.clone().end(), f(fallback)))
                }
                Err(err) => Err(err),
            }
        }
    }

    /// Replaces a recoverable error with `value` & the rest of the input in the recoverable error.
    ///
    /// Be aware that `value` will be cloned every time it's to be returned.
    ///
    /// See [`Parser::or`], [`Parser::or_nonempty`], [`Parser::or_map_rest`].
    fn or_value(mut self, value: Out) -> impl Parser<In, Out, Reason>
    where
        Out: Clone,
    {
        move |src| {
            let fallback = src.clone();
            match self(src) {
                Ok(res) => Ok(res),
                Err(err) if err.is_recoverable() => Ok((fallback, value.clone())),
                Err(err) => Err(err),
            }
        }
    }

    /// Parses the rest of the input after the first parser, returning both outputs
    /// & short-circuiting on an error.
    ///
    /// The reason for the errors of the first parser is adapted to the one of the second parser.
    ///
    /// See also [`Parser::add`], [`Parser::and_value`].
    fn and<Other>(
        mut self,
        mut parser: impl Parser<In, Other, Reason>,
    ) -> impl Parser<In, (Out, Other), Reason> {
        move |src| {
            let (rest, out) = self(src.clone())?;
            match parser(rest) {
                Ok((rest, new_out)) => Ok((rest, (out, new_out))),
                Err(mut err) => {
                    if err.is_recoverable() {
                        err.rest = src;
                    }
                    Err(err)
                }
            }
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
    fn add<New>(
        mut self,
        mut parser: impl Parser<In, New, Reason>,
    ) -> impl Parser<In, Out::Appended<New>, Reason>
    where
        Out: Tuple,
    {
        move |src| {
            let (rest, out) = self(src.clone())?;
            match parser(rest) {
                Ok((rest, new_out)) => Ok((rest, out.append(new_out))),
                Err(mut err) => {
                    if err.is_recoverable() {
                        err.rest = src;
                    }
                    Err(err)
                }
            }
        }
    }

    /// Like [`Parser::and_value`], but specific to parsers that output a tuple:
    /// the new output is appended to the tuple of other tuples using the [`Tuple`] trait.
    fn add_value<Other: Clone>(
        mut self,
        value: Other,
    ) -> impl Parser<In, Out::Appended<Other>, Reason>
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
    fn then<NewOut>(
        mut self,
        mut parser: impl Parser<In, NewOut, Reason>,
    ) -> impl Parser<In, NewOut, Reason> {
        move |src| {
            let rest = self(src.clone())?.0;
            parser(rest).map_err(|mut err| {
                if err.is_recoverable() {
                    err.rest = src;
                }
                err
            })
        }
    }

    /// Same as [`Parser::and`] but discards the output of the second parser.
    ///
    /// Effectively, all this function does is advance the input to right after the second parser,
    /// if it succeeds, otherwise the input stays as if only the first parser was called.
    fn skip<Skipped>(
        mut self,
        mut parser: impl Parser<In, Skipped, Reason>,
    ) -> impl Parser<In, Out, Reason> {
        move |src| {
            let (rest, out) = self(src.clone())?;
            match parser(rest) {
                Ok((rest, _)) => Ok((rest, out)),
                Err(mut err) => {
                    if err.is_recoverable() {
                        err.rest = src;
                    }
                    Err(err)
                }
            }
        }
    }

    /// Sets the reason for errors returned from the parser, making all errors fatal.
    fn expect<NewReason: Clone>(mut self, expected: NewReason) -> impl Parser<In, Out, NewReason> {
        move |src| self(src).map_err(|e| e.reason(expected.clone()))
    }

    /// Makes a recoverable error fatal by giving it a reason. If the error is already fatal,
    /// nothing is changed.
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

    /// Adds the part of the input that was consumed by the parser to the outputs.
    ///
    /// If the input increased in length after the parser (which should not happen), an empty
    /// string is added.
    /// See also [`Parser::add_span`], which adds the span to the tuple of other outputs.
    fn and_span(self) -> impl Parser<In, (Out, In), Reason> {
        self.map_out(tuple).add_span()
    }

    /// Like [`Parser::and_span`], but adds the output to the tuple of other outputs using the
    /// [`Tuple`] trait.
    fn add_span(mut self) -> impl Parser<In, Out::Appended<In>, Reason>
    where
        Out: Tuple,
    {
        move |src| {
            let (rest, out) = self(src.clone())?;
            let end = src.len().saturating_sub(rest.len());
            let consumed = src.before(end);
            Ok((rest, out.append(consumed)))
        }
    }

    /// Adds a copy of rest of the input to the output.
    fn and_rest(self) -> impl Parser<In, (Out, In), Reason> {
        self.map_out(tuple).add_rest()
    }

    /// Like [`Parser::get_rest`], but adds the input to the tuple of other outputs using the
    /// [`Tuple`] trait.
    fn add_rest(mut self) -> impl Parser<In, Out::Appended<In>, Reason>
    where
        Out: Tuple,
    {
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

    /// Repeats the parser until an error is met, discarding all the output.
    fn repeat(mut self) -> impl Parser<In, (), Reason> {
        move |mut src| loop {
            match self(src) {
                Ok((rest, _)) => src = rest,
                Err(err) if err.is_recoverable() => return Ok((err.rest, ())),
                Err(err) => return Err(err),
            }
        }
    }

    /// Applies the parser repeatedly, collecting the output into a collection, until an error is
    /// met.
    fn collect<C: Default + Extend<Out>>(mut self) -> impl Parser<In, C, Reason> {
        move |mut src| {
            let mut res = C::default();
            loop {
                match self(src) {
                    Ok((rest, new)) => {
                        res.extend([new]);
                        src = rest;
                    }
                    Err(err) if err.is_recoverable() => return Ok((err.rest, res)),
                    Err(err) => return Err(err),
                }
            }
        }
    }

    /// Prints the output using its `Debug` implementation & the first 16 bytes of the rest of the
    /// input, all along with a custom provided message.
    fn dbg(mut self, label: impl Display) -> impl Parser<In, Out, Reason>
    where
        In: Input,
        Out: Debug,
        Reason: Debug,
    {
        move |src| match self(src) {
            Ok((rest, out)) => {
                let until = rest.char_indices().nth(16).map_or(rest.len(), |x| x.0);
                let r = &rest[..until].escape_debug();
                eprintln!("{label}: Ok({out:?}) : {r}...");
                Ok((rest, out))
            }
            Err(err) => {
                let until = err
                    .rest
                    .char_indices()
                    .nth(16)
                    .map_or(err.rest.len(), |x| x.0);
                let r = &err.rest[..until].escape_debug();
                eprintln!("{label}: Err({:?}) : {r}...", err.reason);
                Err(err)
            }
        }
    }

    /// Turns the parser into an iterator that yields output until the first recoverable error.
    /// If an error is yielded from the iterator, it's guaranteed to be fatal.
    fn iter(self, input: In) -> Iter<In, Out, Reason, Self> {
        Iter {
            input: Some(input),
            parser: self,
            _params: PhantomData,
        }
    }

    /// Augments the parsing error, if present, with location in the `input`.
    /// `path` is the reported path to the file where the error occured.
    /// Note that the `input` passed here is only used for error reporting, not as the input to the
    /// parser.
    fn with_full_error<'a>(
        mut self,
        path: impl PathLike<'a>,
        full_src: &'a str,
    ) -> impl FnOnce(In) -> Result<(In, Out), FullParsingError<'a, Reason>>
    where
        In: Input,
    {
        move |src| self(src).map_err(|e| e.with_src_loc(path, full_src))
    }
}

impl<In, Out, Reason, F> Parser<In, Out, Reason> for F
where
    In: Input,
    F: FnMut(In) -> ParsingResult<In, Out, Reason>,
{
}

/// Iterator returned by [`Parser::iter`]
pub struct Iter<In, Out, Reason, P> {
    input: Option<In>,
    parser: P,
    _params: PhantomData<(Out, Reason)>,
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
{
}

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

/// Returns a parser that always returns the provided value.
///
/// Beware that the value is always cloned.
pub fn ready<In: Input, T: Clone, Reason>(value: T) -> impl Parser<In, T, Reason> {
    move |i| Ok((i, value.clone()))
}

/// Parses 1 instance of pattern `pat`.
///
/// # Errors
/// The returned parser returns a recoverable error if the pattern didn't match at the beginning of
/// the input.
pub fn one<In: Input, Reason>(pat: impl IntoPattern) -> impl Parser<In, In, Reason> {
    let pat = pat.into_pattern();
    move |input| {
        pat.immediate_match(input)
            .map_err(ParsingError::new_recoverable)
    }
}

/// Parses contiguous instances of pattern `pat`.
///
/// The returned parser never returns an error, if no matches are found at the start of the input,
/// the returned string is empty (but also points to the start of the input)
///
/// See also [`until`], [`until_ex`].
pub fn many<In: Input, Reason>(pat: impl IntoPattern) -> impl Parser<In, In, Reason> {
    let pat = pat.into_pattern();
    move |input| Ok(pat.immediate_matches(input))
}

/// Parses a span of the input until a match of pattern `pat` is met.
///
/// The returned rest of the input will still have the match.
///
/// The returned parser never returns an error, if `pred` returns `false` for all the characters
/// in the input, then the output is the entire input, and the rest of the input is an empty string.
///
/// See also [`many`], [`until_ex`].
pub fn until<In: Input, Reason>(pat: impl IntoPattern) -> impl Parser<In, In, Reason> {
    let pat = pat.into_pattern();
    move |input| {
        let input_len = input.len();
        Ok({
            pat.first_match(input)
                .map_or_else(|input| input.split_at(input_len).rev(), map_second(first))
        })
    }
}

/// Like [`until`], but also removes the match of `pat` from the rest of the input.
///
/// # Errors
/// Unlike [`until`], this parser returns a recoverable error if `pred` returned `false` for
/// all the characters in the input.
pub fn until_ex<In: Input, Reason>(pat: impl IntoPattern) -> impl Parser<In, In, Reason> {
    let pat = pat.into_pattern();
    move |input| {
        pat.first_match_ex(input)
            .map(map_second(first))
            .map_err(ParsingError::new_recoverable)
    }
}

/// Parse a balanced group of `open` & `close` patterns.
///
/// The start & end of the group are <u>included</u> in the output.
/// See [`group_ex`] for a parser that excludes them.
///
/// # Errors
/// - If no initial `open` was found, a recoverable error is returned.
/// - If the end was reached before a matching `close` pattern, a fatal error is returned.
///
/// An example use of this is parsing balanced parentheses:
/// ```rust
/// # fn main() {
/// use shrimple_parser::{parser::group, ParsingError};
/// let src = "(foo ()) bar";
/// assert_eq!(group('(', ')')(src), Ok((" bar", "(foo ())")));
///
/// let src = "(oops";
/// assert_eq!(group('(', ')')(src), Err(ParsingError::new("oops", ())));
/// # }
/// ```
pub fn group<In: Input>(open: impl IntoPattern, close: impl Pattern) -> impl Parser<In, In, ()> {
    let open = open.into_pattern();
    let close = close.into_pattern();
    move |input| {
        let Ok((mut rest, _)) = open.immediate_match(&*input) else {
            return Err(ParsingError::new_recoverable(input));
        };
        let mut nesting = 1;
        while nesting > 0 {
            let (after_open, (before_open, open)) =
                open.first_match_ex(rest).unwrap_or(("", (rest, "")));
            let (after_close, (before_close, close)) =
                close.first_match_ex(rest).unwrap_or(("", (rest, "")));

            if [open, close] == ["", ""] {
                // neither `open` nor `close` matched, and nesting > 0
                let rest_start = input.len() - rest.len();
                return Err(ParsingError::new(input.after(rest_start), ()));
            }

            if before_open.len() < before_close.len() {
                rest = after_open;
                nesting += 1;
            } else {
                rest = after_close;
                nesting -= 1;
            }
        }

        let res_len = input.len() - rest.len();
        Ok(input.split_at(res_len).rev())
    }
}

/// Parse a balanced group of `open` & `close` patterns.
///
/// The start & end of the group are <u>excluded</u> in the output.
/// See [`group`] for a parser that includes them.
///
/// # Errors
/// - If no initial `open` was found, a recoverable error is returned.
/// - If the end was reached before a matching `close` pattern, a fatal error is returned.
///
/// An example use of this is parsing balanced parentheses:
/// ```rust
/// # fn main() {
/// use shrimple_parser::{parser::group_ex, ParsingError};
/// let src = "(foo ()) bar";
/// assert_eq!(group_ex('(', ')')(src), Ok((" bar", "foo ()")));
///
/// let src = "(oops";
/// assert_eq!(group_ex('(', ')')(src), Err(ParsingError::new("oops", ())));
/// # }
/// ```
pub fn group_ex<In: Input>(
    open: impl IntoPattern,
    close: impl IntoPattern,
) -> impl Parser<In, In, ()> {
    let open = open.into_pattern();
    let close = close.into_pattern();

    move |input| {
        let input = match open.immediate_match(input) {
            Ok((rest, _)) => rest,
            Err(input) => return Err(ParsingError::new_recoverable(input)),
        };
        let mut rest = &*input;
        let mut nesting = 1;
        let mut close_len = 0;
        while nesting > 0 {
            let (after_open, (before_open, open)) =
                open.first_match_ex(rest).unwrap_or(("", (rest, "")));
            let (after_close, (before_close, close)) =
                close.first_match_ex(rest).unwrap_or(("", (rest, "")));

            if [open, close] == ["", ""] {
                // neither `open` nor `close` matched, and nesting > 0
                let rest_start = input.len() - rest.len();
                return Err(ParsingError::new(input.after(rest_start), ()));
            }

            if before_open.len() < before_close.len() {
                rest = after_open;
                nesting += 1;
            } else {
                rest = after_close;
                close_len = close.len();
                nesting -= 1;
            }
        }

        let res_len = input.len() - rest.len() - close_len;
        Ok(input
            .split_at(res_len)
            .map_second(|rest| rest.after(close_len))
            .rev())
    }
}
