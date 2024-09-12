//! Abstractions for working with patterns.

use {
    crate::{tuple::{first, map_second, Tuple}, Input, Parser, ParsingError},
    core::ops::Not,
};

/// This trait represents an object that can be matched onto a string.
/// This includes functions, characters, [arrays of] characters, strings, but also custom patterns
/// like [`NotEscaped`]
pub trait Pattern {
    /// The return values are (rest of the input, matched fragment at the beginning).
    ///
    /// # Errors
    /// In the case of no match, the original `input` is returned as the [`Err`] variant.
    ///
    /// Used by [`parse`].
    fn immediate_match<I: Input>(&self, input: I) -> Result<(I, I), I>;

    /// The return values are (rest of the input, contiguous matched fragments from the beginning).
    ///
    /// 0 is also a valid number of matches.
    ///
    /// Used by [`parse_while`]
    #[expect(clippy::unwrap_used, reason = "this will only panic if the pattern does")]
    fn immediate_matches<I: Input>(&self, input: I) -> (I, I) {
        let mut rest = Some(input.clone());
        let rest_ptr = loop {
            match self.immediate_match(rest.take().unwrap()) {
                Ok((x, _)) => rest = Some(x),
                Err(x) => break x.as_ptr(),
            }
        };
        let input_ptr = input.as_ptr();
        input.split_at(rest_ptr as usize - input_ptr as usize).rev()
    }

    /// Like [`Pattern::immediate_matches`], but also counts the number of matches.
    ///
    /// Used by the [`Pattern`] impl of [`NotEscaped`]
    #[expect(clippy::unwrap_used, reason = "this will only panic if the pattern does")]
    fn immediate_matches_counted<I: Input>(&self, input: I) -> (I, (I, usize)) {
        let mut rest = Some(input.clone());
        let mut n = 0;
        let rest_ptr = loop {
            match self.immediate_match(rest.take().unwrap()) {
                Ok((x, _)) => {
                    rest = Some(x);
                    n += 1;
                }
                Err(x) => break x.as_ptr(),
            }
        };
        let input_ptr = input.as_ptr();
        input.split_at(rest_ptr as usize - input_ptr as usize).rev().map_second(|s| (s, n))
    }

    /// Like [`Pattern::immediate_match`], but matches at the end of `input`.
    /// The return values are (the input before the match, the match)
    ///
    /// # Errors
    /// In the case of no match, the original `input` is returned as the [`Err`] variant.
    ///
    /// Used by the [`Pattern`] impl of [`NotEscaped`]
    fn trailing_match<I: Input>(&self, input: I) -> Result<(I, I), I>;

    /// Like [`Pattern::immediate_matches_counted`], but matches at the end of `input`,
    /// and doesn't return the matched fragment of the input.
    ///
    /// Used by the [`Pattern`] impl of [`NotEscaped`]
    #[expect(clippy::unwrap_used, reason = "this will only panic if the pattern does")]
    fn trailing_matches_counted<I: Input>(&self, input: I) -> (I, usize) {
        let mut rest = Some(input);
        let mut n = 0;
        loop {
            match self.trailing_match(rest.take().unwrap()) {
                Ok((before, _)) => {
                    rest = Some(before);
                    n += 1;
                }
                Err(rest) => break (rest, n),
            }
        }
    }

    /// The return values are (the match + rest of the input, (string before the match, the match)).
    ///
    /// # Errors
    /// Returns the provided `input` unchanged in the [`Err`] variant if there's no match.
    ///
    /// Used by [`parse_until`].
    fn first_match<I: Input>(&self, input: I) -> Result<(I, (I, I)), I>;

    /// Like [`Pattern::first_match`], but the match is excluded from the rest of the input.
    ///
    /// # Errors
    /// Returns the provided `input` unchanged in the [`Err`] variant if there's no match.
    ///
    /// Used by [`parse_until_ex`].
    fn first_match_ex<I: Input>(&self, input: I) -> Result<(I, (I, I)), I>;

    /// Get the pattern by reference to avoid moving it, which will happen in generic code
    ///
    /// Do not override this method.
    fn by_ref(&self) -> impl Pattern + Copy {
        #[repr(transparent)]
        struct Ref<'this, T: ?Sized>(&'this T);

        impl<T: ?Sized> Clone for Ref<'_, T> {
            fn clone(&self) -> Self { *self }
        }

        impl<T: ?Sized> Copy for Ref<'_, T> {}

        impl<T: Pattern + ?Sized> Pattern for Ref<'_, T> {
            fn immediate_match<I: Input>(&self, input: I) -> Result<(I, I), I> {
                T::immediate_match(self.0, input)
            }

            fn immediate_matches<I: Input>(&self, input: I) -> (I, I) {
                T::immediate_matches(self.0, input)
            }

            fn immediate_matches_counted<I: Input>(&self, input: I) -> (I, (I, usize)) {
                T::immediate_matches_counted(self.0, input)
            }

            fn trailing_match<I: Input>(&self, input: I) -> Result<(I, I), I> {
                T::trailing_match(self.0, input)
            }

            fn trailing_matches_counted<I: Input>(&self, input: I) -> (I, usize) {
                T::trailing_matches_counted(self.0, input)
            }

            fn first_match<I: Input>(&self, input: I) -> Result<(I, (I, I)), I> {
                T::first_match(self.0, input)
            }

            fn first_match_ex<I: Input>(&self, input: I) -> Result<(I, (I, I)), I> {
                T::first_match_ex(self.0, input)
            }
        }

        Ref(self)
    }
}

impl<F: Fn(&char) -> bool> Pattern for F {
    fn immediate_match<I: Input>(&self, input: I) -> Result<(I, I), I> {
        match input.chars().next().filter(self) {
            Some(c) => Ok(input.split_at(c.len_utf8()).rev()),
            None => Err(input),
        }
    }

    fn immediate_matches<I: Input>(&self, input: I) -> (I, I) {
        let mid = input.find(|c| !self(&c)).unwrap_or(input.len());
        input.split_at(mid).rev()
    }

    fn immediate_matches_counted<I: Input>(&self, input: I) -> (I, (I, usize)) {
        let mut char_index = 0;
        let byte_index = input.char_indices()
            .inspect(|_| char_index += 1)
            .find_map(|(bi, c)| self(&c).not().then_some(bi))
            .inspect(|_| char_index -= 1)
            .unwrap_or(input.len());
        input.split_at(byte_index).rev().map_second(|s| (s, char_index))
    }

    fn trailing_match<I: Input>(&self, input: I) -> Result<(I, I), I> {
        match input.strip_suffix(|c| self(&c)).map(str::len) {
            Some(len) => Ok(input.split_at(len)),
            None => Err(input),
        }
    }

    fn first_match<I: Input>(&self, input: I) -> Result<(I, (I, I)), I> {
        match input.char_indices().find(|(_, c)| self(c)) {
            Some((at, ch)) => {
                let (before, after) = input.split_at(at);
                let r#match = after.clone().before(ch.len_utf8());
                Ok((after, (before, r#match)))
            }
            None => Err(input),
        }
    }

    fn first_match_ex<I: Input>(&self, input: I) -> Result<(I, (I, I)), I> {
        match input.char_indices().find(|(_, c)| self(c)) {
            Some((at, ch)) => {
                let (before, after) = input.split_at(at);
                let (r#match, after) = after.split_at(ch.len_utf8());
                Ok((after, (before, r#match)))
            }
            None => Err(input),
        }
    }
}

impl Pattern for &str {
    fn immediate_match<I: Input>(&self, input: I) -> Result<(I, I), I> {
        if input.starts_with(*self) {
            Ok(input.split_at(self.len()).rev())
        } else {
            Err(input)
        }
    }

    fn immediate_matches<I: Input>(&self, input: I) -> (I, I) {
        let rest_len = input.trim_start_matches(self).len();
        let input_len = input.len();
        input.split_at(input_len - rest_len).rev()
    }

    fn immediate_matches_counted<I: Input>(&self, input: I) -> (I, (I, usize)) {
        self.immediate_matches(input)
            .map_second(|s| (s.len().checked_div(self.len()).unwrap_or(0), s).rev())
    }

    fn trailing_match<I: Input>(&self, input: I) -> Result<(I, I), I> {
        if input.ends_with(self) {
            let mid = input.len() - self.len();
            Ok(input.split_at(mid))
        } else {
            Err(input)
        }
    }

    fn trailing_matches_counted<I: Input>(&self, input: I) -> (I, usize) {
        let trimmed_len = input.trim_end_matches(self).len();
        let input_len = input.len();
        (input.before(trimmed_len), (input_len - trimmed_len) / self.len())
    }

    fn first_match<I: Input>(&self, input: I) -> Result<(I, (I, I)), I> {
        match input.find(*self) {
            Some(at) => {
                let (before, after) = input.split_at(at);
                let r#match = after.clone().before(self.len());
                Ok((after, (before, r#match)))
            }
            None => Err(input),
        }
    }

    fn first_match_ex<I: Input>(&self, input: I) -> Result<(I, (I, I)), I> {
        match input.find(*self) {
            Some(at) => {
                let (before, after) = input.split_at(at);
                let (r#match, after) = after.split_at(self.len());
                Ok((after, (before, r#match)))
            }
            None => Err(input),
        }
    }
}

impl Pattern for char {
    fn immediate_match<I: Input>(&self, input: I) -> Result<(I, I), I> {
        if input.starts_with(*self) {
            Ok(input.split_at(self.len_utf8()).rev())
        } else {
            Err(input)
        }
    }

    fn immediate_matches<I: Input>(&self, input: I) -> (I, I) {
        let rest_len = input.trim_start_matches(*self).len();
        let input_len = input.len();
        input.split_at(input_len - rest_len).rev()
    }

    fn immediate_matches_counted<I: Input>(&self, input: I) -> (I, (I, usize)) {
        self.immediate_matches(input)
            .map_second(|s| (s.len() / self.len_utf8(), s).rev())
    }

    fn trailing_match<I: Input>(&self, input: I) -> Result<(I, I), I> {
        if input.ends_with(*self) {
            let mid = input.len() - self.len_utf8();
            Ok(input.split_at(mid))
        } else {
            Err(input)
        }
    }

    fn trailing_matches_counted<I: Input>(&self, input: I) -> (I, usize) {
        let trimmed_len = input.trim_end_matches(*self).len();
        let input_len = input.len();
        (input.before(trimmed_len), (input_len - trimmed_len) / self.len_utf8())
    }

    fn first_match<I: Input>(&self, input: I) -> Result<(I, (I, I)), I> {
        match input.find(*self) {
            Some(at) => {
                let (before, after) = input.split_at(at);
                let r#match = after.clone().before(self.len_utf8());
                Ok((after, (before, r#match)))
            }
            None => Err(input),
        }
    }

    fn first_match_ex<I: Input>(&self, input: I) -> Result<(I, (I, I)), I> {
        match input.find(*self) {
            Some(at) => {
                let (before, after) = input.split_at(at);
                let (r#match, after) = after.split_at(self.len_utf8());
                Ok((after, (before, r#match)))
            }
            None => Err(input),
        }
    }
}

/// Pattern that matches pattern `Inner` not escaped by `Prefix`.
/// "escaped" here means that the pattern `Inner` is preceded by an odd number
/// of contiguous `Prefix`es.
///
/// For example, for a pattern `NotEscaped('\', '0')`, the strings "0", "\\0" & "\\\\\\0" will have
/// a match, but the strings "\0", "\\ \0" & "\\\\\\\0" won't.
pub struct NotEscaped<Prefix, Inner>(pub Prefix, pub Inner);

impl<Prefix: Pattern, Inner: Pattern> Pattern for NotEscaped<Prefix, Inner> {
    fn immediate_match<I: Input>(&self, input: I) -> Result<(I, I), I> {
        self.1.immediate_match(input)
    }

    fn trailing_match<I: Input>(&self, input: I) -> Result<(I, I), I> {
        let (rest, r#match) = self.1.trailing_match(input.clone())?;
        let (rest, n_prefixes) = self.0.trailing_matches_counted(rest);
        (n_prefixes % 2 == 0).then_some((rest, r#match)).ok_or(input)
    }

    fn trailing_matches_counted<I: Input>(&self, input: I) -> (I, usize) {
        let (rest, n) = self.1.trailing_matches_counted(input);
        if n == 0 {
            return (rest, 0);
        }
        let no_1st_prefix = match self.0.trailing_match(rest.clone()) {
            Ok((x, _)) => x,
            Err(rest) => return (rest, n),
        };
        let (_, n_prefixes_minus_one) = self.0.trailing_matches_counted(no_1st_prefix.clone());
        if n_prefixes_minus_one % 2 != 0 {
            (rest, n)
        } else {
            (no_1st_prefix, n - 1)
        }
    }

    fn first_match<I: Input>(&self, input: I) -> Result<(I, (I, I)), I> {
        let mut rest = input.clone();
        while !rest.is_empty() {
            let (before, r#match);
            (rest, (before, r#match)) = self.1.first_match(rest)?;
            let before = match self.0.trailing_match(before) {
                Ok((x, _)) => x,
                Err(before) => return Ok((rest, (before, r#match))),
            };
            let (before, n_prefixes_minus_one) = self.0.trailing_matches_counted(before);
            if n_prefixes_minus_one % 2 != 0 {
                return Ok((rest, (before, r#match)));
            }
        }
        Err(input)
    }

    fn first_match_ex<I: Input>(&self, input: I) -> Result<(I, (I, I)), I> {
        let mut rest = input.clone();
        loop {
            let (before, r#match);
            (rest, (before, r#match)) = self.1.first_match_ex(rest)?;
            let Ok((before, _)) = self.0.trailing_match(before) else {
                let index = r#match.as_ptr() as usize - input.as_ptr() as usize;
                let before = input.before(index);
                return Ok((rest, (before, r#match)))
            };
            let (_, n_prefixes_minus_one) = self.0.trailing_matches_counted(before);
            if n_prefixes_minus_one % 2 != 0 {
                let index = r#match.as_ptr() as usize - input.as_ptr() as usize;
                let before = input.before(index);
                return Ok((rest, (before, r#match)));
            }
        }
    }
}

/// A pattern that matches anything.
pub struct AnyChar;

impl Pattern for AnyChar {
    fn immediate_match<I: Input>(&self, input: I) -> Result<(I, I), I> {
        match input.chars().next() {
            Some(ch) => Ok(input.split_at(ch.len_utf8()).rev()),
            None => Err(input)
        }
    }

    fn trailing_match<I: Input>(&self, input: I) -> Result<(I, I), I> {
        match input.chars().next_back() {
            Some(ch) => Ok(input.split_at(ch.len_utf8())),
            None => Err(input),
        }
    }

    fn first_match<I: Input>(&self, input: I) -> Result<(I, (I, I)), I> {
        Ok((input.clone(), (I::default(), input)))
    }

    fn first_match_ex<I: Input>(&self, input: I) -> Result<(I, (I, I)), I> {
        Ok((I::default(), (I::default(), input)))
    }
}

/// Parses 1 instance of pattern `pat`.
///
/// # Errors
/// The returned parser returns a recoverable error if the pattern didn't match at the beginning of
/// the input.
pub fn parse<In: Input>(pat: impl Pattern) -> impl Parser<In, In> {
    move |input| pat.immediate_match(input).map_err(ParsingError::new_recoverable)
}

/// Parses contiguous instances of pattern `pat`.
///
/// The returned parser never returns an error, if no matches are found at the start of the input,
/// the returned string is empty (but also points to the start of the input)
///
/// See also [`parse_until`], [`parse_until_ex`].
pub fn parse_while<In: Input>(pat: impl Pattern) -> impl Parser<In, In> {
    move |input| Ok(pat.immediate_matches(input))
}

/// Parses a span of the input until a match of pattern `pat` is met.
///
/// The returned rest of the input will still have the match.
///
/// The returned parser never returns an error, if `pred` returns `false` for all the characters
/// in the input, then the output is the entire input, and the rest of the input is an empty string.
///
/// See also [`parse_while`], [`parse_until_ex`].
pub fn parse_until<In: Input>(pat: impl Pattern) -> impl Parser<In, In> {
    move |input| Ok({
        pat.first_match(input).map_or_else(|input| (In::default(), input), map_second(first))
    })
}

/// Like [`parse_until`], but also removes the match of `pat` from the rest of the input.
///
/// # Errors
/// Unlike [`parse_until`], this parser returns a recoverable error if `pred` returned `false` for
/// all the characters in the input.
pub fn parse_until_ex<In: Input>(pat: impl Pattern) -> impl Parser<In, In> {
    move |input| pat.first_match_ex(input).map(map_second(first))
        .map_err(ParsingError::new_recoverable)
}

/// Parse a balanced group of `open` & `close` patterns.
///
/// # Errors
/// - If no initial `open` was found, a recoverable error is returned.
/// - If the end was reached before a matching `close` pattern, a fatal error is returned.
///
/// An example use of this is parsing balanced parentheses:
/// ```rust
/// # fn main() {
/// use shrimple_parser::{pattern::parse_group, ParsingError};
/// let src = "(foo ()) bar";
/// assert_eq!(parse_group('(', ')')(src), Ok((" bar", "foo ()")));
///
/// let src = "(oops";
/// assert_eq!(parse_group('(', ')')(src), Err(ParsingError::new("(oops", ())));
/// # }
/// ```
#[expect(clippy::missing_panics_doc, clippy::unwrap_used, reason = "Panics only if the pattern does")]
pub fn parse_group<In: Input>(
    open: impl Pattern,
    close: impl Pattern,
) -> impl Parser<In, In, ()> {
    move |input| {
        let (open, close) = (open.by_ref(), close.by_ref());
        let (mut rest, _) = parse(open).map_reason(|x| match x {})(input.clone())?;
        let mut depth = 0usize;
        loop {
            let mut group;
            match parse_until_ex(close)(rest) {
                Ok(x) => (rest, group) = x,
                Err(_) => break Err(ParsingError::new(input, ())),
            }
            let mut after_open = Some(group);
            group = loop {
                match parse_until_ex(open)(after_open.take().unwrap()) {
                    Ok((x, _)) => {
                        depth += 1;
                        after_open = Some(x);
                    }
                    Err(x) => break x.rest,
                };
            };
            if depth == 0 {
                break Ok((rest, group));
            }
            depth -= 1;
        }
    }
}

#[test]
fn test_char_pat() {
    assert_eq!(
        parse_until_ex('"')
            .parse(r#"this is what they call a \"test\", right?" - he said"#),
        Ok((r#"test\", right?" - he said"#, r"this is what they call a \")),
    );
}

#[test]
fn test_not_escaped_pat() {
    assert_eq!(
        parse_until_ex(NotEscaped('\\', '"'))
            .parse(r#"this is what they call a \"test\", right?" - he said"#),
        Ok((" - he said", r#"this is what they call a \"test\", right?"#)),
    );
}

#[test]
fn test_str_pat() {
    assert_eq!(parse("abc")("abcdef"), Ok(("def", "abc")));
}
