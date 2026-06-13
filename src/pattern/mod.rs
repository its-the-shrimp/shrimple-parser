//! Abstractions for working with patterns.

mod char_predicates;
mod into_pattern;

pub use {
    char_predicates::*,
    into_pattern::*,
};

use {
    crate::{tuple::Tuple, Input},
    core::ops::Not,
};

#[cfg(test)]
use {
    crate::{
        parser::{one, until_ex, Parser},
        error::ParsingError,
    },
    core::convert::Infallible,
};

/// This trait represents an object that can be matched onto a string.
/// This includes functions, characters, [arrays of] characters, strings, but also custom patterns
/// like [`NotEscaped`]
///
/// See built-in patterns and parser adapters for patterns in the [`pattern`](self) module
///
/// Hint: on the success path, the 1st element of the return tuple is the rest of the input (with
/// or without the matched pattern at the start)
pub trait Pattern {
    /// The return values are (rest of the input, matched fragment at the beginning).
    ///
    /// # Errors
    /// In the case of no match, the original `input` is returned as the [`Err`] variant.
    ///
    /// Used by [`crate::parser::one`].
    fn immediate_match<I: Input>(&self, input: I) -> Result<(I, I), I>;

    /// The return values are (rest of the input, contiguous matched fragments from the beginning).
    ///
    /// 0 is also a valid number of matches.
    ///
    /// Used by [`crate::parser::many`]
    #[expect(
        clippy::unwrap_used,
        reason = "this will only panic if the pattern does"
    )]
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
    #[expect(
        clippy::unwrap_used,
        reason = "this will only panic if the pattern does"
    )]
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
        input
            .split_at(rest_ptr as usize - input_ptr as usize)
            .rev()
            .map_second(|s| (s, n))
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
    #[expect(
        clippy::unwrap_used,
        reason = "this will only panic if the pattern does"
    )]
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
    /// Used by [`crate::parser::until`].
    fn first_match<I: Input>(&self, input: I) -> Result<(I, (I, I)), I>;

    /// Like [`Pattern::first_match`], but the match is excluded from the rest of the input.
    ///
    /// # Errors
    /// Returns the provided `input` unchanged in the [`Err`] variant if there's no match.
    ///
    /// Used by [`crate::parser::until_ex`].
    fn first_match_ex<I: Input>(&self, input: I) -> Result<(I, (I, I)), I>;

    /// Get the pattern by reference to avoid moving it, which will happen in generic code
    ///
    /// Do not override this method.
    fn by_ref(&self) -> Ref<'_, Self> {
        Ref(self)
    }

    /// Combine `self` and another pattern into a pattern that matches both of them in a sequence,
    /// with `self` before `other`
    ///
    /// Do not override this method.
    fn and<Other: Pattern>(self, other: Other) -> Chain<Self, Other>
    where
        Self: Sized,
    {
        Chain(self, other)
    }

    /// Create a pattern that'll match `self` only if it's not escaped (immediately preceded)
    /// by the provided pattern.
    ///
    /// Do not override this method.
    fn not_escaped_by<Prefix: Pattern>(self, prefix: Prefix) -> NotEscaped<Prefix, Self>
    where
        Self: Sized,
    {
        NotEscaped(prefix, self)
    }

    /// Create a pattern that'll match `self` only if it's not enclosed (preceded & superceded) by
    /// the provided pattern.
    ///
    /// Do not override this method.
    fn not_enclosed_by<Enclosure: Pattern>(self, enc: Enclosure) -> NotEnclosed<Enclosure, Self>
    where
        Self: Sized,
    {
        NotEnclosed(enc, self)
    }

    /// Creates a greedy pattern that matches `self` as many times as possible. See [`Many`]
    fn many(self) -> Many<Self> 
    where
        Self: Sized,
    {
        Many(self)
    }

    /// Creates a pattern that matches `self` 0 or 1 times. See [`Maybe`]
    fn maybe(self) -> Maybe<Self>
    where
        Self: Sized,
    {
        Maybe(self)
    }
}

impl<F: Fn(char) -> bool> Pattern for F {
    fn immediate_match<I: Input>(&self, input: I) -> Result<(I, I), I> {
        match input.chars().next().filter(|c| self(*c)) {
            Some(c) => Ok(input.split_at(c.len_utf8()).rev()),
            None => Err(input),
        }
    }

    fn immediate_matches<I: Input>(&self, input: I) -> (I, I) {
        let mid = input.find(|c| !self(c)).unwrap_or(input.len());
        input.split_at(mid).rev()
    }

    fn immediate_matches_counted<I: Input>(&self, input: I) -> (I, (I, usize)) {
        let mut char_index = 0;
        let byte_index = input
            .char_indices()
            .inspect(|_| char_index += 1)
            .find_map(|(bi, c)| self(c).not().then_some(bi))
            .inspect(|_| char_index -= 1)
            .unwrap_or(input.len());
        input
            .split_at(byte_index)
            .rev()
            .map_second(|s| (s, char_index))
    }

    fn trailing_match<I: Input>(&self, input: I) -> Result<(I, I), I> {
        match input.strip_suffix(self).map(str::len) {
            Some(len) => Ok(input.split_at(len)),
            None => Err(input),
        }
    }

    fn first_match<I: Input>(&self, input: I) -> Result<(I, (I, I)), I> {
        match input.char_indices().find(|(_, c)| self(*c)) {
            Some((at, ch)) => {
                let (before, after) = input.split_at(at);
                let r#match = after.clone().before(ch.len_utf8());
                Ok((after, (before, r#match)))
            }
            None => Err(input),
        }
    }

    fn first_match_ex<I: Input>(&self, input: I) -> Result<(I, (I, I)), I> {
        match input.char_indices().find(|(_, c)| self(*c)) {
            Some((at, ch)) => {
                let (before, after) = input.split_at(at);
                let (r#match, after) = after.split_at(ch.len_utf8());
                Ok((after, (before, r#match)))
            }
            None => Err(input),
        }
    }
}

/// This is a specialised, optimised impl for matching any `char` in the array. For a more general
/// pattern combinator, use a tuple.
impl<const N: usize> Pattern for [char; N] {
    fn immediate_match<I: Input>(&self, input: I) -> Result<(I, I), I> {
        match input.strip_prefix(self) {
            Some(rest) => {
                let matched_pat_len = input.len() - rest.len();
                Ok(input.split_at(matched_pat_len).rev())
            }
            None => Err(input),
        }
    }

    fn trailing_match<I: Input>(&self, input: I) -> Result<(I, I), I> {
        match input.strip_suffix(self) {
            Some(rest) => {
                let rest_len = rest.len();
                Ok(input.split_at(rest_len))
            }
            None => Err(input),
        }
    }

    fn first_match<I: Input>(&self, input: I) -> Result<(I, (I, I)), I> {
        match input.find(self) {
            Some(at) => {
                let (prev, match_and_rest) = input.split_at(at);
                let matched_pat_len = match_and_rest.chars().next().map_or(0, char::len_utf8);
                let r#match = match_and_rest.clone().before(matched_pat_len);
                Ok((match_and_rest, (prev, r#match)))
            }
            None => Err(input),
        }
    }

    fn first_match_ex<I: Input>(&self, input: I) -> Result<(I, (I, I)), I> {
        match input.find(self) {
            Some(at) => {
                let (prev, match_and_rest) = input.split_at(at);
                let matched_pat_len = match_and_rest.chars().next().map_or(0, char::len_utf8);
                let (r#match, rest) = match_and_rest.split_at(matched_pat_len);
                Ok((rest, (prev, r#match)))
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
        (
            input.before(trimmed_len),
            (input_len - trimmed_len) / self.len(),
        )
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
        (
            input.before(trimmed_len),
            (input_len - trimmed_len) / self.len_utf8(),
        )
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

#[cfg(feature = "either")]
macro_rules! fwd_method_impl {
    ($(fn $name:ident -> $ret:ty;)+) => {
        $(
            fn $name<I: Input>(&self, input: I) -> $ret {
                match self {
                    either::Either::Left(l) => l.$name(input),
                    either::Either::Right(r) => r.$name(input),
                }
            }
        )+
    };
}

#[cfg(feature = "either")]
impl<L: Pattern, R: Pattern> Pattern for either::Either<L, R> {
    fwd_method_impl! {
        fn immediate_match -> Result<(I, I), I>;
        fn immediate_matches -> (I, I);
        fn immediate_matches_counted -> (I, (I, usize));
        fn trailing_match -> Result<(I, I), I>;
        fn trailing_matches_counted -> (I, usize);
        fn first_match -> Result<(I, (I, I)), I>;
        fn first_match_ex -> Result<(I, (I, I)), I>;
    }
}

/// Pattern that's the reference to another pattern, used in generic code to reuse the pattern.
#[repr(transparent)]
pub struct Ref<'this, T: ?Sized + Pattern>(&'this T);

impl<T: ?Sized + Pattern> Clone for Ref<'_, T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T: ?Sized + Pattern> Copy for Ref<'_, T> {}

impl<T: ?Sized + Pattern> Pattern for Ref<'_, T> {
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

/// Pattern that matches pattern `Inner` not escaped by `Prefix`.
/// "escaped" here means that the pattern `Inner` is preceded by a `Prefix` that's not preceded by
/// itself.
///
/// For example, for a pattern `NotEscaped('\', '0')`, the strings "0", "\\0" & "\\\\\\0" will have
/// a match, but the strings "\0", "\\ \0" & "\\\\\\\0" won't.
#[derive(Clone, Copy)]
pub struct NotEscaped<Prefix: Pattern, Inner: Pattern>(pub Prefix, pub Inner);

impl<Prefix: Pattern, Inner: Pattern> Pattern for NotEscaped<Prefix, Inner> {
    fn immediate_match<I: Input>(&self, input: I) -> Result<(I, I), I> {
        self.1.immediate_match(input)
    }

    fn trailing_match<I: Input>(&self, input: I) -> Result<(I, I), I> {
        let (rest, r#match) = self.1.trailing_match(input.clone())?;
        let (rest, n_prefixes) = self.0.trailing_matches_counted(rest);
        (n_prefixes % 2 == 0)
            .then_some((rest, r#match))
            .ok_or(input)
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
                return Ok((rest, (before, r#match)));
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

/// Pattern that matches pattern `Inner` not surrounded by `Enclosure`.
pub struct NotEnclosed<Enclosure: Pattern, Inner: Pattern>(pub Enclosure, pub Inner);

impl<Enclosure: Pattern, Inner: Pattern> Pattern for NotEnclosed<Enclosure, Inner> {
    fn immediate_match<I: Input>(&self, input: I) -> Result<(I, I), I> {
        self.1.immediate_match(input)
    }

    fn immediate_matches<I: Input>(&self, input: I) -> (I, I) {
        self.1.immediate_matches(input)
    }

    fn trailing_match<I: Input>(&self, input: I) -> Result<(I, I), I> {
        self.1.trailing_match(input)
    }

    fn first_match<I: Input>(&self, input: I) -> Result<(I, (I, I)), I> {
        let mut enclosed = false;
        let mut rest = &*input;
        loop {
            let (after_enc, (before_enc, enc)) =
                self.0.first_match_ex(rest).unwrap_or(("", (rest, "")));
            let (after_inner, (before_inner, inner)) =
                self.1.first_match_ex(rest).unwrap_or(("", (rest, "")));

            if [enc, inner] == ["", ""] {
                break Err(input);
            }

            if before_enc.len() < before_inner.len() {
                rest = after_enc;
                enclosed = !enclosed;
            } else if enclosed {
                rest = after_inner;
            } else {
                let match_len = inner.len();
                let before_len = input.len() - after_inner.len() - match_len;
                let (before, rest_and_match) = input.split_at(before_len);
                let r#match = rest_and_match.clone().before(match_len);
                break Ok((rest_and_match, (before, r#match)));
            }
        }
    }

    fn first_match_ex<I: Input>(&self, input: I) -> Result<(I, (I, I)), I> {
        let mut enclosed = false;
        let mut rest = &*input;
        loop {
            let (after_enc, (before_enc, enc)) =
                self.0.first_match_ex(rest).unwrap_or(("", (rest, "")));
            let (after_inner, (before_inner, inner)) =
                self.1.first_match_ex(rest).unwrap_or(("", (rest, "")));

            if [enc, inner] == ["", ""] {
                break Err(input);
            }

            if before_enc.len() < before_inner.len() {
                rest = after_enc;
                enclosed = !enclosed;
            } else if enclosed {
                rest = after_inner;
            } else {
                let match_len = inner.len();
                let before_len = input.len() - after_inner.len() - match_len;
                let (before, rest_and_match) = input.split_at(before_len);
                let (r#match, rest) = rest_and_match.split_at(match_len);
                break Ok((rest, (before, r#match)));
            }
        }
    }
}

/// A pattern that matches any 1 character.
#[derive(Clone, Copy)]
pub struct Any;

impl Pattern for Any {
    fn immediate_match<I: Input>(&self, input: I) -> Result<(I, I), I> {
        match input.chars().next() {
            Some(ch) => Ok(input.split_at(ch.len_utf8()).rev()),
            None => Err(input),
        }
    }

    fn immediate_matches<I: Input>(&self, input: I) -> (I, I) {
        let input_len = input.len();
        input.split_at(input_len).rev()
    }

    fn immediate_matches_counted<I: Input>(&self, input: I) -> (I, (I, usize)) {
        let input_len = input.len();
        let input_n_chars = input.chars().count();
        input.split_at(input_len).rev().map_second(|matched| (matched, input_n_chars))
    }

    fn trailing_match<I: Input>(&self, input: I) -> Result<(I, I), I> {
        match input.chars().next_back() {
            Some(ch) => Ok(input.split_at(ch.len_utf8())),
            None => Err(input),
        }
    }

    fn trailing_matches_counted<I: Input>(&self, input: I) -> (I, usize) {
        let input_n_chars = input.chars().count();
        (input.start(), input_n_chars)
    }

    fn first_match<I: Input>(&self, input: I) -> Result<(I, (I, I)), I> {
        let first_char_len = input.chars().next().map_or(0, char::len_utf8);
        let before = input.clone().start();
        let first_char_span = input.clone().before(first_char_len);
        Ok((input, (before, first_char_span)))
    }

    fn first_match_ex<I: Input>(&self, input: I) -> Result<(I, (I, I)), I> {
        let first_char_len = input.chars().next().map_or(0, char::len_utf8);
        let before = input.clone().start();
        let (first_char_span, after) = input.split_at(first_char_len);
        Ok((after, (before, first_char_span)))
    }
}

/// A tuple pattern matches either of the 2 patterns in a short-circuiting & commutative manner,
/// with `self` tried first. Tuples of more than 2 elements can be turned into a pattern via
/// the [`IntoPattern`] trait.
///
/// # Performance
/// If you want to match either of N chars, use an array of them as a pattern instead, as this
/// struct has a general impl that may miss optimisations applicable to the case of `[char; N]`
/// being the pattern.
impl<P1: Pattern, P2: Pattern> Pattern for (P1, P2) {
    fn immediate_match<I: Input>(&self, input: I) -> Result<(I, I), I> {
        self.0
            .immediate_match(input)
            .or_else(|input| self.1.immediate_match(input))
    }

    fn trailing_match<I: Input>(&self, input: I) -> Result<(I, I), I> {
        self.0
            .trailing_match(input)
            .or_else(|input| self.1.trailing_match(input))
    }

    fn first_match<I: Input>(&self, input: I) -> Result<(I, (I, I)), I> {
        let (before1, match1) = self.0.first_match(&*input).map_or((&*input, ""), |x| x.1);
        let (before2, match2) = self.1.first_match(&*input).map_or((&*input, ""), |x| x.1);

        if [match1, match2] == ["", ""] {
            return Err(input);
        }

        let [before_len, match_len] = if before1.len() < before2.len() {
            [before1.len(), match1.len()]
        } else {
            [before2.len(), match2.len()]
        };

        let (before, match_rest) = input.split_at(before_len);
        let r#match = match_rest.clone().before(match_len);
        Ok((match_rest, (before, r#match)))
    }

    fn first_match_ex<I: Input>(&self, input: I) -> Result<(I, (I, I)), I> {
        let (before1, match1) = self.0.first_match(&*input).map_or((&*input, ""), |x| x.1);
        let (before2, match2) = self.1.first_match(&*input).map_or((&*input, ""), |x| x.1);

        if [match1, match2] == ["", ""] {
            return Err(input);
        }

        let [before_len, match_len] = if before1.len() < before2.len() {
            [before1.len(), match1.len()]
        } else {
            [before2.len(), match2.len()]
        };

        let (before, match_rest) = input.split_at(before_len);
        let (r#match, rest) = match_rest.split_at(match_len);
        Ok((rest, (before, r#match)))
    }
}

/// A pattern that matches `P1` immediately followed by `P2`.
///
/// A match is only produced when **both** patterns match consecutively at
/// the same position: `P1` at the current position and `P2` right after it.
/// The combined match spans the entirety of both sub-matches.
///
/// # Note
/// For `first_match` / `first_match_ex`, every occurrence of `P1` in the
/// input is tried in left-to-right order; the first one where `P2`
/// immediately follows is returned.  Occurrences of `P1` that are *not*
/// followed by `P2` are skipped.
///
/// More conveniently created via [`Pattern::and`].
///
/// # Example
/// ```rust
/// # fn main() {
/// use {
///     shrimple_parser::{
///         Pattern,
///         parser::{one, until_ex},
///         pattern::{ascii_digit, alphabetic, Chain},
///     },
///     core::convert::Infallible,
/// };
///
/// // Matches a digit immediately followed by an alphabetic character.
/// assert_eq!(
///     one::<_, Infallible>(ascii_digit.and(alphabetic))("3x rest"),
///     Ok((" rest", "3x")),
/// );
///
/// // Returns an error when the pattern is not at the start.
/// assert!(
///     one::<_, Infallible>(ascii_digit.and(alphabetic))("x3 rest")
///         .is_err()
/// );
///
/// // Finds the first '$' that is immediately followed by '{'.
/// assert_eq!(
///     until_ex::<_, Infallible>('$'.and('{'))("foo${bar}"),
///     Ok(("bar}", "foo")),
/// );
/// # }
/// ```
#[derive(Debug, Clone, Copy)]
pub struct Chain<P1: Pattern, P2: Pattern>(pub P1, pub P2);

impl<P1: Pattern, P2: Pattern> Pattern for Chain<P1, P2> {
    fn immediate_match<I: Input>(&self, input: I) -> Result<(I, I), I> {
        // Try P1 at the start; keep the original `input` for the error path.
        let rest_after_p1 = match self.0.immediate_match(input.clone()) {
            Ok((rest, _)) => rest,
            Err(_) => return Err(input),
        };
        // Try P2 immediately after P1.
        match self.1.immediate_match(rest_after_p1) {
            Ok((rest_after_p2, _)) => {
                // The combined match spans from the start of `input` to the
                // start of `rest_after_p2`.
                let match_len = input.len() - rest_after_p2.len();
                let (matched, rest) = input.split_at(match_len);
                Ok((rest, matched))
            }
            Err(_) => Err(input),
        }
    }

    fn trailing_match<I: Input>(&self, input: I) -> Result<(I, I), I> {
        // First strip P2 from the end.
        let before_p2 = match self.1.trailing_match(input.clone()) {
            Ok((before, _)) => before,
            Err(_) => return Err(input),
        };
        // Then strip P1 from the end of what remains.
        match self.0.trailing_match(before_p2) {
            Ok((before_p1, _)) => {
                // `before_p1.len()` is the byte offset where the chain match
                // starts inside `input`.
                Ok(input.split_at(before_p1.len()))
            }
            Err(_) => Err(input),
        }
    }

    fn first_match<I: Input>(&self, input: I) -> Result<(I, (I, I)), I> {
        let mut rest = input.clone();
        loop {
            // Find the next P1, advancing `rest` past each failed candidate.
            let (after_p1, (_, p1_match)) = match self.0.first_match_ex(rest) {
                Ok(result) => result,
                Err(_) => return Err(input),
            };
            // Check whether P2 immediately follows this P1.
            match self.1.immediate_match(after_p1.clone()) {
                Ok((after_p2, _)) => {
                    // Reconstruct `before` and the chain match relative to the
                    // original `input` using length arithmetic so that the
                    // returned slices stay within the same allocation.
                    let p1_start = input.len() - after_p1.len() - p1_match.len();
                    let chain_len = p1_match.len() + after_p1.len() - after_p2.len();
                    let (before, chain_and_rest) = input.split_at(p1_start);
                    let chain = chain_and_rest.clone().before(chain_len);
                    return Ok((chain_and_rest, (before, chain)));
                }
                // P2 did not follow this P1; advance past P1 and keep looking.
                Err(_) => rest = after_p1,
            }
        }
    }

    fn first_match_ex<I: Input>(&self, input: I) -> Result<(I, (I, I)), I> {
        let mut rest = input.clone();
        loop {
            // Find the next P1, advancing `rest` past each failed candidate.
            let (after_p1, (_, p1_match)) = match self.0.first_match_ex(rest) {
                Ok(result) => result,
                Err(_) => return Err(input),
            };
            // Check whether P2 immediately follows this P1.
            match self.1.immediate_match(after_p1.clone()) {
                Ok((after_p2, _)) => {
                    let p1_start = input.len() - after_p1.len() - p1_match.len();
                    let chain_len = p1_match.len() + after_p1.len() - after_p2.len();
                    let (before, chain_start) = input.split_at(p1_start);
                    let chain = chain_start.before(chain_len);
                    return Ok((after_p2, (before, chain)));
                }
                // P2 did not follow this P1; advance past P1 and keep looking.
                Err(_) => rest = after_p1,
            }
        }
    }
}

/// A pattern that matches any number of contiguous occurrences of the inner pattern `T`,
/// including 0.
///
/// Because 0 occurrences is always a valid match, [`Many`] never fails: [`Pattern::immediate_match`]
/// and [`Pattern::trailing_match`] always return [`Ok`], and [`Pattern::first_match`] /
/// [`Pattern::first_match_ex`] always match at the very start of the input (with a possibly
/// empty match).
///
/// More conveniently created via [`Pattern::many`]
///
/// # Example
/// ```rust
/// # fn main() {
/// use {
///     shrimple_parser::{
///         Pattern,
///         parser::one,
///         pattern::{ascii_digit, Many},
///     },
///     core::convert::Infallible,
/// };
///
/// // Matches 0 or more ASCII digits from the start of the input.
/// assert_eq!(
///     one::<_, Infallible>(ascii_digit.many())("123abc"),
///     Ok(("abc", "123")),
/// );
///
/// // 0 matches is still a match, with an empty matched fragment.
/// assert_eq!(
///     one::<_, Infallible>(ascii_digit.many())("abc"),
///     Ok(("abc", "")),
/// );
/// # }
/// ```
#[derive(Debug, Clone, Copy)]
pub struct Many<T: Pattern>(pub T);

impl<T: Pattern> Pattern for Many<T> {
    fn immediate_match<I: Input>(&self, input: I) -> Result<(I, I), I> {
        Ok(self.0.immediate_matches(input))
    }

    /// Repeating "0 or more `T`" is the same as "0 or more `T`", so this delegates directly to
    /// `T`'s implementation rather than looping on [`Pattern::immediate_match`], which would
    /// never terminate since [`Many::immediate_match`] never fails.
    fn immediate_matches<I: Input>(&self, input: I) -> (I, I) {
        self.0.immediate_matches(input)
    }

    fn immediate_matches_counted<I: Input>(&self, input: I) -> (I, (I, usize)) {
        self.0.immediate_matches_counted(input)
    }

    fn trailing_match<I: Input>(&self, input: I) -> Result<(I, I), I> {
        let (rest, _) = self.0.trailing_matches_counted(input.clone());
        let rest_len = rest.len();
        Ok(input.split_at(rest_len))
    }

    /// See [`Many::immediate_matches`] for why this delegates straight to `T` instead of
    /// looping on [`Pattern::trailing_match`].
    fn trailing_matches_counted<I: Input>(&self, input: I) -> (I, usize) {
        self.0.trailing_matches_counted(input)
    }

    fn first_match<I: Input>(&self, input: I) -> Result<(I, (I, I)), I> {
        let (after_first, (before, first)) = self.0.first_match_ex(input.clone())?;
        let (_, more) = self.0.immediate_matches(after_first);

        let before_len = before.len();
        let match_len = first.len() + more.len();

        let (before, match_and_rest) = input.split_at(before_len);
        let matched = match_and_rest.clone().before(match_len);
        Ok((match_and_rest, (before, matched)))
    }

    fn first_match_ex<I: Input>(&self, input: I) -> Result<(I, (I, I)), I> {
        let (after_first, (before, first)) = self.0.first_match_ex(input.clone())?;
        let (_, more) = self.0.immediate_matches(after_first);

        let before_len = before.len();
        let match_len = first.len() + more.len();

        let (before, match_and_rest) = input.split_at(before_len);
        let (matched, rest) = match_and_rest.split_at(match_len);
        Ok((rest, (before, matched)))
    }
}

/// A pattern that matches 0 or 1 occurrences of the inner pattern `T`, making it optional.
///
/// Because both 0 and 1 occurrences are valid matches, [`Maybe`] never fails:
/// [`Pattern::immediate_match`] and [`Pattern::trailing_match`] always return [`Ok`], falling
/// back to an empty match at the relevant end of the input if `T` doesn't match there. Likewise,
/// [`Pattern::first_match`] / [`Pattern::first_match_ex`] always match at the very start of the
/// input.
///
/// More conveniently created via [`Pattern::maybe`]
///
/// # Example
/// ```rust
/// # fn main() {
/// use {
///     shrimple_parser::{
///         Pattern,
///         parser::one,
///         pattern::Maybe,
///     },
///     core::convert::Infallible,
/// };
///
/// // Matches an optional '-' sign at the start of the input.
/// assert_eq!(
///     one::<_, Infallible>('-'.maybe())("-123"),
///     Ok(("123", "-")),
/// );
///
/// // No '-' present - still matches, with an empty matched fragment.
/// assert_eq!(
///     one::<_, Infallible>('-'.maybe())("123"),
///     Ok(("123", "")),
/// );
/// # }
/// ```
#[derive(Debug, Clone, Copy)]
pub struct Maybe<T: Pattern>(pub T);

impl<T: Pattern> Pattern for Maybe<T> {
    fn immediate_match<I: Input>(&self, input: I) -> Result<(I, I), I> {
        self.0
            .immediate_match(input)
            .or_else(|input| Ok(input.split_at(0).rev()))
    }

    /// Repeating "0 or 1 `T`" is the same as "0 or more `T`", so this delegates directly to
    /// `T`'s implementation rather than looping on [`Pattern::immediate_match`], which would
    /// never terminate since [`Maybe::immediate_match`] never fails.
    fn immediate_matches<I: Input>(&self, input: I) -> (I, I) {
        self.0.immediate_matches(input)
    }

    fn immediate_matches_counted<I: Input>(&self, input: I) -> (I, (I, usize)) {
        self.0.immediate_matches_counted(input)
    }

    fn trailing_match<I: Input>(&self, input: I) -> Result<(I, I), I> {
        self.0.trailing_match(input).or_else(|input| {
            let len = input.len();
            Ok(input.split_at(len))
        })
    }

    /// See [`Maybe::immediate_matches`] for why this delegates straight to `T` instead of
    /// looping on [`Pattern::trailing_match`].
    fn trailing_matches_counted<I: Input>(&self, input: I) -> (I, usize) {
        self.0.trailing_matches_counted(input)
    }

    fn first_match<I: Input>(&self, input: I) -> Result<(I, (I, I)), I> {
        let (_, matched) = self.immediate_match(input.clone())?;
        let before = input.clone().before(0);
        Ok((input, (before, matched)))
    }

    fn first_match_ex<I: Input>(&self, input: I) -> Result<(I, (I, I)), I> {
        let (rest, matched) = self.immediate_match(input.clone())?;
        let before = input.before(0);
        Ok((rest, (before, matched)))
    }
}

#[test]
fn char_pat() {
    assert_eq!(
        until_ex::<_, Infallible>('"')
            .parse(r#"this is what they call a \"test\", right?" - he said"#),
        Ok((
            r#"test\", right?" - he said"#,
            r"this is what they call a \"
        )),
    );
}

#[test]
fn not_escaped_pat() {
    assert_eq!(
        until_ex::<_, Infallible>(NotEscaped('\\', '"'))
            .parse(r#"this is what they call a \"test\", right?" - he said"#),
        Ok((" - he said", r#"this is what they call a \"test\", right?"#)),
    );
}

#[test]
fn str_pat() {
    assert_eq!(one::<_, Infallible>("abc")("abcdef"), Ok(("def", "abc")));
}

#[test]
fn array_pat() {
    assert_eq!(
        until_ex::<_, Infallible>([';', '\''])("abc;def'xyz"),
        Ok(("def'xyz", "abc"))
    );
}

#[test]
fn union_pat() {
    let src = "abc\\def'xyz;";
    assert_eq!(
        until_ex::<_, Infallible>((';', '\''))(src),
        until_ex([';', '\''])(src)
    );
}

#[test]
fn chain_pattern_immediate_match_success() {
    assert_eq!(
        one::<_, Infallible>('a'.and('b'))("abcde"),
        Ok(("cde", "ab")),
    );
}

#[test]
fn chain_pattern_immediate_match_p1_fails() {
    assert_eq!(
        one::<_, Infallible>('a'.and('b'))("xbc"),
        Err(ParsingError::new_recoverable("xbc")),
    );
}

#[test]
fn chain_pattern_immediate_match_p2_fails() {
    assert_eq!(
        one::<_, Infallible>('a'.and('b'))("axc"),
        Err(ParsingError::new_recoverable("axc")),
    );
}

#[test]
fn chain_pattern_immediate_match_predicate_patterns() {
    assert_eq!(
        one::<_, Infallible>(ascii_digit.and(alphabetic))("3x rest"),
        Ok((" rest", "3x")),
    );
}

#[test]
fn chain_pattern_first_match_ex_found_immediately() {
    assert_eq!(
        one::<_, Infallible>('$'.and('{'))("${bar}"),
        Ok(("bar}", "${")),
    );
}

#[test]
fn chain_pattern_first_match_ex_skips_p1_without_p2() {
    assert_eq!(
        until_ex::<_, Infallible>('a'.and('b'))("xaabyz"),
        Ok(("yz", "xa")),
    );
}

#[test]
fn chain_pattern_first_match_ex_string_patterns() {
    assert_eq!(
        until_ex::<_, Infallible>('$'.and('{'))("foo${bar}"),
        Ok(("bar}", "foo")),
    );
}

#[test]
fn chain_pattern_first_match_ex_no_match() {
    // No 'a' is ever immediately followed by 'b'.
    assert!(until_ex::<_, Infallible>('a'.and('b'))("xaxcyz").is_err());
}

#[test]
fn chain_pattern_first_match_not_first_p1_match() {
    assert_eq!(
        until_ex::<_, Infallible>('a'.and("--"))("aaaa--aaa"),
        Ok(("aaa", "aaa")),
    )
}

#[test]
fn many_matches_zero_or_more() {
    assert_eq!(
        one::<_, Infallible>(ascii_digit.many())("123abc"),
        Ok(("abc", "123")),
    );
    assert_eq!(
        one::<_, Infallible>(ascii_digit.many())("abc"),
        Ok(("abc", "")),
    );
}

#[test]
fn many_chains_with_other_patterns() {
    // "1" or more digits followed by an alphabetic character.
    assert_eq!(
        one::<_, Infallible>(ascii_digit.and(ascii_digit.many()))("123abc"),
        Ok(("abc", "123")),
    );
}

#[test]
fn many_used_in_until_ex() {
    assert_eq!(
        until_ex::<_, Infallible>(ascii_digit.many().and(';'))("abc123;rest"),
        Ok(("rest", "abc")),
    );
}

#[test]
fn maybe_matches_zero_or_one() {
    assert_eq!(
        one::<_, Infallible>('-'.maybe())("-123"),
        Ok(("123", "-")),
    );
    assert_eq!(
        one::<_, Infallible>('-'.maybe())("123"),
        Ok(("123", "")),
    );
}

#[test]
fn maybe_chains_with_other_patterns() {
    assert_eq!(
        one::<_, Infallible>('-'.maybe().and(ascii_digit).and(ascii_digit.many()))("-123abc"),
        Ok(("abc", "-123")),
    );
    assert_eq!(
        one::<_, Infallible>('-'.many().and(ascii_digit).and(ascii_digit.many()))("123abc"),
        Ok(("abc", "123")),
    );
}

#[test]
fn maybe_pattern_immediate_match_p1_fails() {
    assert_eq!(
        one::<_, Infallible>('-'.maybe().and('1'))("1xyz"),
        Ok(("xyz", "1")),
    );
    assert_eq!(
        one::<_, Infallible>('-'.maybe().and('1'))("2xyz"),
        Err(ParsingError::new_recoverable("2xyz")),
    );
}
