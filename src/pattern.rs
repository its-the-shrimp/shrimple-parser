//! Abstractions for working with patterns.

use {
    crate::{
        tuple::{first, map_second, Tuple},
        Input, Parser, ParsingError,
    },
    core::ops::Not,
};

#[cfg(test)]
use {
    crate::utils::char::{is_alphabetic, is_ascii_digit},
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
    /// Used by [`parse`].
    fn immediate_match<I: Input>(&self, input: I) -> Result<(I, I), I>;

    /// The return values are (rest of the input, contiguous matched fragments from the beginning).
    ///
    /// 0 is also a valid number of matches.
    ///
    /// Used by [`parse_while`]
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
    fn by_ref(&self) -> Ref<'_, Self> {
        Ref(self)
    }

    /// Combine `self` and another pattern into a pattern that matches either of them in a
    /// short-circuiting manner, with `self` tried first.
    ///
    /// Do not override this method.
    fn or<Other: Pattern>(self, other: Other) -> Union<Self, Other>
    where
        Self: Sized,
    {
        Union(self, other)
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
    fn not_escaped_by<Prefix: Pattern>(self, prefix: Prefix) -> NotEscaped<Prefix, Self>
    where
        Self: Sized,
    {
        NotEscaped(prefix, self)
    }

    /// Create a pattern that'll match `self` only if it's not enclosed (preceded & superceded) by
    /// the provided pattern.
    fn not_enclosed_by<Enclosure: Pattern>(self, enc: Enclosure) -> NotEnclosed<Enclosure, Self>
    where
        Self: Sized,
    {
        NotEnclosed(enc, self)
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
/// pattern combinator, use the [`Union`] pattern by calling the [`Pattern::or`] method
impl<const N: usize> Pattern for [char; N] {
    // TODO: specialise for `[char; N]`
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

/// A pattern that matches anything.
#[derive(Clone, Copy)]
pub struct AnyChar;

impl Pattern for AnyChar {
    fn immediate_match<I: Input>(&self, input: I) -> Result<(I, I), I> {
        match input.chars().next() {
            Some(ch) => Ok(input.split_at(ch.len_utf8()).rev()),
            None => Err(input),
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

/// A pattern that matches either of the 2 patterns in a short-circuiting manner,
/// with `self` tried first. May be created by [`Pattern::or`] for convenience.
///
/// # Note
/// If you want to match either of N chars, use an array of them as a pattern instead, as this
/// struct has a general impl that may miss optimisations applicable to the case of `[char; N]`
/// being the pattern.
#[derive(Debug, Clone, Copy)]
pub struct Union<P1: Pattern, P2: Pattern>(pub P1, pub P2);

impl<P1: Pattern, P2: Pattern> Pattern for Union<P1, P2> {
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
/// use shrimple_parser::{
///     pattern::{parse, parse_until_ex, Chain},
///     utils::char::{is_ascii_digit, is_alphabetic},
/// };
/// use core::convert::Infallible;
///
/// // Matches a digit immediately followed by an alphabetic character.
/// assert_eq!(
///     parse::<_, Infallible>(Chain(is_ascii_digit, is_alphabetic))("3x rest"),
///     Ok((" rest", "3x")),
/// );
///
/// // Returns an error when the pattern is not at the start.
/// assert!(
///     parse::<_, Infallible>(Chain(is_ascii_digit, is_alphabetic))("x3 rest")
///         .is_err()
/// );
///
/// // Finds the first '$' that is immediately followed by '{'.
/// assert_eq!(
///     parse_until_ex::<_, Infallible>(Chain('$', '{'))("foo${bar}"),
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

/// Parses 1 instance of pattern `pat`.
///
/// # Errors
/// The returned parser returns a recoverable error if the pattern didn't match at the beginning of
/// the input.
pub fn parse<In: Input, Reason>(pat: impl Pattern) -> impl Parser<In, In, Reason> {
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
/// See also [`parse_until`], [`parse_until_ex`].
pub fn parse_while<In: Input, Reason>(pat: impl Pattern) -> impl Parser<In, In, Reason> {
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
pub fn parse_until<In: Input, Reason>(pat: impl Pattern) -> impl Parser<In, In, Reason> {
    move |input| {
        Ok({
            pat.first_match(input)
                .map_or_else(|input| (In::default(), input), map_second(first))
        })
    }
}

/// Like [`parse_until`], but also removes the match of `pat` from the rest of the input.
///
/// # Errors
/// Unlike [`parse_until`], this parser returns a recoverable error if `pred` returned `false` for
/// all the characters in the input.
pub fn parse_until_ex<In: Input, Reason>(pat: impl Pattern) -> impl Parser<In, In, Reason> {
    move |input| {
        pat.first_match_ex(input)
            .map(map_second(first))
            .map_err(ParsingError::new_recoverable)
    }
}

/// Parse a balanced group of `open` & `close` patterns.
///
/// The start & end of the group are <u>included</u> in the output.
/// See [`parse_group_ex`] for a parser that excludes them.
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
/// assert_eq!(parse_group('(', ')')(src), Ok((" bar", "(foo ())")));
///
/// let src = "(oops";
/// assert_eq!(parse_group('(', ')')(src), Err(ParsingError::new("oops", ())));
/// # }
/// ```
pub fn parse_group<In: Input>(open: impl Pattern, close: impl Pattern) -> impl Parser<In, In, ()> {
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
/// See [`parse_group`] for a parser that includes them.
///
/// # Errors
/// - If no initial `open` was found, a recoverable error is returned.
/// - If the end was reached before a matching `close` pattern, a fatal error is returned.
///
/// An example use of this is parsing balanced parentheses:
/// ```rust
/// # fn main() {
/// use shrimple_parser::{pattern::parse_group_ex, ParsingError};
/// let src = "(foo ()) bar";
/// assert_eq!(parse_group_ex('(', ')')(src), Ok((" bar", "foo ()")));
///
/// let src = "(oops";
/// assert_eq!(parse_group_ex('(', ')')(src), Err(ParsingError::new("oops", ())));
/// # }
/// ```
pub fn parse_group_ex<In: Input>(
    open: impl Pattern,
    close: impl Pattern,
) -> impl Parser<In, In, ()> {
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

#[test]
fn char_pat() {
    assert_eq!(
        parse_until_ex::<_, Infallible>('"')
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
        parse_until_ex::<_, Infallible>(NotEscaped('\\', '"'))
            .parse(r#"this is what they call a \"test\", right?" - he said"#),
        Ok((" - he said", r#"this is what they call a \"test\", right?"#)),
    );
}

#[test]
fn str_pat() {
    assert_eq!(parse::<_, Infallible>("abc")("abcdef"), Ok(("def", "abc")));
}

#[test]
fn array_pat() {
    assert_eq!(
        parse_until_ex::<_, Infallible>([';', '\''])("abc;def'xyz"),
        Ok(("def'xyz", "abc"))
    );
}

#[test]
fn union_pat() {
    let src = "abc\\def'xyz;";
    assert_eq!(
        parse_until_ex::<_, Infallible>(';'.or('\''))(src),
        parse_until_ex([';', '\''])(src)
    );
}

#[test]
fn chain_pattern_immediate_match_success() {
    assert_eq!(
        parse::<_, Infallible>(Chain('a', 'b'))("abcde"),
        Ok(("cde", "ab")),
    );
}

#[test]
fn chain_pattern_immediate_match_p1_fails() {
    assert_eq!(
        parse::<_, Infallible>('a'.and('b'))("xbc"),
        Err(ParsingError::new_recoverable("xbc")),
    );
}

#[test]
fn chain_pattern_immediate_match_p2_fails() {
    assert_eq!(
        parse::<_, Infallible>('a'.and('b'))("axc"),
        Err(ParsingError::new_recoverable("axc")),
    );
}

#[test]
fn chain_pattern_immediate_match_predicate_patterns() {
    assert_eq!(
        parse::<_, Infallible>(is_ascii_digit.and(is_alphabetic))("3x rest"),
        Ok((" rest", "3x")),
    );
}

#[test]
fn chain_pattern_first_match_ex_found_immediately() {
    assert_eq!(
        parse_until_ex::<_, Infallible>('$'.and('{'))("${bar}"),
        Ok(("bar}", "")),
    );
}

#[test]
fn chain_pattern_first_match_ex_skips_p1_without_p2() {
    assert_eq!(
        parse_until_ex::<_, Infallible>('a'.and('b'))("xaabyz"),
        Ok(("yz", "xa")),
    );
}

#[test]
fn chain_pattern_first_match_ex_string_patterns() {
    assert_eq!(
        parse_until_ex::<_, Infallible>('$'.and('{'))("foo${bar}"),
        Ok(("bar}", "foo")),
    );
}

#[test]
fn chain_pattern_first_match_ex_no_match() {
    // No 'a' is ever immediately followed by 'b'.
    assert!(parse_until_ex::<_, Infallible>('a'.and('b'))("xaxcyz").is_err());
}

#[test]
fn chain_pattern_first_match_not_first_p1_match() {
    assert_eq!(
        parse_until_ex::<_, Infallible>('a'.and("--"))("aaaa--aaa"),
        Ok(("aaa", "aaa")),
    )
}
