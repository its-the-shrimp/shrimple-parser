//! This module provides utility functions for locating pointers into text.

extern crate alloc;

use alloc::borrow::Cow;
#[cfg(feature = "std")]
use std::{
    ffi::{OsStr, OsString},
    path::{Path, PathBuf},
};

/// Create a non-zero integer from a literal.
/// ```rust
/// # fn main() {
/// use shrimple_parser::nonzero;
///
/// assert_eq!(nonzero!(69), core::num::NonZero::new(69).unwrap())
/// # }
/// ```
#[macro_export]
macro_rules! nonzero {
    (0 $_:ident) => {
        compile_error!("`0` passed to `nonzero!`")
    };
    ($n:literal) => {
        core::num::NonZero::new($n).unwrap()
    };
}

/// Safety:
/// `bytes` must come from an `str`, `OsStr` or `Path`.
#[cfg(feature = "std")]
pub(crate) unsafe fn bytes_as_path(bytes: &[u8]) -> &std::path::Path {
    std::path::Path::new(std::ffi::OsStr::from_encoded_bytes_unchecked(bytes))
}

/// Effectively an alias to `move |y| &x == y`.
pub fn eq<T: PartialEq<Other>, Other>(x: T) -> impl Fn(&Other) -> bool {
    move |y| &x == y
}

/// Effectively an alias to `move |y| &x != y`.
pub fn ne<T: PartialEq<Other>, Other>(x: T) -> impl Fn(&Other) -> bool {
    move |y| &x != y
}

/// A trait that represents a sequence of bytes that can be interpreted as a path.
/// This is better than `AsRef<Path>` for the following reasons:
/// - Doesn't actually require [`Path`] or [`OsStr`], thus working in `#[no_std]` environments
/// - Preserves ownership, being closer to `into Into<Cow>` in this regard.
///
/// # Safety
/// Only implement this for types whose representation is the same as that of [`OsStr`]. Currently
/// in the standard library those are [`str`], [`OsStr`] & [`Path`] (and all their varieties)
pub unsafe trait PathLike<'data>: Sized {
    /// Convert this to a possibly owned sequence of bytes that's guaranteed to uphold the same
    /// guarantees as an [`OsStr`].
    fn into_path_bytes(self) -> Cow<'data, [u8]>;

    /// Convert this to a possibly owned [`Path`].
    #[cfg(feature = "std")]
    fn into_path(self) -> Cow<'data, Path> {
        match self.into_path_bytes() {
            Cow::Borrowed(x) => unsafe { bytes_as_path(x) }.into(),
            Cow::Owned(x) => {
                PathBuf::from(unsafe { OsString::from_encoded_bytes_unchecked(x) }).into()
            }
        }
    }
}

macro_rules! impl_path_like {
    (<$data:lifetime> for $t:ty: $self:ident => $res:expr) => {
        unsafe impl<$data> PathLike<$data> for $t {
            fn into_path_bytes(self) -> Cow<'data, [u8]> {let $self = self; $res.into()}
        }
    };

    (owned $owned:ty: $self:ident => $res:expr) => {
        unsafe impl PathLike<'static> for $owned {
            fn into_path_bytes(self) -> Cow<'static, [u8]> {let $self = self; $res.into()}
        }
    };

    (
        $(for $owned:ty[$borrowed:ty]:
            $self:ident => $res:expr;
            box $bself:ident => $bres:expr;
            ref $rself:ident => $rres:expr;
        )+
    ) => {
        $(
            impl_path_like!(owned $owned: $self => $res);
            impl_path_like!(owned Box<$borrowed>: $bself => $bres);
            impl_path_like!(<'data> for &'data $owned: $rself => $rres);
            impl_path_like!(<'data> for &'data $borrowed: $rself => $rres);
            impl_path_like!(<'data> for &'data Box<$borrowed>: $rself => $rres);
            impl_path_like!(<'data> for &'data Cow<'data, $borrowed>: $rself => $rres);

            unsafe impl<'data> PathLike<'data> for Cow<'data, $borrowed> {
                fn into_path_bytes(self) -> Cow<'data, [u8]> {
                    match self {
                        Cow::Owned($self) => $res.into(),
                        Cow::Borrowed($rself) => $rres.into(),
                    }
                }
            }
        )+
    };
}

impl_path_like! {
    for String[str]:
        x => x.into_bytes();
        box x => x.into_boxed_bytes().into_vec();
        ref x => x.as_bytes();
}

#[cfg(feature = "std")]
impl_path_like! {
    for PathBuf[Path]:
        x => x.into_os_string().into_encoded_bytes();
        box x => x.into_path_buf().into_os_string().into_encoded_bytes();
        ref x => x.as_os_str().as_encoded_bytes();
    for OsString[OsStr]:
        x => x.into_encoded_bytes();
        box x => x.into_os_string().into_encoded_bytes();
        ref x => x.as_encoded_bytes();
}

/// Make a parser/pattern that tries any of the provided paths.
///
/// If the last expression is prefixed with `else: `, it will be applied as a
/// [`crate::Parser::or_map_rest`] instead of [`crate::Parser::or`]
/// Right now it's merely syntactic sugar, but it might bring performance benefits in the future,
/// if such possibility is found.
#[macro_export]
macro_rules! any {
    ($first:expr, $($rest:expr),* $(, $(else: $map_rest:expr)?)?) => {
        $first $(.or($rest))* $($(.or_map_rest($map_rest))?)?
    };
}

/// Make a [mapping parser](`crate::MappingParser`) that chooses the path based on the current output of the parser.
/// The usage
#[macro_export]
macro_rules! match_out {
    {
        $($p:pat => $e:expr),+ $(,)?
    } => {
        |i, o| match o {
            $($p => $e.parse(i)),+
        }
    };
}

macro_rules! make_char_fns {
    ($(fn $name:ident;)+) => {
        $(
            pub fn $name(c: char) -> bool {
                c.$name()
            }
        )+
    };
}

pub mod char {
    make_char_fns! {
        fn is_alphabetic;
        fn is_alphanumeric;
        fn is_control;
        fn is_numeric;
        fn is_lowercase;
        fn is_uppercase;
        fn is_whitespace;
        fn is_ascii;
        fn is_ascii_alphabetic;
        fn is_ascii_uppercase;
        fn is_ascii_lowercase;
        fn is_ascii_alphanumeric;
        fn is_ascii_digit;
        fn is_ascii_hexdigit;
        fn is_ascii_punctuation;
        fn is_ascii_graphic;
        fn is_ascii_whitespace;
        fn is_ascii_control;
    }
}
