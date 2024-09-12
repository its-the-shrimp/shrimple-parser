//! This module provides utility functions for locating pointers into text.

extern crate alloc;

use core::{fmt::{Write, Display, Formatter}, num::NonZeroU32, char::REPLACEMENT_CHARACTER};
use alloc::borrow::Cow;
#[cfg(feature = "std")]
use std::{io::{BufRead, BufReader}, fs::File, path::{Path, PathBuf}, ffi::{OsStr, OsString}};


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
    (0 $_:ident) => { compile_error!("`0` passed to `nonzero!`") };
    ($n:literal) => {
        core::num::NonZero::new($n).unwrap()
    };
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
/// Location of the error. Useful for error reporting, and used by [`crate::FullParsingError`]
pub struct Location {
    /// Source code line of the location
    pub line: NonZeroU32,
    /// Source code column of the location.
    pub col: u32,
}

impl Default for Location {
    fn default() -> Self {
        Self { line: nonzero!(1), col: 0 }
    }
}

impl Display for Location {
    fn fmt(&self, f: &mut Formatter) -> core::fmt::Result {
        write!(f, "{}:{}", self.line, self.col)
    }
}

impl Location {
    /// Turn a [`Location`] into a [`FullLocation`] by providing the file path.
    pub fn with_path<'path>(self, path: impl PathLike<'path>) -> FullLocation<'path> {
        FullLocation { path: path.into_path_bytes(), loc: self }
    }
}

/// Like [`Location`], but also stores the path to the file.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct FullLocation<'path> {
    /// The path to the file associated with the location.
    pub path: Cow<'path, [u8]>,
    /// The line & column numbers of the location.
    pub loc: Location,
}

/// Safety:
/// `bytes` must come from an `str`, `OsStr` or `Path`.
#[cfg(feature = "std")]
pub(crate) unsafe fn bytes_as_path(bytes: &[u8]) -> &std::path::Path {
    std::path::Path::new(std::ffi::OsStr::from_encoded_bytes_unchecked(bytes))
}

impl Display for FullLocation<'_> {
    fn fmt(&self, f: &mut Formatter) -> core::fmt::Result {
        for chunk in self.path.utf8_chunks() {
            f.write_str(chunk.valid())?;
            f.write_char(REPLACEMENT_CHARACTER)?;
        }
        write!(f, ":{}", self.loc)
    }
}

impl FullLocation<'_> {
    /// Unbind the location from the lifetimes by allocating the path if it hasn't been already.
    pub fn own(self) -> FullLocation<'static> {
        FullLocation { path: self.path.into_owned().into(), loc: self.loc }
    }
}

/// A wrapper for [`FullLocation`] & [`crate::FullParsingError`] that will change their `Display`
/// implementations to get the source line from the filesystem and print it in a Rust-like format.
#[cfg(feature = "std")]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct WithSourceLine<T>(pub T);

#[cfg(feature = "std")]
impl Display for WithSourceLine<&FullLocation<'_>> {
    fn fmt(&self, f: &mut Formatter) -> core::fmt::Result {
        writeln!(f, "{}", self.0)?;
        let file = File::open(unsafe { bytes_as_path(&self.0.path) })
            .map_err(|_| core::fmt::Error)?;
        let line = BufReader::new(file)
            .lines()
            .nth(self.0.loc.line.get() as usize - 1)
            .and_then(Result::ok)
            .ok_or(core::fmt::Error)?;
        let line_col_off = self.0.loc.line.ilog10() as usize + 1;
        writeln!(f, "{:line_col_off$} |",        "")?;
        writeln!(f, "{:line_col_off$} | {line}", self.0.loc.line)?;
        write  !(f, "{:line_col_off$} | {:>2$}", "", '^', self.0.loc.col as usize)?;
        Ok(())
    }
}

/// Locates address `ptr` in `src` and returns its source code location, or None if `ptr` is
/// outside of the memory range of `src`.
pub fn locate(ptr: *const u8, src: &str) -> Option<Location> {
    let progress = usize::checked_sub(ptr as _, src.as_ptr() as _).filter(|x| *x <= src.len())?;

    Some(src.bytes().take(progress).fold(Location::default(), |loc, b| match b {
        b'\n' => Location { line: loc.line.saturating_add(1), col: 0 },
        _ => Location { col: loc.col.saturating_add(1), ..loc },
    }))
}

/// Same as [`locate`], except for the `None` case:
/// - If `ptr` is before `src`, the returned location points to the beginning of `src`.
/// - If `ptr` is after `src`, the returned location points to the end of `src`.
///
/// This function is used by [`crate::ParsingError::with_src_loc`]
pub fn locate_saturating(ptr: *const u8, src: &str) -> Location {
    let progress = usize::saturating_sub(ptr as _, src.as_ptr() as _);

    let res = src.bytes().take(progress).fold(Location::default(), |loc, b| match b {
        b'\n' => Location { line: loc.line.saturating_add(1), col: 0 },
        _ => Location { col: loc.col.saturating_add(1), ..loc },
    });
    res
}

/// Same as [`locate`], but searches in multiple "files".
///
/// A file, per definition of this function, is a key `K` that identifies it,
/// and a memory range that is its content.
/// The function returns the key of the file where `ptr` is contained, or `None` if no files
/// matched.
/// ```rust
/// # fn main() {
/// use std::collections::HashMap;
/// use shrimple_parser::{utils::{locate_in_multiple, Location}, nonzero, tuple::copied};
/// 
/// let file2 = "          \n\nfn main() { panic!() }";
/// let sources = HashMap::from([
///     ("file1.rs", r#"fn main() { println!("Hiiiii!!!!! :3") }"#),
///     ("file2.rs", file2),
/// ]);
/// let no_ws = file2.trim();
/// assert_eq!(
///     locate_in_multiple(no_ws.as_ptr(), sources.iter().map(copied)),
///     Some(("file2.rs", Location { line: nonzero!(3), col: 0 })),
/// )
/// # }
/// ```
/// Also see [`crate::tuple::copied`], [`crate::nonzero`]
pub fn locate_in_multiple<K>(
    ptr: *const u8,
    files: impl IntoIterator<Item = (K, impl AsRef<str>)>
) -> Option<(K, Location)> {
    files.into_iter().find_map(|(k, src)| Some((k, locate(ptr, src.as_ref())?)))
}

/// Effectively an alias to `move |y| &x == y`.
pub fn eq<T: PartialEq<Other>, Other>(x: T) -> impl Fn(&Other) -> bool {
    move |y| &x == y
}

/// Effectively an alias to `move |y| &x != y`.
pub fn ne<T: PartialEq<Other>, Other>(x: T) -> impl Fn(&Other) -> bool {
    move |y| &x != y
}

trait Sealed: Sized {}

/// A trait that represents a sequence of bytes that can be interpreted as a path.
/// This is better than `AsRef<Path>` for the following reasons:
/// - Doesn't actually require [`Path`] or [`OsStr`], thus working in `#[no_std]` environments
/// - Preserves ownership, being closer to `into Into<Cow>` in this regard.
#[expect(private_bounds, reason="sealed trait")]
pub trait PathLike<'data>: Sealed {
    /// Convert this to a possibly owned sequence of bytes that's guaranteed to uphold the same
    /// guarantees as an [`OsStr`].
    fn into_path_bytes(self) -> Cow<'data, [u8]>;

    /// Convert this to a possibly owned [`Path`].
    #[cfg(feature = "std")]
    fn into_path(self) -> Cow<'data, Path> {
        match self.into_path_bytes() {
            Cow::Borrowed(x) => unsafe { bytes_as_path(x) }.into(),
            Cow::Owned(x) => PathBuf::from(unsafe {
                OsString::from_encoded_bytes_unchecked(x)
            }).into(),
        }
    }
}

macro_rules! impl_path_like {
    (<$data:lifetime> for $t:ty: $self:ident => $res:expr) => {
        impl<$data> Sealed for $t {}
        impl<$data> PathLike<$data> for $t {
            fn into_path_bytes(self) -> Cow<'data, [u8]> {let $self = self; $res.into()}
        }
    };

    (owned $owned:ty: $self:ident => $res:expr) => {
        impl Sealed for $owned {}
        impl PathLike<'static> for $owned {
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

            impl Sealed for Cow<'_, $borrowed> {}
            impl<'data> PathLike<'data> for Cow<'data, $borrowed> {
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

/// Make a parser that tries any of the provided paths.
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
