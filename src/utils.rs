//! This module provides utility functions for locating pointers into text.

use core::{fmt::{Display, Formatter}, num::NonZeroU32};
use std::{fs::File, io::{BufRead, BufReader}, path::Path};

#[macro_export]
#[doc(hidden)]
macro_rules! __nonzero_int_type {
    (i8) => { ::core::num::NonZeroI8 };
    (i16) => { ::core::num::NonZeroI16 };
    (i32) => { ::core::num::NonZeroI32 };
    (isize) => { ::core::num::NonZeroIsize };
    (i64) => { ::core::num::NonZeroI64 };
    (u8) => { ::core::num::NonZeroU8 };
    (u16) => { ::core::num::NonZeroU16 };
    (u32) => { ::core::num::NonZeroU32 };
    (usize) => { ::core::num::NonZeroUsize };
    (u64) => { ::core::num::NonZeroU64 };
}

/// Create a non-zero integer from a literal.
/// ```rust
/// # fn main() {
/// use shrimple_parser::nonzero;
/// assert_eq!(nonzero!(69 u32), core::num::NonZeroU32::new(69).unwrap())
/// # }
/// ```
#[macro_export]
macro_rules! nonzero {
    (0 $_:ident) => { compile_error!("`0` passed to `nonzero!`") };
    ($n:literal $int_type:ident) => {
        <$crate::__nonzero_int_type!($int_type)>::new($n).unwrap()
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
        Self {
            line: nonzero!(1 u32),
            col: 0
        }
    }
}

impl Display for Location {
    fn fmt(&self, f: &mut Formatter) -> core::fmt::Result {
        write!(f, "{}:{}", self.line, self.col)
    }
}

impl Location {
    /// Turn a [`Location`] into a [`FullLocation`] by providing the file path.
    pub const fn with_path(self, path: &Path) -> FullLocation {
        FullLocation { path, loc: self }
    }
}

/// Like [`Location`], but also stores the path to the file.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct FullLocation<'path> {
    /// The path to the file associated with the location.
    pub path: &'path Path,
    /// The line & column numbers of the location.
    pub loc: Location,
}

impl Display for FullLocation<'_> {
    fn fmt(&self, f: &mut Formatter) -> core::fmt::Result {
        write!(f, "{}:{}", self.path.display(), self.loc)
    }
}

/// A wrapper for [`FullLocation`] & [`crate::FullParsingError`] that will change their `Display`
/// implementations to get the source line from the filesystem and print it in a Rust-like format.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct WithSourceLine<T>(pub T);

impl Display for WithSourceLine<FullLocation<'_>> {
    fn fmt(&self, f: &mut Formatter) -> core::fmt::Result {
        writeln!(f, "{}", self.0)?;
        let line = BufReader::new(File::open(self.0.path).map_err(|_| core::fmt::Error)?)
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

    Some(src.bytes().take(progress + 1).fold(Location::default(), |loc, b| match b {
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

    let res = src.bytes().take(progress + 1).fold(Location::default(), |loc, b| match b {
        b'\n' => Location { line: loc.line.saturating_add(1), col: 0 },
        _ => Location { col: loc.col.saturating_add(1), ..loc },
    });
    res
}

/// Same as [`locate`], but searches in multiple "files". A file, per definition of this
/// function, is a key `K` that identifies it, and a memory range that is its content.
/// The function returns the key of the file where `ptr` is contained, or `None` if no files
/// matched.
/// ```rust
/// # fn main() {
/// use std::collections::HashMap;
/// use shrimple_parser::{utils::locate_in_multiple, Location, nonzero, tuple::copied};
/// 
/// let file2 = "          \n\nfn main() { panic!() }";
/// let sources = HashMap::from([
///     ("file1.rs", r#"fn main() { println!("Hiiiii!!!!! :3") }"#),
///     ("file2.rs", file2),
/// ]);
/// let no_ws = file2.trim();
/// assert_eq!(
///     locate_in_multiple(no_ws.as_ptr(), sources.iter().map(copied)),
///     Some(("file2.rs", Location { line: nonzero!(3 u32), col: 0 })),
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
pub fn eq<T: Eq>(x: T) -> impl Fn(&T) -> bool {
    move |y| &x == y
}

/// Effectively an alias to `move |y| &x != y`.
pub fn ne<T: Eq>(x: T) -> impl Fn(&T) -> bool {
    move |y| &x != y
}
