extern crate alloc;

use {
    crate::{nonzero, utils::PathLike, FullParsingError},
    alloc::borrow::Cow,
    core::{
        char::REPLACEMENT_CHARACTER,
        fmt::{Display, Formatter, Write},
        num::NonZero,
    },
    std::{convert::Infallible, fs::read_to_string, path::Path},
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
/// Location of the error. Useful for error reporting, and used by [`crate::FullParsingError`]
pub struct Location {
    /// Source code line of the location.
    pub line: NonZero<u32>,
    /// Source code column of the location.
    pub col: u32,
}

/// The error returned when converting a [`proc_macro2::LineColumn`] to [`Location`].
#[cfg(feature = "proc-macro2")]
#[derive(Debug, Clone, Copy)]
pub enum LineColumnToLocationError {
    /// Line 0 was encountered, which is invalid, source lines are 1-indexed.
    LineZero,
    /// Line number overflowed a u32.
    LineNumberTooBig,
    /// Column number overflowed a u32.
    ColumnNumberTooBig,
}

#[cfg(feature = "proc-macro2")]
impl Display for LineColumnToLocationError {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        f.write_str(match self {
            Self::LineZero => "`LineColumn` with line #0 found",
            Self::LineNumberTooBig => "`LineColumn`s line number overflowed a u32",
            Self::ColumnNumberTooBig => "`LineColumn`s column number overflowed a u32",
        })
    }
}

#[cfg(feature = "proc-macro2")]
impl TryFrom<proc_macro2::LineColumn> for Location {
    type Error = LineColumnToLocationError;

    fn try_from(value: proc_macro2::LineColumn) -> Result<Self, Self::Error> {
        let line =
            u32::try_from(value.line).map_err(|_| LineColumnToLocationError::LineNumberTooBig)?;
        let line = NonZero::new(line).ok_or(LineColumnToLocationError::LineZero)?;
        let col = u32::try_from(value.column)
            .map_err(|_| LineColumnToLocationError::ColumnNumberTooBig)?;

        Ok(Self { line, col })
    }
}

#[cfg(feature = "proc-macro2")]
impl From<Location> for proc_macro2::LineColumn {
    fn from(value: Location) -> Self {
        Self {
            line: value.line.get() as usize,
            column: value.col as usize,
        }
    }
}

impl Default for Location {
    fn default() -> Self {
        Self {
            line: nonzero!(1),
            col: 0,
        }
    }
}

impl Display for Location {
    fn fmt(&self, f: &mut Formatter) -> core::fmt::Result {
        write!(f, "{}:{}", self.line, self.col)
    }
}

impl Location {
    /// Returns the [`Location`] that's calculated with `self` as the base & `rhs` as the offset
    /// from the base.
    ///
    /// # Panics
    /// Panics if the line or column overflow a `u32`
    #[must_use]
    pub const fn offset(self, rhs: Self) -> Self {
        if rhs.line.get() == 1 {
            Self {
                line: self.line,
                col: self.col + rhs.col,
            }
        } else {
            Self {
                line: NonZero::new(self.line.get() + rhs.line.get() - 1).expect("no overflow"),
                col: rhs.col,
            }
        }
    }

    /// Turn a [`Location`] into a [`FullLocation`] by providing the file path.
    pub fn with_path<'path>(self, path: impl PathLike<'path>) -> FullLocation<'path> {
        FullLocation {
            path: path.into_path_bytes(),
            loc: self,
        }
    }

    /// Locates address `ptr` in `src` and returns its source code location, or None if `ptr` is
    /// outside of the memory range of `src`.
    pub fn find(ptr: *const u8, src: &str) -> Option<Self> {
        let progress =
            usize::checked_sub(ptr as _, src.as_ptr() as _).filter(|x| *x <= src.len())?;

        Some(
            src.bytes()
                .take(progress)
                .fold(Self::default(), |loc, b| match b {
                    b'\n' => Self {
                        line: loc.line.saturating_add(1),
                        col: 0,
                    },
                    _ => Self {
                        col: loc.col.saturating_add(1),
                        ..loc
                    },
                }),
        )
    }

    /// Same as [`find`](Self::find), except for the `None` case:
    /// - If `ptr` is before `src`, the returned location points to the beginning of `src`.
    /// - If `ptr` is after `src`, the returned location points to the end of `src`.
    ///
    /// This function is used by [`crate::ParsingError::with_src_loc`]
    pub fn find_saturating(ptr: *const u8, src: &str) -> Self {
        let progress = usize::saturating_sub(ptr as _, src.as_ptr() as _);

        let res = src
            .bytes()
            .take(progress)
            .fold(Self::default(), |loc, b| match b {
                b'\n' => Self {
                    line: loc.line.saturating_add(1),
                    col: 0,
                },
                _ => Self {
                    col: loc.col.saturating_add(1),
                    ..loc
                },
            });
        res
    }

    /// Same as [`find`](Self::find), but searches in multiple "files".
    ///
    /// A file, per definition of this function, is a key `K` that identifies it,
    /// and a memory range that is its content.
    /// The function returns the key of the file where `ptr` is contained, or `None` if no files
    /// matched.
    /// ```rust
    /// # fn main() {
    /// use std::collections::HashMap;
    /// use shrimple_parser::{Location, nonzero, tuple::copied};
    ///
    /// let file2 = "          \n\nfn main() { panic!() }";
    /// let sources = HashMap::from([
    ///     ("file1.rs", r#"fn main() { println!("Hiiiii!!!!! :3") }"#),
    ///     ("file2.rs", file2),
    /// ]);
    /// let no_ws = file2.trim();
    /// assert_eq!(
    ///     Location::find_in_multiple(no_ws.as_ptr(), sources.iter().map(copied)),
    ///     Some(("file2.rs", Location { line: nonzero!(3), col: 0 })),
    /// )
    /// # }
    /// ```
    /// Also see [`tuple::copied`], [`nonzero`]
    pub fn find_in_multiple<K>(
        ptr: *const u8,
        files: impl IntoIterator<Item = (K, impl AsRef<str>)>,
    ) -> Option<(K, Self)> {
        files
            .into_iter()
            .find_map(|(k, src)| Some((k, Self::find(ptr, src.as_ref())?)))
    }
}

/// Like [`Location`], but also stores the path to the file.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct FullLocation<'path> {
    /// The path to the file associated with the location, stored as bytes
    path: Cow<'path, [u8]>,
    /// The line & column numbers of the location.
    pub loc: Location,
}

impl Display for FullLocation<'_> {
    fn fmt(&self, f: &mut Formatter) -> core::fmt::Result {
        for chunk in self.path.utf8_chunks() {
            f.write_str(chunk.valid())?;
            if !chunk.invalid().is_empty() {
                f.write_char(REPLACEMENT_CHARACTER)?;
            }
        }
        write!(f, ":{}", self.loc)
    }
}

impl<'path> FullLocation<'path> {
    /// The path to the file to which the location points
    pub fn path(&self) -> &Path {
        #[cfg(unix)]
        let res = <std::ffi::OsStr as std::os::unix::ffi::OsStrExt>::from_bytes(&self.path);

        #[cfg(not(unix))]
        let res = str::from_utf8(&self.path).expect("UTF-8 path when calling FullLocation::path");

        Path::new(res)
    }

    /// Returns an object that will display the location along with the line of the source code
    /// that it points to, Rust style
    pub fn with_source_line(&self) -> impl Display + '_ {
        let src = read_to_string(self.path()).unwrap_or_default();

        FullParsingError::<Infallible> {
            loc: FullLocation {
                path: Cow::Borrowed(&self.path),
                loc: self.loc,
            },
            reason: None,
            src: src.into(),
        }
    }

    /// Unbind the location from the lifetimes by allocating the path if it hasn't been already.
    pub fn own(self) -> FullLocation<'static> {
        FullLocation {
            path: self.path.into_owned().into(),
            loc: self.loc,
        }
    }
}
