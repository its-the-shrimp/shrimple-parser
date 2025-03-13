extern crate alloc;

use {
    crate::{utils::PathLike, FullLocation, Input, Location},
    alloc::borrow::Cow,
    core::{
        convert::Infallible,
        error::Error,
        fmt::{Debug, Display, Formatter},
        ops::Not,
    },
    std::{fs::read_to_string, io},
};

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
        write!(
            f,
            "error source: {}{}",
            self.rest[..self.rest.len().min(16)].escape_debug(),
            if self.rest.len() > 16 { "..." } else { "" }
        )?;
        Ok(())
    }
}

impl<In: Input, Reason: Error> Error for ParsingError<In, Reason> {}

impl<In, Reason> ParsingError<In, Reason> {
    /// Create a new fatal parsing error.
    pub const fn new(rest: In, reason: Reason) -> Self {
        Self {
            rest,
            reason: Some(reason),
        }
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
    pub fn reason<NewReason>(self, reason: NewReason) -> ParsingError<In, NewReason> {
        ParsingError {
            reason: Some(reason),
            rest: self.rest,
        }
    }

    /// Makes a recoverable error fatal by giving it a reason, if it's already fatal, does nothing
    #[must_use]
    pub fn or_reason(self, reason: Reason) -> Self {
        Self {
            reason: self.reason.or(Some(reason)),
            rest: self.rest,
        }
    }

    /// Like [`ParsingError::or_reason`] but does nothing if the rest of the input is empty
    #[must_use]
    pub fn or_reason_if_nonempty(self, reason: Reason) -> Self
    where
        In: Input,
    {
        Self {
            reason: self
                .reason
                .or_else(|| self.rest.is_empty().not().then_some(reason)),
            rest: self.rest,
        }
    }

    /// Transforms the reason by calling `f`, except if it's a recoverable error,
    /// in which case it remains recoverable.
    pub fn map_reason<NewReason>(
        self,
        f: impl FnOnce(Reason) -> NewReason,
    ) -> ParsingError<In, NewReason> {
        ParsingError {
            reason: self.reason.map(f),
            rest: self.rest,
        }
    }

    /// Convert the reason of an always recoverable error to another type. This will be a no-op
    /// since it's statically guaranteed that the reason doesn't exist.
    #[allow(unreachable_code)]
    pub fn adapt_reason<NewReason>(self) -> ParsingError<In, NewReason>
    where
        Infallible: From<Reason>,
    {
        ParsingError {
            reason: self.reason.map(|x| match Infallible::from(x) {}),
            rest: self.rest,
        }
    }

    /// Turns the error into a [`FullParsingError`] for a more informative report.
    ///
    /// The error will point to the provided source code.
    /// The provided path will only be used for display purposes, this method won't access the file
    /// system.
    pub fn with_src_loc<'a>(
        self,
        path: impl PathLike<'a>,
        src: &'a str,
    ) -> FullParsingError<'a, Reason>
    where
        In: Input,
    {
        FullParsingError {
            loc: Location::find_saturating(self.rest.as_ptr(), src).with_path(path),
            reason: self.reason,
            src: src.into(),
        }
    }

    /// Turns this error into a [`FullParsingError`] that points to a file on the machine, for a more informative report.
    ///
    /// # Errors
    /// Returns an error if [`std::fs::read_to_string`] does.
    #[cfg(feature = "std")]
    pub fn with_file_loc<'a>(
        self,
        path: impl PathLike<'a>,
    ) -> io::Result<FullParsingError<'a, Reason>>
    where
        In: Input,
    {
        let path = path.into_path();
        let src = read_to_string(&path)?;
        Ok(FullParsingError {
            loc: Location::find_saturating(self.rest.as_ptr(), &src).with_path(path),
            reason: self.reason,
            src: src.into(),
        })
    }
}

/// A final error with information about where in the source did the error occur.
///
/// This should be constructed at the top-level of a parser as the final action before returning
/// the result. Main ways to construct this are [`ParsingError::with_src_loc`] and
/// [`Parser::with_full_error`]
///
/// To print the source line of the error along with the reason & location, use the value returned
/// by its method [`with_source_line`](Self::with_source_line),
/// this will alter its [`Display`] implementation.
#[derive(Debug, Clone)]
pub struct FullParsingError<'a, Reason> {
    /// Where the error occured.
    pub loc: FullLocation<'a>,
    /// What the parser expected to see at the location of the error.
    /// If `None`, then the error was recoverable and the parser didn't have any particular
    /// reason.
    pub reason: Option<Reason>,
    /// The source code to which the error points.
    pub src: Cow<'a, str>,
}

impl<Reason: Display> Display for FullParsingError<'_, Reason> {
    fn fmt(&self, f: &mut Formatter) -> core::fmt::Result {
        if let Some(reason) = &self.reason {
            writeln!(f, "{reason}")?;
        }
        writeln!(f, "--> {}", self.loc)?;
        let line = self
            .src
            .lines()
            .nth(self.loc.loc.line.get() as usize - 1)
            .ok_or(core::fmt::Error)?;
        let line_col_off = self.loc.loc.line.ilog10() as usize + 1;
        writeln!(f, "{:line_col_off$} |", "")?;
        writeln!(f, "{:line_col_off$} | {line}", self.loc.loc.line)?;
        write!(
            f,
            "{:line_col_off$} | {:>2$}",
            "",
            '^',
            self.loc.loc.col as usize + 1
        )?;
        Ok(())
    }
}

impl<Reason: Error> Error for FullParsingError<'_, Reason> {}

impl<Reason> FullParsingError<'_, Reason> {
    /// Unbind the error from the lifetimes by allocating the file path if it hasn't been already.
    pub fn own(self) -> FullParsingError<'static, Reason> {
        FullParsingError {
            loc: self.loc.own(),
            src: self.src.into_owned().into(),
            ..self
        }
    }
}

/// The result of a parser.
pub type ParsingResult<In, T, Reason = Infallible> =
    core::result::Result<(In, T), ParsingError<In, Reason>>;
