//! Zero-dependency library with no-std support for writing parsers in a concise functional style
//! & with rich error-reporting.
//!
//! The library's structure can be represented as the trinity of
//! - [`Input`]
//! - [`Pattern`]
//!     All patterns live in the [`pattern`] module
//! - [`Parser`]
//!     All parsers live in the [`parser`] module
//!
//! The basic form of a parser is
//!
//! ```rust,ignore
//! use shrimple_parser::{Input, ParsingResult};
//!
//! fn foo<In: Input>(input: In) -> ParsingResult<In, Foo, FooParseError> { ... }
//! ```
//!
//! If the parser is infallible, i.e. never returns an unrecoverable error, it's customary to make
//! it generic over the reason type, to make combining it easier.
//!
//! ```rust,ignore
//! fn foo<In: Input, Reason>(input: In) -> ParsingResult<In, Foo, Reason> { ... }
//! ```
//!
//! Kinds of errors are distinguished via a user-defined `Reason` type, which signals what did
//! a parser expect.
//! A [`ParsingError`] can also have no reason, which will mean that the error is recoverable.
//!
//! The distinction between recoverable & fatal errors is important for parsers that need to try
//! multiple options.
//!
//! Error reporting with precise location in the source is facilitated by
//! constructing a [`FullParsingError`] with methods such as
//! [`Parser::with_full_error`], [`ParsingError::with_src_loc`]

#![cfg_attr(
    feature = "nightly",
    feature(unboxed_closures, fn_traits, tuple_trait, doc_cfg)
)]

mod error;
mod input;
mod loc;
pub mod parser;
pub mod pattern;
pub mod tuple;
pub mod utils;

pub use {
    error::{FullParsingError, ParsingError, ParsingResult},
    input::Input,
    loc::{FullLocation, Location},
    parser::{MappingParser, Parser},
    pattern::Pattern,
};

#[cfg(feature = "proc-macro2")]
pub use loc::LineColumnToLocationError;
