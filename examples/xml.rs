//! This is an example of an XML parser implemented with `shrimple_parser`

use {
    core::fmt::{Display, Formatter},
    shrimple_parser::{
        from_tuple, match_out, parse_whitespace,
        pattern::{parse, parse_until, parse_until_ex, NotEscaped},
        ready, Input, Parser, ParsingError, ParsingResult,
    },
    std::env::args,
};

#[derive(Debug, Clone)]
enum Error {
    TagUnclosed,
    NoAttrValue,
    UnclosedString,
}

impl Display for Error {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        f.write_str(match self {
            Self::TagUnclosed => "expected the tag closed with `>`",
            Self::NoAttrValue => "expected an attribute value enclosed in quotes",
            Self::UnclosedString => "expected the string closed with `\"`",
        })
    }
}

#[derive(Debug, Clone)]
struct Attr<In> {
    name: In,
    value: Option<In>,
}

#[derive(Debug, Clone)]
enum Fragment<In> {
    Tag {
        self_closing: bool,
        name: In,
        attrs: Vec<Attr<In>>,
    },
    ClosingTag {
        name: In,
    },
    Text(In),
}

fn parse_ident<In: Input, Reason>(input: In) -> ParsingResult<In, In, Reason> {
    parse_until(|c| ['>', '/', '='].contains(&c) || c.is_whitespace())
        .filter(|i: &In| !i.is_empty())
        .parse(input)
}

fn parse_string<In: Input>(input: In) -> ParsingResult<In, In, Error> {
    parse('"')
        .then(parse_until_ex(NotEscaped('\\', '"')).or_reason(Error::UnclosedString))
        .parse(input)
}

fn parse_attr<In: Input>(input: In) -> ParsingResult<In, Attr<In>, Error> {
    parse_ident
        .skip(parse_whitespace)
        .and(
            parse('=')
                .skip(parse_whitespace)
                .then(parse_string.or_reason(Error::NoAttrValue))
                .skip(parse_whitespace)
                .maybe(),
        )
        .map_out(from_tuple!(Attr { name, value }))
        .parse(input)
}

fn parse_tag<In: Input>(input: In) -> ParsingResult<In, Fragment<In>, Error> {
    parse_whitespace::<In, Error>
        .then(parse('<'))
        .then(parse_whitespace)
        .then(parse('/').ok())
        .skip(parse_whitespace)
        .and(parse_ident)
        .skip(parse_whitespace)
        .map(match_out! {
            (true, name) => ready(Fragment::ClosingTag { name }),
            (false, name) => parse_attr
                .collect()
                .and(parse('/').ok())
                .skip(parse_whitespace)
                .map_out(|(attrs, self_closing)| Fragment::Tag { self_closing, name: name.clone(), attrs })
        })
        .skip(parse_whitespace)
        .skip(parse('>').or_reason(Error::TagUnclosed))
        .parse(input)
}

fn xml_fragments<In: Input>(
    input: In,
) -> impl Iterator<Item = Result<Fragment<In>, ParsingError<In, Error>>> {
    parse_tag
        .or_nonempty(parse_until('<').map_out(Fragment::Text))
        .iter(input)
}

// TODO: analog to `.with_source_line()` without FS access
fn main() {
    let input = args().nth(1).expect("XML input");
    for fragment in xml_fragments(&*input) {
        match fragment {
            Ok(fragment) => println!("{fragment:?}"),
            Err(e) => eprintln!("{}", e.with_src_loc("<input>", &input)),
        }
    }
}
