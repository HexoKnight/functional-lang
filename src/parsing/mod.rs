use lalrpop_util::lalrpop_mod;

use crate::reprs::ast::Term;

lalrpop_mod!(
    #[allow(clippy::pedantic)]
    syntax,
    "/parsing/syntax.rs"
);

type ParseError<'i> =
    lalrpop_util::ParseError<usize, lalrpop_util::lexer::Token<'i>, UserParserError>;

type UserParserError = String;

#[derive(Default)]
pub struct Parser {
    term_parser: syntax::TermParser,
}
impl Parser {
    pub fn parse<'i>(&self, input: &'i str) -> Result<Term<'i>, ParseError<'i>> {
        self.term_parser.parse(input)
    }
}

#[cfg(test)]
pub mod tests {
    use pretty_assertions::assert_eq;

    use super::*;

    #[track_caller]
    pub(crate) fn parse_success(src: &str) -> Term<'_> {
        match Parser::default().parse(src) {
            Ok(o) => o,
            Err(e) => panic!("parse failure:\n'{}'\n{}", src, e),
        }
    }

    #[track_caller]
    pub(crate) fn parse_failure(src: &'_ str) -> ParseError<'_> {
        match Parser::default().parse(src) {
            Ok(o) => panic!("parse success:\n'{}'\n{:#?}", src, o),
            Err(e) => e,
        }
    }

    #[track_caller]
    fn parse_eq(src1: &str, src2: &str) {
        assert_eq!(parse_success(src1), parse_success(src2))
    }

    #[test]
    fn parsing() {
        parse_success(r"\x:bool x // comment");
        #[rustfmt::skip]
        parse_failure(r"
            \
            // x:bool
        ");

        parse_success(r"\x:bool x");
        parse_success(r"(\x:bool x)");
        parse_success(r"\x:bool \ y : bool x");
        parse_failure(r"\x x");
        parse_failure(r"\x:bool");

        parse_success(r"\x:bool x x");

        parse_success(r"(\x:bool x) true");
        parse_success(r"(\x: bool -> bool x) (\y: bool false)");
        parse_failure(r"(\x: bool -> bool x)  \y: bool false");
        parse_eq(
            r"\x:bool ->  bool -> bool  x x x",
            r"\x:bool -> (bool -> bool)(x x)x",
        )
    }
}
