use self::utils::*;

mod utils {
    use pretty_assertions::assert_eq;

    use functional_lang::{
        evaluation::evaluate,
        parsing::{ParseError, Parser},
        reprs::{ast::Term, typed_ir, untyped_ir, value::Value},
        typing::{TypeCheckError, type_check},
        validation::{ValidationError, validate},
    };

    #[track_caller]
    pub fn parse_success(src: &str) -> Term<'_> {
        match Parser::default().parse(src) {
            Ok(o) => o,
            Err(e) => panic!("parse failure:\n'{}'\n{}", src, e),
        }
    }

    #[track_caller]
    pub fn parse_failure(src: &'_ str) -> ParseError<'_> {
        match Parser::default().parse(src) {
            Ok(o) => panic!("parse success:\n'{}'\n{:#?}", src, o),
            Err(e) => e,
        }
    }

    #[track_caller]
    pub fn validate_success(src: &str) -> untyped_ir::Term<'_> {
        let ast = parse_success(src);
        match validate(&ast) {
            Ok(o) => o,
            Err(e) => panic!("validate failure:\n'{}'\n{}", src, e),
        }
    }

    #[track_caller]
    pub fn validate_failure(src: &str) -> ValidationError {
        let ast = parse_success(src);
        match validate(&ast) {
            Ok(o) => panic!("validate success:\n'{}'\n{:#?}", src, o),
            Err(e) => e,
        }
    }

    #[track_caller]
    pub fn type_check_success(src: &str) -> (typed_ir::Term<'_>, String) {
        let untyped_ir = validate_success(src);
        match type_check(&untyped_ir) {
            Ok(o) => o,
            Err(e) => panic!("type check failure:\n'{}'\n{}", src, e),
        }
    }

    #[track_caller]
    pub fn type_check_failure(src: &str) -> TypeCheckError {
        let ast = validate_success(src);
        match type_check(&ast) {
            Ok(o) => panic!("type check success:\n'{}'\n{:#?}", src, o),
            Err(e) => e,
        }
    }

    #[track_caller]
    pub fn evaluate_success(src: &str) -> Value<'_> {
        let (typed_ir, _) = type_check_success(src);
        match evaluate(&typed_ir) {
            Ok(o) => o,
            Err(e) => panic!("evaluate failure:\n'{}'\n{}", src, e),
        }
    }

    pub fn wrapped(wrappers: &[impl Fn(&str) -> String], inner: &str) -> String {
        let mut res = inner.to_string();
        for wrapper in wrappers {
            res = wrapper(&res);
        }
        res
    }

    pub fn def(signature: &str, body: &str) -> impl Fn(&str) -> String {
        move |s: &str| [r"(\", signature, "(", s, "))(", body, ")"].join("\n")
    }

    #[track_caller]
    pub fn parse_eq(src1: &str, src2: &str) {
        assert_eq!(parse_success(src1), parse_success(src2))
    }

    #[track_caller]
    pub fn evaluate_eq(src1: &str, src2: &str) {
        assert_eq!(evaluate_success(src1), evaluate_success(src2))
    }
}

#[test]
fn comments() {
    evaluate_success(r"\x:bool x // comment");
    #[rustfmt::skip]
    parse_failure(r"
        \
        // x:bool x
    ");
}

#[test]
fn basic_abs() {
    evaluate_success(r"(\x:bool x)");
    evaluate_success(r"\x:bool x");
    evaluate_success(r"\x:bool \ y : bool x");

    parse_failure(r"\x x");
    parse_failure(r"\x:bool");

    validate_failure(r"\x:bool y");
}

#[test]
fn basic_app() {
    type_check_failure(r"\x:bool x x");

    evaluate_success(r"(\x:bool x) true");
    evaluate_success(r"(\x: bool -> bool x) (\y: bool false)");

    parse_failure(r"(\x: bool -> bool x)  \y: bool false");
    parse_eq(
        r"\x:bool ->  bool -> bool  x x x",
        r"\x:bool -> (bool -> bool)(x x)x",
    );

    evaluate_success(r"(\x: bool -> bool x) (\y: bool false)");
    evaluate_eq(r"(\x: bool -> bool x true) (\y: bool false)", r"false");
    evaluate_success(r"(\id:bool->bool id) (\x:bool x)");

    evaluate_eq(r"(\x:bool \y:bool (\z:bool z) x) false true", r"false");

    let id = def(r"id:bool->bool", r"\x:bool x");
    let idf = def(r"idf:(bool->bool)->bool->bool", r"\x:bool->bool x");
    let c = def(r"c:bool->bool->bool", r"\x:bool \y:bool x");

    evaluate_success(&wrapped(&[&id, &idf, &c], r"(c true) ((idf id) false)"));
    evaluate_success(&wrapped(&[&id, &idf, &c], r"idf (c (id true))"));
    type_check_failure(&wrapped(&[&idf, &c], r"idf c"));

    evaluate_eq(
        &wrapped(&[&id, &idf, &c], r"(c true) ((idf id) false)"),
        r"true",
    );
    evaluate_success(&wrapped(&[&id, &idf, &c], r"idf (c (id true))"));
}

#[test]
fn tuples() {
    evaluate_success(r"(true, false)");
    evaluate_success(r"()");
    evaluate_eq(r"(\x:(bool, ()) x) (false, ())", r"(false, ())");
    evaluate_eq(r"(\(x, y):(bool, bool) x) (false, true)", r"false");
    evaluate_eq(r"(\(x, x):(bool, bool) x) (false, true)", r"true");

    evaluate_success(r"\(x,y,(z,x)): ((),(),((),bool)) x");
    type_check_failure(r"\(x,y,(z,x)): ((),(),(),bool) x");
    type_check_failure(r"\(x,x):(bool,()) (\y:bool ()) x");

    evaluate_eq(r"(\(x,y,z):(bool,(),()) x) (true, (), ())", r"true")
}

#[test]
fn enums() {
    evaluate_success(r"\x: enum {} x");
    evaluate_success(r"\x: enum { single: enum {nested: enum {}} } x");
    evaluate_success(r"\x: enum { some: bool, none: () } x");

    parse_failure(r"\enum:() ()");
    parse_failure(r"enum enum {some:bool,none:()}");
    type_check_failure(r"enum enum {some:bool,none:()} otherlabel");
    evaluate_eq(
        r"enum enum {some:bool,none:()} some",
        r"enum enum {some:bool        } some",
    );

    evaluate_success(
        r"(\x: bool -> enum { some: bool, none: () } x) (enum enum {some:bool,none:()} some)",
    );

    evaluate_success(
        r"(\x: bool -> enum { some: bool, none: () } x) (enum enum {some:bool,none:()} some)",
    );
}
