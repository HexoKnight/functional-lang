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
    pub fn evaluate_success(src: &str) -> (Value<'_>, String) {
        let (typed_ir, ty) = type_check_success(src);
        match evaluate(&typed_ir) {
            Ok(o) => (o, ty),
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
        move |s: &str| ["(", body, ").\n  \\ ", signature, "\n", s].join("")
    }

    #[track_caller]
    pub fn parse_eq(src1: &str, src2: &str) {
        assert_eq!(parse_success(src1), parse_success(src2))
    }

    #[track_caller]
    pub fn evaluate_eq(src1: &str, src2: &str) {
        assert_eq!(evaluate_success(src1).0, evaluate_success(src2).0)
    }

    #[track_caller]
    pub fn evaluate_check_type(src1: &str, ty: &str) {
        assert_eq!(evaluate_success(src1).1, ty)
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
    evaluate_check_type(r"(\x:bool x)", "bool -> bool");
    evaluate_check_type(r" \x:bool x ", "bool -> bool");
    evaluate_check_type(r"\x:bool \ y : bool x", "bool -> bool -> bool");

    parse_failure(r"\x x");
    parse_failure(r"\x:bool");

    validate_failure(r"\x:bool y");
}

#[test]
fn basic_app() {
    type_check_failure(r"\x:bool x x");

    evaluate_check_type(r"(\x:bool x) true", "bool");
    evaluate_check_type(r"(\x: bool -> bool x) (\y: bool false)", "bool -> bool");
    evaluate_check_type(r"(\x: bool -> bool x)  \y: bool false ", "bool -> bool");

    parse_eq(
        r"(\x:()->()->bool x()()) (\x:() (\x:() false))",
        r"(\x:()->()->bool x()())  \x:()  \x:() false",
    );

    parse_eq(
        r"\x:bool ->  bool -> bool  x x x",
        r"\x:bool -> (bool -> bool)(x x)x",
    );

    evaluate_check_type(r"(\x: bool -> bool x) (\y: bool false)", "bool -> bool");
    evaluate_eq(r"(\x: bool -> bool x true) (\y: bool false)", r"false");
    evaluate_check_type(r"(\id:bool->bool id) (\x:bool x)", "bool -> bool");

    evaluate_eq(r"(\x:bool \y:bool (\z:bool z) x) false true", r"false");
}

#[test]
fn dot_app() {
    parse_eq(r"x.y z", r"y x z");
    parse_eq(r"x y.z", r"x (z y)");

    parse_eq(r"x.y .\x:() z.y a", r"(\x:() y z a)(y x)");

    parse_eq(r"x.\x:() z a.b", r"(\x:() z (b a)) x");

    evaluate_eq(r"().(\x:() false)", r"false");
    evaluate_eq(r"true.(\x:bool false)", r"true.\x:bool false");

    evaluate_eq(r"().(\x:() \y:() false) ()", r"false");
}

#[test]
fn complex_app() {
    let id = def(r"id:bool->bool", r"\x:bool x");
    let idf = def(r"idf:(bool->bool)->bool->bool", r"\x:bool->bool x");
    let c = def(r"c:bool->bool->bool", r"\x:bool \y:bool x");

    evaluate_check_type(
        &wrapped(&[&id, &idf, &c], r"(c true) ((idf id) false)"),
        "bool",
    );
    evaluate_check_type(
        &wrapped(&[&id, &idf, &c], r"idf (c (id true))"),
        "bool -> bool",
    );
    type_check_failure(&wrapped(&[&idf, &c], r"idf c"));

    evaluate_eq(
        &wrapped(&[&id, &idf, &c], r"(c true) ((idf id) false)"),
        r"true",
    );
    evaluate_check_type(
        &wrapped(&[&id, &idf, &c], r"idf (c (id true))"),
        "bool -> bool",
    );
}

#[test]
fn tuples() {
    evaluate_check_type(r"(true, false)", "(bool, bool)");
    evaluate_check_type(r"()", "()");
    evaluate_eq(r"(\x:(bool, ()) x) (false, ())", r"(false, ())");
    evaluate_eq(r"(\(x, y):(bool, bool) x) (false, true)", r"false");
    evaluate_eq(r"(\(x, x):(bool, bool) x) (false, true)", r"true");

    evaluate_check_type(
        r"\(x,y,(z,x)): ((),(),((),bool)) x",
        "((), (), ((), bool)) -> bool",
    );
    type_check_failure(r"\(x,y,(z,x)): ((),(),(),bool) x");
    type_check_failure(r"\(x,x):(bool,()) (\y:bool ()) x");

    evaluate_eq(r"(\(x,y,z):(bool,(),()) x) (true, (), ())", r"true")
}

#[test]
fn enums() {
    evaluate_check_type(r"\x: enum {} x", "enum {} -> enum {}");
    evaluate_check_type(
        r"\x: enum { single: enum {nested: enum {}} } x",
        "enum {single: enum {nested: enum {}}} -> enum {single: enum {nested: enum {}}}",
    );
    evaluate_check_type(
        r"\x: enum { some: bool, none: () } x",
        "enum {none: (), some: bool} -> enum {none: (), some: bool}",
    );

    parse_failure(r"\enum:() ()");
    parse_failure(r"enum enum {some:bool,none:()}");
    type_check_failure(r"enum enum {some:bool,none:()} otherlabel");
    evaluate_eq(
        r"enum enum {some:bool,none:()} some",
        r"enum enum {some:bool        } some",
    );

    evaluate_check_type(
        r"(\x: bool -> enum { some: bool, none: () } x) (enum enum {some:bool,none:()} some)",
        "bool -> enum {none: (), some: bool}",
    );

    evaluate_check_type(
        r"(\x: bool -> enum { some: bool, none: () } x) (enum enum {some:bool,none:()} some)",
        "bool -> enum {none: (), some: bool}",
    );

    type_check_failure(r"match enum {} {}");
    type_check_failure(
        r"match enum {some:bool,none:()} {
            hello(\x:bool ()),
            none(\():() ()),
        }",
    );
    type_check_failure(
        r"match enum {some:bool,none:()} {
            some(\x:bool x),
            none(\():() ()),
        }",
    );
    evaluate_check_type(
        r"match enum {
            some: bool,
            none: (),
        } {
            some \x:bool x,
            none \():() false,
        }",
        "enum {none: (), some: bool} -> bool",
    );
    evaluate_eq(
        r"
        (\x:
            enum {
                onlya: enum { a:() },
                none: enum { },
                onlyb: enum { b:bool },
            }
            -> enum { a:(), b:bool }
        x)
        match enum {
            onlya: enum { a:() },
            none: enum { },
            onlyb: enum { b:bool },
        } {
            onlya \x: enum { a:() } x,
            none  \x: enum { } x,
            onlyb \x: enum { b:bool } x,
        }
        (enum
            enum {
                onlyb: enum { b:bool },
            }
            onlyb (enum enum { b:bool } b false)
        )",
        r"enum enum { b:bool } b false",
    );
}

#[test]
fn subtyping() {
    evaluate_success(r"(). enum enum {a:()} a .\x:enum{a:(), new:()} x");
    evaluate_success(r"\x:(enum{}, ()) x.\x:(enum{new:()}, ()) x");
    evaluate_success(r"\x:enum{a:()} -> () x.\x:enum{} -> () x");
}
