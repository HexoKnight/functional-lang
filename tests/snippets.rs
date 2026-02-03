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
    fn parse_success(src: &str) -> Term<'_> {
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
    fn validate_success(src: &str) -> untyped_ir::Term<'_> {
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
    fn type_check_success(src: &str) -> (typed_ir::Term<'_>, String) {
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
    fn evaluate_success(src: &str) -> (Value<'_>, String) {
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
    pub fn type_check_eq(src1: &str, src2: &str) {
        assert_eq!(type_check_success(src1), type_check_success(src2))
    }

    #[track_caller]
    pub fn type_check_type_eq(src1: &str, src2: &str) {
        assert_eq!(type_check_success(src1).1, type_check_success(src2).1)
    }

    #[track_caller]
    pub fn evaluate_eq(src1: &str, src2: &str) {
        assert_eq!(evaluate_success(src1).0, evaluate_success(src2).0)
    }

    #[track_caller]
    pub fn evaluate_check_type(src: &str, ty: &str) {
        assert_eq!(evaluate_success(src).1, ty)
    }
}

#[test]
fn comments() {
    evaluate_eq(r"\x:bool x // comment", r"\x:bool x");
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

    type_check_failure(r"\x x");
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
fn records() {
    evaluate_check_type(r"{a:true, b:()}", "{a: bool, b: ()}");
    evaluate_check_type(r"{}", "{}");
    evaluate_eq(
        r"(\x:{a: bool, b:{}} x) {a:false, b:{}}",
        r"{a: false, b: {}}",
    );
    validate_failure(r"\{a, b:x} b");
    evaluate_eq(
        r"(\{a, b:x}:{a:bool, b:bool} a) {a:false, b:true}",
        r"false",
    );
    evaluate_eq(
        r"(\{a:x, b:x}:{a:bool, b:bool} x) {a:false, b:true}",
        r"true",
    );

    evaluate_check_type(
        r"\{x,y,z:{w,x}}: {x:{},y:{},z:{w:{},x:bool}} x",
        "{x: {}, y: {}, z: {w: {}, x: bool}} -> bool",
    );
    type_check_failure(r"\{x,y,z:{w,x}}: {x:{},y:{},z:{},w:bool} x");
    type_check_failure(r"\{x,y:x}:{x:bool,y:{}} (\y:bool {}) x");
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

    parse_failure(r"\enum ()");
    parse_failure(r"enum: enum {some:bool,none:()}");
    type_check_failure(r"enum: bool otherlabel ()");
    evaluate_eq(
        r"enum some .\x: bool -> enum {some:bool,none:()} x",
        r"enum some .\x: bool -> enum {some:bool        } x",
    );

    evaluate_check_type(
        r"(\x: bool -> enum { some: bool, none: () } x) (enum some)",
        "bool -> enum {none: (), some: bool}",
    );

    evaluate_check_type(
        r"(\x: bool -> enum { some: bool, none: () } x) (enum some)",
        "bool -> enum {none: (), some: bool}",
    );

    evaluate_check_type(r"match {}", "enum {} -> !");
    validate_failure(r"match: enum {none:(),none:()} { none\():()()}");
    validate_failure(r"match { none\():()(), none\():()()}");

    type_check_failure(
        r"match: enum {some:bool,none:()} {
            none\x:()x,
        }",
    );
    type_check_failure(
        r"match: enum {some:bool,none:()} {
            hello(\x:bool ()),
            none(\():() ()),
        }",
    );
    type_check_failure(
        r"match: enum {some:bool,none:()} {
            some(\x:bool x),
            none(\():() ()),
        }",
    );
    evaluate_check_type(
        r"match {
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
        match {
            onlya \x: enum { a:() } x,
            none  \x: enum { } x,
            onlyb \x: enum { b:bool } x,
        }
        (enum
            onlyb (enum b false)
        )",
        r"enum: bool b false",
    );

    validate_failure("match: enum{} { a notfound }");
}

#[test]
fn subtyping() {
    evaluate_check_type(
        r"(). enum a .\x:enum{a:(), new:()} x",
        "enum {a: (), new: ()}",
    );
    evaluate_check_type(
        r"\x:(enum{}, ()) x.\x:(enum{new:()}, ()) x",
        "(enum {}, ()) -> (enum {new: ()}, ())",
    );
    evaluate_check_type(
        r"\x:enum{a:()} -> () x.\x:enum{} -> () x",
        "(enum {a: ()} -> ()) -> enum {} -> ()",
    );
}

#[test]
fn never() {
    evaluate_check_type(
        r"\never:enum{} never.match {} .\actualnever:! actualnever",
        "enum {} -> !",
    );
    evaluate_check_type(
        r"\x:! x.\anytype: (bool, (), enum{}) anytype",
        "! -> (bool, (), enum {})",
    );
}

#[test]
fn any() {
    evaluate_check_type(
        r"match: enum{a:(), b:bool} {a\x:_ x, b\x:_ x}",
        "enum {a: (), b: bool} -> _",
    );

    evaluate_check_type(r"true .\x:_ x", "_");
    evaluate_check_type(r"\x:enum{a:()} x.\x:_ x", "enum {a: ()} -> _");
}

#[test]
fn ty_abs() {
    evaluate_check_type(r"?T \x:T x", "[T] T -> T");
    evaluate_check_type(
        r"?T<enum{a:()} \x:T x.match {a\():()()}",
        "[T <enum {a: ()}] T -> ()",
    );

    type_check_type_eq(
        r"(?T<bool \x:T x)",
        r"(?T      \x:T x) .\id: [T<bool] T -> T id",
    );
    type_check_type_eq(
        r"(?T       \x:T x)",
        r"(?T <_ >! \x:T x) .\id: [T] T -> T id",
    );
}

#[test]
fn ty_app() {
    evaluate_eq(r"(?T \x:T x) [bool] true", "true");
    type_check_eq(
        r"(?T \x:T x) .\id: [T] T -> T id",
        r"(?A \a:A a) .\id: [T] T -> T id",
    );
    type_check_eq(
        r"(?T<bool \x:T x) .\id: [T<bool] T -> T id",
        r"(?T      \x:T x) .\id: [T<bool] T -> T id",
    );

    evaluate_check_type(r"(?T<enum{a:()} \x:T x) [enum{}]", "enum {} -> enum {}");
    evaluate_check_type(
        r"?T<enum{a:()} enum: T e",
        "[T <enum {a: ()}] T -> enum {e: T}",
    );
    evaluate_check_type(
        r"(?T<enum{a:()} enum: T e) [enum{}]",
        "enum {} -> enum {e: enum {}}",
    );

    evaluate_check_type(
        r"?A ?R ?F<A->R \(f, a):(F, A) f a",
        "[A] [R] [F <A -> R] (F, A) -> R",
    );
    evaluate_check_type(r"?A ?R \(f, a):(A->R, A) f a", "[A] [R] (A -> R, A) -> R");
    evaluate_check_type(
        r"?A ?B ?R \(f, a, b):(A->B->R, A, B) f a b",
        "[A] [B] [R] (A -> B -> R, A, B) -> R",
    );

    evaluate_check_type(r"?T<bool \x:T x.\x:bool x", "[T <bool] T -> bool");
    type_check_failure(r" ?T ?R   \t:T \f:T -> R (t, f t) .\x:(R, R) x");
    #[rustfmt::skip]
    evaluate_check_type(r"?T ?R>T \t:T \f:T -> R (t, f t) .\x:(R, R) x",
        "[T] [R >T] T -> (T -> R) -> (R, R)",
    );

    evaluate_check_type(r"?T ?R>T \t:T t.\r:R r", "[T] [R >T] T -> R");
    evaluate_check_type(
        r"?A ?T<A ?R>A \t:T t.\a:A a.\r:R r",
        "[A] [T <A] [R >A] T -> R",
    );
    evaluate_check_type(r"?A ?T<A ?R>A \t:T t.\r:R r", "[A] [T <A] [R >A] T -> R");

    evaluate_check_type(r"?A (?B (?C \x:C x)[B])[bool]", "[A] bool -> bool");
    evaluate_check_type(r"?A (?B (?C \x:A x)[B])[bool]", "[A] A -> A");

    evaluate_check_type(
        r"match {
            a\():() ?A<bool \a:A (a, true),
            b\():() ?B>bool \b:B (b, false),
        }",
        "enum {a: (), b: ()} -> [A <bool >bool] A -> (A, bool)",
    );
}

#[test]
fn type_inference() {
    evaluate_check_type(r"(\e e.match {}) .\x:enum{} -> bool x", "enum {} -> bool");
    evaluate_check_type(r"match {} .\x:enum{} -> bool x", "enum {} -> bool");

    evaluate_check_type(r"enum wrap .\x:bool->_ x", "bool -> _");

    evaluate_check_type(
        r"(\op: (bool, bool -> ()) -> () op (false, \x ())) (\(b, f) f b)",
        "()",
    );
    evaluate_check_type(
        r"
        (\op: enum {a:(), b:()} -> ()
            op (enum a ())
        )
        (\e
            (\() ()).
                \id:()->()

            (e.match {a id, b id}).
                \():()

            e.match {a id, b id, c id}
        )",
        "()",
    );
    evaluate_check_type(
        r"
        (\() ()). \id:()->()
        (\op: enum {a:(), b:()} -> ()
            op (enum a ())
        )
        match: enum{a:(),b:(),c:()} {a id, b id, c id}",
        "()",
    );
    type_check_failure(
        r"
        (\() ()). \id:()->()
        (\op: enum {a:(), b:()} -> ()
            op (enum a ())
        )
        match {a id, b id, c id}",
    );
}

#[test]
fn type_arg_inference() {
    evaluate_eq(
        r"(?A \a a) .\id:[A]A->A \b:bool id [bool] b",
        r"(?A \a a) .\id:[A]A->A \b:bool id        b",
    );
    evaluate_check_type(
        r"(?A \a a) .\id:[A]A->A \b:bool id        b",
        "bool -> bool",
    );

    evaluate_check_type(r"\id:[A]A->A id true", "([A] A -> A) -> bool");
    evaluate_check_type(r"\x:bool \id:[A]A->A id x", "bool -> ([A] A -> A) -> bool");
    type_check_failure(r"\x:! \id:[A]A->A id x");

    evaluate_check_type(r"(?T \x:T x) true", "bool");
    // may relax in the future
    type_check_failure(r"(?T \x:bool x) true");

    let uncurry = def(
        "uncurry: [A] [B] [C] (A -> B -> C) -> ((A, B) -> C)",
        r"?A ?B ?C \f \(a, b) f a b",
    );

    let k = def("K: [T] T -> () -> T", r"?T \x \() x");
    let k2 = def("KK: [T] [U] T -> U -> T", r"?T ?U \x \u x");

    let delay = def(
        "delay: [A] [B] [C] (A -> B -> C) -> A -> B -> C",
        r"?A ?B ?C \f \a \b f a b",
    );

    evaluate_check_type(
        &wrapped(&[&uncurry, &k], r"(K [bool]).uncurry (K true (), ())"),
        "bool",
    );
    type_check_failure(&wrapped(&[&delay, &k], r"delay K true ()"));
    evaluate_check_type(&wrapped(&[&delay, &k], r"delay (K[bool]) true ()"), "bool");

    evaluate_check_type(&wrapped(&[&k2], r"KK true ()"), "bool");

    let map = def(
        "map: [T] [R] (T -> R) -> enum {some:T,none:()} -> enum {some:R,none:()}",
        r"
        ?T ?R \f
            match {
                some(\t enum some (f t)),
                none enum none,
            }
        ",
    );

    evaluate_check_type(
        &wrapped(&[&map], r"map (\b:bool ())"),
        "enum {none: (), some: bool} -> enum {none: (), some: ()}",
    );

    evaluate_check_type(
        &wrapped(&[&map], r"?A map enum: A wrap"),
        "[A] enum {none: (), some: A} -> enum {none: (), some: enum {wrap: A}}",
    );

    evaluate_check_type(
        &wrapped(&[&map], r"?A map (enum wrap .\x:A->_ x)"),
        "[A] enum {none: (), some: A} -> enum {none: (), some: _}",
    );

    evaluate_check_type(r"(?A \a:A a) true", "bool");
    evaluate_check_type(
        r"(\() ?A \a:A a) .\f: () -> bool -> bool f",
        "() -> bool -> bool",
    );

    evaluate_check_type(
        r"(?T \t t).\id:[T]T->T match {wrap id [bool]}",
        "enum {wrap: bool} -> bool",
    );
    evaluate_check_type(
        r"(?T \t t).\id:[T]T->T match {wrap id} .\x:enum{wrap:bool}->bool x",
        "enum {wrap: bool} -> bool",
    );
    // inference is very local currently (app <-> match <-> id is 2 separations)
    type_check_failure(r"(?T \t t).\id:[T]T->T match {wrap id} (enum wrap true)");
}
