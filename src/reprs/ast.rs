use crate::{common::WithInfo, reprs::common::Span};

pub type Term<'i> = WithInfo<Span<'i>, RawTerm<'i>>;

#[derive(Eq, PartialEq, Debug)]
pub enum RawTerm<'i> {
    Abs {
        arg: Assignee<'i>,
        arg_type: Option<Type<'i>>,

        body: Box<Term<'i>>,
    },
    App {
        func: Box<Term<'i>>,
        arg: Box<Term<'i>>,
    },

    TyAbs {
        arg: Ident<'i>,
        bounds: TyBounds<'i>,

        body: Box<Term<'i>>,
    },
    TyApp {
        func: Box<Term<'i>>,
        arg: Box<Type<'i>>,
    },

    Var(Ident<'i>),

    Import(ImportPath<'i>),

    Enum(Option<Type<'i>>, Ident<'i>),
    Match(Option<Type<'i>>, Box<[(Ident<'i>, Term<'i>)]>),

    Record(Box<[(Ident<'i>, Term<'i>)]>),

    Tuple(Box<[Term<'i>]>),

    Bool(bool),
}

pub type Assignee<'i> = WithInfo<Span<'i>, RawAssignee<'i>>;

#[derive(Eq, PartialEq, Debug)]
pub enum RawAssignee<'i> {
    Record(Box<[(Ident<'i>, Option<Assignee<'i>>)]>),
    Tuple(Box<[Assignee<'i>]>),
    Ident(Ident<'i>),
}

#[derive(Eq, PartialEq, Debug)]
pub struct TyBounds<'i> {
    pub upper: Option<Type<'i>>,
    pub lower: Option<Type<'i>>,
}

#[derive(Debug)]
pub enum ImportPath<'i> {
    Relative {
        span: Span<'i>,
    },
    Package {
        span: Span<'i>,
        package: Span<'i>,
        path: Span<'i>,
    },
}

impl Eq for ImportPath<'_> {}
impl PartialEq for ImportPath<'_> {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (ImportPath::Relative { span }, ImportPath::Relative { span: other_span }) => {
                span.text() == other_span.text()
            }
            (
                ImportPath::Package { span, .. },
                ImportPath::Package {
                    span: other_span, ..
                },
            ) => span.text() == other_span.text(),
            _ => false,
        }
    }
}

#[derive(Debug)]
pub struct Ident<'i>(pub Span<'i>);

impl Eq for Ident<'_> {}
impl PartialEq for Ident<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.0.text() == other.0.text()
    }
}

pub type Type<'i> = WithInfo<Span<'i>, RawType<'i>>;

#[derive(Eq, PartialEq, Debug)]
pub enum RawType<'i> {
    TyAbs {
        arg: Ident<'i>,
        bounds: Box<TyBounds<'i>>,
        result: Box<Type<'i>>,
    },

    TyVar(Ident<'i>),

    Arr {
        arg: Box<Type<'i>>,
        result: Box<Type<'i>>,
    },

    Enum(Box<[(Ident<'i>, Type<'i>)]>),
    Record(Box<[(Ident<'i>, Type<'i>)]>),
    Tuple(Box<[Type<'i>]>),

    Bool,
    Any,
    Never,
}
