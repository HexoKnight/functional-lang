use derive_where::derive_where;

use crate::{common::WithInfo, reprs::common::Span};

pub type Term<'i> = WithInfo<Span<'i>, RawTerm<'i>>;

#[derive(Eq, PartialEq, Debug)]
pub enum RawTerm<'i> {
    Abs {
        arg: Assignee<'i>,
        arg_type: Option<Type<'i>>,

        effects: Option<EffectGroup<'i, Effect<'i>>>,

        body: Box<Term<'i>>,
    },
    App {
        func: Box<Term<'i>>,

        effects: Option<EffectGroup<'i, Ident<'i>>>,

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

    Type(Type<'i>),

    Handle(Effect<'i>),
    Trigger(Effect<'i>),

    Import(ImportPath<'i>),

    Fold(Option<Type<'i>>),
    Unfold(Option<Type<'i>>),

    Enum(Option<Type<'i>>, Ident<'i>),
    Match(Option<Type<'i>>, Box<[(Ident<'i>, Term<'i>)]>),

    Record(Box<[(Ident<'i>, Option<Term<'i>>)]>),

    Tuple(Box<[Term<'i>]>),

    Bool(bool),
}

pub type Assignee<'i> = WithInfo<Span<'i>, RawTermAssignee<'i>>;
pub type TypeAssignee<'i> = WithInfo<Span<'i>, RawTypeAssignee<'i>>;

#[derive(Eq, PartialEq, Debug)]
pub enum RawAssignee<'i, A> {
    Record(Box<[(Ident<'i>, Option<A>)]>),
    Tuple(Box<[A]>),
    Ident(Ident<'i>),
}
#[derive(Eq, PartialEq, Debug)]
pub enum RawTermAssignee<'i> {
    Term(RawAssignee<'i, Assignee<'i>>),
    Type(TypeAssignee<'i>),
}
#[derive(Eq, PartialEq, Debug)]
pub struct RawTypeAssignee<'i>(pub RawAssignee<'i, TypeAssignee<'i>>);

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
    TyApp {
        abs: Box<Type<'i>>,
        arg: Box<Type<'i>>,
    },

    RecAbs {
        arg: Ident<'i>,
        result: Box<Type<'i>>,
    },

    TyVar(Ident<'i>),

    Arr {
        arg: Box<Type<'i>>,

        effects: Option<EffectGroup<'i, Effect<'i>>>,

        result: Box<Type<'i>>,
    },

    Enum(Box<[(Ident<'i>, Type<'i>)]>),
    Record(Box<[(Ident<'i>, Option<Type<'i>>)]>),
    Tuple(Box<[Type<'i>]>),

    Bool,
    Any,
    Never,
}

pub type Effect<'i> = WithInfo<Span<'i>, RawEffect<'i>>;

#[derive(Eq, PartialEq, Debug)]
pub enum RawEffect<'i> {
    Def {
        name: Ident<'i>,
        arg: Box<Type<'i>>,
        result: Box<Type<'i>>,
    },
}

#[derive(Eq, PartialEq, Debug)]
#[derive_where(Default)]
pub struct EffectGroup<'i, T>(pub Box<[(Option<Ident<'i>>, T)]>);
