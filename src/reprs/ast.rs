use std::collections::HashMap;

use crate::{common::WithInfo, reprs::common::Span};

pub type Term<'i> = WithInfo<Span<'i>, RawTerm<'i>>;

#[derive(Eq, PartialEq, Debug)]
pub enum RawTerm<'i> {
    Abs {
        arg: Assignee<'i>,
        arg_type: Type<'i>,

        body: Box<Term<'i>>,
    },
    App {
        func: Box<Term<'i>>,
        arg: Box<Term<'i>>,
    },

    Var {
        ident: Ident<'i>,
    },

    Enum(Type<'i>, Ident<'i>),

    Tuple(Box<[Term<'i>]>),

    Bool(bool),
}

#[derive(Eq, PartialEq, Debug)]
pub enum Assignee<'i> {
    Tuple(Box<[Assignee<'i>]>),
    Ident(Ident<'i>),
}

#[derive(Hash, Eq, PartialEq, Debug)]
pub struct Ident<'i> {
    pub name: &'i str,
}

pub type Type<'i> = WithInfo<Span<'i>, RawType<'i>>;

#[derive(Eq, PartialEq, Debug)]
pub enum RawType<'i> {
    Arr {
        arg: Box<Type<'i>>,
        result: Box<Type<'i>>,
    },

    Tuple(Box<[Type<'i>]>),
    Enum(HashMap<Ident<'i>, Type<'i>>),

    Bool,
}
