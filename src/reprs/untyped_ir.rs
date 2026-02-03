use std::collections::HashMap;

use crate::{
    common::WithInfo,
    reprs::common::{ArgStructure, Idx, Label, Lvl, Span},
};

pub type Term<'i> = WithInfo<Span<'i>, RawTerm<'i>>;

#[derive(Eq, PartialEq, Debug)]
pub enum RawTerm<'i> {
    Abs {
        arg_structure: ArgStructure<'i>,
        arg_type: Option<Type<'i>>,

        body: Box<Term<'i>>,
    },
    App {
        func: Box<Term<'i>>,
        arg: Box<Term<'i>>,
    },

    TyAbs {
        name: &'i str,
        bounds: TyBounds<'i>,

        body: Box<Term<'i>>,
    },
    TyApp {
        abs: Box<Term<'i>>,
        arg: Box<Type<'i>>,
    },

    Var(Idx),

    Enum(Option<Type<'i>>, Label<'i>),
    Match(Option<Type<'i>>, HashMap<Label<'i>, Term<'i>>),

    Record(Box<[(Label<'i>, Term<'i>)]>),

    Tuple(Box<[Term<'i>]>),

    Bool(bool),
}

#[derive(Eq, PartialEq, Debug)]
pub struct TyBounds<'i> {
    pub upper: Option<Type<'i>>,
    pub lower: Option<Type<'i>>,
}

pub type Type<'i> = WithInfo<Span<'i>, RawType<'i>>;

#[derive(Eq, PartialEq, Debug)]
pub enum RawType<'i> {
    TyAbs {
        name: &'i str,
        bounds: Box<TyBounds<'i>>,
        result: Box<Type<'i>>,
    },

    TyVar(Lvl),

    Arr {
        arg: Box<Type<'i>>,
        result: Box<Type<'i>>,
    },

    Enum(HashMap<Label<'i>, Type<'i>>),
    Record(HashMap<Label<'i>, Type<'i>>),
    Tuple(Box<[Type<'i>]>),

    Bool,
    Any,
    Never,
}
