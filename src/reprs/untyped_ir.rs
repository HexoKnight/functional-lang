use std::collections::HashMap;

use derive_where::derive_where;

use crate::{
    common::WithInfo,
    importing::ImportId,
    reprs::common::{ArgStructure, Idx, Label, Lvl, Span},
};

pub type Term<'i> = WithInfo<Span<'i>, RawTerm<'i>>;

#[derive(Eq, PartialEq, Debug)]
pub enum RawTerm<'i> {
    Abs {
        arg_structure: ArgStructure<'i>,
        arg_type: Option<Type<'i>>,

        effects: EffectGroup<'i, Effect<'i>>,

        body: Box<Term<'i>>,
    },
    App {
        func: Box<Term<'i>>,

        effects: EffectGroup<'i, Lvl>,

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

    Type(Type<'i>),

    Handle(Effect<'i>),
    Trigger(Effect<'i>),

    Import(WithInfo<Span<'i>, ImportId>),

    Fold(Option<Type<'i>>),
    Unfold(Option<Type<'i>>),

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
    TyApp {
        abs: Box<Type<'i>>,
        arg: Box<Type<'i>>,
    },

    RecAbs {
        name: &'i str,
        result: Box<Type<'i>>,
    },

    TyVar(Lvl),

    Arr {
        arg: Box<Type<'i>>,

        effects: EffectGroup<'i, Effect<'i>>,

        result: Box<Type<'i>>,
    },

    Enum(HashMap<Label<'i>, Type<'i>>),
    Record(HashMap<Label<'i>, Type<'i>>),
    Tuple(Box<[Type<'i>]>),

    Bool,
    Any,
    Never,
}

pub type Effect<'i> = WithInfo<Span<'i>, RawEffect<'i>>;

#[derive(Eq, PartialEq, Debug)]
pub enum RawEffect<'i> {
    Def {
        name: Label<'i>,
        arg: Box<Type<'i>>,
        result: Box<Type<'i>>,
    },
}

#[derive(Eq, PartialEq, Debug)]
#[derive_where(Default)]
pub struct EffectGroup<'i, T>(pub Box<[(Option<Label<'i>>, T)]>);
