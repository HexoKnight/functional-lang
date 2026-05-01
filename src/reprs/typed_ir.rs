use crate::{
    common::WithInfo,
    importing::ImportId,
    reprs::common::{ArgTermStructure, Idx, Label, Span},
};

pub type Term<'i> = WithInfo<Span<'i>, RawTerm<'i>>;

#[derive(Eq, PartialEq, Debug)]
pub enum RawTerm<'i> {
    Abs {
        arg_structure: ArgTermStructure<'i>,
        body: Box<Term<'i>>,
    },
    App {
        func: Box<Term<'i>>,
        arg: Box<Term<'i>>,
    },

    Var(Idx),

    // TODO
    Handle(EffectId<'i>),
    Trigger(EffectId<'i>),

    Import(ImportId),

    Identity,

    Enum(Label<'i>),
    Match(Box<[(Label<'i>, Term<'i>)]>),

    Record(Box<[(Label<'i>, Term<'i>)]>),
    Tuple(Box<[Term<'i>]>),

    Bool(bool),
}

#[derive(Copy, Clone, Hash, Eq, PartialEq, Debug)]
pub enum EffectRef<'i> {
    Labelled(Label<'i>),
    Anonymous(EffectId<'i>),
}
#[derive(Copy, Clone, Hash, Eq, PartialEq, Debug)]
pub enum EffectId<'i> {
    Def(Label<'i>),
}
