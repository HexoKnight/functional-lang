use std::collections::HashMap;

use crate::{
    common::WithInfo,
    reprs::common::{ArgStructure, Idx, Label, Span},
};

pub type Term<'i> = WithInfo<Span<'i>, RawTerm<'i>>;

#[derive(Eq, PartialEq, Debug)]
pub enum RawTerm<'i> {
    Abs {
        arg_structure: ArgStructure<'i>,
        body: Box<Term<'i>>,
    },
    App {
        func: Box<Term<'i>>,
        arg: Box<Term<'i>>,
    },

    Var(Idx),

    Enum(Label<'i>),
    Match(HashMap<Label<'i>, Term<'i>>),

    Record(Box<[(Label<'i>, Term<'i>)]>),
    Tuple(Box<[Term<'i>]>),

    Bool(bool),
}
