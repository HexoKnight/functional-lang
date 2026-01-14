use crate::{
    common::WithInfo,
    reprs::common::{ArgStructure, EnumLabel, Span},
};

pub type Term<'i> = WithInfo<Span<'i>, RawTerm<'i>>;

#[derive(Eq, PartialEq, Debug)]
pub enum RawTerm<'i> {
    Abs {
        arg_structure: ArgStructure,
        body: Box<Term<'i>>,
    },
    App {
        func: Box<Term<'i>>,
        arg: Box<Term<'i>>,
    },

    Var {
        index: usize,
    },

    Enum(EnumLabel<'i>),

    Tuple(Box<[Term<'i>]>),

    Bool(bool),
}
