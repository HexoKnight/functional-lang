use std::collections::HashMap;

use derive_where::derive_where;

use crate::{
    common::WithInfo,
    evaluation::ContextClosure,
    reprs::{
        common::{ArgStructure, Label, Span},
        typed_ir,
    },
};

pub type Value<'i, Closure = ()> = WithInfo<Span<'i>, RawValue<'i, Closure>>;

#[derive(Clone, Eq, PartialEq, Debug)]
pub enum RawValue<'i, Closure> {
    Func(Func<'i, Closure>),

    EnumVariant(Label<'i>, Box<Value<'i, Closure>>),
    Record(HashMap<Label<'i>, Value<'i, Closure>>),
    Tuple(Box<[Value<'i, Closure>]>),
    Bool(bool),
}

#[derive(Clone, Eq, PartialEq, Debug)]
pub enum Func<'i, Closure> {
    Abs(ArgStructure<'i>, Closure),

    EnumCons(Label<'i>),
    Match(HashMap<Label<'i>, Closure>),
}

#[derive(Clone)]
#[derive_where(Debug)]
pub struct Closure<'i, 'ir, 'a> {
    #[derive_where(skip)]
    pub closed_ctx: ContextClosure<'i, 'ir, 'a>,

    pub body: &'ir typed_ir::Term<'i>,
}

impl<'i, Closure> Value<'i, Closure> {
    fn map_closure_rec<T>(self, map: &mut impl FnMut(Closure) -> T) -> Value<'i, T> {
        WithInfo(
            self.0,
            match self.1 {
                RawValue::Func(f) => RawValue::Func(f.map_closure_rec(map)),

                RawValue::EnumVariant(l, v) => {
                    RawValue::EnumVariant(l, Box::new(v.map_closure_rec(map)))
                }
                RawValue::Record(f) => RawValue::Record(
                    f.into_iter()
                        .map(|(l, f)| (l, f.map_closure_rec(map)))
                        .collect(),
                ),
                RawValue::Tuple(e) => {
                    RawValue::Tuple(e.into_iter().map(|e| e.map_closure_rec(map)).collect())
                }
                RawValue::Bool(b) => RawValue::Bool(b),
            },
        )
    }

    pub fn map_closure<T>(self, mut f: impl FnMut(Closure) -> T) -> Value<'i, T> {
        self.map_closure_rec(&mut f)
    }
}
impl<'i, Closure> Func<'i, Closure> {
    fn map_closure_rec<T>(self, map: &mut impl FnMut(Closure) -> T) -> Func<'i, T> {
        match self {
            Func::Abs(a, closure) => Func::Abs(a, map(closure)),
            Func::EnumCons(l) => Func::EnumCons(l),
            Func::Match(arms) => Func::Match(
                arms.into_iter()
                    .map(|(l, closure)| (l, map(closure)))
                    .collect(),
            ),
        }
    }
}
