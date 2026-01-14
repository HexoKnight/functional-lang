use derive_where::derive_where;

use crate::{
    common::WithInfo,
    evaluation::ContextClosure,
    reprs::{
        common::{ArgStructure, EnumLabel, Span},
        typed_ir,
    },
};

pub type Value<'i, Abs = ()> = WithInfo<Span<'i>, RawValue<'i, Abs>>;

#[derive(Clone, Eq, PartialEq, Debug)]
pub enum RawValue<'i, Abs> {
    Func(Func<'i, Abs>),

    EnumVariant(EnumLabel<'i>, Box<Value<'i, Abs>>),
    Tuple(Box<[Value<'i, Abs>]>),
    Bool(bool),
}

#[derive(Clone, Eq, PartialEq, Debug)]
pub enum Func<'i, Abs> {
    Abs(Abs),

    EnumCons(EnumLabel<'i>),
}

#[derive(Clone)]
#[derive_where(Debug)]
pub struct Abs<'i, 'ir, 'a> {
    #[derive_where(skip)]
    pub closed_ctx: ContextClosure<'i, 'ir, 'a>,

    pub arg_structure: ArgStructure,
    pub body: &'ir typed_ir::Term<'i>,
}

impl<'i, A> Value<'i, A> {
    fn map_abs_ref<T>(self, f: &mut impl FnMut(A) -> T) -> Value<'i, T> {
        WithInfo(
            self.0,
            match self.1 {
                RawValue::Func(Func::Abs(a)) => RawValue::Func(Func::Abs(f(a))),
                RawValue::Func(Func::EnumCons(l)) => RawValue::Func(Func::EnumCons(l)),

                RawValue::EnumVariant(l, v) => RawValue::EnumVariant(l, Box::new(v.map_abs_ref(f))),
                RawValue::Tuple(e) => {
                    RawValue::Tuple(e.into_iter().map(|e| e.map_abs_ref(f)).collect())
                }
                RawValue::Bool(b) => RawValue::Bool(b),
            },
        )
    }

    pub fn map_abs<T>(self, mut f: impl FnMut(A) -> T) -> Value<'i, T> {
        self.map_abs_ref(&mut f)
    }
}
