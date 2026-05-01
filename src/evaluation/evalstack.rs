use std::collections::HashMap;

use itertools::Either;

use crate::{
    evaluation::{Value, VarClosure},
    reprs::{
        common::{Label, Lvl, Span},
        typed_ir::{self, EffectId, EffectRef},
        value::{self, Closure},
    },
};

type Func<'i, 'ir> = value::Func<'i, Closure<'i, 'ir>>;

#[derive(Clone)]
pub(super) enum EvalNode<'i, 'ir> {
    App(Span<'i>, Either<&'ir typed_ir::Term<'i>, Func<'i, 'ir>>),
    AppAbs(VarClosure<'i, 'ir>),

    Match(
        Span<'i>,
        HashMap<Label<'i>, Func<'i, 'ir>>,
        Label<'i>,
        &'ir [(Label<'i>, typed_ir::Term<'i>)],
    ),

    Record(
        Span<'i>,
        HashMap<Label<'i>, Value<'i, 'ir>>,
        Label<'i>,
        &'ir [(Label<'i>, typed_ir::Term<'i>)],
    ),
    Tuple(Span<'i>, Vec<Value<'i, 'ir>>, &'ir [typed_ir::Term<'i>]),
}
