use itertools::{Itertools, zip_eq};
use typed_arena::Arena;

use crate::common::WithInfo;
use crate::reprs::common::ArgStructure;
use crate::reprs::typed_ir::{self as tir};
use crate::reprs::value::{self, Closure, Func, RawValue};

use self::context::Context;
pub use self::context::ContextClosure;

mod context {
    use typed_arena::Arena;

    use crate::reprs::common::Idx;

    use super::Value;

    // due to self references and dropck, this type must (transitively) have a 'safe' drop impl ie.:
    // - an automatic impl
    // - use the unstable `may_dangle` (limited to stdlib types on stable)
    // eg. not im::Vector :(
    // see: https://doc.rust-lang.org/nomicon/dropck.html
    // but perhaps some kind of cons list, though Vec works fine for now
    /// Cheaply cloneable (hopefully) append-only stack
    type Stack<T> = Vec<T>;

    #[derive(Clone, Debug)]
    pub struct ContextClosure<'i, 'ir, 'a> {
        var_stack: Stack<&'a Value<'i, 'ir, 'a>>,
    }

    #[must_use]
    #[derive(Clone)]
    pub(super) struct Context<'i, 'ir, 'a> {
        var_arena: &'a Arena<Value<'i, 'ir, 'a>>,
        var_stack: Stack<&'a Value<'i, 'ir, 'a>>,
    }

    impl<'i, 'ir, 'a> Context<'i, 'ir, 'a> {
        pub(super) fn with_arena(arena: &'a Arena<Value<'i, 'ir, 'a>>) -> Self {
            Self {
                var_arena: arena,
                var_stack: Vec::new(),
            }
        }

        pub(super) fn push_vars(&self, vars: impl IntoIterator<Item = Value<'i, 'ir, 'a>>) -> Self {
            let mut new = self.clone();
            new.var_stack
                .extend(vars.into_iter().map(|v| &*self.var_arena.alloc(v)));
            new
        }

        pub(super) fn get_var(&self, index: Idx) -> Option<&'a Value<'i, 'ir, 'a>> {
            index.get(&self.var_stack).copied()
        }

        // TODO: perhaps try to close only over referenced vars
        pub(super) fn create_closure(&self) -> ContextClosure<'i, 'ir, 'a> {
            ContextClosure {
                var_stack: self.var_stack.clone(),
            }
        }

        pub(super) fn apply_closure(&self, closure: ContextClosure<'i, 'ir, 'a>) -> Self {
            let ContextClosure { var_stack } = closure;
            Self {
                var_arena: self.var_arena,
                var_stack,
            }
        }
    }
}

type Value<'i, 'ir, 'a> = value::Value<'i, Closure<'i, 'ir, 'a>>;

pub type EvaluationError = String;

trait Evaluate<'i, 'ir, 'a> {
    type Evaluated;

    fn evaluate(&'ir self, ctx: &Context<'i, 'ir, 'a>) -> Result<Self::Evaluated, EvaluationError>;
}

/// Takes a [`typed_ir::Term`][tir::Term] and evaluates it, returning the resulting
/// [`Value`][value::Value].
///
/// # Errors
/// When evaluation fails.
pub fn evaluate<'i>(typed_ir: &tir::Term<'i>) -> Result<value::Value<'i, ()>, EvaluationError> {
    let arena = Arena::new();
    let value = typed_ir.evaluate(&Context::with_arena(&arena))?;
    Ok(value.map_closure(|_| ()))
}

impl<'i: 'ir, 'ir: 'a, 'a> Evaluate<'i, 'ir, 'a> for tir::Term<'i> {
    type Evaluated = Value<'i, 'ir, 'a>;

    fn evaluate(&'ir self, ctx: &Context<'i, 'ir, 'a>) -> Result<Self::Evaluated, EvaluationError> {
        let WithInfo(info, term) = self;

        let value = match term {
            // we cannot evaluate a solitary abstraction any further so we treat it like a closure
            tir::RawTerm::Abs {
                arg_structure,
                body,
            } => RawValue::Func(Func::Abs(
                arg_structure.clone(),
                value::Closure {
                    closed_ctx: ctx.create_closure(),
                    body: body.as_ref(),
                },
            )),
            tir::RawTerm::App { func, arg } => {
                let RawValue::Func(func) = func.evaluate(ctx)?.1 else {
                    return Err(
                        "illegal failure: type checking failed: application on non-function"
                            .to_string(),
                    );
                };

                let arg = arg.evaluate(ctx)?;
                func.evaluate_arg(arg, ctx)?
            }
            tir::RawTerm::Var(index) => ctx
                .get_var(*index)
                .ok_or_else(|| format!("illegal failure: variable index not found: {index:?}\n"))?
                .1
                // TODO: maybe try eliminate this clone??
                .clone(),
            tir::RawTerm::Enum(label) => RawValue::Func(Func::EnumCons(*label)),
            tir::RawTerm::Match(arms) => RawValue::Func(Func::Match(
                arms.iter()
                    .map(|(l, body)| {
                        (
                            *l,
                            value::Closure {
                                closed_ctx: ctx.create_closure(),
                                body,
                            },
                        )
                    })
                    .collect(),
            )),
            tir::RawTerm::Record(fields) => RawValue::Record(
                fields
                    .iter()
                    .map(|(l, f)| f.evaluate(ctx).map(|f| (*l, f)))
                    .try_collect()?,
            ),
            tir::RawTerm::Tuple(elems) => {
                RawValue::Tuple(elems.iter().map(|e| e.evaluate(ctx)).try_collect()?)
            }
            tir::RawTerm::Bool(b) => RawValue::Bool(*b),
        };

        Ok(WithInfo(*info, value))
    }
}

impl<'i: 'ir, 'ir: 'a, 'a> Func<'i, Closure<'i, 'ir, 'a>> {
    fn evaluate_arg(
        self,
        arg: Value<'i, 'ir, 'a>,
        ctx: &Context<'i, 'ir, 'a>,
    ) -> Result<RawValue<'i, Closure<'i, 'ir, 'a>>, EvaluationError> {
        let value = match self {
            Func::Abs(arg_structure, value::Closure { closed_ctx, body }) => {
                let args = arg.destructure(arg_structure)?;

                let ctx_ = ctx.apply_closure(closed_ctx).push_vars(args);
                body.evaluate(&ctx_)?.1
            }
            Func::EnumCons(label) => RawValue::EnumVariant(label, Box::new(arg)),
            Func::Match(mut arms) => {
                let WithInfo(_info, arg) = arg;
                let RawValue::EnumVariant(label, value) = arg else {
                    return Err(
                        "illegal failure: type checking failed: match on non-enum".to_string()
                    );
                };
                let Some(Closure { closed_ctx, body }) = arms.remove(&label) else {
                    return Err(
                        "illegal failure: type checking failed: match missing enum label"
                            .to_string(),
                    );
                };

                let ctx_ = ctx.apply_closure(closed_ctx);
                let func = body.evaluate(&ctx_)?.1;
                let RawValue::Func(func) = func else {
                    return Err(
                        "illegal failure: type checking failed: match arm is non-function"
                            .to_string(),
                    );
                };
                func.evaluate_arg(*value, ctx)?
            }
        };
        Ok(value)
    }
}

impl Value<'_, '_, '_> {
    fn destructure(
        self,
        arg_structure: ArgStructure,
    ) -> Result<impl Iterator<Item = Self>, EvaluationError> {
        fn inner<'i, 'ir, 'a>(
            arg_structure: ArgStructure,
            val: Value<'i, 'ir, 'a>,
            output: &mut impl FnMut(Value<'i, 'ir, 'a>),
        ) -> Result<(), EvaluationError> {
            let WithInfo(info, val) = val;
            match arg_structure {
                ArgStructure::Record(st_fields) => {
                    let RawValue::Record(mut val_fields) = val else {
                        return Err(
                            "illegal failure: type checking failed: record destructure on non-record"
                                .to_string(),
                        );
                    };

                    st_fields.into_iter().try_for_each(|(l, st)| {
                        if let Some(val) = val_fields.remove(&l) {
                            inner(st, val, output)
                        } else {
                        Err(format!(
                            "illegal failure: type checking failed: destructured record missing label: '{l}'"
                        ))
                        }
                    })?;
                }

                ArgStructure::Tuple(st_elems) => {
                    let RawValue::Tuple(val_elems) = val else {
                        return Err(
                            "illegal failure: type checking failed: tuple destructure on non-tuple"
                                .to_string(),
                        );
                    };

                    let st_len = st_elems.len();
                    let val_len = val_elems.len();
                    if st_len != val_len {
                        return Err(format!(
                            "illegal failure: type checking failed: {st_len}-tuple destructure on {val_len}-tuple"
                        ));
                    }
                    zip_eq(st_elems, val_elems).try_for_each(|(st, val)| inner(st, val, output))?;
                }

                ArgStructure::Var => output(WithInfo(info, val)),
            }
            Ok(())
        }
        let mut buffer = Vec::new();
        inner(arg_structure, self, &mut |val| buffer.push(val))?;
        Ok(buffer.into_iter())
    }
}
