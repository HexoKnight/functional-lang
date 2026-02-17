use std::{borrow::Borrow, collections::HashMap};

use itertools::{Itertools, zip_eq};
use typed_arena::Arena;

use crate::{
    common::WithInfo,
    evaluation::context::ContextInner,
    reprs::{
        common::{ArgStructure, ImportId, RawArgStructure},
        typed_ir::{RawTerm, Term},
        value::{self, Closure, Func, RawValue},
    },
};

use self::context::Context;
pub use self::context::ContextClosure;
pub use self::error::EvaluationError;

mod context {
    use std::collections::HashMap;

    use typed_arena::Arena;

    use crate::reprs::common::{Idx, ImportId};

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

    pub(super) struct ContextInner<'i, 'ir, 'a> {
        var_arena: &'a Arena<Value<'i, 'ir, 'a>>,
    }

    impl<'i, 'ir, 'a> ContextInner<'i, 'ir, 'a> {
        pub(super) fn new(arena: &'a Arena<Value<'i, 'ir, 'a>>) -> Self {
            Self { var_arena: arena }
        }

        pub(super) fn alloc(&self, value: Value<'i, 'ir, 'a>) -> &'a Value<'i, 'ir, 'a> {
            self.var_arena.alloc(value)
        }
    }

    #[must_use]
    #[derive(Clone)]
    pub(super) struct Context<'i, 'ir, 'a, 'inn> {
        inner: &'inn ContextInner<'i, 'ir, 'a>,
        imports: &'inn HashMap<ImportId, &'a Value<'i, 'ir, 'a>>,

        var_stack: Stack<&'a Value<'i, 'ir, 'a>>,
    }

    impl<'i, 'ir, 'a, 'inn> Context<'i, 'ir, 'a, 'inn> {
        pub(super) fn new(
            imports: &'inn HashMap<ImportId, &'a Value<'i, 'ir, 'a>>,
            inner: &'inn ContextInner<'i, 'ir, 'a>,
        ) -> Self {
            Self {
                inner,
                imports,
                var_stack: Vec::new(),
            }
        }

        pub(super) fn push_vars(&self, vars: impl IntoIterator<Item = Value<'i, 'ir, 'a>>) -> Self {
            let mut new = self.clone();
            new.var_stack
                .extend(vars.into_iter().map(|v| self.inner.alloc(v)));
            new
        }

        pub(super) fn get_var(&self, index: Idx) -> Option<&'a Value<'i, 'ir, 'a>> {
            index.get(&self.var_stack).copied()
        }

        pub(super) fn get_import(&self, import_id: ImportId) -> Option<&'a Value<'i, 'ir, 'a>> {
            self.imports.get(&import_id).copied()
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
                inner: self.inner,
                imports: self.imports,
                var_stack,
            }
        }
    }
}

mod error {
    use annotate_snippets::{Group, Level};

    pub enum EvaluationError {
        Illegal(String),
    }

    impl EvaluationError {
        pub fn into_record(self) -> Vec<Group<'static>> {
            let group = match self {
                EvaluationError::Illegal(str) => Level::ERROR
                    .primary_title("illegal error (bug)")
                    .element(Level::ERROR.message(str)),
            };

            vec![group]
        }
    }
}

type Value<'i, 'ir, 'a> = value::Value<'i, Closure<'i, 'ir, 'a>>;

/// Takes a [`typed_ir::Term`][tir::Term] and all it's dependencies and evaluates it,
/// returning the resulting [`Value`][value::Value].
///
/// # Errors
/// When evaluation fails.
pub fn evaluate<'i: 't, 't, I>(
    typed_ir: impl Borrow<Term<'i>>,
    imports: I,
) -> Result<value::Value<'i, ()>, EvaluationError>
where
    I: IntoIterator<Item = (ImportId, &'t Term<'i>)>,
{
    let typed_ir = typed_ir.borrow();

    let arena = Arena::new();
    let inner = ContextInner::new(&arena);

    let imports =
        imports
            .into_iter()
            .try_fold(HashMap::new(), |mut imports, (import_id, term)| {
                let value = term.evaluate(&Context::new(&imports, &inner))?;
                imports.insert(import_id, inner.alloc(value));
                Ok(imports)
            })?;
    let value = typed_ir.evaluate(&Context::new(&imports, &inner))?;
    Ok(value.map_closure(|_| ()))
}

trait Evaluate<'i, 'ir, 'a> {
    type Evaluated;
    fn evaluate(
        &'ir self,
        ctx: &Context<'i, 'ir, 'a, '_>,
    ) -> Result<Self::Evaluated, EvaluationError>;
}

impl<'i: 'ir, 'ir: 'a, 'a> Evaluate<'i, 'ir, 'a> for Term<'i> {
    type Evaluated = Value<'i, 'ir, 'a>;

    fn evaluate(
        &'ir self,
        ctx: &Context<'i, 'ir, 'a, '_>,
    ) -> Result<Self::Evaluated, EvaluationError> {
        let WithInfo(info, term) = self;

        let value = match term {
            // we cannot evaluate a solitary abstraction any further so we treat it like a closure
            RawTerm::Abs {
                arg_structure,
                body,
            } => RawValue::Func(Func::Abs(
                arg_structure.clone(),
                value::Closure {
                    closed_ctx: ctx.create_closure(),
                    body: body.as_ref(),
                },
            )),
            RawTerm::App { func, arg } => {
                let RawValue::Func(func) = func.evaluate(ctx)?.1 else {
                    return Err(EvaluationError::Illegal(
                        "type checking failed: application on non-function".to_string(),
                    ));
                };

                let arg = arg.evaluate(ctx)?;
                func.evaluate_arg(arg, ctx)?
            }
            RawTerm::Var(index) => ctx
                .get_var(*index)
                .ok_or_else(|| {
                    EvaluationError::Illegal(format!("variable index not found: {index:?}\n"))
                })?
                .1
                // TODO: maybe try eliminate this clone??
                .clone(),
            RawTerm::Import(import_id) => ctx
                .get_import(*import_id)
                .ok_or_else(|| {
                    EvaluationError::Illegal(format!("import id not found: {import_id:?}"))
                })?
                .1
                // TODO: maybe try eliminate this clone??
                .clone(),
            RawTerm::Enum(label) => RawValue::Func(Func::EnumCons(*label)),
            RawTerm::Match(arms) => RawValue::Func(Func::Match(
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
            RawTerm::Record(fields) => RawValue::Record(
                fields
                    .iter()
                    .map(|(l, f)| f.evaluate(ctx).map(|f| (*l, f)))
                    .try_collect()?,
            ),
            RawTerm::Tuple(elems) => {
                RawValue::Tuple(elems.iter().map(|e| e.evaluate(ctx)).try_collect()?)
            }
            RawTerm::Bool(b) => RawValue::Bool(*b),
        };

        Ok(WithInfo(*info, value))
    }
}

impl<'i: 'ir, 'ir: 'a, 'a> Func<'i, Closure<'i, 'ir, 'a>> {
    fn evaluate_arg(
        self,
        arg: Value<'i, 'ir, 'a>,
        ctx: &Context<'i, 'ir, 'a, '_>,
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
                    return Err(EvaluationError::Illegal(
                        "type checking failed: match on non-enum".to_string(),
                    ));
                };
                let Some(Closure { closed_ctx, body }) = arms.remove(&label) else {
                    return Err(EvaluationError::Illegal(
                        "type checking failed: match missing enum label".to_string(),
                    ));
                };

                let ctx_ = ctx.apply_closure(closed_ctx);
                let func = body.evaluate(&ctx_)?.1;
                let RawValue::Func(func) = func else {
                    return Err(EvaluationError::Illegal(
                        "type checking failed: match arm is non-function".to_string(),
                    ));
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
            let WithInfo(_arg_structure_span, arg_structure) = arg_structure;
            match arg_structure {
                RawArgStructure::Record(st_fields) => {
                    let RawValue::Record(mut val_fields) = val else {
                        return Err(EvaluationError::Illegal(
                            "type checking failed: record destructure on non-record".to_string(),
                        ));
                    };

                    st_fields.into_iter().try_for_each(|(l, st)| {
                        if let Some(val) = val_fields.remove(&l) {
                            inner(st, val, output)
                        } else {
                            Err(EvaluationError::Illegal(format!(
                                "type checking failed: destructured record missing label: '{l}'"
                            )))
                        }
                    })?;
                }

                RawArgStructure::Tuple(st_elems) => {
                    let RawValue::Tuple(val_elems) = val else {
                        return Err(EvaluationError::Illegal(
                            "type checking failed: tuple destructure on non-tuple".to_string(),
                        ));
                    };

                    let st_len = st_elems.len();
                    let val_len = val_elems.len();
                    if st_len != val_len {
                        return Err(EvaluationError::Illegal(format!(
                            "type checking failed: {st_len}-tuple destructure on {val_len}-tuple"
                        )));
                    }
                    zip_eq(st_elems, val_elems).try_for_each(|(st, val)| inner(st, val, output))?;
                }

                RawArgStructure::Var => output(WithInfo(info, val)),
            }
            Ok(())
        }
        let mut buffer = Vec::new();
        inner(arg_structure, self, &mut |val| buffer.push(val))?;
        Ok(buffer.into_iter())
    }
}
