use std::{borrow::Borrow, collections::HashMap, rc::Rc};

use itertools::{Either, zip_eq};

use crate::{
    common::WithInfo,
    evaluation::evalstack::EvalNode,
    importing::ImportId,
    reprs::{
        common::{ArgTermStructure, Lvl, RawArgStructure, RawArgTermStructure},
        typed_ir::{RawTerm, Term},
        value::{self, Closure, Func, RawValue},
    },
};

use self::context::State;
pub use self::context::VarClosure;
pub use self::error::EvaluationError;

mod evalstack;

mod context {
    use std::{collections::HashMap, rc::Rc};

    use crate::{
        evaluation::EvaluationError,
        reprs::common::{Idx, Lvl},
    };

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
    pub struct VarClosure<'i, 'ir> {
        var_stack: Stack<Rc<Value<'i, 'ir>>>,
    }

    #[must_use]
    #[derive(Clone)]
    pub(super) struct State<'i, 'ir> {
        var_stack: Stack<Rc<Value<'i, 'ir>>>,
    }

    impl<'i, 'ir> State<'i, 'ir> {
        pub(super) fn new() -> Self {
            Self {
                var_stack: Vec::new(),
            }
        }

        pub(super) fn push_vars(&mut self, vars: impl IntoIterator<Item = Value<'i, 'ir>>) {
            self.var_stack.extend(vars.into_iter().map(Rc::new));
        }

        pub(super) fn get_var(&self, index: Idx) -> Option<&Rc<Value<'i, 'ir>>> {
            index.get(&self.var_stack)
        }

        // TODO: perhaps try to close only over referenced vars
        pub(super) fn create_var_closure(&self) -> VarClosure<'i, 'ir> {
            VarClosure {
                var_stack: self.var_stack.clone(),
            }
        }

        pub(super) fn swap_var_closure(
            &mut self,
            mut closure: VarClosure<'i, 'ir>,
        ) -> VarClosure<'i, 'ir> {
            std::mem::swap(&mut self.var_stack, &mut closure.var_stack);
            closure
        }
    }
}

mod error {
    use annotate_snippets::{Group, Level};

    use crate::error::RenderError;

    pub enum EvaluationError {
        Illegal(String),
    }

    impl RenderError<'_> for EvaluationError {
        fn push_groups(self, buf: &mut Vec<Group<'_>>) {
            let group = match self {
                EvaluationError::Illegal(str) => Level::ERROR
                    .primary_title("illegal error (bug)")
                    .element(Level::ERROR.message(str)),
            };

            buf.push(group);
        }
    }
}

type Value<'i, 'ir> = value::Value<'i, Closure<'i, 'ir>>;

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

    let imports =
        imports
            .into_iter()
            .try_fold(HashMap::new(), |mut imports, (import_id, term)| {
                let value = evaluate_loop(term, &imports)?;
                imports.insert(import_id, Rc::new(value));
                Ok(imports)
            })?;
    let value = evaluate_loop(typed_ir, &imports)?;
    Ok(value.map_closure(|_| ()))
}

fn evaluate_loop<'i, 'ir>(
    root_term: &'ir Term<'i>,
    imports: &HashMap<ImportId, Rc<Value<'i, 'ir>>>,
) -> Result<Value<'i, 'ir>, EvaluationError> {
    let mut eval_stack = Vec::new();

    let mut state = State::new();

    enum Transition<'i, 'ir> {
        EvalTerm(&'ir Term<'i>),
        ReturnValue(Value<'i, 'ir>),
    }

    let mut transition = Transition::EvalTerm(root_term);
    loop {
        transition = match transition {
            Transition::EvalTerm(WithInfo(span, raw_term)) => 'transition: {
                let value = match raw_term {
                    RawTerm::Abs {
                        arg_structure,
                        body,
                    } => RawValue::Func(Func::Abs(
                        arg_structure.clone(),
                        value::Closure {
                            closure: state.create_var_closure(),
                            body: body.as_ref(),
                        },
                    )),
                    RawTerm::App { func, arg } => {
                        eval_stack.push(Rc::new(EvalNode::App(*span, Either::Left(arg))));
                        break 'transition Transition::EvalTerm(func);
                    }
                    RawTerm::Var(index) => state
                        .get_var(*index)
                        .ok_or_else(|| {
                            EvaluationError::Illegal(format!(
                                "variable index not found: {index:?}\n"
                            ))
                        })?
                        .as_ref()
                        .1
                        // TODO: maybe try eliminate this clone??
                        .clone(),
                    RawTerm::Handle(effect_id) => RawValue::Func(Func::HandlerFunc(*effect_id)),
                    RawTerm::Trigger(effect_id) => RawValue::Func(Func::Trigger(*effect_id)),
                    RawTerm::Import(import_id) => imports
                        .get(import_id)
                        .ok_or_else(|| {
                            EvaluationError::Illegal(format!("import id not found: {import_id:?}"))
                        })?
                        .as_ref()
                        .1
                        // TODO: maybe try eliminate this clone??
                        .clone(),
                    RawTerm::Identity => RawValue::Func(Func::Identity),
                    RawTerm::Enum(label) => RawValue::Func(Func::EnumCons(*label)),
                    RawTerm::Match(arms) => {
                        if let Some((first_label, first_term)) = arms.first() {
                            eval_stack.push(Rc::new(EvalNode::Match(
                                *span,
                                HashMap::with_capacity(arms.len()),
                                *first_label,
                                arms,
                            )));
                            break 'transition Transition::EvalTerm(first_term);
                        } else {
                            RawValue::Record(HashMap::new())
                        }
                    }
                    RawTerm::Record(fields) => {
                        if let Some((first_label, first)) = fields.first() {
                            eval_stack.push(Rc::new(EvalNode::Record(
                                *span,
                                HashMap::with_capacity(fields.len()),
                                *first_label,
                                fields,
                            )));
                            break 'transition Transition::EvalTerm(first);
                        } else {
                            RawValue::Record(HashMap::new())
                        }
                    }
                    RawTerm::Tuple(elems) => {
                        if let Some(first) = elems.first() {
                            eval_stack.push(Rc::new(EvalNode::Tuple(
                                *span,
                                Vec::with_capacity(elems.len()),
                                elems,
                            )));
                            break 'transition Transition::EvalTerm(first);
                        } else {
                            RawValue::Tuple(Box::new([]))
                        }
                    }
                    RawTerm::Bool(b) => RawValue::Bool(*b),
                };
                Transition::ReturnValue(WithInfo(*span, value))
            }
            Transition::ReturnValue(value) => {
                let Some(top) = eval_stack.pop() else {
                    break Ok(value);
                };

                let top_node = Rc::unwrap_or_clone(top);

                match top_node {
                    EvalNode::App(span, Either::Left(arg)) => {
                        let RawValue::Func(func) = value.1 else {
                            Err(EvaluationError::Illegal(
                                "type checking failed: application on non-function".to_string(),
                            ))?
                        };

                        eval_stack.push(Rc::new(EvalNode::App(span, Either::Right(func))));
                        Transition::EvalTerm(arg)
                    }
                    EvalNode::App(span, Either::Right(func)) => {
                        let arg = value;
                        match func {
                            Func::Abs(arg_structure, Closure { closure, body }) => {
                                let args = arg.destructure(arg_structure)?;

                                let prev_var_closure = state.swap_var_closure(closure);
                                state.push_vars(args);

                                eval_stack.push(Rc::new(EvalNode::AppAbs(prev_var_closure)));
                                Transition::EvalTerm(body)
                            }
                            Func::Identity => Transition::ReturnValue(arg),
                            Func::EnumCons(label) => Transition::ReturnValue(WithInfo(
                                span,
                                RawValue::EnumVariant(label, Box::new(arg)),
                            )),
                            Func::Match(mut arms) => {
                                let WithInfo(_span, raw_arg) = arg;
                                let RawValue::EnumVariant(label, value) = raw_arg else {
                                    Err(EvaluationError::Illegal(
                                        "type checking failed: match on non-enum".to_string(),
                                    ))?
                                };
                                let Some(func) = arms.remove(&label) else {
                                    Err(EvaluationError::Illegal(
                                        "type checking failed: match missing enum label"
                                            .to_string(),
                                    ))?
                                };

                                // essentially just rerun this match with a different `func`
                                eval_stack.push(Rc::new(EvalNode::App(span, Either::Right(func))));
                                Transition::ReturnValue(*value)
                            }
                            Func::HandlerFunc(label) => todo!(),
                            Func::Handler(effect_id, func) => todo!(),
                            Func::Continuation() => todo!(),
                            Func::Trigger(effect_id) => todo!(),
                        }
                    }
                    EvalNode::AppAbs(closure) => {
                        state.swap_var_closure(closure);
                        Transition::ReturnValue(value)
                    }
                    EvalNode::Match(span, mut evaled, label, arms) => {
                        let RawValue::Func(func) = value.1 else {
                            return Err(EvaluationError::Illegal(
                                "type checking failed: match arm is non-function".to_string(),
                            ));
                        };
                        evaled.insert(label, func);
                        if let Some((next_label, next_term)) = arms.get(evaled.len()) {
                            eval_stack.push(Rc::new(EvalNode::Match(
                                span,
                                evaled,
                                *next_label,
                                arms,
                            )));
                            Transition::EvalTerm(next_term)
                        } else {
                            Transition::ReturnValue(WithInfo(
                                span,
                                RawValue::Func(Func::Match(evaled)),
                            ))
                        }
                    }
                    EvalNode::Record(span, mut evaled, label, fields) => {
                        evaled.insert(label, value);
                        if let Some((next_label, next_term)) = fields.get(evaled.len()) {
                            eval_stack.push(Rc::new(EvalNode::Record(
                                span,
                                evaled,
                                *next_label,
                                fields,
                            )));
                            Transition::EvalTerm(next_term)
                        } else {
                            Transition::ReturnValue(WithInfo(span, RawValue::Record(evaled)))
                        }
                    }
                    EvalNode::Tuple(span, mut evaled, elems) => {
                        evaled.push(value);
                        if let Some(next_term) = elems.get(evaled.len()) {
                            eval_stack.push(Rc::new(EvalNode::Tuple(span, evaled, elems)));
                            Transition::EvalTerm(next_term)
                        } else {
                            Transition::ReturnValue(WithInfo(
                                span,
                                RawValue::Tuple(evaled.into_boxed_slice()),
                            ))
                        }
                    }
                }
            }
        };
    }
}

impl Value<'_, '_> {
    fn destructure(
        self,
        arg_structure: ArgTermStructure,
    ) -> Result<impl Iterator<Item = Self>, EvaluationError> {
        fn inner<'i, 'ir, 'a>(
            arg_structure: ArgTermStructure,
            val: Value<'i, 'ir>,
            output: &mut impl FnMut(Value<'i, 'ir>),
        ) -> Result<(), EvaluationError> {
            let WithInfo(info, val) = val;
            let WithInfo(_arg_structure_span, arg_structure) = arg_structure;
            match arg_structure {
                RawArgTermStructure::Term(RawArgStructure::Record(st_fields)) => {
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

                RawArgTermStructure::Term(RawArgStructure::Tuple(st_elems)) => {
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

                RawArgTermStructure::Term(RawArgStructure::Var) => output(WithInfo(info, val)),
                RawArgTermStructure::Type(()) => {}
            }
            Ok(())
        }
        let mut buffer = Vec::new();
        inner(arg_structure, self, &mut |val| buffer.push(val))?;
        Ok(buffer.into_iter())
    }
}
