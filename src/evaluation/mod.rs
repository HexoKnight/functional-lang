use typed_arena::Arena;

use crate::common::WithInfo;
use crate::reprs::typed_ir::{self as tir};
use crate::reprs::value::{self, Abs, RawValue};

use self::context::Context;
pub use self::context::ContextClosure;

mod context {
    use typed_arena::Arena;

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

        pub(super) fn push_var(&self, var: Value<'i, 'ir, 'a>) -> Self {
            let mut new = self.clone();
            new.var_stack.push(self.var_arena.alloc(var));
            new
        }

        pub(super) fn get_var(&self, index: usize) -> Option<&'a Value<'i, 'ir, 'a>> {
            self.var_stack.iter().copied::<&_>().nth_back(index)
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

type Value<'i, 'ir, 'a> = value::Value<'i, Abs<'i, 'ir, 'a>>;

type EvaluationError = String;

trait Evaluate<'i, 'ir, 'a> {
    type Evaluated;

    fn evaluate(&'ir self, ctx: &Context<'i, 'ir, 'a>) -> Result<Self::Evaluated, EvaluationError>;
}

pub fn evaluate<'i>(typed_ir: &tir::Term<'i>) -> Result<value::Value<'i, ()>, EvaluationError> {
    let arena = Arena::new();
    let value = typed_ir.evaluate(&Context::with_arena(&arena))?;
    Ok(value.map_abs(|_| ()))
}

impl<'i: 'ir, 'ir: 'a, 'a> Evaluate<'i, 'ir, 'a> for tir::Term<'i> {
    type Evaluated = Value<'i, 'ir, 'a>;

    fn evaluate(&'ir self, ctx: &Context<'i, 'ir, 'a>) -> Result<Self::Evaluated, EvaluationError> {
        let WithInfo(info, term) = self;

        let value = match term {
            // we cannot evaluate a solitary abstraction any further so we treat it like a closure
            tir::RawTerm::Abs(tir::Abs { body }) => RawValue::Abs(value::Abs {
                closed_ctx: ctx.create_closure(),
                body: body.as_ref(),
            }),
            tir::RawTerm::App(tir::App { func, arg }) => {
                let RawValue::Abs(value::Abs { closed_ctx, body }) = func.evaluate(ctx)?.1 else {
                    return Err(
                        "illegal failure: type checking failed: application on non-abstraction"
                            .to_string(),
                    );
                };

                let arg = arg.evaluate(ctx)?;

                let ctx_ = ctx.apply_closure(closed_ctx).push_var(arg);
                let res = body.evaluate(&ctx_)?;
                res.1
            }
            tir::RawTerm::Var(tir::Var { index }) => ctx
                .get_var(*index)
                .ok_or_else(|| format!("illegal failure: variable index not found: {index}\n"))?
                .1
                // TODO: maybe try eliminate this clone??
                .clone(),
            tir::RawTerm::Bool(b) => RawValue::Bool(*b),
        };

        Ok(WithInfo(*info, value))
    }
}

#[cfg(test)]
pub mod tests {
    use crate::typing::tests::{def, type_check_success, wrapped};

    use super::*;

    #[track_caller]
    pub(crate) fn evaluate_success(src: &str) -> value::Value<'_> {
        let (typed_ir, _) = type_check_success(src);
        match evaluate(&typed_ir) {
            Ok(o) => o,
            Err(e) => panic!("evaluate failure:\n'{}'\n{}", src, e),
        }
    }

    #[track_caller]
    fn evaluate_eq(src1: &str, src2: &str) {
        assert_eq!(evaluate_success(src1), evaluate_success(src2))
    }

    #[test]
    fn evaluation() {
        evaluate_success(r"\x:bool x");
        evaluate_success(r"\x:bool \y:bool x");

        evaluate_success(r"(\x:bool x) true");
        evaluate_success(r"(\x: bool -> bool x true) (\y: bool false)");

        evaluate_success(r"(\id:bool->bool id) (\x:bool x)");

        evaluate_eq(r"(\x:bool \y:bool (\z:bool z) x) false true", r"false");

        let id = def(r"id:bool->bool", r"\x:bool x");
        let idf = def(r"idf:(bool->bool)->bool->bool", r"\x:bool->bool x");
        let c = def(r"c:bool->bool->bool", r"\x:bool \y:bool x");

        evaluate_eq(
            &wrapped(&[&id, &idf, &c], r"(c true) ((idf id) false)"),
            r"true",
        );
        evaluate_success(&wrapped(&[&id, &idf, &c], r"idf (c (id true))"));

        evaluate_eq(r"(\x:bool true) false", r"true");
    }
}
