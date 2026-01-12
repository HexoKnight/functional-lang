use typed_arena::Arena;

use crate::common::WithInfo;
use crate::reprs::{
    typed_ir::{self as tir},
    untyped_ir as uir,
};

use self::context::{Context, ContextInner};
use self::ty::Type;

mod ty;

mod context {
    use typed_arena::Arena;

    use crate::intern::InternedArena;

    use super::{InternedType, ty::Type};

    // doesn't suffer from the same dropck issues as self references
    // do not (currently) pass through this type
    /// Cheaply cloneable (hopefully) append-only stack
    type Stack<T> = Vec<T>;

    pub(super) struct ContextInner<'a> {
        ty_arena: InternedArena<'a, Type<'a>>,
    }
    impl<'a> ContextInner<'a> {
        pub(super) fn new(arena: &'a Arena<Type<'a>>) -> Self {
            Self {
                ty_arena: InternedArena::with_arena(arena),
            }
        }

        fn intern(&self, var: Type<'a>) -> InternedType<'a> {
            self.ty_arena.intern(var)
        }
    }

    #[must_use]
    #[derive(Clone)]
    pub(super) struct Context<'a, 'inn> {
        inner: &'inn ContextInner<'a>,
        var_ty_stack: Stack<InternedType<'a>>,
    }

    impl<'a, 'inn> Context<'a, 'inn> {
        pub(super) fn with_inner(inner: &'inn ContextInner<'a>) -> Self {
            Self {
                inner,
                var_ty_stack: Vec::new(),
            }
        }

        pub(super) fn intern<'s>(&'s self, var: Type<'a>) -> InternedType<'a> {
            self.inner.intern(var)
        }

        pub(super) fn push_var_ty(&self, var_ty: InternedType<'a>) -> Self {
            let mut new = self.clone();
            new.var_ty_stack.push(var_ty);
            new
        }

        pub(super) fn get_var_ty(&self, index: usize) -> Option<&'a Type<'a>> {
            self.var_ty_stack.iter().copied::<&_>().nth_back(index)
        }
    }
}

type TypeCheckError = String;

type InternedType<'a> = &'a Type<'a>;

trait TypeCheck<'i, 'a> {
    type TypeChecked;

    fn type_check(
        &self,
        ctx: &Context<'a, '_>,
    ) -> Result<(Self::TypeChecked, InternedType<'a>), TypeCheckError>;
}

pub fn type_check<'i>(
    untyped_ir: &uir::Term<'i>,
) -> Result<(tir::Term<'i>, String), TypeCheckError> {
    let arena = Arena::new();
    let inner = ContextInner::new(&arena);
    let ctx = Context::with_inner(&inner);

    let (term, ty) = untyped_ir.type_check(&ctx)?;
    Ok((term, format!("{ty:?}")))
}

impl<'i, 'a, T: TypeCheck<'i, 'a>> TypeCheck<'i, 'a> for Box<T> {
    type TypeChecked = Box<T::TypeChecked>;

    fn type_check(
        &self,
        ctx: &Context<'a, '_>,
    ) -> Result<(Self::TypeChecked, InternedType<'a>), TypeCheckError> {
        T::type_check(self, ctx).map(|(term, ty)| (Box::new(term), ty))
    }
}

impl<'i, 'a> TypeCheck<'i, 'a> for uir::Term<'i> {
    type TypeChecked = tir::Term<'i>;

    fn type_check(
        &self,
        ctx: &Context<'a, '_>,
    ) -> Result<(Self::TypeChecked, InternedType<'a>), TypeCheckError> {
        let WithInfo(info, term) = self;

        let (term, ty) = match term {
            uir::RawTerm::Abs(uir::Abs { arg_type, body }) => {
                let arg_type = arg_type.eval(ctx)?;

                let ctx_ = ctx.push_var_ty(arg_type);
                let (body, body_type) = body.type_check(&ctx_)?;

                let ty = Type::Arr(ty::Arr {
                    arg: arg_type,
                    result: body_type,
                });

                (tir::RawTerm::Abs(tir::Abs { body }), ctx.intern(ty))
            }
            uir::RawTerm::App(uir::App { func, arg }) => {
                let (func, func_type) = func.type_check(ctx)?;
                let (arg, arg_type) = arg.type_check(ctx)?;
                let ty = match (func_type, arg_type) {
                    (
                        Type::Arr(ty::Arr {
                            arg: func_arg_type,
                            result: func_result_type,
                        }),
                        arg_type,
                    ) => {
                        // TODO: ensure pointer equality optimisation
                        if *func_arg_type == arg_type {
                            *func_result_type
                        } else {
                            // TODO
                            return Err(format!(
                                "incorrect arg type:\n\
                                expected arg type: {func_arg_type:?}\n\
                                got arg type: {arg_type:?}",
                            ));
                        }
                    }
                    (func_type, _arg_type) => {
                        // TODO
                        return Err(format!("cannot apply an argument to type: {func_type:?}"));
                    }
                };
                (tir::RawTerm::App(tir::App { func, arg }), ty)
            }
            uir::RawTerm::Var(uir::Var { name: _, index }) => (
                tir::RawTerm::Var(tir::Var { index: *index }),
                ctx.get_var_ty(*index).ok_or_else(|| {
                    format!("illegal failure: variable index not found: {index}\n")
                })?,
            ),
            uir::RawTerm::Bool(b) => (tir::RawTerm::Bool(*b), ctx.intern(Type::Bool)),
        };

        Ok((WithInfo(*info, term), ty))
    }
}

impl<'a> uir::Type<'_> {
    fn eval(&self, ctx: &Context<'a, '_>) -> Result<InternedType<'a>, TypeCheckError> {
        let WithInfo(_info, ty) = self;

        let ty = match ty {
            uir::RawType::Arr(uir::Arr { arg, result }) => {
                let arg = arg.as_ref().eval(ctx)?;
                let result = result.as_ref().eval(ctx)?;
                Type::Arr(ty::Arr { arg, result })
            }
            uir::RawType::Bool => Type::Bool,
        };

        Ok(ctx.intern(ty))
    }
}

#[cfg(test)]
pub mod tests {
    use crate::validation::tests::validate_success;

    use super::*;

    #[track_caller]
    pub(crate) fn type_check_success(src: &str) -> (tir::Term<'_>, String) {
        let untyped_ir = validate_success(src);
        match type_check(&untyped_ir) {
            Ok(o) => o,
            Err(e) => panic!("type check failure:\n'{}'\n{}", src, e),
        }
    }

    #[track_caller]
    pub(crate) fn type_check_failure(src: &str) -> TypeCheckError {
        let ast = validate_success(src);
        match type_check(&ast) {
            Ok(o) => panic!("type check success:\n'{}'\n{:#?}", src, o),
            Err(e) => e,
        }
    }

    pub(crate) fn wrapped(wrappers: &[impl Fn(&str) -> String], inner: &str) -> String {
        let mut res = inner.to_string();
        for wrapper in wrappers {
            res = wrapper(&res);
        }
        res
    }

    pub(crate) fn def(signature: &str, body: &str) -> impl Fn(&str) -> String {
        move |s: &str| [r"(\", signature, "(", s, "))(", body, ")"].join("\n")
    }

    #[test]
    fn type_checking() {
        type_check_success(r"\x:bool x");
        type_check_success(r"\x:bool \y:bool x");

        type_check_success(r"(\x:bool x) true");
        type_check_success(r"\x:bool->bool x false");
        type_check_success(r"(\x: bool -> bool x) (\y: bool false)");

        type_check_success(r"(\id:bool->bool id) (\x:bool x)");

        let id = def(r"id:bool->bool", r"\x:bool x");
        let idf = def(r"idf:(bool->bool)->bool->bool", r"\x:bool->bool x");
        let c = def(r"c:bool->bool->bool", r"\x:bool \y:bool x");

        type_check_success(&wrapped(&[&id, &idf, &c], r"(c true) ((idf id) false)"));
        type_check_success(&wrapped(&[&id, &idf, &c], r"idf (c (id true))"));
        type_check_failure(&wrapped(&[&idf, &c], r"idf c"));

        type_check_failure(&wrapped(&[&idf, &c], r"idf c"));
    }
}
