use typed_arena::Arena;

use crate::common::WithInfo;
use crate::intern::InternedArena;
use crate::reprs::{
    typed_ir::{self as tir},
    untyped_ir as uir,
};

use self::ty::Type;

mod ty;

type TypeCheckError = String;

type InternedType<'ctx> = &'ctx Type<'ctx>;

struct Context<'ctx> {
    ty_arena: InternedArena<'ctx, Type<'ctx>>,
    var_ty_stack: Vec<InternedType<'ctx>>,
}

trait TypeCheck<'i, 'ctx>
where
    'i: 'ctx,
{
    type TypeChecked;

    fn type_check<'s>(
        &self,
        ctx: &mut Context<'ctx>,
    ) -> Result<(Self::TypeChecked, InternedType<'ctx>), TypeCheckError>;
}

pub fn type_check<'i>(
    untyped_ir: &uir::Term<'i>,
) -> Result<(tir::Term<'i>, String), TypeCheckError> {
    let arena = Arena::new();
    let mut ctx = Context {
        ty_arena: InternedArena::with_arena(&arena),
        var_ty_stack: Vec::new(),
    };

    let (term, ty) = untyped_ir.type_check(&mut ctx)?;
    Ok((term, format!("{ty:?}")))
}

impl<'i: 'ctx, 'ctx, T: TypeCheck<'i, 'ctx>> TypeCheck<'i, 'ctx> for Box<T> {
    type TypeChecked = Box<T::TypeChecked>;

    fn type_check<'s>(
        &self,
        ctx: &mut Context<'ctx>,
    ) -> Result<(Self::TypeChecked, InternedType<'ctx>), TypeCheckError> {
        T::type_check(&self, ctx).map(|(term, ty)| (Box::new(term), ty))
    }
}

impl<'i: 'ctx, 'ctx> TypeCheck<'i, 'ctx> for uir::Term<'i> {
    type TypeChecked = tir::Term<'i>;

    fn type_check<'s>(
        &self,
        ctx: &mut Context<'ctx>,
    ) -> Result<(Self::TypeChecked, InternedType<'ctx>), TypeCheckError> {
        let WithInfo(info, term) = self;

        let (term, ty) = match term {
            uir::RawTerm::Abs(uir::Abs { arg_type, body }) => {
                let arg_type = arg_type.eval(ctx)?;
                ctx.var_ty_stack.push(arg_type);

                let (body, body_type) = body.type_check(ctx)?;

                let ty = Type::Arr(ty::Arr {
                    arg: arg_type,
                    result: body_type,
                });

                (
                    tir::RawTerm::Abs(tir::Abs { body }),
                    ctx.ty_arena.intern(ty),
                )
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
                                expected arg type: {:?}\n\
                                got arg type: {:?}",
                                func_arg_type, arg_type,
                            ));
                        }
                    }
                    (func_type, _arg_type) => {
                        // TODO
                        return Err(format!("cannot apply an argument to type: {:?}", func_type));
                    }
                };
                (tir::RawTerm::App(tir::App { func, arg }), ty)
            }
            uir::RawTerm::Var(uir::Var { name: _, index }) => (
                tir::RawTerm::Var(tir::Var { index: *index }),
                *ctx.var_ty_stack
                    .iter()
                    .nth_back(*index)
                    .ok_or_else(|| format!("something has gone very wrong"))?,
            ),
            uir::RawTerm::Bool(b) => (tir::RawTerm::Bool(*b), ctx.ty_arena.intern(Type::Bool)),
        };

        Ok((WithInfo(*info, term), ty))
    }
}

impl<'i: 'ctx, 'ctx> uir::Type<'i> {
    fn eval(&self, ctx: &mut Context<'ctx>) -> Result<InternedType<'ctx>, TypeCheckError> {
        let WithInfo(_info, ty) = self;

        let ty = match ty {
            uir::RawType::Arr(uir::Arr { arg, result }) => {
                let arg = arg.as_ref().eval(ctx)?;
                let result = result.as_ref().eval(ctx)?;
                Type::Arr(ty::Arr { arg, result })
            }
            uir::RawType::Bool => Type::Bool,
        };

        Ok(ctx.ty_arena.intern(ty))
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
            Err(e) => panic!("validate failure:\n'{}'\n{}", src, e),
        }
    }

    #[track_caller]
    pub(crate) fn type_check_failure(src: &str) -> TypeCheckError {
        let ast = validate_success(src);
        match type_check(&ast) {
            Ok(o) => panic!("validate success:\n'{}'\n{:#?}", src, o),
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
