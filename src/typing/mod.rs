use itertools::{Itertools, zip_eq};
use typed_arena::Arena;

use crate::common::WithInfo;
use crate::reprs::common::ArgStructure;
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

        pub(super) fn push_var_tys(
            &self,
            vars: impl IntoIterator<Item = InternedType<'a>>,
        ) -> Self {
            let mut new = self.clone();
            new.var_ty_stack.extend(vars);
            new
        }

        pub(super) fn get_var_ty(&self, index: usize) -> Option<&'a Type<'a>> {
            self.var_ty_stack.iter().copied::<&_>().nth_back(index)
        }
    }
}

type InternedType<'a> = &'a Type<'a>;

pub type TypeCheckError = String;

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

impl<'i: 'a, 'a> TypeCheck<'i, 'a> for uir::Term<'i> {
    type TypeChecked = tir::Term<'i>;

    fn type_check(
        &self,
        ctx: &Context<'a, '_>,
    ) -> Result<(Self::TypeChecked, InternedType<'a>), TypeCheckError> {
        let WithInfo(info, term) = self;

        let (term, ty) = match term {
            uir::RawTerm::Abs {
                arg_structure,
                arg_type,
                body,
            } => {
                let arg_type = arg_type.eval(ctx)?;
                let destructured_arg_types = arg_type.destructure(arg_structure)?;

                let ctx_ = ctx.push_var_tys(destructured_arg_types);
                let (body, body_type) = body.type_check(&ctx_)?;

                let ty = Type::Arr {
                    arg: arg_type,
                    result: body_type,
                };

                (
                    tir::RawTerm::Abs {
                        arg_structure: arg_structure.clone(),
                        body,
                    },
                    ctx.intern(ty),
                )
            }
            uir::RawTerm::App { func, arg } => {
                let (func, func_type) = func.type_check(ctx)?;
                let (arg, arg_type) = arg.type_check(ctx)?;
                let ty = match (func_type, arg_type) {
                    (
                        Type::Arr {
                            arg: func_arg_type,
                            result: func_result_type,
                        },
                        arg_type,
                    ) => {
                        if eq_ty(func_arg_type, arg_type) {
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
                (tir::RawTerm::App { func, arg }, ty)
            }
            uir::RawTerm::Var { name: _, index } => (
                tir::RawTerm::Var { index: *index },
                ctx.get_var_ty(*index).ok_or_else(|| {
                    format!("illegal failure: variable index not found: {index}\n")
                })?,
            ),
            uir::RawTerm::Enum(enum_type, label) => {
                let enum_type = enum_type.eval(ctx)?;

                let Type::Enum(variants) = enum_type else {
                    // TODO
                    return Err(format!(
                        "cannot construct an enum with a non-enum type: {enum_type:?}"
                    ));
                };
                let Some(variant_type) = variants.0.get(label.0) else {
                    // TODO
                    return Err(format!(
                        "enum type does not contain label '{label:?}': {enum_type:?}"
                    ));
                };
                (
                    tir::RawTerm::Enum(*label),
                    ctx.intern(Type::Arr {
                        arg: variant_type,
                        result: enum_type,
                    }),
                )
            }
            uir::RawTerm::Tuple(elems) => {
                let (elems, types): (Vec<_>, Vec<_>) =
                    elems.iter().map(|e| e.type_check(ctx)).try_collect()?;
                (
                    tir::RawTerm::Tuple(elems.into_boxed_slice()),
                    ctx.intern(Type::Tuple(types.into_boxed_slice())),
                )
            }
            uir::RawTerm::Bool(b) => (tir::RawTerm::Bool(*b), ctx.intern(Type::Bool)),
        };

        Ok((WithInfo(*info, term), ty))
    }
}

impl<'i: 'a, 'a> uir::Type<'i> {
    fn eval(&self, ctx: &Context<'a, '_>) -> Result<InternedType<'a>, TypeCheckError> {
        let WithInfo(_info, ty) = self;

        let ty = match ty {
            uir::RawType::Arr { arg, result } => {
                let arg = arg.as_ref().eval(ctx)?;
                let result = result.as_ref().eval(ctx)?;
                Type::Arr { arg, result }
            }
            uir::RawType::Tuple(elems) => {
                Type::Tuple(elems.iter().map(|e| e.eval(ctx)).try_collect()?)
            }
            uir::RawType::Enum(variants) => Type::Enum(
                variants
                    .iter()
                    .map(|(l, t)| t.eval(ctx).map(|t| (*l, t)))
                    .try_collect()?,
            ),
            uir::RawType::Bool => Type::Bool,
        };

        Ok(ctx.intern(ty))
    }
}

fn eq_ty<'a>(ty1: InternedType<'a>, ty2: InternedType<'a>) -> bool {
    std::ptr::eq(ty1, ty2)
}

impl Type<'_> {
    fn destructure(
        &self,
        arg_structure: &ArgStructure,
    ) -> Result<impl Iterator<Item = &Self>, TypeCheckError> {
        fn inner<'ctx, 's>(
            arg_structure: &ArgStructure,
            ty: &'s Type<'ctx>,
            output: &mut impl FnMut(&'s Type<'ctx>),
        ) -> Result<(), TypeCheckError> {
            match (arg_structure, ty) {
                (ArgStructure::Tuple(st_elems), Type::Tuple(ty_elems)) => {
                    let st_len = st_elems.len();
                    let ty_len = ty_elems.len();
                    if st_len != ty_len {
                        // TODO
                        return Err(format!(
                            "destructured tuple has {st_len} elements\nwhile it's type has {ty_len} elements"
                        ));
                    }
                    zip_eq(st_elems, ty_elems).try_for_each(|(st, ty)| inner(st, ty, output))?;
                }

                (ArgStructure::Tuple(_), ty) => {
                    // TODO
                    return Err(format!("cannot tuple-destructure value of type {ty:?}"));
                }
                (ArgStructure::Var, ty) => output(ty),
            }
            Ok(())
        }
        let mut buffer = Vec::new();
        inner(arg_structure, self, &mut |ty| buffer.push(ty))?;
        Ok(buffer.into_iter())
    }
}
