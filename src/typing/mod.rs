use std::collections::HashMap;

use itertools::{Itertools, zip_eq};
use typed_arena::Arena;

use crate::common::WithInfo;
use crate::reprs::common::{ArgStructure, Lvl};
use crate::reprs::{
    typed_ir::{self as tir},
    untyped_ir as uir,
};
use crate::typing::merge::join;
use crate::typing::subtyping::check_subtype;
use crate::typing::ty::TyBounds;

use self::context::{Context, ContextInner};
use self::ty::Type;

mod merge;
mod subtyping;
mod ty;

mod context {
    use typed_arena::Arena;

    use crate::{
        intern::InternedArena,
        reprs::common::{Idx, Lvl},
        typing::ty::TyBounds,
    };

    use super::{InternedType, TypeCheckError, ty::Type};

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
        ty_var_stack: Stack<(&'a str, TyBounds<'a>)>,
    }

    impl<'a, 'inn> Context<'a, 'inn> {
        pub(super) fn with_inner(inner: &'inn ContextInner<'a>) -> Self {
            Self {
                inner,
                var_ty_stack: Vec::new(),
                ty_var_stack: Vec::new(),
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

        pub(super) fn get_var_ty(&self, index: Idx) -> Option<&'a Type<'a>> {
            index.get(&self.var_ty_stack).copied()
        }

        pub(super) fn push_ty_var(&self, ty_var_name: &'a str, ty_var: TyBounds<'a>) -> Self {
            let mut new = self.clone();
            new.ty_var_stack.push((ty_var_name, ty_var));
            new
        }

        pub(super) fn get_ty_var(&self, level: Lvl) -> Option<(&'a str, TyBounds<'a>)> {
            level.get(&self.ty_var_stack).copied()
        }

        pub(super) fn get_ty_var_unwrap(
            &self,
            level: Lvl,
        ) -> Result<(&'a str, TyBounds<'a>), TypeCheckError> {
            self.get_ty_var(level)
                .ok_or_else(|| format!("illegal failure: type variable level not found: {level:?}"))
        }

        pub(super) fn next_ty_var_level(&self) -> Lvl {
            Lvl::get_depth(&self.ty_var_stack)
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

/// Takes an [`untyped_ir::Term`][uir::Term] and checks that it can be typed, returning a
/// [`typed_ir::Term`][tir::Term], which is entirely type erased, along with a string
/// representing the type of the term.
///
/// # Errors
/// When type checking fails.
pub fn type_check<'i>(
    untyped_ir: &uir::Term<'i>,
) -> Result<(tir::Term<'i>, String), TypeCheckError> {
    let arena = Arena::new();
    let inner = ContextInner::new(&arena);
    let ctx = Context::with_inner(&inner);

    let (term, ty) = untyped_ir.type_check(&ctx)?;
    Ok((term, ty.display(&ctx)?))
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
                let destructured_arg_types = arg_type.destructure(arg_structure, ctx)?;

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

                let func_result_type = func_type.get_function_result_type(ctx)?;
                check_subtype(
                    ctx.intern(Type::Arr {
                        arg: arg_type,
                        result: ctx.intern(Type::Any),
                    }),
                    func_type,
                    ctx,
                )
                .map_err(|mut e| {
                    e.insert_str(0, "error typing function application:\n");
                    e
                })?;
                (tir::RawTerm::App { func, arg }, func_result_type)
            }
            uir::RawTerm::TyAbs { name, bounds, body } => {
                let bounds = bounds.eval(ctx)?;

                let ctx_ = ctx.push_ty_var(name, bounds);
                let (body, body_type) = body.type_check(&ctx_)?;

                let WithInfo(_info, body) = *body;

                (
                    body,
                    ctx.intern(Type::TyAbs {
                        name,
                        bounds,
                        result: body_type,
                    }),
                )
            }
            uir::RawTerm::TyApp { abs, arg } => {
                let (abs, abs_type) = abs.type_check(ctx)?;
                let WithInfo(_info, abs) = *abs;

                let arg = arg.eval(ctx)?;
                let Type::TyAbs {
                    name: _,
                    bounds,
                    result,
                } = abs_type
                else {
                    // TODO
                    return Err(format!(
                        "cannot apply a type argument to type: {abs_type}",
                        abs_type = abs_type.display(ctx)?
                    ));
                };
                if let Some(upper) = bounds.upper {
                    check_subtype(upper, arg, ctx)
                        .map_err(prepend(|| "unsatisfied type arg upper bound:\n"))?;
                }
                if let Some(lower) = bounds.lower {
                    check_subtype(arg, lower, ctx)
                        .map_err(prepend(|| "unsatisfied type arg lower bound:\n"))?;
                }
                let ty = result.substitute_ty_var(arg, ctx);
                (abs, ty)
            }
            uir::RawTerm::Var(index) => (
                tir::RawTerm::Var(*index),
                ctx.get_var_ty(*index).ok_or_else(|| {
                    format!("illegal failure: variable index not found: {index:?}\n")
                })?,
            ),
            uir::RawTerm::Enum(enum_type, label) => {
                let enum_type = enum_type.eval(ctx)?;

                let Type::Enum(variants) = enum_type else {
                    // TODO
                    return Err(format!(
                        "cannot construct an enum with a non-enum type: {enum_type}",
                        enum_type = enum_type.display(ctx)?
                    ));
                };
                let Some(variant_type) = variants.0.get(label) else {
                    // TODO
                    return Err(format!(
                        "enum type does not contain label '{label}': {enum_type}",
                        enum_type = enum_type.display(ctx)?
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
            uir::RawTerm::Match(enum_type, arms) => {
                let enum_type = enum_type.eval(ctx)?;
                let Type::Enum(variants) = enum_type else {
                    // TODO
                    return Err(format!(
                        "cannot match on a non-enum type: {enum_type}",
                        enum_type = enum_type.display(ctx)?
                    ));
                };

                let (arms, result_types): (HashMap<_, _>, Vec<_>) = arms
                    .iter()
                    .map(|(label, func)| -> Result<_, TypeCheckError> {
                        let (func, func_type) = func.type_check(ctx)?;
                        // check dead branches
                        let Some(variant_type) = variants.0.get(label) else {
                            // TODO
                            return Err(format!(
                                "enum type does not contain label '{label}': {enum_type}",
                                enum_type = enum_type.display(ctx)?
                            ));
                        };
                        let Type::Arr {
                            arg: func_arg_type,
                            result: func_result_type,
                        } = func_type
                        else {
                            // TODO
                            return Err(format!(
                                "match arm must be a function type: {func_type}",
                                func_type = func_type.display(ctx)?
                            ));
                        };
                        check_subtype(func_arg_type, variant_type, ctx)
                            .map_err(prepend(|| "incorrect match arm type:\n"))?;
                        Ok(Some(((*label, func), *func_result_type)))
                    })
                    .filter_map_ok(|o| o)
                    .try_collect()?;

                variants.0.iter().try_for_each(|(label, _)| {
                    if arms.contains_key(label) {
                        Ok(())
                    } else {
                        // TODO
                        Err(format!("match missing arm with label '{label}'"))
                    }
                })?;
                (
                    tir::RawTerm::Match(arms),
                    ctx.intern(Type::Arr {
                        arg: enum_type,
                        result: join(result_types, ctx)?,
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
            uir::RawType::TyAbs {
                name,
                bounds,
                result,
            } => {
                let bounds = bounds.eval(ctx)?;
                Type::TyAbs {
                    name,
                    bounds,
                    // ty_vars are not currently used so this is useless but may as well push it if
                    // only for future correctness
                    result: result.eval(&ctx.push_ty_var(name, bounds))?,
                }
            }
            uir::RawType::TyVar(level) => Type::TyVar(*level),
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
            uir::RawType::Any => Type::Any,
            uir::RawType::Never => Type::Never,
        };

        Ok(ctx.intern(ty))
    }
}

impl<'i: 'a, 'a> uir::TyBounds<'i> {
    fn eval(&self, ctx: &Context<'a, '_>) -> Result<TyBounds<'a>, TypeCheckError> {
        let uir::TyBounds { upper, lower } = self;
        let upper = upper.as_ref().map(|ty| ty.eval(ctx)).transpose()?;
        let lower = lower.as_ref().map(|ty| ty.eval(ctx)).transpose()?;
        if let (Some(upper), Some(lower)) = (upper, lower) {
            check_subtype(upper, lower, ctx).map_err(prepend(
                || "type bound error: upper bound must be supertype of lower bound",
            ))?;
        }
        Ok(TyBounds { upper, lower })
    }
}

fn ty_eq<'a>(ty1: InternedType<'a>, ty2: InternedType<'a>) -> bool {
    std::ptr::eq(ty1, ty2)
}

impl<'a> Type<'a> {
    fn get_function_result_type(
        &'a self,
        ctx: &Context<'a, '_>,
    ) -> Result<&'a Self, TypeCheckError> {
        match self {
            Type::Arr { arg: _, result } => Ok(result),
            Type::TyVar(level) => ctx
                .get_ty_var_unwrap(*level)?
                .1
                .upper
                .map(|t| t.get_function_result_type(ctx))
                .unwrap_or(Err(format!(
                    "expected function type but got a type arg without an upper bound:\n{}",
                    self.display(ctx)?
                ))),
            Type::Never => Ok(self),
            _ => Err(format!(
                "expected function type\ngot: {}",
                self.display(ctx)?
            )),
        }
    }
}

impl<'a> Type<'a> {
    fn destructure(
        &self,
        arg_structure: &ArgStructure,
        ctx: &Context<'a, '_>,
    ) -> Result<impl Iterator<Item = &Self>, TypeCheckError> {
        fn inner<'a, 's>(
            arg_structure: &ArgStructure,
            ty: &'s Type<'a>,
            ctx: &Context<'a, '_>,
            output: &mut impl FnMut(&'s Type<'a>),
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
                    zip_eq(st_elems, ty_elems)
                        .try_for_each(|(st, ty)| inner(st, ty, ctx, output))?;
                }

                (ArgStructure::Tuple(_), ty) => {
                    // TODO
                    return Err(format!(
                        "cannot tuple-destructure value of type {ty}",
                        ty = ty.display(ctx)?
                    ));
                }
                (ArgStructure::Var, ty) => output(ty),
            }
            Ok(())
        }
        let mut buffer = Vec::new();
        inner(arg_structure, self, ctx, &mut |ty| buffer.push(ty))?;
        Ok(buffer.into_iter())
    }

    fn substitute_ty_var_rec(
        &'a self,
        depth: Lvl,
        ty: &'a Self,
        ctx: &Context<'a, '_>,
    ) -> &'a Self {
        let ty = match self {
            Type::TyAbs {
                name,
                bounds: TyBounds { upper, lower },
                result,
            } => Type::TyAbs {
                name,
                bounds: TyBounds {
                    upper: upper.map(|t| t.substitute_ty_var_rec(depth, ty, ctx)),
                    lower: lower.map(|t| t.substitute_ty_var_rec(depth, ty, ctx)),
                },
                result: result.substitute_ty_var_rec(depth, ty, ctx),
            },
            Type::TyVar(level) if *level == depth => return ty,
            Type::TyVar(level) => match level.shallower() {
                // deeper than replaced but not equal (due to prev arm)
                Some(shallower) if level.deeper_than(depth) => Type::TyVar(shallower),
                // either:
                // - shallowest so could not be strictly deeper
                // - not deeper
                None | Some(_) => return self,
            },
            Type::Arr { arg, result } => Type::Arr {
                arg: arg.substitute_ty_var_rec(depth, ty, ctx),
                result: result.substitute_ty_var_rec(depth, ty, ctx),
            },
            Type::Enum(variants) => Type::Enum(
                variants
                    .0
                    .iter()
                    .map(|(l, t)| (*l, t.substitute_ty_var_rec(depth, ty, ctx)))
                    .collect(),
            ),
            Type::Tuple(elems) => Type::Tuple(
                elems
                    .iter()
                    .map(|e| e.substitute_ty_var_rec(depth, ty, ctx))
                    .collect(),
            ),
            Type::Bool | Type::Any | Type::Never => return self,
        };

        ctx.intern(ty)
    }

    fn substitute_ty_var(&'a self, ty: &'a Self, ctx: &Context<'a, '_>) -> &'a Self {
        self.substitute_ty_var_rec(ctx.next_ty_var_level(), ty, ctx)
    }
}

fn prepend<'s, F, S>(f: F) -> impl FnOnce(TypeCheckError) -> TypeCheckError
where
    F: FnOnce() -> S,
    S: Into<std::borrow::Cow<'s, str>>,
{
    |mut e| {
        e.insert(0, '\n');
        e.insert_str(0, &f().into());
        e
    }
}

fn try_prepend<'s, F, S>(f: F) -> impl FnOnce(TypeCheckError) -> TypeCheckError
where
    F: FnOnce() -> Result<S, TypeCheckError>,
    S: Into<std::borrow::Cow<'s, str>>,
{
    |mut e| match f() {
        Ok(s) => {
            e.insert(0, '\n');
            e.insert_str(0, &s.into());
            e
        }
        Err(e) => e,
    }
}
