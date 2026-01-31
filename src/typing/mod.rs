use std::collections::HashMap;
use std::convert::Infallible;

use itertools::{Itertools, zip_eq};
use typed_arena::Arena;

use crate::common::{WithInfo, maybe_zip_eq};
use crate::reprs::common::{ArgStructure, Lvl};
use crate::reprs::{
    typed_ir::{self as tir},
    untyped_ir as uir,
};
use crate::typing::context::{TyArenaContext, TyVarContext};
use crate::typing::eval::TyEval;
use crate::typing::merge::join;
use crate::typing::subtyping::expect_type;
use crate::typing::ty::{TyBounds, TyDisplay};

use self::context::ContextInner;
use self::ty::Type;
use self::typing_context::Context;

mod context;
mod eval;
mod merge;
mod subtyping;
mod ty;

mod typing_context {
    use crate::{
        reprs::common::{Idx, Lvl},
        typing::{
            context::{ContextInner, Stack, TyArenaContext, TyVarContext},
            ty::TyBounds,
        },
    };

    use super::{InternedType, ty::Type};

    #[must_use]
    #[derive(Clone)]
    pub(super) struct Context<'a, 'inn> {
        pub(super) inner: &'inn ContextInner<'a>,
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
    }

    impl<'a, 'inn> TyArenaContext<'a> for Context<'a, 'inn> {
        type Inner = &'inn ContextInner<'a>;

        fn get_inner(&self) -> &'inn ContextInner<'a> {
            self.inner
        }
    }

    impl<'a> TyVarContext<'a> for Context<'a, '_> {
        type TyVar = TyBounds<'a>;

        fn push_ty_var(&self, ty_var_name: &'a str, ty_var: TyBounds<'a>) -> Self {
            let mut new = self.clone();
            new.ty_var_stack.push((ty_var_name, ty_var));
            new
        }

        fn get_ty_var(&self, level: Lvl) -> Option<(&'a str, TyBounds<'a>)> {
            level.get(&self.ty_var_stack).copied()
        }

        fn next_ty_var_level(&self) -> Lvl {
            Lvl::get_depth(&self.ty_var_stack)
        }

        fn get_ty_vars(&self) -> impl Iterator<Item = (&'a str, TyBounds<'a>)> {
            self.ty_var_stack.iter().copied()
        }
    }
}

type InternedType<'a> = &'a Type<'a>;

pub type TypeCheckError = String;

trait TypeCheck<'i, 'a> {
    type TypeChecked;

    fn type_check(
        &self,
        check_type: Option<InternedType<'a>>,
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

    let (term, ty) = untyped_ir.type_check(None, &ctx)?;
    Ok((term, ty.display(&ctx)?))
}

impl<'i, 'a, T: TypeCheck<'i, 'a>> TypeCheck<'i, 'a> for Box<T> {
    type TypeChecked = Box<T::TypeChecked>;

    fn type_check(
        &self,
        check_type: Option<InternedType<'a>>,
        ctx: &Context<'a, '_>,
    ) -> Result<(Self::TypeChecked, InternedType<'a>), TypeCheckError> {
        T::type_check(self, check_type, ctx).map(|(term, ty)| (Box::new(term), ty))
    }
}

impl<'i: 'a, 'a> TypeCheck<'i, 'a> for uir::Term<'i> {
    type TypeChecked = tir::Term<'i>;

    fn type_check(
        &self,
        check_type: Option<InternedType<'a>>,
        ctx: &Context<'a, '_>,
    ) -> Result<(Self::TypeChecked, InternedType<'a>), TypeCheckError> {
        let WithInfo(info, term) = self;

        // mutable so it can be `take()`n when used then for cases that don't use it, it will be
        // checked afterwards
        let mut check_type = if let Some(ty) = check_type {
            // we need a concrete type to do any real checking
            ty.upper_concrete(ctx)?
                // top type provides no information and is equivalent to no check_type at all
                .not_any()
        } else {
            None
        };

        let (term, ty) = match term {
            uir::RawTerm::Abs {
                arg_structure,
                arg_type: arg,
                body,
            } => {
                if let Some(arg) = arg {
                    let arg = arg.eval(ctx)?;

                    let (check_arg, check_body) = if let Some(check_type) = check_type.take() {
                        let Type::Arr {
                            arg: check_arg,
                            result: check_result,
                        } = check_type
                        else {
                            return Err(format!(
                                "expected: {}\n\
                                got function definition",
                                check_type.display(ctx)?
                            ));
                        };
                        (Some(*check_arg), Some(*check_result))
                    } else {
                        (None, None)
                    };

                    if let Some(check_arg) = check_arg {
                        expect_type(check_arg, arg, false, ctx)?;
                    }

                    let destructured_arg_types = arg.destructure(arg_structure, ctx)?;
                    let ctx_ = ctx.push_var_tys(destructured_arg_types);
                    let (body, result) = body.type_check(check_body, &ctx_)?;

                    let ty = Type::Arr { arg, result };

                    (
                        tir::RawTerm::Abs {
                            arg_structure: arg_structure.clone(),
                            body,
                        },
                        ctx.intern(ty),
                    )
                } else if let Some(check_type) = check_type.take() {
                    let Type::Arr {
                        arg: check_arg,
                        result: check_result,
                    } = check_type
                    else {
                        return Err(format!(
                            "expected: {}\n\
                            got function definition",
                            check_type.display(ctx)?
                        ));
                    };

                    let check_destructured_args = check_arg.destructure(arg_structure, ctx)?;

                    let ctx_ = ctx.push_var_tys(check_destructured_args);
                    let (body, result) = body.type_check(Some(check_result), &ctx_)?;

                    let ty = Type::Arr {
                        arg: check_arg,
                        result,
                    };

                    (
                        tir::RawTerm::Abs {
                            arg_structure: arg_structure.clone(),
                            body,
                        },
                        ctx.intern(ty),
                    )
                } else {
                    return Err(format!(
                        "type inference error: cannot infer type of argument: {}",
                        "TODO"
                    ));
                }
            }
            uir::RawTerm::App {
                func: func_term,
                arg: arg_term,
            } => {
                let check_type = check_type.take();
                let check_func = ctx.intern(Type::Arr {
                    arg: ctx.intern(Type::Never),
                    result: check_type.unwrap_or_else(|| ctx.intern(Type::Any)),
                });

                let (func_term, func) = func_term.type_check(Some(check_func), ctx)?;

                let Type::Arr {
                    arg: func_arg,
                    result,
                } = func.upper_concrete(ctx)?
                else {
                    return Err(if let Some(check_type) = check_type {
                        format!(
                            "expected: {}\n\
                            got:      {}",
                            check_type.display(ctx)?,
                            func.display(ctx)?
                        )
                    } else {
                        format!(
                            "expected function\n\
                            got: {}",
                            func.display(ctx)?
                        )
                    });
                };

                let (arg_term, arg) = arg_term.type_check(Some(func_arg), ctx)?;

                expect_type(func_arg, arg, true, ctx)
                    .map_err(prepend(|| "incorrect argument type:"))?;
                (
                    tir::RawTerm::App {
                        func: func_term,
                        arg: arg_term,
                    },
                    *result,
                )
            }
            uir::RawTerm::TyAbs { name, bounds, body } => {
                let bounds = bounds.eval(ctx)?;

                let check_result = if let Some(check_type) = check_type.take() {
                    let Type::TyAbs {
                        name: _,
                        bounds: check_bounds,
                        result: check_result,
                    } = check_type
                    else {
                        return Err(format!(
                            "expected: {}\n\
                            found a type abstraction",
                            check_type.display(ctx)?
                        ));
                    };

                    TyBounds::expect_bounds(check_bounds, &bounds, true, ctx).map_err(
                        try_prepend(|| {
                            Ok(format!(
                                "expected bounds (or wider): {}\n\
                                but found:                  {}",
                                check_bounds.display(ctx)?,
                                bounds.display(ctx)?
                            ))
                        }),
                    )?;

                    Some(*check_result)
                } else {
                    None
                };

                let ctx_ = ctx.push_ty_var(name, bounds);
                let (body, result) = body.type_check(check_result, &ctx_)?;

                let WithInfo(_info, body) = *body;

                (
                    body,
                    ctx.intern(Type::TyAbs {
                        name,
                        bounds,
                        result,
                    }),
                )
            }
            uir::RawTerm::TyApp { abs: abs_term, arg } => {
                let arg = arg.eval(ctx)?;

                let check_abs = check_type.take().map(|check_type| {
                    ctx.intern(Type::TyAbs {
                        name: "$",
                        bounds: TyBounds {
                            upper: Some(arg),
                            lower: Some(arg),
                        },
                        result: check_type,
                    })
                });

                let (abs_term, abs) = abs_term.type_check(check_abs, ctx)?;
                let WithInfo(_info, abs_term) = *abs_term;

                let Type::TyAbs {
                    name: _,
                    bounds,
                    result,
                } = abs
                else {
                    return Err(format!(
                        "cannot apply a type argument to type: {abs}",
                        abs = abs.display(ctx)?
                    ));
                };
                if let Some(upper) = bounds.get_upper(ctx).not_any() {
                    expect_type(upper, arg, true, ctx)
                        .map_err(prepend(|| "unsatisfied type arg upper bound:\n"))?;
                }
                if let Some(lower) = bounds.get_lower(ctx).not_never() {
                    expect_type(lower, arg, false, ctx)
                        .map_err(prepend(|| "unsatisfied type arg lower bound:\n"))?;
                }
                let ty = result.substitute_ty_var(ctx.next_ty_var_level(), arg, ctx);
                (abs_term, ty)
            }
            uir::RawTerm::Var(index) => {
                let ty = ctx.get_var_ty(*index).ok_or_else(|| {
                    format!("illegal failure: variable index not found: {index:?}\n")
                })?;

                let ty = if let Some(check_type) = check_type.take() {
                    expect_type(check_type, ty, true, ctx).map_err(try_prepend(|| {
                        Ok(format!(
                            "expected: {}\n\
                            got:      {}",
                            check_type.display(ctx)?,
                            ty.display(ctx)?,
                        ))
                    }))?;
                    ty
                } else {
                    ty
                };

                (tir::RawTerm::Var(*index), ty)
            }
            uir::RawTerm::Enum(arg, label) => {
                let arg = arg.eval(ctx)?;

                let (check_arg, check_enum) = if let Some(check_type) = check_type.take() {
                    let Type::Arr {
                        arg: check_arg,
                        result: check_enum,
                    } = check_type
                    else {
                        return Err(format!(
                            "expected: {}\n\
                            found an enum constructor (a function)",
                            check_type.display(ctx)?
                        ));
                    };
                    (
                        check_arg.upper_concrete(ctx)?.not_never(),
                        check_enum.upper_concrete(ctx)?.not_any(),
                    )
                } else {
                    (None, None)
                };

                let arg = if let (Some(arg), Some(check_arg)) = (arg, check_arg) {
                    Some(expect_type(check_arg, arg, false, ctx)?)
                } else {
                    arg
                };

                if let Some(check_enum) = check_enum {
                    let Type::Enum(check_variants) = check_enum else {
                        return Err(format!(
                            "expected a function that returns: {}\n\
                            found an enum constructor (a function that returns an enum)",
                            check_enum.display(ctx)?
                        ));
                    };

                    let Some(check_variant_type) = check_variants.0.get(label) else {
                        return Err(format!(
                            "expected enum type does not contain label '{label}': {}",
                            check_enum.display(ctx)?
                        ));
                    };

                    let result = ctx.intern(Type::Enum(
                        std::iter::once((*label, *check_variant_type)).collect(),
                    ));

                    let result = expect_type(check_enum, result, true, ctx)
                        .map_err(prepend(|| "incorrect enum result type:\n"))?;

                    (
                        tir::RawTerm::Enum(*label),
                        ctx.intern(Type::Arr {
                            arg: check_variant_type,
                            result,
                        }),
                    )
                } else if let Some(arg) = arg {
                    let result = ctx.intern(Type::Enum(std::iter::once((*label, arg)).collect()));
                    (
                        tir::RawTerm::Enum(*label),
                        ctx.intern(Type::Arr { arg, result }),
                    )
                } else {
                    return Err(format!(
                        "type inference error: cannot infer type of enum constructor with label: '{label}'",
                    ));
                }
            }
            uir::RawTerm::Match(enum_type, arms) => {
                let enum_type = enum_type.eval(ctx)?;

                let (enum_type, check_result) = if let Some(check_type) = check_type.take() {
                    let Type::Arr {
                        arg: check_arg,
                        result: check_result,
                    } = check_type
                    else {
                        return Err(format!(
                            "expected: {}\n\
                            found a match expression (a function)",
                            check_type.display(ctx)?
                        ));
                    };

                    if let Some(enum_type) = enum_type {
                        expect_type(check_arg, enum_type, false, ctx)
                            .map_err(prepend(|| "incorrect match arg type:\n"))?;
                    }

                    (
                        enum_type.or(check_arg.upper_concrete(ctx)?.not_never()),
                        check_result.upper_concrete(ctx)?.not_any(),
                    )
                } else {
                    (enum_type, None)
                };

                if let Some(enum_type) = enum_type {
                    let Type::Enum(variants) = enum_type else {
                        return Err(format!(
                            "cannot match on a non-enum type: {enum_type}",
                            enum_type = enum_type.display(ctx)?
                        ));
                    };

                    let (arms, results): (HashMap<_, _>, Vec<_>) = arms
                        .iter()
                        .map(|(label, func_term)| -> Result<_, TypeCheckError> {
                            // check dead branches
                            let Some(variant) = variants.0.get(label) else {
                                return Err(format!(
                                    "enum type does not contain label '{label}': {enum_type}",
                                    enum_type = enum_type.display(ctx)?
                                ));
                            };

                            let check_func = ctx.intern(Type::Arr {
                                arg: variant,
                                result: check_result.unwrap_or_else(|| ctx.intern(Type::Any)),
                            });

                            let (func_term, func) = func_term.type_check(Some(check_func), ctx)?;

                            let Type::Arr {
                                arg: func_arg,
                                result: func_result,
                            } = func
                            else {
                                return Err(format!(
                                    "match arm must be a function type: {func}",
                                    func = func.display(ctx)?
                                ));
                            };
                            expect_type(variant, func_arg, false, ctx)
                                .map_err(prepend(|| "incorrect match arm type:\n"))?;

                            Ok(Some(((*label, func_term), *func_result)))
                        })
                        .filter_map_ok(|o| o)
                        .try_collect()?;

                    variants.0.iter().try_for_each(|(label, _)| {
                        if arms.contains_key(label) {
                            Ok(())
                        } else {
                            Err(format!("match missing arm with label '{label}'"))
                        }
                    })?;
                    (
                        tir::RawTerm::Match(arms),
                        ctx.intern(Type::Arr {
                            arg: enum_type,
                            result: join(results, ctx)?,
                        }),
                    )
                } else {
                    let (arms, variants, results): (HashMap<_, _>, _, Vec<_>) = arms
                        .iter()
                        .map(|(label, func_term)| -> Result<_, TypeCheckError> {
                            let (func_term, func) = func_term.type_check(
                                Some(ctx.intern(Type::Arr {
                                    arg: ctx.intern(Type::Never),
                                    result: ctx.intern(Type::Any),
                                })),
                                ctx,
                            )?;

                            let Type::Arr {
                                arg: func_arg,
                                result: func_result,
                            } = func
                            else {
                                return Err(format!(
                                    "match arm must be a function type: {func}",
                                    func = func.display(ctx)?
                                ));
                            };

                            Ok(Some((
                                (*label, func_term),
                                (*label, *func_arg),
                                *func_result,
                            )))
                        })
                        .filter_map_ok(|o| o)
                        .try_collect()?;
                    (
                        tir::RawTerm::Match(arms),
                        ctx.intern(Type::Arr {
                            arg: ctx.intern(Type::Enum(variants)),
                            result: join(results, ctx)?,
                        }),
                    )
                }
            }
            uir::RawTerm::Tuple(elem_terms) => {
                let check_elems = check_type
                    .take()
                    .map(|check_type| {
                        let Type::Tuple(check_elems) = check_type else {
                            return Err(format!(
                                "expected: {}\n\
                                got a tuple type",
                                check_type.display(ctx)?
                            ));
                        };
                        let len = elem_terms.len();
                        let check_len = check_elems.len();
                        if len != check_len {
                            return Err(format!(
                                "expected: {}\n\
                                got tuple with {len} elements",
                                check_type.display(ctx)?
                            ));
                        }
                        Ok(check_elems.iter().copied())
                    })
                    .transpose()?;
                let (elem_terms, elems): (Vec<_>, Vec<_>) = maybe_zip_eq(elem_terms, check_elems)
                    .map(|(elem_term, check_elem)| elem_term.type_check(check_elem, ctx))
                    .try_collect()?;
                (
                    tir::RawTerm::Tuple(elem_terms.into_boxed_slice()),
                    ctx.intern(Type::Tuple(elems.into_boxed_slice())),
                )
            }
            uir::RawTerm::Bool(b) => (tir::RawTerm::Bool(*b), ctx.intern(Type::Bool)),
        };

        // if we don't explicity check above (using `.take()`), we do a basic subtype check here
        let ty = if let Some(check_type) = check_type.take() {
            expect_type(check_type, ty, true, ctx).map_err(try_prepend(|| {
                Ok(format!(
                    "expected: {}\n\
                    got:      {}",
                    check_type.display(ctx)?,
                    ty.display(ctx)?,
                ))
            }))?
        } else {
            ty
        };

        Ok((WithInfo(*info, term), ty))
    }
}

fn ty_eq<'a>(ty1: InternedType<'a>, ty2: InternedType<'a>) -> bool {
    std::ptr::eq(ty1, ty2)
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
                        return Err(format!(
                            "destructured tuple has {st_len} elements\nwhile it's type has {ty_len} elements"
                        ));
                    }
                    zip_eq(st_elems, ty_elems)
                        .try_for_each(|(st, ty)| inner(st, ty, ctx, output))?;
                }

                (ArgStructure::Tuple(_), ty) => {
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

    fn try_map_ty_vars<E>(
        &'a self,
        f: &mut impl FnMut(Lvl) -> Result<&'a Self, E>,
        ctx: &impl TyArenaContext<'a>,
    ) -> Result<&'a Self, E> {
        let ty = match self {
            Type::TyAbs {
                name,
                bounds: TyBounds { upper, lower },
                result,
            } => Type::TyAbs {
                name,
                bounds: TyBounds {
                    upper: upper.map(|t| t.try_map_ty_vars(f, ctx)).transpose()?,
                    lower: lower.map(|t| t.try_map_ty_vars(f, ctx)).transpose()?,
                },
                result: result.try_map_ty_vars(f, ctx)?,
            },
            Type::TyVar(level) => return f(*level),
            Type::Arr { arg, result } => Type::Arr {
                arg: arg.try_map_ty_vars(f, ctx)?,
                result: result.try_map_ty_vars(f, ctx)?,
            },
            Type::Enum(variants) => Type::Enum(
                variants
                    .0
                    .iter()
                    .map(|(l, t)| t.try_map_ty_vars(f, ctx).map(|t| (*l, t)))
                    .try_collect()?,
            ),
            Type::Tuple(elems) => Type::Tuple(
                elems
                    .iter()
                    .map(|e| e.try_map_ty_vars(f, ctx))
                    .try_collect()?,
            ),
            Type::Bool | Type::Any | Type::Never => return Ok(self),
        };

        Ok(ctx.intern(ty))
    }

    fn map_ty_vars(
        &'a self,
        mut f: impl FnMut(Lvl) -> &'a Self,
        ctx: &impl TyArenaContext<'a>,
    ) -> &'a Self {
        let Ok(res) = self.try_map_ty_vars(&mut |l| Ok::<_, Infallible>(f(l)), ctx);
        res
    }

    fn substitute_ty_var(
        &'a self,
        depth: Lvl,
        ty: &'a Self,
        ctx: &impl TyArenaContext<'a>,
    ) -> &'a Self {
        self.map_ty_vars(
            |level| {
                if level == depth {
                    return ty;
                }
                let new_level = match level.shallower() {
                    // deeper than replaced but not equal (due to prev arm)
                    Some(shallower) if level.deeper_than(depth) => shallower,
                    // either:
                    // - shallowest so could not be strictly deeper
                    // - not deeper
                    None | Some(_) => level,
                };
                ctx.intern(Type::TyVar(new_level))
            },
            ctx,
        )
    }

    // TODO: maybe ensure type safety by Type::Concrete(ConcreteType::{Arr, Enum, ...})
    /// Get the minimal concrete supertype
    fn upper_concrete(&'a self, ctx: &Context<'a, '_>) -> Result<&'a Self, TypeCheckError> {
        match self {
            Type::TyVar(level) => ctx
                .get_ty_var_unwrap(*level)?
                .1
                .get_upper(ctx)
                .upper_concrete(ctx),
            Type::TyAbs { .. }
            | Type::Arr { .. }
            | Type::Enum(..)
            | Type::Tuple(..)
            | Type::Bool
            | Type::Any
            | Type::Never => Ok(self),
        }
    }

    /// `Some()` only if not `Type::Any`
    fn not_any(&'a self) -> Option<&'a Self> {
        match self {
            Type::Any => None,
            Type::TyAbs { .. }
            | Type::TyVar { .. }
            | Type::Arr { .. }
            | Type::Enum(..)
            | Type::Tuple(..)
            | Type::Bool
            | Type::Never => Some(self),
        }
    }

    /// `Some()` only if not `Type::Never`
    fn not_never(&'a self) -> Option<&'a Self> {
        match self {
            Type::Never => None,
            Type::TyAbs { .. }
            | Type::TyVar { .. }
            | Type::Arr { .. }
            | Type::Enum(..)
            | Type::Tuple(..)
            | Type::Bool
            | Type::Any => Some(self),
        }
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
