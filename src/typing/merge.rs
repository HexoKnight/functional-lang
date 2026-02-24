use itertools::{Itertools, zip_eq};

use crate::{
    common::{hashmap_intersection, hashmap_union},
    typing::{
        InternedType, TyConfig,
        context::{ContextInner, TyArenaContext, TyVarContext},
        error::{ContextError, IllegalError, PlainContextError, TypeCheckResult},
        subtyping::expect_type,
        ty::{TyBounds, TyDisplay, Type},
        ty_eq,
    },
};

// unfortunately no trait aliases
macro_rules! ctx {
    () => {
         impl TyArenaContext<'a, Inner = &'inn ContextInner<'a>>
            + TyVarContext<'a, TyVar = TyBounds<'a>>
    };
}

/// `join` specifies whether joining or meeting types.
///
/// Currently folds over the types, merging them one by one.
/// This isn't great for type interning among other things.
/// Preferably, we would match on all elements of the iterator at once somehow and then merge all
/// inner types recursively, but that would be a bit more difficult and irritating to implement
/// properly.
///
/// # Errors
/// see docs for [`join`] and [`meet`]
fn merge<'a: 'inn, 'inn>(
    types: impl IntoIterator<Item = InternedType<'a>>,
    join: bool,
    ctx: &ctx!(),
) -> Result<InternedType<'a>, ContextError<'static>> {
    fn merge2<'a: 'inn, 'inn>(
        ty1: InternedType<'a>,
        ty2: InternedType<'a>,
        join: bool,
        ctx: &ctx!(),
    ) -> Result<InternedType<'a>, ContextError<'static>> {
        // these checks are meant as optimisations, and shouldn't be necessary for correctness
        if ty_eq(ty1, ty2) {
            return Ok(ty1);
        }

        fn ignore_noninternal_err<T>(
            res: Result<T, ContextError>,
        ) -> Result<Option<T>, ContextError> {
            match res {
                Ok(t) => Ok(Some(t)),
                Err(error) => {
                    if error.is_internal() {
                        Err(error)
                    } else {
                        Ok(None)
                    }
                }
            }
        }

        if let Some(ty) = ignore_noninternal_err(expect_type(
            ty2,
            ty1,
            !join,
            TyConfig::ty_inference_disabled(),
            ctx,
        ))? {
            return Ok(ty);
        }
        if let Some(ty) = ignore_noninternal_err(expect_type(
            ty1,
            ty2,
            !join,
            TyConfig::ty_inference_disabled(),
            ctx,
        ))? {
            return Ok(ty);
        }

        let op = if join { "join" } else { "meet" };

        let ty = match (ty1, ty2) {
            (
                Type::TyAbs {
                    name: name1,
                    bounds:
                        TyBounds {
                            upper: upper1,
                            lower: lower1,
                        },
                    result: res1,
                },
                Type::TyAbs {
                    name: name2,
                    bounds:
                        TyBounds {
                            upper: upper2,
                            lower: lower2,
                        },
                    result: res2,
                },
            ) => {
                // we take the minimum arbitrarily,
                // it doesn't even have to match elsewhere but it should
                let name = std::cmp::min(name1, name2);
                let bounds = TyBounds {
                    upper: match (upper1, upper2) {
                        (Some(upper1), Some(upper2)) => Some(merge2(upper1, upper2, join, ctx)?),
                        (Some(upper), None) | (None, Some(upper)) => Some(*upper),
                        (None, None) => None,
                    },
                    lower: match (lower1, lower2) {
                        (Some(lower1), Some(lower2)) => Some(merge2(lower1, lower2, join, ctx)?),
                        (Some(lower), None) | (None, Some(lower)) => Some(*lower),
                        (None, None) => None,
                    },
                };
                Type::TyAbs {
                    name,
                    bounds,
                    result: merge2(res1, res2, join, &ctx.push_ty_var(name, bounds))?,
                }
            }
            (Type::TyVar(level1), Type::TyVar(level2)) => {
                return if level1 == level2 {
                    Ok(ty1)
                } else {
                    Err(PlainContextError::new(format!(
                        "cannot {op} type variables:\n\
                        variable 1: {ty1}\n\
                        variable 2: {ty2}",
                        ty1 = ty1.display(ctx)?,
                        ty2 = ty2.display(ctx)?
                    )))?
                };
            }
            (
                Type::Arr {
                    arg: arg1,
                    result: res1,
                },
                Type::Arr {
                    arg: arg2,
                    result: res2,
                },
            ) => Type::Arr {
                arg: if ty_eq(arg1, arg2) {
                    arg1
                } else {
                    // func arg is contravariant so swap join/meet
                    merge2(arg1, arg2, !join, ctx)?
                },
                result: merge2(res1, res2, join, ctx)?,
            },
            (Type::Enum(variants1), Type::Enum(variants2)) => Type::Enum(if join {
                hashmap_union(
                    &variants1.0,
                    &variants2.0,
                    |ty1| Ok(*ty1),
                    |ty2| Ok(*ty2),
                    |ty1, ty2| merge2(ty1, ty2, join, ctx),
                )
                .map(|(l, r)| r.map(|ty| (*l, ty)))
                .try_collect()?
            } else {
                hashmap_intersection(&variants1.0, &variants2.0, |ty1, ty2| {
                    merge2(ty1, ty2, join, ctx)
                })
                .map(|(l, r)| r.map(|ty| (*l, ty)))
                .try_collect()?
            }),
            (Type::Record(fields1), Type::Record(fields2)) => Type::Record(if join {
                hashmap_intersection(&fields1.0, &fields2.0, |ty1, ty2| {
                    merge2(ty1, ty2, join, ctx)
                })
                .map(|(l, r)| r.map(|ty| (*l, ty)))
                .try_collect()?
            } else {
                hashmap_union(
                    &fields1.0,
                    &fields2.0,
                    |ty1| Ok(*ty1),
                    |ty2| Ok(*ty2),
                    |ty1, ty2| merge2(ty1, ty2, join, ctx),
                )
                .map(|(l, r)| r.map(|ty| (*l, ty)))
                .try_collect()?
            }),
            (Type::Tuple(elems1), Type::Tuple(elems2)) => {
                let len1 = elems1.len();
                let len2 = elems2.len();
                if len1 == len2 {
                    Type::Tuple(
                        zip_eq(elems1, elems2)
                            .map(|(ty1, ty2)| merge2(ty1, ty2, join, ctx))
                            .try_collect()?,
                    )
                } else if join {
                    Err(PlainContextError::new(format!(
                        "cannot {op} tuples with different lengths:\n\
                        tuple 1: {len1} elements: {ty1}\n\
                        tuple 2: {len2} elements: {ty2}",
                        ty1 = ty1.display(ctx)?,
                        ty2 = ty2.display(ctx)?
                    )))?
                } else {
                    Type::Never
                }
            }
            (Type::Unknown, _) | (_, Type::Unknown) => Err(IllegalError::new(
                "unknown type should never be merged",
                None,
            ))?,
            (Type::Bool, Type::Bool) => Type::Bool,
            (ty_super @ Type::Any, ty_sub)
            | (ty_sub, ty_super @ Type::Any)
            | (ty_sub @ Type::Never, ty_super)
            | (ty_super, ty_sub @ Type::Never) => return Ok(if join { ty_super } else { ty_sub }),
            // not using _ to avoid catching more cases than intended
            (
                Type::TyAbs { .. }
                | Type::TyVar { .. }
                | Type::Arr { .. }
                | Type::Enum(..)
                | Type::Record(..)
                | Type::Tuple(..)
                | Type::Bool,
                _,
            ) => Err(PlainContextError::new(format!(
                "cannot {op} incompatible types:\n\
                type 1: {ty1}\n\
                type 2: {ty2}\n",
                ty1 = ty1.display(ctx)?,
                ty2 = ty2.display(ctx)?
            )))?,
        };

        let ty = ctx.intern(ty);

        #[cfg(debug_assertions)]
        if join {
            [ty1, ty2]
                .into_iter()
                .try_for_each(|ty_input| {
                    expect_type(ty, ty_input, true, TyConfig::ty_inference_disabled(), ctx)
                        .map(|_| ())
                })
                .try_wrap_error(|| {
                    Ok(IllegalError::new(
                        format!(
                            "join result:               {}\n\
                            is not supertype of input: {}",
                            ty.display(ctx)?,
                            ty1.display(ctx)?,
                        ),
                        None,
                    ))
                })?;
        } else {
            [ty1, ty2]
                .into_iter()
                .try_for_each(|ty_input| {
                    expect_type(ty, ty_input, false, TyConfig::ty_inference_disabled(), ctx)
                        .map(|_| ())
                })
                .try_wrap_error(|| {
                    Ok(IllegalError::new(
                        format!(
                            "meet result:             {}\n\
                            is not subtype of input: {}",
                            ty.display(ctx)?,
                            ty1.display(ctx)?,
                        ),
                        None,
                    ))
                })?;
        }

        Ok(ty)
    }
    let mut iter = types.into_iter();
    let Some(first) = iter.next() else {
        return Ok(ctx.intern(if join {
            Type::Never
        } else {
            // not really sure when this could ever occur but this would be the result
            Type::Any
        }));
    };
    iter.try_fold(first, |ty1, ty2| merge2(ty1, ty2, join, ctx))
}

/// Join multiple types to produce the 'minimal' supertype.
/// Intuitively, it's the union of the input types.
///
/// Specifically, should be the type that is:
/// - a supertype of every input type
/// - a subtype of all other supertypes of every input type.
///
/// # Errors
/// When joining types with no common supertype.
///
/// The top/any type is the supertype of all types so it could be returned instead of an error
/// but we choose an error in cases where the user probably wouldn't want to lose all type
/// information (they can manually coerce their types to any beforehand if they so wish).
pub(super) fn join<'a: 'inn, 'inn>(
    types: impl IntoIterator<Item = InternedType<'a>>,
    ctx: &ctx!(),
) -> Result<InternedType<'a>, ContextError<'static>> {
    merge(types, true, ctx)
}

/// Meet multiple types to produce the 'maximal' subtype.
/// Intuitively, it's the intersection of the input types.
///
/// Specifically, should be the type that is:
/// - a subtype of every input type
/// - a supertype of all other subtypes of every input type.
///
/// # Errors
/// When meeting types with no common subtype.
///
/// The bottom/never type is the subtype of all types so it could be returned instead of an error
/// but we choose an error in cases where the user probably wouldn't want to lose all type
/// information (they can manually coerce their types to never beforehand if they so wish).
#[allow(dead_code)]
pub(super) fn meet<'a: 'inn, 'inn>(
    types: impl IntoIterator<Item = InternedType<'a>>,
    ctx: &ctx!(),
) -> Result<InternedType<'a>, ContextError<'static>> {
    merge(types, false, ctx)
}
