use itertools::{Itertools, zip_eq};

use crate::{
    common::{hashmap_intersection, hashmap_union, hashmap_union_with_key},
    typing::{
        InternedType, TyConfig, TyVar,
        effects::{Effect, EffectGroup},
        error::{ContextError, IllegalError, PlainContextError, TypeCheckResult},
        subtyping::expect_type,
        ty::{TyBounds, TyDisplay, Type},
        ty_eq,
    },
};

fn op_name(join: bool) -> &'static str {
    if join { "join" } else { "meet" }
}

pub(super) trait Mergeable<'a>: Sized {
    type Output;

    fn merge2<'inn>(
        mergee1: Self,
        mergee2: Self,
        join: bool,
        ctx: &ctx!(arena 'inn; ty_var),
    ) -> Result<Self::Output, ContextError<'static>>
    where
        'a: 'inn;

    fn merge<'inn>(
        mergees: impl IntoIterator<Item = Self>,
        join: bool,
        ctx: &ctx!(arena 'inn; ty_var),
    ) -> Result<Self::Output, ContextError<'static>>
    where
        'a: 'inn;
}

impl<'a> Mergeable<'a> for InternedType<'a> {
    type Output = Self;

    fn merge2<'inn>(
        ty1: InternedType<'a>,
        ty2: InternedType<'a>,
        join: bool,
        ctx: &ctx!(arena 'inn; ty_var),
    ) -> Result<InternedType<'a>, ContextError<'static>>
    where
        'a: 'inn,
    {
        let merge2 = Self::merge2;

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

        let op = op_name(join);

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
                    result: merge2(
                        res1,
                        res2,
                        join,
                        &ctx.push_ty_var(name, TyVar::Bounded(bounds)),
                    )?,
                }
            }
            (
                Type::RecAbs {
                    name: name1,
                    result: res1,
                },
                Type::RecAbs {
                    name: name2,
                    result: res2,
                },
            ) => {
                // we take the minimum arbitrarily,
                // it doesn't even have to match elsewhere but it should
                let name = std::cmp::min(name1, name2);
                Type::RecAbs {
                    name,
                    result: merge2(res1, res2, join, &ctx.push_ty_var(name, TyVar::Rec))?,
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
            (Type::TyObj(ty1), Type::TyObj(ty2)) => Type::TyObj(merge2(ty1, ty2, join, ctx)?),
            (
                Type::Arr {
                    arg: arg1,
                    effects: effects1,
                    result: res1,
                },
                Type::Arr {
                    arg: arg2,
                    effects: effects2,
                    result: res2,
                },
            ) => Type::Arr {
                arg: if ty_eq(arg1, arg2) {
                    arg1
                } else {
                    // func arg is contravariant so swap join/meet
                    merge2(arg1, arg2, !join, ctx)?
                },
                effects: Mergeable::merge2(effects1, effects2, join, ctx)?,
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
                | Type::RecAbs { .. }
                | Type::TyVar { .. }
                | Type::TyObj(_)
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
    fn merge<'inn>(
        types: impl IntoIterator<Item = Self>,
        join: bool,
        ctx: &ctx!(arena 'inn; ty_var),
    ) -> Result<Self, ContextError<'static>>
    where
        'a: 'inn,
    {
        let mut iter = types.into_iter();
        let Some(first) = iter.next() else {
            return Ok(ctx.intern(if join {
                Type::Never
            } else {
                // not really sure when this could ever occur but this would be the result
                Type::Any
            }));
        };
        iter.try_fold(first, |ty1, ty2| Self::merge2(ty1, ty2, join, ctx))
    }
}

impl<'a> Mergeable<'a> for &EffectGroup<'a> {
    type Output = EffectGroup<'a>;

    fn merge2<'inn>(
        e1: Self,
        e2: Self,
        join: bool,
        ctx: &ctx!(arena 'inn; ty_var),
    ) -> Result<Self::Output, ContextError<'static>>
    where
        'a: 'inn,
    {
        if join {
            Ok(EffectGroup {
                labelled: hashmap_union_with_key(
                    &e1.labelled.0,
                    &e2.labelled.0,
                    |_, e1| Ok(*e1),
                    |_, e2| Ok(*e2),
                    |label, e1, e2| {
                        Effect::merge2(*e1, *e2, join, ctx).wrap_error(|| {
                            PlainContextError::new(format!("for effects of label '{label}'"))
                        })
                    },
                )
                .map(|(l, e)| e.map(|e| (*l, e)))
                .try_collect()?,
                anonymous: hashmap_union(
                    &e1.anonymous.0,
                    &e2.anonymous.0,
                    |e1| Ok(*e1),
                    |e2| Ok(*e2),
                    |e1, e2| Effect::merge2(*e1, *e2, join, ctx),
                )
                .map(|(l, e)| e.map(|e| (*l, e)))
                .try_collect()?,
                exhaustive: e1.exhaustive && e2.exhaustive,
            })
        } else {
            todo!()
        }
    }

    fn merge<'inn>(
        effect_groups: impl IntoIterator<Item = Self>,
        join: bool,
        ctx: &ctx!(arena 'inn; ty_var),
    ) -> Result<Self::Output, ContextError<'static>>
    where
        'a: 'inn,
    {
        let mut iter = effect_groups.into_iter();
        let Some(first) = iter.next() else {
            if join {
                return Ok(EffectGroup::default());
            } else {
                // TODO: check
                // I don't believe this should ever be called
                Err(PlainContextError::new("cannot meet 0 effect groups"))?
            }
        };
        iter.try_fold(first.clone(), |e1, e2| {
            Mergeable::merge2(&e1, e2, join, ctx)
        })
    }
}

impl<'a> Mergeable<'a> for Effect<'a> {
    type Output = Self;

    fn merge2<'inn>(
        e1: Self,
        e2: Self,
        join: bool,
        ctx: &ctx!(arena 'inn; ty_var),
    ) -> Result<Self, ContextError<'static>>
    where
        'a: 'inn,
    {
        let op = op_name(join);

        let effect = match (e1, e2) {
            (
                Effect::Def {
                    name: name1,
                    arg: arg1,
                    result: result1,
                },
                Effect::Def {
                    name: name2,
                    arg: arg2,
                    result: result2,
                },
            ) => {
                if name1 != name2 {
                    Err(PlainContextError::new(format!(
                        "cannot {op} incompatible effects: '{name1}' with '{name2}'"
                    )))?
                }

                Effect::Def {
                    name: name1,
                    arg: InternedType::merge2(arg1, arg2, join, ctx)?,
                    result: InternedType::merge2(result1, result2, !join, ctx)?,
                }
            }
        };

        Ok(effect)
    }

    fn merge<'inn>(
        effects: impl IntoIterator<Item = Self>,
        join: bool,
        ctx: &ctx!(arena 'inn; ty_var),
    ) -> Result<Self, ContextError<'static>>
    where
        'a: 'inn,
    {
        let mut iter = effects.into_iter();
        let Some(first) = iter.next() else {
            // TODO: check
            Err(PlainContextError::new(format!(
                "cannot {} 0 effects",
                op_name(join)
            )))?
        };
        iter.try_fold(first, |e1, e2| Self::merge2(e1, e2, join, ctx))
    }
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
pub(super) fn join<'a: 'inn, 'inn, T: Mergeable<'a>>(
    joinees: impl IntoIterator<Item = T>,
    ctx: &ctx!(arena 'inn; ty_var),
) -> Result<T::Output, ContextError<'static>> {
    T::merge(joinees, true, ctx)
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
pub(super) fn meet<'a: 'inn, 'inn, T: Mergeable<'a>>(
    meetees: impl IntoIterator<Item = T>,
    ctx: &ctx!(arena 'inn; ty_var),
) -> Result<T::Output, ContextError<'static>> {
    T::merge(meetees, false, ctx)
}
