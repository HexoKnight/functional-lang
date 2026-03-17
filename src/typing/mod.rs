use std::iter::{Sum, chain};

use itertools::{Itertools, zip_eq};

use crate::{
    common::WithInfo,
    reprs::common::{
        ArgStructure, ArgTermStructure, ArgTypeStructure, Lvl, RawArgStructure,
        RawArgTermStructure, Span,
    },
    typing::{
        context::TyArenaContext,
        effects::{EffId, Effect, EffectGroup},
        error::{IllegalError, SpannedError, TypeCheckResult},
        map_vars::MapVars,
        subtyping::expect_type,
        ty::{TyBounds, TyDisplay, Type},
    },
};

mod checking;
#[macro_use]
mod context;
mod effects;
mod error;
mod eval;
mod map_vars;
mod merge;
mod subtyping;
mod ty;

type InternedType<'a> = &'a Type<'a>;

pub use self::checking::type_check;
pub use self::error::TypeCheckError;

#[derive(Copy, Clone)]
struct TyConfig {
    /// whether inferring type arguments is allowed
    infer_ty_args: bool,
    /// whether failing to infer types is allowed (ie. will be caught)
    ty_infer_fail: bool,
}
impl TyConfig {
    fn infer_ty_args(mut self, infer_ty_args: bool) -> Self {
        self.infer_ty_args = infer_ty_args;
        self
    }

    fn ty_infer_fail(mut self, ty_infer_fail: bool) -> Self {
        self.ty_infer_fail = ty_infer_fail;
        self
    }

    fn ty_inference_disabled() -> Self {
        Self {
            infer_ty_args: false,
            ty_infer_fail: false,
        }
    }
}

#[derive(Copy, Clone, Eq, PartialEq)]
pub(super) struct TyEffLvl {
    ty: Lvl,
    eff: Lvl,
}

impl TyEffLvl {
    pub fn new(ty: Lvl, eff: Lvl) -> Self {
        Self { ty, eff }
    }

    pub fn map_ty(self, mut f: impl FnMut(Lvl) -> Lvl) -> Self {
        Self {
            ty: f(self.ty),
            ..self
        }
    }
    pub fn map_eff(self, mut f: impl FnMut(Lvl) -> Lvl) -> Self {
        Self {
            eff: f(self.eff),
            ..self
        }
    }
}

/// anytime this is accessed, we must make sure any
/// referenced types are valid in the current context
#[derive(Copy, Clone)]
enum TyVar<'a> {
    Type { ty: InternedType<'a>, eff_lvl: Lvl },
    Bounded { bounds: TyBounds<'a>, eff_lvl: Lvl },
    Rec,
}

/// anytime this is accessed, we must make sure any
/// referenced types are valid in the current context
#[derive(Copy, Clone)]
enum EffVar<'a> {
    Effect { effect: Effect<'a>, ty_lvl: Lvl },
    Unbound,
}

impl<'a> EffVar<'a> {
    fn get_id(&self, level: Lvl) -> EffId<'a> {
        match self {
            EffVar::Effect { effect, ty_lvl: _ } => effect.get_id(),
            EffVar::Unbound => EffId::Unbound(level),
        }
    }
}

#[derive(Copy, Clone, Debug)]
enum Variance {
    Constant,
    Covariant,
    Contravariant,
    Invariant,
}

impl Variance {
    fn invert(self) -> Self {
        match self {
            Self::Constant | Self::Invariant => self,
            Self::Covariant => Self::Contravariant,
            Self::Contravariant => Self::Covariant,
        }
    }

    fn add(self, other: Self) -> Self {
        match (self, other) {
            (Self::Constant, other) | (other, Self::Constant) => other,
            (Self::Covariant, Self::Covariant) => Self::Covariant,
            (Self::Contravariant, Self::Contravariant) => Self::Contravariant,
            (Self::Covariant, Self::Contravariant)
            | (Self::Contravariant, Self::Covariant)
            | (Self::Invariant, _)
            | (_, Self::Invariant) => Self::Invariant,
        }
    }
}
impl Sum<Self> for Variance {
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(Self::Constant, Self::add)
    }
}

impl<'a> Type<'a> {
    fn get_variance_of(
        &self,
        ty_var_level: Lvl,
        ctx: &ctx!(ty_var; eff_var),
    ) -> Result<Variance, IllegalError<'static>> {
        fn get_variance_in_effect<'a>(
            effect: &Effect<'a>,
            ty_var_level: Lvl,
            ctx: &ctx!(ty_var; eff_var),
        ) -> Result<Variance, IllegalError<'static>> {
            match effect {
                Effect::Def {
                    name: _,
                    arg,
                    result,
                } => [
                    arg.get_variance_of(ty_var_level, ctx),
                    result
                        .get_variance_of(ty_var_level, ctx)
                        .map(Variance::invert),
                ]
                .into_iter()
                .sum(),
                Effect::Var(level, _) => Ok(
                    if let (_, EffVar::Effect { effect, ty_lvl }) =
                        ctx.get_eff_var_unwrap(*level)?
                        && ty_lvl.deeper_than(ty_var_level)
                    {
                        get_variance_in_effect(&effect, ty_var_level, ctx)?
                    } else {
                        Variance::Constant
                    },
                ),
            }
        }

        match self {
            Type::Unknown => Err(IllegalError::new(
                "tried to get variance of unknown type",
                None,
            )),
            Type::TyAbs {
                name,
                bounds: bounds @ TyBounds { upper, lower },
                result,
            } => [
                upper
                    .map(|t| t.get_variance_of(ty_var_level, ctx).map(Variance::invert))
                    .unwrap_or(Ok(Variance::Constant)),
                lower
                    .map(|t| t.get_variance_of(ty_var_level, ctx))
                    .unwrap_or(Ok(Variance::Constant)),
                result.get_variance_of(
                    ty_var_level,
                    &ctx.push_ty_var(
                        name,
                        TyVar::Bounded {
                            bounds: *bounds,
                            eff_lvl: ctx.next_eff_var_level(),
                        },
                    ),
                ),
            ]
            .into_iter()
            .sum(),
            Type::RecAbs { name, result } => {
                result.get_variance_of(ty_var_level, &ctx.push_ty_var(name, TyVar::Rec))
            }
            Type::EffAbs { name, result } => {
                result.get_variance_of(ty_var_level, &ctx.push_eff_var(name.0, EffVar::Unbound))
            }
            Type::TyVar(level) => {
                if *level == ty_var_level {
                    Ok(Variance::Covariant)
                } else if level.deeper_than(ty_var_level)
                    && let (_, TyVar::Type { ty, eff_lvl: _ }) = ctx.get_ty_var_unwrap(*level)?
                {
                    ty.get_variance_of(ty_var_level, ctx)
                } else {
                    Ok(Variance::Constant)
                }
            }
            Type::TyObj(ty) => ty.get_variance_of(ty_var_level, ctx),
            Type::Arr {
                arg,
                effects,
                result,
            } => [
                arg.get_variance_of(ty_var_level, ctx).map(Variance::invert),
                effects
                    .iter_sorted()
                    .map(|(_, effect)| get_variance_in_effect(effect, ty_var_level, ctx))
                    .sum(),
                result.get_variance_of(ty_var_level, ctx),
            ]
            .into_iter()
            .sum(),
            Type::Enum(variants) => variants
                .0
                .values()
                .map(|t| t.get_variance_of(ty_var_level, ctx))
                .sum(),
            Type::Record(fields) => fields
                .0
                .values()
                .map(|t| t.get_variance_of(ty_var_level, ctx))
                .sum(),
            Type::Tuple(elems) => elems
                .iter()
                .map(|t| t.get_variance_of(ty_var_level, ctx))
                .sum(),
            Type::Bool | Type::Any | Type::Never => Ok(Variance::Constant),
        }
    }
}

fn ty_eq<'a>(ty1: InternedType<'a>, ty2: InternedType<'a>) -> bool {
    std::ptr::eq(ty1, ty2)
}

impl<'a> Type<'a> {
    fn arr(arg: &'a Self, result: &'a Self) -> Self {
        Self::Arr {
            arg,
            effects: EffectGroup::new_non_exhaustive(),
            result,
        }
    }

    fn destructure<'i, 's>(
        &'a self,
        arg_structure: &'s ArgStructure<'i>,
        ctx: &ctx!(arena; ty_var; eff_var),
    ) -> Result<
        (
            ArgTermStructure<'i>,
            Box<[(&'i str, &'a Self)]>,
            Box<[(&'i str, &'a Self)]>,
        ),
        TypeCheckError<'i>,
    > {
        type TyVec<'i, 'a> = Vec<(&'i str, InternedType<'a>)>;

        fn destructure_inner<'i, 'a, 's, A1, A2>(
            span: Span<'i>,
            arg_structure: &'s RawArgStructure<'i, A1>,
            ty: InternedType<'a>,
            tys: &mut TyVec<'i, 'a>,
            mut inner: impl FnMut(
                &'s A1,
                InternedType<'a>,
                &mut TyVec<'i, 'a>,
            ) -> Result<WithInfo<Span<'i>, A2>, TypeCheckError<'i>>,
            wrap: impl Fn(RawArgStructure<'i, WithInfo<Span<'i>, A2>>) -> A2,
            ctx: &ctx!(arena; ty_var; eff_var),
        ) -> Result<A2, TypeCheckError<'i>> {
            let arg_structure = match arg_structure {
                RawArgStructure::Record(st_fields) => {
                    let Type::Record(ty_fields) = ty else {
                        Err(SpannedError::new(
                            "type mismatch: record-destructure non-record",
                            format!(
                                "cannot record-destructure value of type {ty}",
                                ty = ty.display(ctx)?
                            ),
                            "",
                            span,
                        ))?
                    };

                    RawArgStructure::Record(
                        st_fields
                            .iter()
                            .map(|(l, st)| {
                                if let Some(ty) = ty_fields.0.get(l) {
                                    inner(st, ty, tys).map(|st| (*l, st))
                                } else {
                                    Err(SpannedError::new(
                                        "type mismatch: record-destructure missing field",
                                        format!(
                                            "destructured record has field with label '{l}'\n\
                                            while it's missing from it's type"
                                        ),
                                        "",
                                        span,
                                    ))?
                                }
                            })
                            .try_collect()?,
                    )
                }

                RawArgStructure::Tuple(st_elems) => {
                    let Type::Tuple(ty_elems) = ty else {
                        Err(SpannedError::new(
                            "type mismatch: tuple-destructure non-tuple",
                            format!(
                                "cannot tuple-destructure value of type {ty}",
                                ty = ty.display(ctx)?
                            ),
                            "",
                            span,
                        ))?
                    };

                    let st_len = st_elems.len();
                    let ty_len = ty_elems.len();
                    if st_len != ty_len {
                        Err(SpannedError::new(
                            "type mismatch: tuple-destructure with wrong number of elements",
                            format!(
                                "destructured tuple has {st_len} elements\n\
                                while it's type has {ty_len} elements"
                            ),
                            "",
                            span,
                        ))?;
                    }
                    RawArgStructure::Tuple(
                        zip_eq(st_elems, ty_elems)
                            .map(|(st, ty)| inner(st, ty, tys))
                            .try_collect()?,
                    )
                }

                RawArgStructure::Var => {
                    tys.push((span.text(), ty));
                    RawArgStructure::Var
                }
            };
            Ok(wrap(arg_structure))
        }

        fn destructure_term_inner<'i, 'a, 's>(
            arg_structure: &'s ArgStructure<'i>,
            ty: InternedType<'a>,
            var_tys: &mut TyVec<'i, 'a>,
            ty_vars: &mut TyVec<'i, 'a>,
            ctx: &ctx!(arena; ty_var; eff_var),
        ) -> Result<ArgTermStructure<'i>, TypeCheckError<'i>> {
            let WithInfo(span, arg_structure) = arg_structure;

            let arg_structure = match arg_structure {
                RawArgTermStructure::Term(arg_structure) => destructure_inner(
                    *span,
                    arg_structure,
                    ty,
                    var_tys,
                    |arg_structure, ty, var_tys| {
                        destructure_term_inner(arg_structure, ty, var_tys, ty_vars, ctx)
                    },
                    RawArgTermStructure::Term,
                    ctx,
                )?,
                RawArgTermStructure::Type(arg_structure) => {
                    let Type::TyObj(ty) = ty else {
                        Err(SpannedError::new(
                            "type mismatch: type-destructure non-type",
                            format!(
                                "cannot type-destructure value of type {ty}",
                                ty = ty.display(ctx)?
                            ),
                            "",
                            *span,
                        ))?
                    };
                    RawArgTermStructure::Type(destructure_type_inner(
                        arg_structure,
                        ty,
                        ty_vars,
                        ctx,
                    )?)
                }
            };

            Ok(WithInfo(*span, arg_structure))
        }

        fn destructure_type_inner<'i, 'a, 's>(
            arg_structure: &'s ArgTypeStructure<'i>,
            ty: InternedType<'a>,
            tys: &mut TyVec<'i, 'a>,
            ctx: &ctx!(arena; ty_var; eff_var),
        ) -> Result<(), TypeCheckError<'i>> {
            let WithInfo(span, arg_structure) = arg_structure;

            destructure_inner(
                *span,
                &arg_structure.0,
                ty,
                tys,
                |arg_structure, ty, tys| {
                    Ok(WithInfo(
                        *span,
                        destructure_type_inner(arg_structure, ty, tys, ctx)?,
                    ))
                },
                |_| (),
                ctx,
            )
        }

        let mut var_tys = Vec::new();
        let mut ty_vars = Vec::new();
        let arg_structure =
            destructure_term_inner(arg_structure, self, &mut var_tys, &mut ty_vars, ctx)?;
        Ok((
            arg_structure,
            var_tys.into_boxed_slice(),
            ty_vars.into_boxed_slice(),
        ))
    }

    fn apply_ty_arg<'i, 'inn>(
        &'a self,
        self_span: Span<'i>,
        arg: &'a Self,
        arg_span: Span<'i>,
        ty_config: TyConfig,
        ctx: &ctx!(arena 'inn; ty_var; eff_var),
    ) -> Result<&'a Self, TypeCheckError<'i>>
    where
        'a: 'inn,
    {
        let Type::TyAbs {
            name: _,
            bounds,
            result,
        } = self.upper_concrete(ctx)?
        else {
            Err(SpannedError::new(
                "type mismatch",
                format!(
                    "cannot apply a type argument to type: `{}`",
                    self.display(ctx)?
                ),
                "",
                self_span,
            ))?
        };
        // bounds can't be unknown but anyway
        if let Some(upper) = bounds.get_upper(ctx).known_not_any() {
            expect_type(upper, arg, true, ty_config.infer_ty_args(false), ctx).try_wrap_error(
                || {
                    Ok(SpannedError::new(
                        "type arg out of bounds",
                        format!(
                            "type must be subtype of upper bound: `{}`",
                            upper.display(ctx)?
                        ),
                        "unsatisfied type arg upper bound",
                        arg_span,
                    ))
                },
            )?;
        }
        if let Some(lower) = bounds.get_lower(ctx).known_not_never() {
            expect_type(lower, arg, false, ty_config.infer_ty_args(false), ctx).try_wrap_error(
                || {
                    Ok(SpannedError::new(
                        "type arg out of bounds",
                        format!(
                            "type must be supertype of lower bound: `{}`",
                            lower.display(ctx)?
                        ),
                        "unsatisfied type arg lower bound",
                        arg_span,
                    ))
                },
            )?;
        }
        let ty = result.substitute_ty_var(ctx.next_ty_eff_level(), arg, ctx);
        Ok(ty)
    }

    fn apply_eff_arg<'i, 'inn>(
        &'a self,
        self_span: Span<'i>,
        effects: &EffectGroup<'a>,
        ctx: &ctx!(arena 'inn; ty_var; eff_var),
    ) -> Result<&'a Self, TypeCheckError<'i>>
    where
        'a: 'inn,
    {
        let Type::EffAbs { name: _, result } = self.upper_concrete(ctx)? else {
            Err(SpannedError::new(
                "type mismatch",
                format!(
                    "cannot apply an effect argument to type: `{}`",
                    self.display(ctx)?
                ),
                "",
                self_span,
            ))?
        };
        let ty = result.substitute_eff_var(
            ctx.next_ty_eff_level(),
            ctx.next_ty_eff_level(),
            effects,
            ctx,
        );
        Ok(ty)
    }

    fn substitute_ty_var(
        &'a self,
        prev_ty_eff_lvl: TyEffLvl,
        ty: &'a Self,
        ctx: &impl TyArenaContext<'a>,
    ) -> &'a Self {
        self.map_vars(
            |ty_level, ty_eff_lvl| {
                if ty_level == prev_ty_eff_lvl.ty {
                    return ty.deepen(prev_ty_eff_lvl, ty_eff_lvl, ctx);
                }
                let new_level = match ty_level.shallower() {
                    // deeper than replaced but not equal (due to prev arm)
                    Some(shallower) if ty_level.deeper_than(prev_ty_eff_lvl.ty) => shallower,
                    // either:
                    // - shallowest so could not be strictly deeper
                    // - not deeper
                    None | Some(_) => ty_level,
                };
                ctx.intern(Type::TyVar(new_level))
            },
            |eff_level, eff_kind, _| Effect::Var(eff_level, eff_kind),
            prev_ty_eff_lvl,
            ctx,
        )
    }
    /// substitutes all `ty_var`s between `ty_eff_lvl.ty` (inclusive) and `ty_eff_lvl.ty + tys.len()` (exclusive)
    fn substitute_ty_vars(
        &'a self,
        ty_eff_lvl: TyEffLvl,
        tys: &[&'a Self],
        ctx: &impl TyArenaContext<'a>,
    ) -> &'a Self {
        self.map_vars(
            |ty_level, new_ty_eff_lvl| {
                let Some(deeper) = ty_level.get_deeper_than(ty_eff_lvl.ty) else {
                    // not deeper so no translation necessary
                    return ctx.intern(Type::TyVar(ty_level));
                };
                let ty = match deeper.get_or_beyond(tys) {
                    Ok(ty) => ty,
                    Err(beyond) => {
                        // beyond the substituted vars so we translate down
                        return ctx.intern(Type::TyVar(ty_eff_lvl.ty.deeper_by(beyond)));
                    }
                };
                ty.deepen(ty_eff_lvl, new_ty_eff_lvl, ctx)
            },
            |eff_level, eff_kind, _| Effect::Var(eff_level, eff_kind),
            ty_eff_lvl,
            ctx,
        )
    }

    fn substitute_eff_var(
        &'a self,
        prev_ty_eff_lvl: TyEffLvl,
        new_ty_eff_lvl: TyEffLvl,
        effects: &EffectGroup<'a>,
        ctx: &impl TyArenaContext<'a>,
    ) -> &'a Self {
        let ty = match self {
            Type::TyAbs {
                name,
                bounds: TyBounds { upper, lower },
                result,
            } => Type::TyAbs {
                name,
                bounds: TyBounds {
                    upper: upper.map(|t| {
                        t.substitute_eff_var(prev_ty_eff_lvl, new_ty_eff_lvl, effects, ctx)
                    }),
                    lower: lower.map(|t| {
                        t.substitute_eff_var(prev_ty_eff_lvl, new_ty_eff_lvl, effects, ctx)
                    }),
                },
                result: result.substitute_eff_var(
                    prev_ty_eff_lvl,
                    new_ty_eff_lvl.map_ty(Lvl::deeper),
                    effects,
                    ctx,
                ),
            },
            Type::RecAbs { name, result } => Type::RecAbs {
                name,
                result: result.substitute_eff_var(
                    prev_ty_eff_lvl,
                    new_ty_eff_lvl.map_ty(Lvl::deeper),
                    effects,
                    ctx,
                ),
            },
            Type::EffAbs { name, result } => Type::EffAbs {
                name: *name,
                result: result.substitute_eff_var(
                    prev_ty_eff_lvl,
                    new_ty_eff_lvl.map_eff(Lvl::deeper),
                    effects,
                    ctx,
                ),
            },
            Type::TyVar(_) => return self,
            Type::TyObj(ty) => {
                Type::TyObj(ty.substitute_eff_var(prev_ty_eff_lvl, new_ty_eff_lvl, effects, ctx))
            }
            Type::Arr {
                arg,
                effects: arr_effects,
                result,
            } => Type::Arr {
                arg: arg.substitute_eff_var(prev_ty_eff_lvl, new_ty_eff_lvl, effects, ctx),
                effects: {
                    if arr_effects
                        .get_anonymous(EffId::Unbound(prev_ty_eff_lvl.eff))
                        .is_some()
                    {
                        chain(
                            effects
                                .iter_unsorted()
                                .map(|(l, e)| (l, e.deepen(prev_ty_eff_lvl, new_ty_eff_lvl, ctx))),
                            arr_effects.iter_unsorted().filter_map(|(l, effect)| {
                                let effect = match effect {
                                    Effect::Def { name, arg, result } => Effect::Def {
                                        name: *name,
                                        arg: arg.substitute_eff_var(
                                            prev_ty_eff_lvl,
                                            new_ty_eff_lvl,
                                            effects,
                                            ctx,
                                        ),
                                        result: result.substitute_eff_var(
                                            prev_ty_eff_lvl,
                                            new_ty_eff_lvl,
                                            effects,
                                            ctx,
                                        ),
                                    },
                                    Effect::Var(lvl, _) => {
                                        if *lvl == prev_ty_eff_lvl.eff {
                                            return None;
                                        } else {
                                            *effect
                                        }
                                    }
                                };
                                Some((l, effect))
                            }),
                        )
                        .collect()
                    } else {
                        arr_effects.clone()
                    }
                },
                result: result.substitute_eff_var(prev_ty_eff_lvl, new_ty_eff_lvl, effects, ctx),
            },
            Type::Enum(variants) => Type::Enum(
                variants
                    .0
                    .iter()
                    .map(|(l, t)| {
                        (
                            *l,
                            t.substitute_eff_var(prev_ty_eff_lvl, new_ty_eff_lvl, effects, ctx),
                        )
                    })
                    .collect(),
            ),
            Type::Record(fields) => Type::Record(
                fields
                    .0
                    .iter()
                    .map(|(l, t)| {
                        (
                            *l,
                            t.substitute_eff_var(prev_ty_eff_lvl, new_ty_eff_lvl, effects, ctx),
                        )
                    })
                    .collect(),
            ),
            Type::Tuple(elems) => Type::Tuple(
                elems
                    .iter()
                    .map(|e| e.substitute_eff_var(prev_ty_eff_lvl, new_ty_eff_lvl, effects, ctx))
                    .collect(),
            ),
            Type::Bool | Type::Any | Type::Never | Type::Unknown => return self,
        };

        ctx.intern(ty)
    }

    // TODO: maybe ensure type safety by Type::Concrete(ConcreteType::{Arr, Enum, ...})
    /// Get the minimal concrete supertype
    fn upper_concrete(
        &'a self,
        ctx: &ctx!(arena; ty_var; eff_var),
    ) -> Result<&'a Self, IllegalError<'static>> {
        match self {
            Type::TyVar(level) => {
                let (_, ty_var) = ctx.get_ty_var_unwrap(*level)?;
                match ty_var {
                    TyVar::Type { ty, eff_lvl } => {
                        Ok(ty.deepen(TyEffLvl::new(*level, eff_lvl), ctx.next_ty_eff_level(), ctx))
                    }
                    TyVar::Bounded { bounds, eff_lvl } => bounds
                        .get_upper(ctx)
                        .deepen(TyEffLvl::new(*level, eff_lvl), ctx.next_ty_eff_level(), ctx)
                        .upper_concrete(ctx),
                    // we have a isorecursive view of recursive types so this is concrete
                    TyVar::Rec => Ok(self),
                }
            }
            Type::TyAbs { .. }
            | Type::RecAbs { .. }
            | Type::EffAbs { .. }
            | Type::TyObj(_)
            | Type::Arr { .. }
            | Type::Enum(..)
            | Type::Record(..)
            | Type::Tuple(..)
            | Type::Bool
            | Type::Any
            | Type::Never
            | Type::Unknown => Ok(self),
        }
    }

    /// `Some()` only if not `Type::Unknown` or `Type::Any`
    fn known_not_any(&'a self) -> Option<&'a Self> {
        match self {
            Type::Unknown | Type::Any => None,
            Type::TyAbs { .. }
            | Type::RecAbs { .. }
            | Type::EffAbs { .. }
            | Type::TyVar { .. }
            | Type::TyObj(_)
            | Type::Arr { .. }
            | Type::Enum(..)
            | Type::Record(..)
            | Type::Tuple(..)
            | Type::Bool
            | Type::Never => Some(self),
        }
    }

    /// `Some()` only if not `Type::Unknown` or `Type::Never`
    fn known_not_never(&'a self) -> Option<&'a Self> {
        match self {
            Type::Unknown | Type::Never => None,
            Type::TyAbs { .. }
            | Type::RecAbs { .. }
            | Type::EffAbs { .. }
            | Type::TyVar { .. }
            | Type::TyObj(_)
            | Type::Arr { .. }
            | Type::Enum(..)
            | Type::Record(..)
            | Type::Tuple(..)
            | Type::Bool
            | Type::Any => Some(self),
        }
    }

    /// `Some()` only if not `Type::Unknown`
    fn known(&'a self) -> Option<&'a Self> {
        match self {
            Type::Unknown => None,
            Type::TyAbs { .. }
            | Type::RecAbs { .. }
            | Type::EffAbs { .. }
            | Type::TyVar { .. }
            | Type::TyObj(_)
            | Type::Arr { .. }
            | Type::Enum(..)
            | Type::Record(..)
            | Type::Tuple(..)
            | Type::Bool
            | Type::Any
            | Type::Never => Some(self),
        }
    }
}
