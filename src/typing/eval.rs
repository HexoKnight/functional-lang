use std::iter::once;

use itertools::Itertools;

use crate::{
    common::WithInfo,
    reprs::{common::Label, untyped_ir as uir},
    typing::{
        EffVar, InternedType, TyConfig, TyVar, Variance,
        effects::{EffId, Effect, EffectGroup},
        error::{SpannedError, TypeCheckError, TypeCheckResult},
        subtyping::expect_type,
        ty::{TyBounds, TyDisplay, Type},
    },
};

pub(super) trait TyEval<'i: 'a, 'a> {
    type Evaled;

    fn eval<'inn>(
        &self,
        ctx: &ctx!(arena 'inn; ty_var; eff_var),
    ) -> Result<Self::Evaled, TypeCheckError<'i>>
    where
        'a: 'inn;
}

impl<'i: 'a, 'a, T: TyEval<'i, 'a>> TyEval<'i, 'a> for Option<T> {
    type Evaled = Option<T::Evaled>;

    fn eval<'inn>(
        &self,
        ctx: &ctx!(arena 'inn; ty_var; eff_var),
    ) -> Result<Self::Evaled, TypeCheckError<'i>>
    where
        'a: 'inn,
    {
        self.as_ref().map(|t| t.eval(ctx)).transpose()
    }
}

impl<'i: 'a, 'a> TyEval<'i, 'a> for uir::Type<'i> {
    type Evaled = InternedType<'a>;

    fn eval<'inn>(
        &self,
        ctx: &ctx!(arena 'inn; ty_var; eff_var),
    ) -> Result<Self::Evaled, TypeCheckError<'i>>
    where
        'a: 'inn,
    {
        let WithInfo(info, ty) = self;

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
                    result: result.eval(&ctx.push_ty_var(
                        name,
                        TyVar::Bounded {
                            bounds,
                            eff_lvl: ctx.next_eff_var_level(),
                        },
                    ))?,
                }
            }
            uir::RawType::TyApp { abs, arg } => {
                let abs_span = abs.0;
                let arg_span = arg.0;
                let abs = abs.eval(ctx)?;
                let arg = arg.eval(ctx)?;

                let ty = abs.apply_ty_arg(
                    abs_span,
                    arg,
                    arg_span,
                    TyConfig::ty_inference_disabled(),
                    ctx,
                )?;

                return Ok(ty);
            }
            uir::RawType::RecAbs { name, result } => {
                let level = ctx.next_ty_var_level();
                let result = result.eval(&ctx.push_ty_var(name, TyVar::Rec))?;

                if let Variance::Invariant | Variance::Contravariant =
                    result.get_variance_of(level, &ctx.push_ty_var(name, TyVar::Rec))?
                {
                    Err(SpannedError::new(
                        "negative recursive types are not allowed",
                        "recursive type variables cannot appear in negative positions,\n\
                        such that the recursive type abstraction's body would be\n\
                        contravariant or invariant in it's variable"
                            .to_string(),
                        "in this type",
                        *info,
                    ))?;
                }

                Type::RecAbs {
                    name,
                    // ty_vars are not currently used so this is useless but may as well push it if
                    // only for future correctness
                    result,
                }
            }
            uir::RawType::EffAbs { name, result } => Type::EffAbs {
                name: Label(name),
                result: result.eval(&ctx.push_eff_var(name, EffVar::Unbound))?,
            },
            uir::RawType::EffApp { abs, effects } => {
                let abs_span = abs.0;
                let abs = abs.eval(ctx)?;
                let effects = effects.eval(ctx)?;

                let ty = abs.apply_eff_arg(abs_span, &effects, ctx)?;

                return Ok(ty);
            }
            uir::RawType::TyVar(level) => Type::TyVar(*level),
            uir::RawType::Arr {
                arg,
                effects,
                result,
            } => {
                let arg = arg.as_ref().eval(ctx)?;
                let effects = effects.eval(ctx)?;
                let result = result.as_ref().eval(ctx)?;
                Type::Arr {
                    arg,
                    effects,
                    result,
                }
            }
            uir::RawType::Enum(variants) => Type::Enum(
                variants
                    .iter()
                    .map(|(l, t)| t.eval(ctx).map(|t| (*l, t)))
                    .try_collect()?,
            ),
            uir::RawType::Record(fields) => Type::Record(
                fields
                    .iter()
                    .map(|(l, t)| t.eval(ctx).map(|t| (*l, t)))
                    .try_collect()?,
            ),
            uir::RawType::Tuple(elems) => {
                Type::Tuple(elems.iter().map(|e| e.eval(ctx)).try_collect()?)
            }
            uir::RawType::Bool => Type::Bool,
            uir::RawType::Any => Type::Any,
            uir::RawType::Never => Type::Never,
        };

        Ok(ctx.intern(ty))
    }
}

impl<'i: 'a, 'a> TyEval<'i, 'a> for uir::TyBounds<'i> {
    type Evaled = TyBounds<'a>;

    fn eval<'inn>(
        &self,
        ctx: &ctx!(arena 'inn; ty_var; eff_var),
    ) -> Result<Self::Evaled, TypeCheckError<'i>>
    where
        'a: 'inn,
    {
        let uir::TyBounds { upper, lower } = self;
        let upper = if let Some(ty @ WithInfo(span, _)) = upper {
            Some((span, ty.eval(ctx)?))
        } else {
            None
        };
        let lower = if let Some(ty @ WithInfo(span, _)) = lower {
            Some((span, ty.eval(ctx)?))
        } else {
            None
        };
        if let (Some((upper_span, upper)), Some((lower_span, lower))) = (upper, lower) {
            // technically we don't really expect either but this is close enough
            expect_type(upper, lower, true, TyConfig::ty_inference_disabled(), ctx).wrap_error(
                || {
                    SpannedError::with_context(
                        "type mismatch: impossible bounds",
                        "upper bound must be supertype of lower bound",
                        "upper bound",
                        *upper_span,
                        once((*lower_span, "lower bound")),
                    )
                },
            )?;
        }
        Ok(TyBounds {
            upper: upper.map(|(_, ty)| ty),
            lower: lower.map(|(_, ty)| ty),
        })
    }
}

impl<'i: 'a, 'a> TyEval<'i, 'a> for uir::EffectGroup<'i, uir::Effect<'i>> {
    type Evaled = EffectGroup<'a>;

    fn eval<'inn>(
        &self,
        ctx: &ctx!(arena 'inn; ty_var; eff_var),
    ) -> Result<Self::Evaled, TypeCheckError<'i>>
    where
        'a: 'inn,
    {
        self.0
            .iter()
            .map(|(label, effect_term)| {
                let effect = effect_term.eval(ctx)?;
                if let Some(_) = label
                    && let EffId::Unbound(_) = effect.get_id()
                {
                    Err(SpannedError::new(
                        format!("cannot label unbound effect: {}", effect.display(ctx)?),
                        "",
                        "",
                        effect_term.0,
                    ))?
                }
                Ok((*label, effect))
            })
            .try_collect()
    }
}

impl<'i: 'a, 'a> TyEval<'i, 'a> for uir::Effect<'i> {
    type Evaled = Effect<'a>;

    fn eval<'inn>(
        &self,
        ctx: &ctx!(arena 'inn; ty_var; eff_var),
    ) -> Result<Self::Evaled, TypeCheckError<'i>>
    where
        'a: 'inn,
    {
        let WithInfo(_span, effect) = self;
        let effect = match effect {
            uir::RawEffect::Def { name, arg, result } => Effect::Def {
                name: *name,
                arg: arg.eval(ctx)?,
                result: result.eval(ctx)?,
            },
            uir::RawEffect::Var(level) => Effect::Var(
                *level,
                ctx.get_eff_var_unwrap(*level)?.1.get_id(*level).to_kind(),
            ),
        };
        Ok(effect)
    }
}
