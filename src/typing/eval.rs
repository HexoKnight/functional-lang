use std::iter::once;

use itertools::Itertools;

use crate::{
    common::WithInfo,
    reprs::untyped_ir as uir,
    typing::{
        InternedType, TyConfig,
        context::{ContextInner, TyArenaContext, TyVarContext},
        error::{SpannedError, TypeCheckError, TypeCheckResult},
        subtyping::expect_type,
        ty::{TyBounds, Type},
    },
};

// unfortunately no trait aliases
macro_rules! ctx {
    () => {
        ctx!('a, 'inn)
    };
    ($a:lifetime, $inn:lifetime) => {
         impl TyArenaContext<$a, Inner = &$inn ContextInner<$a>>
            + TyVarContext<$a, TyVar = TyBounds<$a>>
    };
}

pub(super) trait TyEval<'i: 'a, 'a> {
    type Evaled;

    fn eval<'inn>(&self, ctx: &ctx!()) -> Result<Self::Evaled, TypeCheckError<'i>>
    where
        'a: 'inn;
}

impl<'i: 'a, 'a> TyEval<'i, 'a> for uir::Type<'i> {
    type Evaled = InternedType<'a>;

    fn eval<'inn>(&self, ctx: &ctx!()) -> Result<Self::Evaled, TypeCheckError<'i>>
    where
        'a: 'inn,
    {
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

    fn eval<'inn>(&self, ctx: &ctx!()) -> Result<Self::Evaled, TypeCheckError<'i>>
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

impl<'i: 'a, 'a, T: TyEval<'i, 'a>> TyEval<'i, 'a> for Option<T> {
    type Evaled = Option<T::Evaled>;

    fn eval<'inn>(&self, ctx: &ctx!()) -> Result<Self::Evaled, TypeCheckError<'i>>
    where
        'a: 'inn,
    {
        self.as_ref().map(|t| t.eval(ctx)).transpose()
    }
}
