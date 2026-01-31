use itertools::Itertools;

use crate::{
    common::WithInfo,
    reprs::untyped_ir as uir,
    typing::{
        Context, InternedType, TypeCheckError,
        context::{TyArenaContext, TyVarContext},
        expect_type, prepend,
        ty::{TyBounds, Type},
    },
};

pub(super) trait TyEval<'i: 'a, 'a> {
    type Evaled;

    fn eval(&self, ctx: &Context<'a, '_>) -> Result<Self::Evaled, TypeCheckError>;
}

impl<'i: 'a, 'a> TyEval<'i, 'a> for uir::Type<'i> {
    type Evaled = InternedType<'a>;

    fn eval(&self, ctx: &Context<'a, '_>) -> Result<Self::Evaled, TypeCheckError> {
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

impl<'i: 'a, 'a> TyEval<'i, 'a> for uir::TyBounds<'i> {
    type Evaled = TyBounds<'a>;

    fn eval(&self, ctx: &Context<'a, '_>) -> Result<Self::Evaled, TypeCheckError> {
        let uir::TyBounds { upper, lower } = self;
        let upper = upper.as_ref().map(|ty| ty.eval(ctx)).transpose()?;
        let lower = lower.as_ref().map(|ty| ty.eval(ctx)).transpose()?;
        if let (Some(upper), Some(lower)) = (upper, lower) {
            // technically we don't really expect either but this is close enough
            expect_type(upper, lower, true, false, ctx).map_err(prepend(
                || "type bound error: upper bound must be supertype of lower bound",
            ))?;
        }
        Ok(TyBounds { upper, lower })
    }
}

impl<'i: 'a, 'a, T: TyEval<'i, 'a>> TyEval<'i, 'a> for Option<T> {
    type Evaled = Option<T::Evaled>;

    fn eval(&self, ctx: &Context<'a, '_>) -> Result<Self::Evaled, TypeCheckError> {
        self.as_ref().map(|t| t.eval(ctx)).transpose()
    }
}
