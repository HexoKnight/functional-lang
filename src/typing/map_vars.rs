use std::convert::Infallible;

use itertools::Itertools;

use crate::{
    reprs::common::Lvl,
    typing::{
        TyArenaContext, TyEffLvl,
        effects::{EffKind, Effect},
        ty::{TyBounds, Type},
    },
};

pub(super) trait MapVars<'a>: Sized {
    fn try_map_vars<E>(
        self,
        ty_f: impl FnMut(Lvl, TyEffLvl) -> Result<&'a Type<'a>, E>,
        eff_f: impl FnMut(Lvl, EffKind<'a>, TyEffLvl) -> Result<Effect<'a>, E>,
        ty_eff_lvl: TyEffLvl,
        ctx: &impl TyArenaContext<'a>,
    ) -> Result<Self, E>;

    fn map_vars(
        self,
        mut ty_f: impl FnMut(Lvl, TyEffLvl) -> &'a Type<'a>,
        mut eff_f: impl FnMut(Lvl, EffKind<'a>, TyEffLvl) -> Effect<'a>,
        ty_eff_lvl: TyEffLvl,
        ctx: &impl TyArenaContext<'a>,
    ) -> Self {
        let Ok(res) = self.try_map_vars(
            |ty_l, l| Ok::<_, Infallible>(ty_f(ty_l, l)),
            |eff_l, eff_k, l| Ok::<_, Infallible>(eff_f(eff_l, eff_k, l)),
            ty_eff_lvl,
            ctx,
        );
        res
    }

    fn try_map_vars_no_level<E>(
        self,
        mut ty_f: impl FnMut(Lvl) -> Result<&'a Type<'a>, E>,
        mut eff_f: impl FnMut(Lvl, EffKind<'a>) -> Result<Effect<'a>, E>,
        ctx: &impl TyArenaContext<'a>,
    ) -> Result<Self, E> {
        let lvl = Lvl::get_depth(&[(); 0]);
        self.try_map_vars(
            |l, _| ty_f(l),
            |l, eff_k, _| eff_f(l, eff_k),
            TyEffLvl::new(lvl, lvl),
            ctx,
        )
    }
    fn map_vars_no_level(
        self,
        mut ty_f: impl FnMut(Lvl) -> &'a Type<'a>,
        mut eff_f: impl FnMut(Lvl, EffKind<'a>) -> Effect<'a>,
        ctx: &impl TyArenaContext<'a>,
    ) -> Self {
        let lvl = Lvl::get_depth(&[(); 0]);
        self.map_vars(
            |l, _| ty_f(l),
            |l, eff_k, _| eff_f(l, eff_k),
            TyEffLvl::new(lvl, lvl),
            ctx,
        )
    }

    /// deepens all `ty_var`s and `eff_var`s deeper than `prev_ty_eff_lvl.*` (inclusive) to `new_ty_eff_lvl.*`
    /// eg. deepen(3, 5): 0 -> 0, 2 -> 2, 3 -> 5, 72 -> 74
    fn deepen(
        self,
        prev_ty_eff_lvl: TyEffLvl,
        new_ty_eff_lvl: TyEffLvl,
        ctx: &impl TyArenaContext<'a>,
    ) -> Self {
        if prev_ty_eff_lvl == new_ty_eff_lvl {
            return self;
        }
        self.map_vars_no_level(
            |ty_level| {
                let new_ty_level =
                    if let Some(deeper) = ty_level.get_deeper_than(prev_ty_eff_lvl.ty) {
                        new_ty_eff_lvl.ty.deeper_by(deeper)
                    } else {
                        ty_level
                    };
                ctx.intern(Type::TyVar(new_ty_level))
            },
            |eff_level, eff_kind| {
                let new_eff_level =
                    if let Some(deeper) = eff_level.get_deeper_than(prev_ty_eff_lvl.eff) {
                        new_ty_eff_lvl.eff.deeper_by(deeper)
                    } else {
                        eff_level
                    };
                Effect::Var(new_eff_level, eff_kind)
            },
            ctx,
        )
    }
}

impl<'a> MapVars<'a> for &'a Type<'a> {
    fn try_map_vars<E>(
        self,
        mut ty_f: impl FnMut(Lvl, TyEffLvl) -> Result<&'a Type<'a>, E>,
        mut eff_f: impl FnMut(Lvl, EffKind<'a>, TyEffLvl) -> Result<Effect<'a>, E>,
        ty_eff_lvl: TyEffLvl,
        ctx: &impl TyArenaContext<'a>,
    ) -> Result<Self, E> {
        self.try_map_vars(MapVarsCtx {
            ty_f: &mut ty_f,
            eff_f: &mut eff_f,
            ty_eff_lvl,
            ctx,
        })
    }
}

impl<'a> MapVars<'a> for Effect<'a> {
    fn try_map_vars<E>(
        self,
        mut ty_f: impl FnMut(Lvl, TyEffLvl) -> Result<&'a Type<'a>, E>,
        mut eff_f: impl FnMut(Lvl, EffKind<'a>, TyEffLvl) -> Result<Effect<'a>, E>,
        ty_eff_lvl: TyEffLvl,
        ctx: &impl TyArenaContext<'a>,
    ) -> Result<Self, E> {
        self.try_map_vars(MapVarsCtx {
            ty_f: &mut ty_f,
            eff_f: &mut eff_f,
            ty_eff_lvl,
            ctx,
        })
    }
}

struct MapVarsCtx<'ctx, TF, EF, C> {
    ty_f: &'ctx mut TF,
    eff_f: &'ctx mut EF,
    ty_eff_lvl: TyEffLvl,
    ctx: &'ctx C,
}

impl<'ctx, TF, EF, C> MapVarsCtx<'ctx, TF, EF, C> {
    fn copy(&mut self) -> MapVarsCtx<'_, TF, EF, C> {
        MapVarsCtx {
            ty_f: self.ty_f,
            eff_f: self.eff_f,
            ..*self
        }
    }

    fn ty_deeper(&mut self) -> MapVarsCtx<'_, TF, EF, C> {
        MapVarsCtx {
            ty_eff_lvl: TyEffLvl {
                ty: self.ty_eff_lvl.ty.deeper(),
                ..self.ty_eff_lvl
            },
            ..self.copy()
        }
    }
    fn eff_deeper(&mut self) -> MapVarsCtx<'_, TF, EF, C> {
        MapVarsCtx {
            ty_eff_lvl: TyEffLvl {
                eff: self.ty_eff_lvl.eff.deeper(),
                ..self.ty_eff_lvl
            },
            ..self.copy()
        }
    }

    fn map_ty_lvl<T>(&mut self, cur_ty_lvl: Lvl) -> T
    where
        TF: FnMut(Lvl, TyEffLvl) -> T,
    {
        (self.ty_f)(cur_ty_lvl, self.ty_eff_lvl)
    }
    fn map_eff_lvl<'a, E>(
        &mut self,
        cur_eff_lvl: Lvl,
        eff_kind: EffKind<'a>,
    ) -> Result<Effect<'a>, E>
    where
        EF: FnMut(Lvl, EffKind<'a>, TyEffLvl) -> Result<Effect<'a>, E>,
    {
        (self.eff_f)(cur_eff_lvl, eff_kind, self.ty_eff_lvl)
    }
}

impl<'a> Type<'a> {
    fn try_map_vars<E>(
        &'a self,
        mut ctx: MapVarsCtx<
            impl FnMut(Lvl, TyEffLvl) -> Result<&'a Type<'a>, E>,
            impl FnMut(Lvl, EffKind<'a>, TyEffLvl) -> Result<Effect<'a>, E>,
            impl TyArenaContext<'a>,
        >,
    ) -> Result<&'a Self, E> {
        let ty = match self {
            Type::TyAbs {
                name,
                bounds: TyBounds { upper, lower },
                result,
            } => Type::TyAbs {
                name,
                bounds: TyBounds {
                    upper: upper.map(|t| t.try_map_vars(ctx.copy())).transpose()?,
                    lower: lower.map(|t| t.try_map_vars(ctx.copy())).transpose()?,
                },
                result: result.try_map_vars(ctx.copy().ty_deeper())?,
            },
            Type::RecAbs { name, result } => Type::RecAbs {
                name,
                result: result.try_map_vars(ctx.copy().ty_deeper())?,
            },
            Type::EffAbs { name, result } => Type::EffAbs {
                name: *name,
                result: result.try_map_vars(ctx.copy().eff_deeper())?,
            },
            Type::TyVar(cur_ty_lvl) => return ctx.map_ty_lvl(*cur_ty_lvl),
            Type::TyObj(ty) => Type::TyObj(ty.try_map_vars(ctx.copy())?),
            Type::Arr {
                arg,
                effects,
                result,
            } => Type::Arr {
                arg: arg.try_map_vars(ctx.copy())?,
                effects: effects.try_map(|_, effect| effect.try_map_vars(ctx.copy()))?,
                result: result.try_map_vars(ctx.copy())?,
            },
            Type::Enum(variants) => Type::Enum(
                variants
                    .0
                    .iter()
                    .map(|(l, t)| t.try_map_vars(ctx.copy()).map(|t| (*l, t)))
                    .try_collect()?,
            ),
            Type::Record(fields) => Type::Record(
                fields
                    .0
                    .iter()
                    .map(|(l, t)| t.try_map_vars(ctx.copy()).map(|t| (*l, t)))
                    .try_collect()?,
            ),
            Type::Tuple(elems) => Type::Tuple(
                elems
                    .iter()
                    .map(|e| e.try_map_vars(ctx.copy()))
                    .try_collect()?,
            ),
            Type::Bool | Type::Any | Type::Never | Type::Unknown => return Ok(self),
        };

        Ok(ctx.ctx.intern(ty))
    }
}

impl<'a> Effect<'a> {
    fn try_map_vars<E>(
        self,
        mut ctx: MapVarsCtx<
            impl FnMut(Lvl, TyEffLvl) -> Result<&'a Type<'a>, E>,
            impl FnMut(Lvl, EffKind<'a>, TyEffLvl) -> Result<Effect<'a>, E>,
            impl TyArenaContext<'a>,
        >,
    ) -> Result<Self, E> {
        Ok(match self {
            Effect::Def { name, arg, result } => Effect::Def {
                name,
                arg: arg.try_map_vars(ctx.copy())?,
                result: result.try_map_vars(ctx.copy())?,
            },
            Effect::Var(cur_eff_lvl, eff_kind) => ctx.map_eff_lvl(cur_eff_lvl, eff_kind)?,
        })
    }
}
