use std::{convert::Infallible, iter::Sum};

use itertools::{Itertools, zip_eq};

use crate::{
    common::WithInfo,
    reprs::common::{ArgStructure, Lvl, RawArgStructure},
    typing::{
        context::{TyArenaContext, TyVarContext},
        error::SpannedError,
        ty::{TyBounds, TyDisplay, Type},
    },
};

mod checking;
mod context;
mod error;
mod eval;
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

#[derive(Copy, Clone)]
enum TyVar<'a> {
    Bounded(TyBounds<'a>),
    Rec,
}

#[derive(Copy, Clone)]
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

impl Type<'_> {
    fn get_variance_of(&self, ty_var_level: Lvl) -> Variance {
        match self {
            Type::TyAbs {
                name: _,
                bounds: TyBounds { upper, lower },
                result,
            } => [
                upper
                    .map(|t| t.get_variance_of(ty_var_level).invert())
                    .unwrap_or(Variance::Constant),
                lower
                    .map(|t| t.get_variance_of(ty_var_level))
                    .unwrap_or(Variance::Constant),
                result.get_variance_of(ty_var_level),
            ]
            .into_iter()
            .sum(),
            Type::RecAbs { name: _, result } => result.get_variance_of(ty_var_level),
            Type::TyVar(lvl) => {
                if *lvl == ty_var_level {
                    Variance::Covariant
                } else {
                    Variance::Constant
                }
            }
            Type::Arr { arg, result } => arg
                .get_variance_of(ty_var_level)
                .invert()
                .add(result.get_variance_of(ty_var_level)),
            Type::Enum(variants) => variants
                .0
                .values()
                .map(|t| t.get_variance_of(ty_var_level))
                .sum(),
            Type::Record(fields) => fields
                .0
                .values()
                .map(|t| t.get_variance_of(ty_var_level))
                .sum(),
            Type::Tuple(elems) => elems.iter().map(|t| t.get_variance_of(ty_var_level)).sum(),
            // the unknown type should in fact never appear here but we allow it because
            // throwing an error would complicate this function
            Type::Bool | Type::Any | Type::Never | Type::Unknown => Variance::Constant,
        }
    }
}

fn ty_eq<'a>(ty1: InternedType<'a>, ty2: InternedType<'a>) -> bool {
    std::ptr::eq(ty1, ty2)
}

impl<'a> Type<'a> {
    fn destructure<'i>(
        &self,
        arg_structure: &ArgStructure<'i>,
        ctx: &(impl TyArenaContext<'a> + TyVarContext<'a>),
    ) -> Result<impl Iterator<Item = &Self>, TypeCheckError<'i>> {
        fn inner<'i, 'a, 's>(
            arg_structure: &ArgStructure<'i>,
            ty: &'s Type<'a>,
            ctx: &(impl TyArenaContext<'a> + TyVarContext<'a>),
            output: &mut impl FnMut(&'s Type<'a>),
        ) -> Result<(), TypeCheckError<'i>> {
            let WithInfo(span, arg_structure) = arg_structure;
            match arg_structure {
                RawArgStructure::Record(st_fields) => {
                    let Type::Record(ty_fields) = ty else {
                        Err(SpannedError::new(
                            "type mismatch: record-destructure non-record",
                            format!(
                                "cannot record-destructure value of type {ty}",
                                ty = ty.display(ctx)?
                            ),
                            "",
                            *span,
                        ))?
                    };

                    st_fields.iter().try_for_each(|(l, st)| {
                        if let Some(ty) = ty_fields.0.get(l) {
                            inner(st, ty, ctx, output)
                        } else {
                            Err(SpannedError::new(
                                "type mismatch: record-destructure missing field",
                                format!(
                                    "destructured record has field with label '{l}'\n\
                                    while it's missing from it's type"
                                ),
                                "",
                                *span,
                            ))?
                        }
                    })?;
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
                            *span,
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
                            *span,
                        ))?;
                    }
                    zip_eq(st_elems, ty_elems)
                        .try_for_each(|(st, ty)| inner(st, ty, ctx, output))?;
                }

                RawArgStructure::Var => output(ty),
            }
            Ok(())
        }
        let mut buffer = Vec::new();
        inner(arg_structure, self, ctx, &mut |ty| buffer.push(ty))?;
        Ok(buffer.into_iter())
    }

    fn try_map_ty_vars<E>(
        &'a self,
        f: &mut impl FnMut(Lvl, Lvl) -> Result<&'a Self, E>,
        level: Lvl,
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
                    upper: upper
                        .map(|t| t.try_map_ty_vars(f, level, ctx))
                        .transpose()?,
                    lower: lower
                        .map(|t| t.try_map_ty_vars(f, level, ctx))
                        .transpose()?,
                },
                result: result.try_map_ty_vars(f, level.deeper(), ctx)?,
            },
            Type::RecAbs { name, result } => Type::RecAbs {
                name,
                result: result.try_map_ty_vars(f, level.deeper(), ctx)?,
            },
            Type::TyVar(ty_level) => return f(*ty_level, level),
            Type::Arr { arg, result } => Type::Arr {
                arg: arg.try_map_ty_vars(f, level, ctx)?,
                result: result.try_map_ty_vars(f, level, ctx)?,
            },
            Type::Enum(variants) => Type::Enum(
                variants
                    .0
                    .iter()
                    .map(|(l, t)| t.try_map_ty_vars(f, level, ctx).map(|t| (*l, t)))
                    .try_collect()?,
            ),
            Type::Record(fields) => Type::Record(
                fields
                    .0
                    .iter()
                    .map(|(l, t)| t.try_map_ty_vars(f, level, ctx).map(|t| (*l, t)))
                    .try_collect()?,
            ),
            Type::Tuple(elems) => Type::Tuple(
                elems
                    .iter()
                    .map(|e| e.try_map_ty_vars(f, level, ctx))
                    .try_collect()?,
            ),
            Type::Bool | Type::Any | Type::Never | Type::Unknown => return Ok(self),
        };

        Ok(ctx.intern(ty))
    }

    fn map_ty_vars(
        &'a self,
        mut f: impl FnMut(Lvl, Lvl) -> &'a Self,
        level: Lvl,
        ctx: &impl TyArenaContext<'a>,
    ) -> &'a Self {
        let Ok(res) =
            self.try_map_ty_vars(&mut |ty_l, l| Ok::<_, Infallible>(f(ty_l, l)), level, ctx);
        res
    }

    fn try_map_ty_vars_no_level<E>(
        &'a self,
        mut f: impl FnMut(Lvl) -> Result<&'a Self, E>,
        ctx: &impl TyArenaContext<'a>,
    ) -> Result<&'a Self, E> {
        self.try_map_ty_vars(&mut |l, _| f(l), Lvl::get_depth(&[(); 0]), ctx)
    }
    fn map_ty_vars_no_level(
        &'a self,
        mut f: impl FnMut(Lvl) -> &'a Self,
        ctx: &impl TyArenaContext<'a>,
    ) -> &'a Self {
        self.map_ty_vars(&mut |l, _| f(l), Lvl::get_depth(&[(); 0]), ctx)
    }

    fn substitute_ty_var(
        &'a self,
        depth: Lvl,
        ty: &'a Self,
        ctx: &impl TyArenaContext<'a>,
    ) -> &'a Self {
        self.map_ty_vars(
            |ty_level, level| {
                if ty_level == depth {
                    return if depth == level {
                        // no substitution necessary
                        ty
                    } else {
                        ty.map_ty_vars(
                            |inner_ty_level, _inner_level| {
                                ctx.intern(Type::TyVar(
                                    // depth <= level
                                    inner_ty_level
                                        .translate(depth, level)
                                        .expect("level within map_ty_vars is never shallower than the level passed in"),
                                ))
                            },
                            level,
                            ctx,
                        )
                    };
                }
                let new_level = match ty_level.shallower() {
                    // deeper than replaced but not equal (due to prev arm)
                    Some(shallower) if ty_level.deeper_than(depth) => shallower,
                    // either:
                    // - shallowest so could not be strictly deeper
                    // - not deeper
                    None | Some(_) => ty_level,
                };
                ctx.intern(Type::TyVar(new_level))
            },
            depth,
            ctx,
        )
    }

    // TODO: maybe ensure type safety by Type::Concrete(ConcreteType::{Arr, Enum, ...})
    /// Get the minimal concrete supertype
    fn upper_concrete(
        &'a self,
        ctx: &(impl TyArenaContext<'a> + TyVarContext<'a, TyVar = TyVar<'a>>),
    ) -> Result<&'a Self, TypeCheckError<'static>> {
        match self {
            Type::TyVar(level) => {
                let (_, ty_var) = ctx.get_ty_var_unwrap(*level)?;
                match ty_var {
                    TyVar::Bounded(bounds) => bounds.get_upper(ctx).upper_concrete(ctx),
                    // we have a isorecursive view of recursive types so this is concrete
                    TyVar::Rec => Ok(self),
                }
            }
            Type::TyAbs { .. }
            | Type::RecAbs { .. }
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
            | Type::TyVar { .. }
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
            | Type::TyVar { .. }
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
            | Type::TyVar { .. }
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
