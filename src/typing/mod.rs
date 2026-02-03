use std::convert::Infallible;

use itertools::{Itertools, zip_eq};

use crate::{
    reprs::common::{ArgStructure, Lvl},
    typing::{
        context::{TyArenaContext, TyVarContext},
        ty::{TyBounds, TyDisplay, Type},
    },
};

mod checking;
mod context;
mod eval;
mod merge;
mod subtyping;
mod ty;

type InternedType<'a> = &'a Type<'a>;

pub type TypeCheckError = String;

pub use self::checking::type_check;

fn ty_eq<'a>(ty1: InternedType<'a>, ty2: InternedType<'a>) -> bool {
    std::ptr::eq(ty1, ty2)
}

impl<'a> Type<'a> {
    fn destructure(
        &self,
        arg_structure: &ArgStructure,
        ctx: &(impl TyArenaContext<'a> + TyVarContext<'a>),
    ) -> Result<impl Iterator<Item = &Self>, TypeCheckError> {
        fn inner<'a, 's>(
            arg_structure: &ArgStructure,
            ty: &'s Type<'a>,
            ctx: &(impl TyArenaContext<'a> + TyVarContext<'a>),
            output: &mut impl FnMut(&'s Type<'a>),
        ) -> Result<(), TypeCheckError> {
            match arg_structure {
                ArgStructure::Record(st_fields) => {
                    let Type::Record(ty_fields) = ty else {
                        return Err(format!(
                            "cannot record-destructure value of type {ty}",
                            ty = ty.display(ctx)?
                        ));
                    };

                    st_fields.iter().try_for_each(|(l, st)| {
                        if let Some(ty) = ty_fields.0.get(l) {
                            inner(st, ty, ctx, output)
                        } else {
                            Err(format!(
                                "destructured record has field with label '{l}'\n\
                                while it's missing from it's type"
                            ))
                        }
                    })?;
                }

                ArgStructure::Tuple(st_elems) => {
                    let Type::Tuple(ty_elems) = ty else {
                        return Err(format!(
                            "cannot tuple-destructure value of type {ty}",
                            ty = ty.display(ctx)?
                        ));
                    };

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

                ArgStructure::Var => output(ty),
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
            Type::Record(fields) => Type::Record(
                fields
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
    fn upper_concrete(
        &'a self,
        ctx: &(impl TyArenaContext<'a> + TyVarContext<'a, TyVar = TyBounds<'a>>),
    ) -> Result<&'a Self, TypeCheckError> {
        match self {
            Type::TyVar(level) => ctx
                .get_ty_var_unwrap(*level)?
                .1
                .get_upper(ctx)
                .upper_concrete(ctx),
            Type::TyAbs { .. }
            | Type::Arr { .. }
            | Type::Enum(..)
            | Type::Record(..)
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
            | Type::Record(..)
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
            | Type::Record(..)
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
