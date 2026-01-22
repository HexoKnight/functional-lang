use itertools::zip_eq;

use crate::typing::{
    Context, InternedType, TypeCheckError, prepend, try_prepend,
    ty::{TyDisplay, Type},
    ty_eq,
};

// TODO: improve error messages by specifying which type is 'expected'
/// # Errors
/// returns Err when not subtype
pub(super) fn check_subtype<'a>(
    supertype: InternedType<'a>,
    subtype: InternedType<'a>,
    ctx: &Context<'a, '_>,
) -> Result<(), TypeCheckError> {
    if ty_eq(supertype, subtype) {
        return Ok(());
    }

    match (supertype, subtype) {
        (
            Type::TyAbs {
                name: name_super,
                bounds: bounds_super,
                result: supertype,
            },
            Type::TyAbs {
                name: name_sub,
                bounds: bounds_sub,
                result: subtype,
            },
        ) => {
            // subtype bounds must enclose supertype bounds
            if let Some(upper_sub) = bounds_sub.upper {
                let upper_super = bounds_super.upper.unwrap_or_else(|| ctx.intern(Type::Any));
                check_subtype(upper_sub, upper_super, ctx)
            } else {
                Ok(())
            }
            .map_err(prepend(|| {
                "subtype upper bound must be a supertype of supertype upper bound".to_string()
            }))
            .and_then(|()| {
                if let Some(lower_sub) = bounds_sub.lower {
                    let lower_super = bounds_super
                        .lower
                        .unwrap_or_else(|| ctx.intern(Type::Never));
                    check_subtype(lower_super, lower_sub, ctx)
                } else {
                    Ok(())
                }
                .map_err(prepend(|| {
                    "subtype lower bound must be a subtype of supertype lower bound".to_string()
                }))
            })
            .map_err(prepend(|| {
                "bounds of subtype type arg must enclose those of the supertype type arg:"
                    .to_string()
            }))
            .and_then(|()| {
                check_subtype(
                    supertype,
                    subtype,
                    &ctx.push_ty_var(std::cmp::min(name_super, name_sub), *bounds_super),
                )
            })
        }
        (
            Type::TyAbs {
                name,
                bounds,
                result: supertype,
            },
            subtype,
        ) => check_subtype(supertype, subtype, &ctx.push_ty_var(name, *bounds)),
        (
            supertype,
            Type::TyAbs {
                name,
                bounds,
                result: subtype,
            },
        ) => check_subtype(supertype, subtype, &ctx.push_ty_var(name, *bounds)),
        // covered by ty_eq above but included regardless
        (Type::TyVar(level_super), Type::TyVar(level_sub)) if level_super == level_sub => Ok(()),
        (Type::TyVar(level), subtype) => {
            // if the lower bound doesn't exist (ie. it is unbounded below), it is equivalent to
            // having a lower bound of the bottom type
            let (_, supertype_bounds) = ctx.get_ty_var_unwrap(*level)?;
            let lower = supertype_bounds
                .lower
                .unwrap_or_else(|| ctx.intern(Type::Never));
            // a type is guaranteed to be a subtype of the instantiated type iff it is a
            // subtype of the lower bound (due to the transitivity of subtyping)
            check_subtype(lower, subtype, ctx).map_err(try_prepend(|| {
                Ok(format!(
                    "subtyping must be guaranteed for all possible instantiations of type var: {}\n\
                    for example, one such instantiation is: {}",
                    supertype.display(ctx)?,
                    lower.display(ctx)?
                ))
            }))
        }
        (supertype, Type::TyVar(level)) => {
            // if the lower bound doesn't exist (ie. it is unbounded below), it is equivalent to
            // having a lower bound of the bottom type
            let (_, subtype_bounds) = ctx.get_ty_var_unwrap(*level)?;
            let upper = subtype_bounds
                .upper
                .unwrap_or_else(|| ctx.intern(Type::Any));
            // a type is guaranteed to be a supertype of the instantiated type iff it is a
            // supertype of the upper bound (due to the transitivity of subtyping)
            check_subtype(supertype, upper, ctx).map_err(try_prepend(|| {
                Ok(format!(
                    "subtyping must be guaranteed for all possible instantiations of type var: {}\n\
                    for example, one such instantiation is: {}",
                    supertype.display(ctx)?,
                    upper.display(ctx)?
                ))
            }))
        }
        (
            Type::Arr {
                arg: arg_super,
                result: res_super,
            },
            Type::Arr {
                arg: arg_sub,
                result: res_sub,
            },
        ) => {
            check_subtype(arg_sub, arg_super, ctx)?;
            check_subtype(res_super, res_sub, ctx)
        }
        (Type::Enum(variants_super), Type::Enum(variants_sub)) => variants_sub
            .0
            .iter()
            // for each variant of the subtype:
            .try_for_each(|(l, ty_sub)| {
                // check that the supertype also has it...
                let Some(ty_super) = variants_super.0.get(l) else {
                    return Err(format!(
                        "subtyping error: label '{l}' missing from supertype",
                    ));
                };
                // and that the variant types maintain the same subtyping relationship
                check_subtype(ty_super, ty_sub, ctx)
            }),
        (Type::Tuple(elems_super), Type::Tuple(elems_sub)) => {
            if elems_super.len() != elems_sub.len() {
                return Err("subtyping error: tuples have different lengths".to_string());
            }
            zip_eq(elems_super, elems_sub)
                .try_for_each(|(elem_super, elem_sub)| check_subtype(elem_super, elem_sub, ctx))
        }
        (Type::Bool, Type::Bool) | (Type::Any, _) | (_, Type::Never) => Ok(()),
        (_, Type::Any) => Err("_ is the any type: \
            it has no supertypes bar itself and cannot be constructed (directly)"
            .to_string()),
        (Type::Never, _) => Err("! is the never type: \
            it has no subtypes bar itself and cannot be constructed"
            .to_string()),
        // not using _ to avoid catching more cases than intended
        (Type::Arr { .. } | Type::Enum(..) | Type::Tuple(..) | Type::Bool, _) => {
            Err("subtyping error: types are incompatible".to_string())
        }
    }
    .map_err(try_prepend(|| {
        Ok(format!(
            "subtyping error:\n\
            {}\n\
            is not a supertype of:\n\
            {}",
            supertype.display(ctx)?,
            subtype.display(ctx)?
        ))
    }))
}
