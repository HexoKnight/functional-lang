use itertools::{Itertools, zip_eq};

use crate::typing::{
    InternedType, TypeCheckError,
    context::{ContextInner, TyArenaContext, TyVarContext},
    prepend, try_prepend,
    ty::{TyBounds, TyDisplay, Type},
    ty_eq,
};

// unfortunately no trait aliases
macro_rules! ctx {
    () => {
         impl TyArenaContext<'a, Inner = &'inn ContextInner<'a>>
            + TyVarContext<'a, TyVar = TyBounds<'a>>
    };
}

fn maybe_swap<T>(a: T, b: T, swap: bool) -> (T, T) {
    if swap { (b, a) } else { (a, b) }
}

/// Checks whether `found` can be used in place of `expected`.
/// Returns the type that `found` would have if so.
/// `subtype` determines whether `found` should be allowed to be a subtype
/// of `expected` or vice versa.
///
/// # Errors
/// returns Err when not subtype
pub(super) fn expect_type<'a: 'inn, 'inn>(
    expected: InternedType<'a>,
    found: InternedType<'a>,
    subtype: bool,
    ctx: &ctx!(),
) -> Result<InternedType<'a>, TypeCheckError> {
    if ty_eq(expected, found) {
        return Ok(found);
    }

    let relation = if subtype { "subtype" } else { "supertype" };

    // whether order is swapped between (expected, found) and (super, sub)
    // ie. swapped: (expected, found) == (sub, super)
    //    !swapped: (expected, found) == (super, sub)
    let swapped = !subtype;
    fn super_sub_of<T>(expected: T, found: T, swapped: bool) -> (T, T) {
        maybe_swap(expected, found, swapped)
    }
    fn exp_found_of<T>(sup: T, sub: T, swapped: bool) -> (T, T) {
        maybe_swap(sup, sub, swapped)
    }

    match (expected, found, subtype) {
        (
            Type::TyAbs {
                name: name_expected,
                bounds: bounds_expected,
                result: expected,
            },
            Type::TyAbs {
                name: name_found,
                bounds: bounds_found,
                result: found,
            },
            _,
        ) => {
            // subtype bounds must enclose supertype bounds
            TyBounds::expect_bounds(bounds_expected, bounds_found, subtype, ctx)
                .map_err(prepend(|| {
                    "bounds of subtype type arg must enclose those of the supertype type arg:"
                        .to_string()
                }))
                .and_then(|()| {
                    let (bounds_super, _) = super_sub_of(bounds_expected, bounds_found, swapped);
                    expect_type(
                        expected,
                        found,
                        subtype,
                        // we choose the narrower bounds
                        &ctx.push_ty_var(std::cmp::min(name_expected, name_found), *bounds_super),
                    )
                })
        }
        (
            Type::TyAbs {
                name,
                bounds,
                result: expected,
            },
            found,
            _,
            // TODO: this is wrong
        ) => expect_type(expected, found, subtype, &ctx.push_ty_var(name, *bounds)),
        (
            expected,
            Type::TyAbs {
                name,
                bounds,
                result: found,
            },
            _,
            // TODO: this is wrong
        ) => expect_type(expected, found, subtype, &ctx.push_ty_var(name, *bounds)),
        // covered by ty_eq above but included regardless
        (Type::TyVar(level_expected), Type::TyVar(level_found), _)
            if level_expected == level_found =>
        {
            Ok(found)
        }
        (Type::TyVar(level_expected), found, _) => {
            // if the lower bound doesn't exist (ie. it is unbounded below), it is equivalent to
            // having a lower bound of the bottom type
            let (_, bounds_expected) = ctx.get_ty_var_unwrap(*level_expected)?;
            let lower_expected = bounds_expected.get_lower(ctx);
            // a type is guaranteed to be a subtype of the instantiated type iff it is a
            // subtype of the lower bound (due to the transitivity of subtyping)
            expect_type(lower_expected, found, subtype, ctx).map_err(try_prepend(|| {
                Ok(format!(
                    "subtyping must be guaranteed for all possible instantiations of type var: {}\n\
                    for example, one such instantiation is: {}",
                    expected.display(ctx)?,
                    lower_expected.display(ctx)?
                ))
            }))
        }
        (expected, Type::TyVar(level_found), _) => {
            // if the lower bound doesn't exist (ie. it is unbounded below), it is equivalent to
            // having a lower bound of the bottom type
            let (_, bounds_found) = ctx.get_ty_var_unwrap(*level_found)?;
            let upper_found = bounds_found.get_upper(ctx);
            // a type is guaranteed to be a supertype of the instantiated type iff it is a
            // supertype of the upper bound (due to the transitivity of subtyping)
            expect_type(expected, upper_found, subtype, ctx).map_err(try_prepend(|| {
                Ok(format!(
                    "subtyping must be guaranteed for all possible instantiations of type var: {}\n\
                    for example, one such instantiation is: {}",
                    found.display(ctx)?,
                    upper_found.display(ctx)?
                ))
            }))
        }
        (
            Type::Arr {
                arg: arg_expected,
                result: res_expected,
            },
            Type::Arr {
                arg: arg_found,
                result: res_found,
            },
            _,
            // no try block :(
        ) => (|| {
            Ok(ctx.intern(Type::Arr {
                arg: expect_type(arg_expected, arg_found, !subtype, ctx)?,
                result: expect_type(res_expected, res_found, subtype, ctx)?,
            }))
        })(),
        (Type::Enum(variants_expected), Type::Enum(variants_found), _) => {
            let (variants_super, variants_sub) =
                super_sub_of(variants_expected, variants_found, swapped);
            variants_sub
                .0
                .iter()
                // for each variant of the subtype:
                .map(|(l, ty_sub)| {
                    // check that the supertype also has it...
                    if let Some(ty_super) = variants_super.0.get(l) {
                        let (ty_expected, ty_found) = exp_found_of(ty_super, ty_sub, swapped);
                        // and that the variant types maintain the same subtyping relationship
                        Ok((*l, expect_type(ty_expected, ty_found, subtype, ctx)?))
                    } else {
                        Err(format!(
                            "label '{l}' missing from supertype:\n\
                            | {}",
                            super_sub_of(expected, found, swapped).0.display(ctx)?
                        ))
                    }
                })
                .try_collect()
                .map(|variants| ctx.intern(Type::Enum(variants)))
        }
        (Type::Tuple(elems_expected), Type::Tuple(elems_found), _) => {
            let len_expected = elems_expected.len();
            let len_found = elems_found.len();
            if len_expected == len_found {
                zip_eq(elems_expected, elems_found)
                    .map(|(elem_expected, elem_found)| {
                        expect_type(elem_expected, elem_found, subtype, ctx)
                    })
                    .try_collect()
                    .map(|elems| ctx.intern(Type::Tuple(elems)))
            } else {
                Err(format!(
                    "tuples have different lengths\n\
                    expected tuple with length {len_expected}: {}\n\
                    found    tuple with length {len_found   }: {}",
                    expected.display(ctx)?,
                    found.display(ctx)?
                ))
            }
        }
        (Type::Bool, Type::Bool, _)
        | (Type::Any, _, true)
        | (_, Type::Any, false)
        | (_, Type::Never, true)
        | (Type::Never, _, false) => Ok(found),
        (_, Type::Any, true) | (Type::Any, _, false) => Err("_ is the any type: \
            it has no supertypes bar itself and cannot be constructed (directly)"
            .to_string()),
        (Type::Never, _, true) | (_, Type::Never, false) => Err("! is the never type: \
            it has no subtypes bar itself and cannot be constructed"
            .to_string()),
        // not using _ to avoid catching more cases than intended
        (Type::Arr { .. } | Type::Enum(..) | Type::Tuple(..) | Type::Bool, _, _) => {
            Err("types are incompatible".to_string())
        }
    }
    .map_err(try_prepend(|| {
        Ok(format!(
            "expected (or a {relation} of):\n\
            |   {}\n\
            found:\n\
            |   {}",
            expected.display(ctx)?,
            found.display(ctx)?
        ))
    }))
}

impl<'a> TyBounds<'a> {
    /// Checks whether `found` can be used in place of `expected`.
    /// `encloses` determines whether `found` should be allowed to enclose
    /// `expected` or vice versa.
    ///
    /// NB. encloses ~= subtype
    pub(super) fn expect_bounds<'inn>(
        expected: &Self,
        found: &Self,
        encloses: bool,
        ctx: &ctx!(),
    ) -> Result<(), TypeCheckError>
    where
        'a: 'inn,
    {
        // whether order is swapped between (expected, self) and (inner, outer)
        // ie. swapped: (expected, self) == (outer, inner)
        //    !swapped: (expected, self) == (inner, outer)
        let swapped = !encloses;
        fn inner_outer_of<T>(expected: T, found: T, swapped: bool) -> (T, T) {
            maybe_swap(expected, found, swapped)
        }
        fn exp_found_of<T>(inner: T, outer: T, swapped: bool) -> (T, T) {
            maybe_swap(inner, outer, swapped)
        }

        let (inner, outer) = inner_outer_of(expected, found, swapped);

        if let Some(upper_outer) = outer.get_upper(ctx).not_any() {
            let upper_inner = inner.get_upper(ctx);
            let (upper_expected, upper_found) = exp_found_of(upper_inner, upper_outer, swapped);
            expect_type(upper_expected, upper_found, !encloses, ctx).map_err(try_prepend(
                || {
                    Ok(format!(
                        "expected upper bound (or {}):\n\
                        {}\n\
                        found upper bound:\n\
                        {}",
                        if encloses { "higher" } else { "lower" },
                        upper_expected.display(ctx)?,
                        upper_found.display(ctx)?
                    ))
                },
            ))?;
        }

        if let Some(lower_outer) = outer.get_lower(ctx).not_never() {
            let lower_inner = inner.get_lower(ctx);
            let (lower_expected, lower_found) = exp_found_of(lower_inner, lower_outer, swapped);
            expect_type(lower_expected, lower_found, encloses, ctx).map_err(try_prepend(|| {
                Ok(format!(
                    "expected lower bound (or {}):\n\
                    {}\n\
                    found lower bound:\n\
                    {}",
                    if encloses { "lower" } else { "higher" },
                    lower_expected.display(ctx)?,
                    lower_found.display(ctx)?
                ))
            }))?;
        }
        Ok(())
    }
}
