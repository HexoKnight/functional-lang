use itertools::{Itertools, zip_eq};

use crate::{
    reprs::common::Lvl,
    typing::{
        InternedType, TypeCheckError,
        context::{ContextInner, TyArenaContext, TyVarContext},
        prepend, try_prepend,
        ty::{TyBounds, TyDisplay, Type},
        ty_eq,
    },
};

use self::{context::Context, inference::TyVar};

#[macro_use]
mod context {
    use std::collections::HashMap;

    use crate::{
        reprs::common::Lvl,
        typing::{
            TypeCheckError,
            context::{ContextInner, Stack, TyArenaContext, TyVarContext, TyVarStack},
            subtyping::inference::{TyConstraint, TyVar},
            ty::TyBounds,
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

    #[must_use]
    #[derive(Clone)]
    pub(super) struct Context<'a, 'inn> {
        inner: &'inn ContextInner<'a>,

        orignial_stack_depth: Lvl,
        expected_ty_var_stack: Stack<(&'a str, TyBounds<'a>)>,
        found_ty_var_stack: Stack<(&'a str, TyVar<'a>)>,

        /// maps `expected_..` levels to `found_..` `TyVar::Unbound` levels
        unbound_map: HashMap<Lvl, Lvl>,
    }

    impl<'a, 'inn> Context<'a, 'inn> {
        pub(super) fn from(ctx: &ctx!()) -> Self {
            let expected_ty_var_stack: Vec<_> = ctx.get_ty_vars().collect();
            Self {
                inner: ctx.get_inner(),
                orignial_stack_depth: Lvl::get_depth(&expected_ty_var_stack),
                expected_ty_var_stack,
                found_ty_var_stack: ctx
                    .get_ty_vars()
                    .map(|(name, ty_var)| (name, TyVar::Unbound(ty_var)))
                    .collect(),
                unbound_map: HashMap::new(),
            }
        }
    }

    impl<'a, 'inn> TyArenaContext<'a> for Context<'a, 'inn> {
        type Inner = &'inn ContextInner<'a>;

        fn get_inner(&self) -> &'inn ContextInner<'a> {
            self.inner
        }
    }

    impl<'a> Context<'a, '_> {
        pub(super) fn push_unbound_ty_var(
            &self,
            ty_var_name_expected: &'a str,
            ty_var_name_found: &'a str,
            ty_var: TyBounds<'a>,
        ) -> Self {
            let mut new = self.clone();

            let expected_level = Lvl::get_depth(&new.expected_ty_var_stack);
            let found_level = Lvl::get_depth(&new.found_ty_var_stack);

            new.expected_ty_var_stack
                .push((ty_var_name_expected, ty_var));
            new.found_ty_var_stack
                .push((ty_var_name_found, TyVar::Unbound(ty_var)));
            new.unbound_map.insert(expected_level, found_level);
            new
        }

        pub(super) fn push_inferred_ty_var(
            &self,
            ty_var_name: &'a str,
            initial_bounds: TyBounds<'a>,
        ) -> (Self, TyConstraint<'a>) {
            let constraint = TyConstraint::from_bounds(initial_bounds, self);

            let mut new = self.clone();

            new.found_ty_var_stack
                .push((ty_var_name, TyVar::Inferred(constraint.clone())));

            (new, constraint)
        }

        pub(super) fn map_expected_level(&self, level: Lvl) -> Result<Lvl, TypeCheckError> {
            if level.deeper_than(Lvl::get_depth(&self.expected_ty_var_stack)) {
                // bound after current context so we just move up
                level
                    .translate(
                        Lvl::get_depth(&self.expected_ty_var_stack),
                        Lvl::get_depth(&self.found_ty_var_stack),
                    )
                    .ok_or_else(|| {
                        format!(
                            "illegal failure: expected stack is larger than found stack: {level:?}"
                        )
                    })
            } else if level.deeper_than(self.orignial_stack_depth) {
                // bound after the original stack so we can use unbound_map to translate
                self.unbound_map.get(&level).copied().ok_or_else(|| {
                    format!(
                        "illegal failure: subtype-captured type variable level not found: {level:?}"
                    )
                })
            } else {
                // bound in the original stack so no translation necessary
                Ok(level)
            }
        }

        pub(super) fn get_expected_ty_var(&self, level: Lvl) -> Option<(&'a str, TyBounds<'a>)> {
            level.get(&self.expected_ty_var_stack).copied()
        }

        pub(super) fn get_found_ty_var(&self, level: Lvl) -> Option<(&'a str, &TyVar<'a>)> {
            level
                .get(&self.found_ty_var_stack)
                .map(|(name, ty_var)| (*name, ty_var))
        }

        pub(super) fn get_expected_ty_var_unwrap(
            &self,
            level: Lvl,
        ) -> Result<(&'a str, TyBounds<'a>), TypeCheckError> {
            self.get_expected_ty_var(level).ok_or_else(|| {
                format!("illegal failure: expected type variable level not found: {level:?}")
            })
        }

        pub(super) fn get_found_ty_var_unwrap(
            &self,
            level: Lvl,
        ) -> Result<(&'a str, &TyVar<'a>), TypeCheckError> {
            self.get_found_ty_var(level).ok_or_else(|| {
                format!("illegal failure: found type variable level not found: {level:?}")
            })
        }

        pub(super) fn next_found_ty_var_level(&self) -> Lvl {
            Lvl::get_depth(&self.found_ty_var_stack)
        }

        pub(super) fn exp_ctx(&self) -> TyVarStack<'a, ()> {
            self.expected_ty_var_stack
                .iter()
                .map(|(name, _)| (*name, ()))
                .collect()
        }

        pub(super) fn fnd_ctx(&self) -> TyVarStack<'a, ()> {
            self.found_ty_var_stack
                .iter()
                .map(|(name, _)| (*name, ()))
                .collect()
        }

        pub(super) fn fnd_ctx_without_inferred(&self) -> TyVarStack<'a, TyBounds<'a>> {
            self.found_ty_var_stack
                .iter()
                .map(|(name, ty_var)| (*name, ty_var.get_bounds()))
                .collect()
        }

        /// Returns whether the expected and found ty var stacks are the same (have not diverged).
        pub(super) fn ty_vars_same(&self) -> bool {
            // the ty_var stacks diverge iff an inferred ty_var is pushed,
            // which causes the sizes of the stacks to differ
            self.expected_ty_var_stack.len() != self.found_ty_var_stack.len()
        }
    }
}

mod inference {
    use std::{cell::RefCell, iter::Sum, rc::Rc};

    use crate::{
        reprs::common::Lvl,
        typing::{
            InternedType, TypeCheckError,
            context::{MultiContext, TyArenaContext},
            merge::{join, meet},
            prepend,
            subtyping::{Context, expect_type_rec},
            ty::{TyBounds, Type},
            ty_eq,
        },
    };

    #[derive(Clone)]
    pub(super) enum TyVar<'a> {
        Unbound(TyBounds<'a>),
        Inferred(TyConstraint<'a>),
    }

    impl<'a> TyVar<'a> {
        pub(super) fn get_bounds(&self) -> TyBounds<'a> {
            match self {
                TyVar::Unbound(bounds) => *bounds,
                TyVar::Inferred(constraint) => constraint.initial_bounds(),
            }
        }
    }

    #[derive(Clone)]
    pub(super) struct TyConstraint<'a>(Rc<RefCell<TyConstraintInner<'a>>>);

    #[derive(Copy, Clone)]
    struct TyConstraintInner<'a> {
        initial_bounds: TyBounds<'a>,

        upper: InternedType<'a>,
        lower: InternedType<'a>,
    }

    impl<'a> TyConstraint<'a> {
        pub(super) fn from_bounds(
            initial_bounds: TyBounds<'a>,
            ctx: &impl TyArenaContext<'a>,
        ) -> Self {
            let TyBounds { upper: _, lower: _ } = initial_bounds;

            Self(Rc::new(RefCell::new(TyConstraintInner {
                initial_bounds,
                upper: initial_bounds.get_upper(ctx),
                lower: initial_bounds.get_lower(ctx),
            })))
        }

        pub(super) fn constrain(
            &self,
            level: Lvl,
            expected: InternedType<'a>,
            subtype: bool,
            ctx: &Context<'a, '_>,
        ) -> Result<(), TypeCheckError> {
            fn map_vars<'a>(
                ty: InternedType<'a>,
                get_bound: impl Fn(TyBounds<'a>) -> InternedType<'a>,
                level: Lvl,
                ctx: &Context<'a, '_>,
            ) -> Result<InternedType<'a>, TypeCheckError> {
                ty.try_map_ty_vars::<TypeCheckError>(
                    &mut |level_expected| {
                        // we convert from the expected stack to the found stack
                        let level_found = ctx.map_expected_level(level_expected)?;
                        if level_found.deeper_than(level) {
                            // replace any ty_vars bound more recently than the current (inclusive)
                            // with their upper/lower bound
                            // this weakens our inferencing ability but prevents cyclic bounds that
                            // we currently can't deal with
                            let (_, found) = ctx.get_found_ty_var_unwrap(level_found)?;
                            Ok(get_bound(found.get_bounds()))
                        } else {
                            Ok(ctx.intern(Type::TyVar(level_found)))
                        }
                    },
                    ctx,
                )
            }

            let merge_ctx = MultiContext(ctx.get_inner(), ctx.fnd_ctx_without_inferred());

            if subtype {
                let upper = map_vars(expected, |bounds| bounds.get_lower(ctx), level, ctx)?;

                let current_upper = self.0.borrow().upper;
                let new_upper = meet([upper, current_upper], &merge_ctx)?;
                self.0.borrow_mut().upper = new_upper;
            } else {
                let lower = map_vars(expected, |bounds| bounds.get_upper(ctx), level, ctx)?;

                let current_lower = self.0.borrow().lower;
                let new_lower = join([lower, current_lower], &merge_ctx)?;
                self.0.borrow_mut().lower = new_lower;
            }

            Ok(())
        }

        fn initial_bounds(&self) -> TyBounds<'a> {
            self.0.borrow().initial_bounds
        }

        pub(super) fn satisfy(
            self,
            variance: Variance,
            subtype: bool,
            ctx: &Context<'a, '_>,
        ) -> Result<InternedType<'a>, TypeCheckError> {
            let num_refs = Rc::strong_count(&self.0);
            let Some(inner_cell) = Rc::into_inner(self.0) else {
                // this is not strictly necessary but it failing is a pretty good indicator that
                // something is up
                return Err(format!(
                    "illegal failure: not all TyContraint references have been dropped before satisfaction: {num_refs}",
                ));
            };
            let TyConstraintInner {
                initial_bounds,
                upper,
                lower,
            } = inner_cell.into_inner();

            // again, should just be an optimisation
            if ty_eq(upper, lower) {
                return Ok(upper);
            }

            // technically we don't really expect either but this is close enough
            expect_type_rec(upper, lower, true, false, ctx)
                .map_err(prepend(|| "unable to satisfy constraints"))?;

            debug_assert_eq!(
                expect_type_rec(initial_bounds.get_upper(ctx), upper, true, false, ctx).map(|_| ()),
                Ok(())
            );
            debug_assert_eq!(
                expect_type_rec(initial_bounds.get_lower(ctx), lower, false, false, ctx)
                    .map(|_| ()),
                Ok(())
            );

            match (variance, subtype) {
                // the best type would be the smallest one
                (Variance::Covariant, true) | (Variance::Contravariant, false) => Ok(lower),
                // the best type would be the largest one
                (Variance::Covariant, false) | (Variance::Contravariant, true) => Ok(upper),
                (
                    // constant: means the type is not mentioned
                    // so it doesn't matter which bound we choose
                    //
                    // invariant: there is no best type so we just try our best,
                    // though this may need to become a hard error in the future
                    Variance::Constant | Variance::Invariant,
                    subtype,
                ) => {
                    if matches!(upper, Type::Any) {
                        Ok(lower)
                    } else if matches!(lower, Type::Never) {
                        Ok(upper)
                    } else if subtype {
                        Ok(lower)
                    } else {
                        Ok(upper)
                    }
                }
            }
        }
    }

    #[derive(Copy, Clone)]
    pub(super) enum Variance {
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
        pub(super) fn get_variance_of(&self, ty_var_level: Lvl) -> Variance {
            match self {
                Type::TyAbs {
                    name: _,
                    bounds: TyBounds { upper, lower },
                    result,
                } => [
                    // TODO: test
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
                Type::Bool | Type::Any | Type::Never => Variance::Constant,
            }
        }
    }
}

fn maybe_swap<T>(a: T, b: T, swap: bool) -> (T, T) {
    if swap { (b, a) } else { (a, b) }
}

pub(super) fn expect_type<'a: 'inn, 'inn>(
    expected: InternedType<'a>,
    found: InternedType<'a>,
    subtype: bool,
    infer_ty_args: bool,
    ctx: &ctx!(),
) -> Result<InternedType<'a>, TypeCheckError> {
    expect_type_rec(expected, found, subtype, infer_ty_args, &Context::from(ctx))
}

/// Checks whether `found` can be used in place of `expected`.
/// Returns the type that `found` would have if so.
/// `subtype` determines whether `found` should be allowed to be a subtype
/// of `expected` or vice versa.
///
/// # Errors
/// returns Err when not subtype
fn expect_type_rec<'a>(
    expected: InternedType<'a>,
    found: InternedType<'a>,
    subtype: bool,
    infer_ty_args: bool,
    ctx: &Context<'a, '_>,
) -> Result<InternedType<'a>, TypeCheckError> {
    fn super_sub_of<T>(expected: T, found: T, swapped: bool) -> (T, T) {
        maybe_swap(expected, found, swapped)
    }
    fn exp_found_of<T>(sup: T, sub: T, swapped: bool) -> (T, T) {
        maybe_swap(sup, sub, swapped)
    }
    // whether order is swapped between (expected, found) and (super, sub)
    // ie. swapped: (expected, found) == (sub, super)
    //    !swapped: (expected, found) == (super, sub)
    let swapped = !subtype;

    // comparing types for equality is only valid when in the same context
    if ctx.ty_vars_same() && ty_eq(expected, found) {
        return Ok(found);
    }

    let relation = if subtype { "subtype" } else { "supertype" };

    match (expected, found, subtype) {
        (Type::Bool, Type::Bool, _)
        | (Type::Any, _, true)
        | (_, Type::Any, false)
        | (_, Type::Never, true)
        | (Type::Never, _, false) => Ok(found),

        (
            Type::TyAbs {
                name: name_expected,
                bounds: bounds_expected,
                result: result_expected,
            },
            Type::TyAbs {
                name: name_found,
                bounds: bounds_found,
                result: result_found,
            },
            _,
        ) => {
            // subtype bounds must enclose supertype bounds
            TyBounds::expect_bounds_rec(bounds_expected, bounds_found, subtype, ctx)
                .map_err(prepend(|| {
                    "bounds of subtype type arg must enclose those of the supertype type arg:"
                        .to_string()
                }))
                .and_then(|()| {
                    let (bounds_super, ctx_super) = if swapped {
                        (bounds_found, ctx.fnd_ctx())
                    } else {
                        (bounds_expected, ctx.exp_ctx())
                    };
                    expect_type_rec(
                        result_expected,
                        result_found,
                        subtype,
                        infer_ty_args,
                        // we choose the narrower bounds
                        &ctx.push_unbound_ty_var(name_expected, name_found, *bounds_super),
                    )
                    .map(|result| {
                        ctx.intern(Type::TyAbs {
                            name: name_found,
                            bounds: *bounds_super,
                            result,
                        })
                    })
                    .map_err(try_prepend(|| {
                        Ok(format!(
                            "taking {} == {} with bounds: {}",
                            name_expected,
                            name_found,
                            bounds_super.display(ctx_super)?
                        ))
                    }))
                })
        }
        (
            expected,
            Type::TyAbs {
                name,
                bounds,
                result: found,
            },
            _,
        ) => {
            if !infer_ty_args {
                return Err(format!(
                    "failed to infer type argument: {name}\n\
                    not allowed to infer type arguments in this position"
                ));
            }
            let (ctx_, constraint) = ctx.push_inferred_ty_var(name, *bounds);
            expect_type_rec(expected, found, subtype, true, &ctx_).and_then(|result| {
                drop(ctx_);
                let level = ctx.next_found_ty_var_level();
                let variance = result.get_variance_of(level);
                let satisfy_result = constraint.satisfy(variance, subtype, ctx);
                match satisfy_result {
                    Ok(ty_arg @ Type::Never) => Err(format!(
                        "failed to infer type argument: {name}\n\
                        note: inferred {} but that is typically incorrect",
                        ty_arg.display(ctx.fnd_ctx())?
                    )),
                    Ok(ty_arg) => Ok(result.substitute_ty_var(level, ty_arg, ctx)),
                    Err(mut e) => {
                        e.insert_str(0, &format!("failed to infer type argument: {name}\n"));
                        Err(e)
                    }
                }
            })
        }
        (Type::TyVar(level_expected), Type::TyVar(level_found), _) => {
            let mapped_level_expected = ctx.map_expected_level(*level_expected)?;
            if mapped_level_expected == *level_found {
                Ok(found)
            } else if mapped_level_expected.deeper_than(*level_found) {
                // if levels are not equal (as above), we 'instantiate' the deeper ty_var first to avoid
                // cyclic dependency issues (as earlier ty_vars cannot reference later ones)
                handle_expected_ty_var(expected, found, *level_expected, subtype, ctx)
            } else {
                handle_found_ty_var(expected, found, *level_found, subtype, ctx)
            }
        }
        (Type::TyVar(level_expected), found, _) => {
            handle_expected_ty_var(expected, found, *level_expected, subtype, ctx)
        }
        (expected, Type::TyVar(level_found), _) => {
            handle_found_ty_var(expected, found, *level_found, subtype, ctx)
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
                arg: expect_type_rec(arg_expected, arg_found, !subtype, false, ctx)?,
                result: expect_type_rec(res_expected, res_found, subtype, infer_ty_args, ctx)?,
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
                        Ok((
                            *l,
                            expect_type_rec(ty_expected, ty_found, subtype, infer_ty_args, ctx)?,
                        ))
                    } else {
                        let (ty_super, ctx_super) = if swapped {
                            (found, ctx.fnd_ctx())
                        } else {
                            (expected, ctx.exp_ctx())
                        };
                        Err(format!(
                            "label '{l}' missing from supertype:\n\
                            | {}",
                            ty_super.display(ctx_super)?
                        ))
                    }
                })
                .try_collect()
                .map(|variants| ctx.intern(Type::Enum(variants)))
        }
        (Type::Record(fields_expected), Type::Record(fields_found), _) => {
            let (fields_super, fields_sub) = super_sub_of(fields_expected, fields_found, swapped);
            fields_super
                .0
                .iter()
                // for each field of the supertype:
                .map(|(l, ty_super)| {
                    // check that the subtype also has it...
                    if let Some(ty_sub) = fields_sub.0.get(l) {
                        let (ty_expected, ty_found) = exp_found_of(ty_super, ty_sub, swapped);
                        // and that the field types maintain the same subtyping relationship
                        Ok((
                            *l,
                            expect_type_rec(ty_expected, ty_found, subtype, infer_ty_args, ctx)?,
                        ))
                    } else {
                        let (ty_sub, ctx_sub) = if swapped {
                            (expected, ctx.exp_ctx())
                        } else {
                            (found, ctx.fnd_ctx())
                        };
                        Err(format!(
                            "label '{l}' missing from subtype:\n\
                            | {}",
                            ty_sub.display(ctx_sub)?
                        ))
                    }
                })
                .try_collect()
                .map(|fields| ctx.intern(Type::Record(fields)))
        }
        (Type::Tuple(elems_expected), Type::Tuple(elems_found), _) => {
            let len_expected = elems_expected.len();
            let len_found = elems_found.len();
            if len_expected == len_found {
                zip_eq(elems_expected, elems_found)
                    .map(|(elem_expected, elem_found)| {
                        expect_type_rec(elem_expected, elem_found, subtype, infer_ty_args, ctx)
                    })
                    .try_collect()
                    .map(|elems| ctx.intern(Type::Tuple(elems)))
            } else {
                Err(format!(
                    "tuples have different lengths\n\
                    expected tuple with length {len_expected}: {}\n\
                    found    tuple with length {len_found   }: {}",
                    expected.display(ctx.exp_ctx())?,
                    found.display(ctx.fnd_ctx())?
                ))
            }
        }
        (_, Type::Any, true) | (Type::Any, _, false) => Err("_ is the any type: \
            it has no supertypes bar itself and cannot be constructed (directly)"
            .to_string()),
        (Type::Never, _, true) | (_, Type::Never, false) => Err("! is the never type: \
            it has no subtypes bar itself and cannot be constructed"
            .to_string()),
        // not using _ to avoid catching more cases than intended
        (
            Type::TyAbs { .. }
            | Type::Arr { .. }
            | Type::Enum(..)
            | Type::Record(..)
            | Type::Tuple(..)
            | Type::Bool,
            Type::Arr { .. } | Type::Enum(..) | Type::Record(..) | Type::Tuple(..) | Type::Bool,
            _,
        ) => Err("types are incompatible".to_string()),
    }
    .map_err(try_prepend(|| {
        Ok(format!(
            "expected (or a {relation} of):\n\
            |   {}\n\
            found:\n\
            |   {}",
            expected.display(ctx.exp_ctx())?,
            found.display(ctx.fnd_ctx())?
        ))
    }))
}

fn handle_found_ty_var<'a>(
    expected: InternedType<'a>,
    found: InternedType<'a>,
    level_found: Lvl,
    subtype: bool,
    ctx: &Context<'a, '_>,
) -> Result<InternedType<'a>, TypeCheckError> {
    let (_, var_found) = ctx.get_found_ty_var_unwrap(level_found)?;
    match var_found {
        TyVar::Unbound(bounds_found) => {
            let upper_found = bounds_found.get_upper(ctx);
            // a type is guaranteed to be a supertype of the instantiated type iff it is a
            // supertype of the upper bound (due to the transitivity of subtyping)
            expect_type_rec(expected, upper_found, subtype, false, ctx).map_err(try_prepend(
                || {
                    Ok(format!(
                        "subtyping must be guaranteed \
                        for all possible instantiations of type var: {}\n\
                        for example, one such instantiation is: {}",
                        found.display(ctx.fnd_ctx())?,
                        upper_found.display(ctx.fnd_ctx())?
                    ))
                },
            ))?;
        }
        TyVar::Inferred(ty_constraint) => {
            ty_constraint.constrain(level_found, expected, subtype, ctx)?;
        }
    }
    Ok(found)
}

fn handle_expected_ty_var<'a>(
    expected: InternedType<'a>,
    found: InternedType<'a>,
    level_expected: Lvl,
    subtype: bool,
    ctx: &Context<'a, '_>,
) -> Result<InternedType<'a>, TypeCheckError> {
    let (_, bounds_expected) = ctx.get_expected_ty_var_unwrap(level_expected)?;
    let lower_expected = bounds_expected.get_lower(ctx);
    // a type is guaranteed to be a subtype of the instantiated type iff it is a
    // subtype of the lower bound (due to the transitivity of subtyping)
    expect_type_rec(lower_expected, found, subtype, false, ctx).map_err(try_prepend(|| {
        Ok(format!(
            "subtyping must be guaranteed \
            for all possible instantiations of type var: {}\n\
            for example, one such instantiation is: {}",
            expected.display(ctx.exp_ctx())?,
            lower_expected.display(ctx.exp_ctx())?
        ))
    }))
}

impl<'a> TyBounds<'a> {
    pub(super) fn expect_bounds<'inn>(
        expected: &Self,
        found: &Self,
        encloses: bool,
        ctx: &ctx!(),
    ) -> Result<(), TypeCheckError>
    where
        'a: 'inn,
    {
        Self::expect_bounds_rec(expected, found, encloses, &Context::from(ctx))
    }

    /// Checks whether `found` can be used in place of `expected`.
    /// `encloses` determines whether `found` should be allowed to enclose
    /// `expected` or vice versa.
    ///
    /// NB. encloses ~= subtype
    fn expect_bounds_rec(
        expected: &Self,
        found: &Self,
        encloses: bool,
        ctx: &Context<'a, '_>,
    ) -> Result<(), TypeCheckError> {
        fn inner_outer_of<T>(expected: T, found: T, swapped: bool) -> (T, T) {
            maybe_swap(expected, found, swapped)
        }
        fn exp_found_of<T>(inner: T, outer: T, swapped: bool) -> (T, T) {
            maybe_swap(inner, outer, swapped)
        }
        // whether order is swapped between (expected, self) and (inner, outer)
        // ie. swapped: (expected, self) == (outer, inner)
        //    !swapped: (expected, self) == (inner, outer)
        let swapped = !encloses;

        let (inner, outer) = inner_outer_of(expected, found, swapped);

        if let Some(upper_outer) = outer.get_upper(ctx).not_any() {
            let upper_inner = inner.get_upper(ctx);
            let (upper_expected, upper_found) = exp_found_of(upper_inner, upper_outer, swapped);
            expect_type_rec(upper_expected, upper_found, !encloses, false, ctx).map_err(
                try_prepend(|| {
                    Ok(format!(
                        "expected upper bound (or {}):\n\
                        {}\n\
                        found upper bound:\n\
                        {}",
                        if encloses { "higher" } else { "lower" },
                        upper_expected.display(ctx.exp_ctx())?,
                        upper_found.display(ctx.fnd_ctx())?
                    ))
                }),
            )?;
        }

        if let Some(lower_outer) = outer.get_lower(ctx).not_never() {
            let lower_inner = inner.get_lower(ctx);
            let (lower_expected, lower_found) = exp_found_of(lower_inner, lower_outer, swapped);
            expect_type_rec(lower_expected, lower_found, encloses, false, ctx).map_err(
                try_prepend(|| {
                    Ok(format!(
                        "expected lower bound (or {}):\n\
                        {}\n\
                        found lower bound:\n\
                        {}",
                        if encloses { "lower" } else { "higher" },
                        lower_expected.display(ctx.exp_ctx())?,
                        lower_found.display(ctx.fnd_ctx())?
                    ))
                }),
            )?;
        }
        Ok(())
    }
}
