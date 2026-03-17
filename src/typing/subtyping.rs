use itertools::{Itertools, zip_eq};

use crate::typing::{
    EffVar, InternedType, TyConfig, TyEffLvl, TyVar,
    context::TyArenaContext,
    effects::Effect,
    error::{ContextError, IllegalError, PlainContextError, TypeCheckResult},
    subtyping::inference::InferenceEffVar,
    ty::{TyBounds, TyDisplay, Type},
    ty_eq,
};

use self::{context::Context, inference::InferenceTyVar};

#[macro_use]
mod context {
    use std::collections::HashMap;

    use crate::{
        reprs::common::Lvl,
        typing::{
            EffVar, TyEffLvl, TyVar,
            context::{ContextInner, EffVarStack, Stack, TyArenaContext, TyVarStack, unwrap_get},
            error::IllegalError,
            subtyping::inference::{EffConstraint, InferenceEffVar, InferenceTyVar, TyConstraint},
            ty::TyBounds,
        },
    };

    #[derive(Clone)]
    struct FndExpStacks<'a, T: FndExpStacksItem> {
        original_stack_depth: Lvl,
        expected_stack: Stack<(&'a str, T)>,
        found_stack: Stack<(&'a str, T)>,
        /// maps `expected_..` levels to `found_..` `Unbound` levels
        unbound_map: HashMap<Lvl, Lvl>,
    }

    trait FndExpStacksItem: Clone {
        const KIND_NAME: &'static str;
    }

    impl<'a> FndExpStacksItem for InferenceTyVar<'a> {
        const KIND_NAME: &'static str = "type variable";
    }
    impl<'a> FndExpStacksItem for InferenceEffVar<'a> {
        const KIND_NAME: &'static str = "effect variable";
    }

    impl<'a, T: FndExpStacksItem> FndExpStacks<'a, T> {
        fn from(stack: Stack<(&'a str, T)>) -> Self {
            Self {
                original_stack_depth: Lvl::get_depth(&stack),
                expected_stack: stack.clone(),
                found_stack: stack,
                unbound_map: HashMap::new(),
            }
        }

        fn push_both(
            &mut self,
            name_expected: &'a str,
            name_found: &'a str,
            expected: T,
            found: T,
        ) {
            let expected_level = Lvl::get_depth(&self.expected_stack);
            let found_level = Lvl::get_depth(&self.found_stack);

            self.expected_stack.push((name_expected, expected));
            self.found_stack.push((name_found, found));
            self.unbound_map.insert(expected_level, found_level);
        }

        fn push_found(&mut self, name: &'a str, found: T) {
            self.found_stack.push((name, found));
        }

        pub(super) fn map_expected_level(&self, level: Lvl) -> Result<Lvl, IllegalError<'static>> {
            if let Some(deeper) = level.get_deeper_than(Lvl::get_depth(&self.expected_stack)) {
                // bound after current context so we just move up
                Ok(Lvl::get_depth(&self.found_stack).deeper_by(deeper))
            } else if level.deeper_than(self.original_stack_depth) {
                // bound after the original stack so we can use unbound_map to translate
                self.unbound_map.get(&level).copied().ok_or_else(|| {
                    IllegalError::new(
                        format!(
                            "subtype-captured {} level not found: {level:?}",
                            T::KIND_NAME
                        ),
                        None,
                    )
                })
            } else {
                // bound in the original stack so no translation necessary
                Ok(level)
            }
        }

        pub(super) fn get_expected(&self, level: Lvl) -> Option<(&'a str, &T)> {
            level.get(&self.expected_stack).map(|(name, t)| (*name, t))
        }
        pub(super) fn get_found(&self, level: Lvl) -> Option<(&'a str, &T)> {
            level.get(&self.found_stack).map(|(name, t)| (*name, t))
        }

        #[track_caller]
        pub(super) fn get_expected_unwrap(
            &self,
            level: Lvl,
        ) -> Result<(&'a str, &T), IllegalError<'static>> {
            unwrap_get(
                self.get_expected(level),
                &format!("expected {}", T::KIND_NAME),
                level,
            )
        }
        #[track_caller]
        pub(super) fn get_found_unwrap(
            &self,
            level: Lvl,
        ) -> Result<(&'a str, &T), IllegalError<'static>> {
            unwrap_get(
                self.get_found(level),
                &format!("found {}", T::KIND_NAME),
                level,
            )
        }

        pub(super) fn next_expected_level(&self) -> Lvl {
            Lvl::get_depth(&self.expected_stack)
        }
        pub(super) fn next_found_level(&self) -> Lvl {
            Lvl::get_depth(&self.found_stack)
        }

        fn fnd_as_exp(&self) -> Self {
            Self {
                original_stack_depth: Lvl::get_depth(&self.found_stack),
                expected_stack: self.found_stack.clone(),
                found_stack: self.found_stack.clone(),
                unbound_map: HashMap::new(),
            }
        }

        /// Returns whether the expected and found stacks are the same (have not diverged).
        pub(super) fn stacks_same(&self) -> bool {
            // the stacks diverge iff a single found is pushed,
            // which causes the sizes of the stacks to differ
            self.expected_stack.len() != self.found_stack.len()
        }
    }

    #[must_use]
    #[derive(Clone)]
    pub(super) struct Context<'a, 'inn> {
        inner: &'inn ContextInner<'a>,

        pub ty_vars: FndExpStacks<'a, InferenceTyVar<'a>>,
        pub eff_vars: FndExpStacks<'a, InferenceEffVar<'a>>,
    }

    impl<'a, 'inn> Context<'a, 'inn> {
        pub(super) fn from(ctx: &ctx!(arena 'inn; ty_var; eff_var)) -> Self {
            let ty_var_stack: Vec<_> = ctx
                .get_ty_vars()
                .map(|(name, ty_var)| (name, InferenceTyVar::TyVar(ty_var)))
                .collect();
            let eff_var_stack: Vec<_> = ctx
                .get_eff_vars()
                .map(|(name, eff_var)| (name, InferenceEffVar::EffVar(eff_var)))
                .collect();
            Self {
                inner: ctx.get_inner(),

                ty_vars: FndExpStacks::from(ty_var_stack),
                eff_vars: FndExpStacks::from(eff_var_stack),
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
        pub(super) fn push_ty_var(
            &self,
            ty_var_name_expected: &'a str,
            ty_var_name_found: &'a str,
            ty_var_expected: TyVar<'a>,
            ty_var_found: TyVar<'a>,
        ) -> Self {
            let mut new = self.clone();

            new.ty_vars.push_both(
                ty_var_name_expected,
                ty_var_name_found,
                InferenceTyVar::TyVar(ty_var_expected),
                InferenceTyVar::TyVar(ty_var_found),
            );

            new
        }

        pub(super) fn push_fnd_inferred_ty_var(
            &self,
            ty_var_name: &'a str,
            initial_bounds: TyBounds<'a>,
        ) -> (Self, TyConstraint<'a>) {
            let constraint =
                TyConstraint::from_bounds(initial_bounds, self.eff_vars.next_found_level(), self);

            let mut new = self.clone();

            new.ty_vars
                .push_found(ty_var_name, InferenceTyVar::Inferred(constraint.clone()));

            (new, constraint)
        }

        pub(super) fn push_eff_var(
            &self,
            eff_var_name_expected: &'a str,
            eff_var_name_found: &'a str,
            eff_var_expected: EffVar<'a>,
            eff_var_found: EffVar<'a>,
        ) -> Self {
            let mut new = self.clone();

            new.eff_vars.push_both(
                eff_var_name_expected,
                eff_var_name_found,
                InferenceEffVar::EffVar(eff_var_expected),
                InferenceEffVar::EffVar(eff_var_found),
            );

            new
        }

        pub(super) fn push_fnd_inferred_eff_var(
            &self,
            eff_var_name: &'a str,
        ) -> (Self, EffConstraint<'a>) {
            let constraint = EffConstraint::from_bounds(self.eff_vars.next_found_level(), self);

            let mut new = self.clone();

            new.eff_vars
                .push_found(eff_var_name, InferenceEffVar::Inferred(constraint.clone()));

            (new, constraint)
        }

        pub(super) fn next_found_ty_eff_level(&self) -> TyEffLvl {
            TyEffLvl {
                ty: self.ty_vars.next_found_level(),
                eff: self.eff_vars.next_found_level(),
            }
        }
        pub(super) fn next_expected_ty_eff_level(&self) -> TyEffLvl {
            TyEffLvl {
                ty: self.ty_vars.next_expected_level(),
                eff: self.eff_vars.next_expected_level(),
            }
        }

        pub(super) fn exp_ctx(&self) -> TyVarStack<'a, ()> {
            self.ty_vars
                .expected_stack
                .iter()
                .map(|(name, _)| (*name, ()))
                .collect()
        }

        pub(super) fn fnd_ctx(&self) -> TyVarStack<'a, ()> {
            self.ty_vars
                .found_stack
                .iter()
                .map(|(name, _)| (*name, ()))
                .collect()
        }

        pub(super) fn fnd_ty_vars_without_inferred(&self) -> TyVarStack<'a, TyVar<'a>> {
            self.ty_vars
                .found_stack
                .iter()
                .map(|(name, ty_var)| (*name, ty_var.without_inferred()))
                .collect()
        }
        pub(super) fn fnd_eff_vars_without_inferred(&self) -> EffVarStack<'a, EffVar<'a>> {
            self.eff_vars
                .found_stack
                .iter()
                .map(|(name, eff_var)| (*name, eff_var.without_inferred()))
                .collect()
        }

        pub(super) fn fnd_as_exp(&self) -> Self {
            Self {
                inner: self.inner,

                ty_vars: self.ty_vars.fnd_as_exp(),
                eff_vars: self.eff_vars.fnd_as_exp(),
            }
        }

        /// Returns whether the expected and found * var stacks are the same (have not diverged).
        pub(super) fn vars_same(&self) -> bool {
            self.ty_vars.stacks_same() && self.eff_vars.stacks_same()
        }
    }
}

mod inference {
    use std::{cell::RefCell, rc::Rc};

    use crate::{
        reprs::common::Lvl,
        typing::{
            EffVar, InternedType, MapVars, TyConfig, TyEffLvl, TyVar, Variance,
            context::{MultiContext, TyArenaContext},
            effects::{Effect, EffectGroup},
            error::{ContextError, IllegalError, PlainContextError, TypeCheckResult},
            merge::{join, meet},
            subtyping::{Context, expect_type_rec},
            ty::{TyBounds, TyDisplay, Type},
            ty_eq,
        },
    };

    /// converts an `expected` (at some level) to a `found` at `ty_eff_level`
    /// ie. swapping stacks and 'removing' vars deeper than `ty_eff_level`
    fn map_exp_vars_to_fnd_level<'a, T: MapVars<'a>>(
        expected: T,
        get_bound: impl Fn(TyBounds<'a>) -> InternedType<'a> + Copy,
        ty_eff_level: TyEffLvl,
        ctx: &Context<'a, '_>,
    ) -> Result<T, ContextError<'static>> {
        expected.try_map_vars_no_level::<ContextError<'static>>(
            |level_expected| {
                // we convert from the expected stack to the found stack
                let level_found = ctx.ty_vars.map_expected_level(level_expected)?;
                if !level_found.deeper_than(ty_eff_level.ty) {
                    // bound before `level` so we leave it
                    return Ok(ctx.intern(Type::TyVar(level_found)));
                }
                if let Some(deeper) = level_found.get_deeper_than(ctx.ty_vars.next_found_level()) {
                    // bound within `expected_ty` so we just move to `ty_eff_level`
                    // (the level of the eventual result)
                    return Ok(ctx.intern(Type::TyVar(ty_eff_level.ty.deeper_by(deeper))));
                }
                // replace any bounded/inferred ty_vars bound more recently than the
                // current (inclusive) with their upper/lower bound
                // this weakens our inferencing ability but prevents cyclic bounds that
                // we currently can't deal with
                let (_, found) = ctx.ty_vars.get_found_unwrap(level_found)?;
                match found.without_inferred() {
                    // `Inferred` are converted to `Bounded` so this catches both
                    TyVar::Bounded { bounds, eff_lvl: _ } => {
                        map_exp_vars_to_fnd_level(get_bound(bounds), get_bound, ty_eff_level, ctx)
                    }
                    TyVar::Type { ty, eff_lvl: _ } => {
                        map_exp_vars_to_fnd_level(ty, get_bound, ty_eff_level, ctx)
                    }
                    TyVar::Rec => Err(PlainContextError::new(
                        "unable to satisfy constraint with recursive type variable",
                    ))?,
                }
            },
            |level_expected| {
                // we convert from the expected stack to the found stack
                let level_found = ctx.eff_vars.map_expected_level(level_expected)?;
                if !level_found.deeper_than(ty_eff_level.eff) {
                    // bound before `level` so we leave it
                    return Ok(Effect::Var(level_found));
                }
                if let Some(deeper) = level_found.get_deeper_than(ctx.eff_vars.next_found_level()) {
                    // bound within `expected_ty` so we just move to `ty_eff_level`
                    // (the level of the eventual result)
                    return Ok(Effect::Var(ty_eff_level.eff.deeper_by(deeper)));
                }
                let (_, found) = ctx.eff_vars.get_found_unwrap(level_found)?;
                match found.without_inferred() {
                    EffVar::Effect { effect, ty_lvl: _ } => {
                        map_exp_vars_to_fnd_level(effect, get_bound, ty_eff_level, ctx)
                    }
                    // `Inferred` are converted to `Unbound` so this catches both
                    EffVar::Unbound => Err(PlainContextError::new(
                        "unable to satisfy constraint with unbound effect variable",
                    ))?,
                }
            },
            ctx,
        )
    }

    #[derive(Clone)]
    pub(super) enum InferenceTyVar<'a> {
        TyVar(TyVar<'a>),
        Inferred(TyConstraint<'a>),
    }

    impl<'a> InferenceTyVar<'a> {
        pub(super) fn without_inferred(&self) -> TyVar<'a> {
            match self {
                InferenceTyVar::TyVar(ty_var) => *ty_var,
                InferenceTyVar::Inferred(constraint) => constraint.without_inferred(),
            }
        }
    }

    #[derive(Clone)]
    pub(super) struct TyConstraint<'a>(Rc<RefCell<TyConstraintInner<'a>>>);

    #[derive(Copy, Clone)]
    struct TyConstraintInner<'a> {
        initial_bounds: TyBounds<'a>,
        initial_eff_lvl: Lvl,

        /// the apparent 'variance' according to how the type is (un)constrained
        ///
        /// eg. `T -> T` is invariant in `T`,
        /// but if it is constrained to `bool -> ?`,
        /// then it's unconstrained variance would be covariant,
        /// while if it is constrained to `bool -> bool`,
        /// it's unconstrained variance would be constant,
        ///
        /// it is calculated here assuming an initial `subtype == true`
        /// so must be `.invert()`ed if `!subtype`
        unconstrained_variance: Variance,

        upper: InternedType<'a>,
        lower: InternedType<'a>,
    }

    impl<'a> TyConstraint<'a> {
        pub(super) fn from_bounds(
            initial_bounds: TyBounds<'a>,
            initial_eff_lvl: Lvl,
            ctx: &impl TyArenaContext<'a>,
        ) -> Self {
            Self(Rc::new(RefCell::new(TyConstraintInner {
                initial_bounds,
                initial_eff_lvl,
                unconstrained_variance: Variance::Constant,
                upper: initial_bounds.get_upper(ctx),
                lower: initial_bounds.get_lower(ctx),
            })))
        }

        pub(super) fn constrain(
            &self,
            ty_eff_level: TyEffLvl,
            expected_ty: InternedType<'a>,
            subtype: bool,
            ctx: &Context<'a, '_>,
        ) -> Result<(), ContextError<'static>> {
            if let Type::Unknown = expected_ty {
                return Ok(());
            }

            let merge_ctx = MultiContext::new()
                .with_ty_arena(ctx.get_inner())
                .with_ty_var(ctx.fnd_ty_vars_without_inferred())
                .with_eff_var(ctx.fnd_eff_vars_without_inferred());

            if subtype {
                let upper = map_exp_vars_to_fnd_level(
                    expected_ty,
                    |bounds| bounds.get_lower(ctx),
                    ty_eff_level,
                    ctx,
                )?;

                let current_upper = self.0.borrow().upper;
                let new_upper = meet([upper, current_upper], &merge_ctx)?;
                self.0.borrow_mut().upper = new_upper;
            } else {
                let lower = map_exp_vars_to_fnd_level(
                    expected_ty,
                    |bounds| bounds.get_upper(ctx),
                    ty_eff_level,
                    ctx,
                )?;

                let current_lower = self.0.borrow().lower;
                let new_lower = join([lower, current_lower], &merge_ctx)?;
                self.0.borrow_mut().lower = new_lower;
            }

            Ok(())
        }

        pub(super) fn initial_eff_lvl(&self) -> Lvl {
            self.0.borrow().initial_eff_lvl
        }

        fn without_inferred(&self) -> TyVar<'a> {
            TyVar::Bounded {
                bounds: self.0.borrow().initial_bounds,
                eff_lvl: self.0.borrow().initial_eff_lvl,
            }
        }

        pub(super) fn satisfy(
            self,
            variance: Variance,
            subtype: bool,
            ctx: &Context<'a, '_>,
        ) -> Result<InternedType<'a>, ContextError<'static>> {
            let num_refs = Rc::strong_count(&self.0);
            let Some(inner_cell) = Rc::into_inner(self.0) else {
                // this is not strictly necessary but it failing is a pretty good indicator that
                // something is up
                Err(IllegalError::new(
                    format!(
                        "not all TyContraint references have been dropped before satisfaction: {num_refs}",
                    ),
                    None,
                ))?
            };
            let TyConstraintInner {
                initial_bounds,
                initial_eff_lvl: _,
                unconstrained_variance,
                upper,
                lower,
            } = inner_cell.into_inner();

            // again, should just be an optimisation
            if ty_eq(upper, lower) {
                return Ok(upper);
            }

            // technically we don't really expect either but this is close enough
            expect_type_rec(
                upper,
                lower,
                true,
                TyConfig::ty_inference_disabled(),
                &ctx.fnd_as_exp(),
            )
            .try_wrap_error(|| {
                Ok(PlainContextError::new(format!(
                    "unable to satisfy constraints:\n\
                    upper: {}\n\
                    lower: {}",
                    upper.display(ctx.fnd_ctx())?,
                    lower.display(ctx.fnd_ctx())?
                )))
            })?;

            #[cfg(debug_assertions)]
            {
                use crate::typing::TyConfig;

                let initial_upper = initial_bounds.get_upper(ctx);
                expect_type_rec(
                    initial_upper,
                    upper,
                    true,
                    TyConfig::ty_inference_disabled(),
                    ctx,
                )
                .try_wrap_error(|| {
                    Ok(IllegalError::new(
                        format!(
                            "final upper type constraint:           {}\n\
                            is not subtype of initial upper bound: {}",
                            upper.display(ctx.fnd_ctx())?,
                            initial_upper.display(ctx.fnd_ctx())?
                        ),
                        None,
                    ))
                })?;

                let initial_lower = initial_bounds.get_lower(ctx);
                expect_type_rec(
                    initial_lower,
                    lower,
                    false,
                    TyConfig::ty_inference_disabled(),
                    ctx,
                )
                .try_wrap_error(|| {
                    Ok(IllegalError::new(
                        format!(
                            "final lower type constraint:             {}\n\
                            is not supertype of initial lower bound: {}",
                            lower.display(ctx.fnd_ctx())?,
                            initial_lower.display(ctx.fnd_ctx())?
                        ),
                        None,
                    ))
                })?;
            }

            // see `constraint_variance` definition
            let unconstrained_variance = if subtype {
                unconstrained_variance
            } else {
                unconstrained_variance.invert()
            };

            // Constant means the type is not mentioned so it doesn't matter which bound we choose.
            // However, we cannot fallback when invariant as in that case it does matter, we just
            // don't know how.
            //
            // We fallback to 'constaint variance' when it's co(ntra)variant as a best effort
            // guess.
            match (variance, unconstrained_variance, subtype) {
                // the best type would be the smallest one
                (Variance::Constant, _, _)
                | (Variance::Covariant, _, true)
                | (Variance::Contravariant, _, false)
                | (Variance::Invariant, Variance::Covariant, true)
                | (Variance::Invariant, Variance::Contravariant, false) => Ok(lower),
                // the best type would be the largest one
                (Variance::Covariant, _, false)
                | (Variance::Contravariant, _, true)
                | (Variance::Invariant, Variance::Covariant, false)
                | (Variance::Invariant, Variance::Contravariant, true) => Ok(upper),
                // invariant so there is no best type so we just try our best,
                // though this may need to become a hard error in the future
                (Variance::Invariant, Variance::Constant | Variance::Invariant, _) => {
                    Err(PlainContextError::new(format!(
                        "cannot infer a single type for invariant type argument\n\
                        upper: {}\n\
                        lower: {}",
                        upper.display(ctx.fnd_ctx())?,
                        lower.display(ctx.fnd_ctx())?
                    ))
                    .into())
                }
            }
        }
    }

    impl<'a> Type<'a> {
        pub(super) fn update_unconstrained_variances(
            &self,
            subtype: bool,
            ctx: &Context<'a, '_>,
        ) -> Result<(), IllegalError<'static>> {
            fn update_unconstrained_variances_effect<'a>(
                effect: &Effect<'a>,
                subtype: bool,
                ctx: &Context<'a, '_>,
            ) -> Result<(), IllegalError<'static>> {
                match effect {
                    Effect::Def {
                        name: _,
                        arg,
                        result,
                    } => {
                        arg.update_unconstrained_variances(subtype, ctx)?;
                        result.update_unconstrained_variances(!subtype, ctx)?;
                    }
                    Effect::Var(level) => {
                        if let (_, InferenceEffVar::EffVar(eff_var)) =
                            ctx.eff_vars.get_found_unwrap(*level)?
                            && let EffVar::Effect { effect, ty_lvl } = eff_var
                        {
                            update_unconstrained_variances_effect(
                                &effect.deepen(
                                    TyEffLvl::new(*ty_lvl, *level),
                                    ctx.next_found_ty_eff_level(),
                                    ctx,
                                ),
                                subtype,
                                ctx,
                            )?;
                        }
                    }
                }
                Ok(())
            }

            match self {
                Type::TyAbs {
                    name,
                    bounds: bounds @ TyBounds { upper, lower },
                    result,
                } => {
                    if let Some(upper) = upper {
                        upper.update_unconstrained_variances(!subtype, ctx)?;
                    }
                    if let Some(lower) = lower {
                        lower.update_unconstrained_variances(subtype, ctx)?;
                    }
                    // TyVars aren't actually read so we could use a 'dummy' value
                    // but we try to be accurate here
                    let ty_var = TyVar::Bounded {
                        bounds: *bounds,
                        eff_lvl: ctx.eff_vars.next_found_level(),
                    };
                    result.update_unconstrained_variances(
                        subtype,
                        &ctx.push_ty_var(name, name, ty_var, ty_var),
                    )
                }
                Type::RecAbs { name, result } => result.update_unconstrained_variances(
                    subtype,
                    &ctx.push_ty_var(name, name, TyVar::Rec, TyVar::Rec),
                ),
                Type::EffAbs { name, result } => result.update_unconstrained_variances(
                    subtype,
                    &ctx.push_eff_var(name.0, name.0, EffVar::Unbound, EffVar::Unbound),
                ),
                Type::TyVar(level) => {
                    let (_, ty_var) = ctx.ty_vars.get_found_unwrap(*level)?;
                    if let InferenceTyVar::Inferred(ty_constraint) = ty_var {
                        let variance = if subtype {
                            Variance::Covariant
                        } else {
                            Variance::Contravariant
                        };
                        let new_varaince = ty_constraint
                            .0
                            .borrow()
                            .unconstrained_variance
                            .add(variance);
                        ty_constraint.0.borrow_mut().unconstrained_variance = new_varaince;
                    }
                    Ok(())
                }
                Type::TyObj(ty) => ty.update_unconstrained_variances(subtype, ctx),
                Type::Arr {
                    arg,
                    effects,
                    result,
                } => {
                    arg.update_unconstrained_variances(!subtype, ctx)?;
                    effects.iter_unsorted().try_for_each(|(_, e)| {
                        update_unconstrained_variances_effect(e, subtype, ctx)
                    })?;
                    result.update_unconstrained_variances(subtype, ctx)
                }
                Type::Enum(variants) => variants
                    .0
                    .values()
                    .try_for_each(|t| t.update_unconstrained_variances(subtype, ctx)),
                Type::Record(fields) => fields
                    .0
                    .values()
                    .try_for_each(|t| t.update_unconstrained_variances(subtype, ctx)),
                Type::Tuple(elems) => elems
                    .iter()
                    .try_for_each(|t| t.update_unconstrained_variances(subtype, ctx)),
                // the unknown type should in fact never appear here but we allow it because
                // throwing an error would complicate this function
                Type::Bool | Type::Any | Type::Never | Type::Unknown => Ok(()),
            }
        }
    }

    #[derive(Clone)]
    pub(super) enum InferenceEffVar<'a> {
        EffVar(EffVar<'a>),
        Inferred(EffConstraint<'a>),
    }

    impl<'a> InferenceEffVar<'a> {
        pub(super) fn without_inferred(&self) -> EffVar<'a> {
            match self {
                InferenceEffVar::EffVar(ty_var) => *ty_var,
                InferenceEffVar::Inferred(_) => EffVar::Unbound,
            }
        }
    }

    #[derive(Clone)]
    pub(super) struct EffConstraint<'a>(Rc<RefCell<EffConstraintInner<'a>>>);

    struct EffConstraintInner<'a> {
        upper: EffectGroup<'a>,
        lower: EffectGroup<'a>,
    }

    impl<'a> EffConstraint<'a> {
        pub(super) fn constrain(
            &self,
            ty_eff_level: TyEffLvl,
            expected_effects: &EffectGroup<'a>,
            subtype: bool,
            ctx: &Context<'a, '_>,
        ) -> Result<(), ContextError<'static>> {
            let merge_ctx = MultiContext::new()
                .with_ty_arena(ctx.get_inner())
                .with_ty_var(ctx.fnd_ty_vars_without_inferred())
                .with_eff_var(ctx.fnd_eff_vars_without_inferred());

            if subtype {
                let upper = expected_effects.try_map(|_, effect| {
                    map_exp_vars_to_fnd_level(
                        *effect,
                        |bounds| bounds.get_lower(ctx),
                        ty_eff_level,
                        ctx,
                    )
                })?;

                let current_upper = &self.0.borrow().upper;
                let new_upper = meet([&upper, current_upper], &merge_ctx)?;
                self.0.borrow_mut().upper = new_upper;
            } else {
                let lower = expected_effects.try_map(|_, effect| {
                    map_exp_vars_to_fnd_level(
                        *effect,
                        |bounds| bounds.get_upper(ctx),
                        ty_eff_level,
                        ctx,
                    )
                })?;

                let current_lower = &self.0.borrow().lower;
                let new_lower = join([&lower, current_lower], &merge_ctx)?;
                self.0.borrow_mut().lower = new_lower;
            }

            Ok(())
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
    ty_config: TyConfig,
    ctx: &ctx!(arena 'inn; ty_var; eff_var),
) -> Result<InternedType<'a>, ContextError<'static>> {
    expect_type_rec(expected, found, subtype, ty_config, &Context::from(ctx))
}

/// Checks whether `found` can be used in place of `expected`.
/// Returns the type that `found` would have if so.
/// `subtype` determines whether `found` should be allowed to be a subtype
/// of `expected` or vice versa.
///
/// `found` should never be `Type::Unknown`
/// should never return `Type::Unknown`
///
/// # Errors
/// returns Err when not subtype
fn expect_type_rec<'a>(
    expected: InternedType<'a>,
    found: InternedType<'a>,
    subtype: bool,
    ty_config: TyConfig,
    ctx: &Context<'a, '_>,
) -> Result<InternedType<'a>, ContextError<'static>> {
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
    if ctx.vars_same() && ty_eq(expected, found) {
        return Ok(found);
    }

    let relation = if subtype { "subtype" } else { "supertype" };

    let handle_ty_var = |level, is_found| {
        let ((name, ty_var), var, other) = if is_found {
            (ctx.ty_vars.get_found_unwrap(level)?, found, expected)
        } else {
            (ctx.ty_vars.get_expected_unwrap(level)?, expected, found)
        };
        let ty = match ty_var {
            InferenceTyVar::TyVar(TyVar::Type { ty, eff_lvl }) => {
                if is_found {
                    let ty = ty.deepen(
                        TyEffLvl::new(level, *eff_lvl),
                        ctx.next_found_ty_eff_level(),
                        ctx,
                    );
                    expect_type_rec(expected, ty, subtype, ty_config, ctx)
                } else {
                    let ty = ty.deepen(
                        TyEffLvl::new(level, *eff_lvl),
                        ctx.next_expected_ty_eff_level(),
                        ctx,
                    );
                    expect_type_rec(ty, found, subtype, ty_config, ctx)
                }?
            }
            InferenceTyVar::TyVar(TyVar::Rec) => Err(PlainContextError::new(
                "recursive type variables are only comparable to themselves".to_string(),
            ))?,
            InferenceTyVar::TyVar(TyVar::Bounded { bounds, eff_lvl }) => {
                // a type is guaranteed to be a supertype/subtype of the instantiated type iff it is a
                // supertype/subtype of the upper/lower bound (due to the transitivity of subtyping)
                let bound = if subtype == is_found {
                    bounds.get_upper(ctx)
                } else {
                    bounds.get_lower(ctx)
                };
                let (bound, var_ctx) = if is_found {
                    (
                        bound.deepen(
                            TyEffLvl::new(level, *eff_lvl),
                            ctx.next_found_ty_eff_level(),
                            ctx,
                        ),
                        ctx.fnd_ctx(),
                    )
                } else {
                    (
                        bound.deepen(
                            TyEffLvl::new(level, *eff_lvl),
                            ctx.next_expected_ty_eff_level(),
                            ctx,
                        ),
                        ctx.exp_ctx(),
                    )
                };
                expect_type_rec(
                    if is_found { expected } else { bound },
                    if is_found { bound } else { found },
                    subtype,
                    TyConfig::ty_inference_disabled(),
                    ctx,
                )
                .try_wrap_error(|| {
                    Ok(PlainContextError::new(format!(
                        "subtyping must be guaranteed \
                        for all possible instantiations of type var: {}\n\
                        for example, one such instantiation is: {}",
                        var.display(var_ctx.clone())?,
                        bound.display(var_ctx)?
                    )))
                })?
            }
            InferenceTyVar::Inferred(ty_constraint) => {
                ty_constraint
                    .constrain(
                        TyEffLvl::new(level, ty_constraint.initial_eff_lvl()),
                        other,
                        subtype,
                        ctx,
                    )
                    .map_err(if ty_config.ty_infer_fail {
                        ContextError::into_type_inference_err
                    } else {
                        std::convert::identity
                    })
                    .try_wrap_error(|| {
                        Ok(PlainContextError::new(format!(
                            "failed to infer type argument: {name}"
                        )))
                    })?;
                other
            }
        };
        Ok(ty)
    };

    match (expected, found, subtype) {
        (Type::Bool, Type::Bool, _)
        | (_, Type::Any, false)
        | (Type::Any, _, true)
        | (_, Type::Never, true)
        | (Type::Never, _, false) => Ok(found),
        (Type::Unknown, _, _) => {
            // this _should_ be only place `found` would be unconstrained
            found.update_unconstrained_variances(subtype, ctx)?;
            Ok(found)
        }
        (_, Type::Unknown, _) => {
            Err(IllegalError::new("Unknown cannot be a found type", None).into())
        }

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
                .wrap_error(|| {
                    PlainContextError::new(
                        "bounds of subtype type arg must enclose those of the supertype type arg:"
                            .to_string(),
                    )
                })
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
                        ty_config,
                        // we choose the narrower bounds
                        &ctx.push_ty_var(
                            name_expected,
                            name_found,
                            TyVar::Bounded {
                                bounds: *bounds_expected,
                                eff_lvl: ctx.eff_vars.next_expected_level(),
                            },
                            TyVar::Bounded {
                                bounds: *bounds_found,
                                eff_lvl: ctx.eff_vars.next_found_level(),
                            },
                        ),
                    )
                    .map(|result| {
                        ctx.intern(Type::TyAbs {
                            name: name_found,
                            bounds: *bounds_super,
                            result,
                        })
                    })
                    .try_wrap_error(|| {
                        Ok(PlainContextError::new(format!(
                            "taking {} == {} with bounds: {}",
                            name_expected,
                            name_found,
                            bounds_super.display(ctx_super)?
                        )))
                    })
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
            if ty_config.infer_ty_args {
                let (ctx_, constraint) = ctx.push_fnd_inferred_ty_var(name, *bounds);
                expect_type_rec(expected, found, subtype, ty_config, &ctx_).and_then(|result| {
                    drop(ctx_);
                    let variance = result.get_variance_of(ctx.ty_vars.next_found_level());
                    constraint
                        .satisfy(variance, subtype, ctx)
                        .map_err(if ty_config.ty_infer_fail {
                            ContextError::into_type_inference_err
                        } else {
                            std::convert::identity
                        })
                        .wrap_error(|| {
                            PlainContextError::new(format!("failed to infer type argument: {name}"))
                        })
                        .map(|ty_arg| {
                            result.substitute_ty_var(ctx.next_found_ty_eff_level(), ty_arg, ctx)
                        })
                })
            } else if ty_config.ty_infer_fail {
                Err(ContextError::NonTerminalTypeInference)
            } else {
                Err(PlainContextError::new(format!(
                    "failed to infer type argument: {name}\n\
                    not allowed to infer type arguments in this position"
                ))
                .into())
            }
        }
        (
            Type::RecAbs {
                name: name_expected,
                result: result_expected,
            },
            Type::RecAbs {
                name: name_found,
                result: result_found,
            },
            _,
        ) => expect_type_rec(
            result_expected,
            result_found,
            subtype,
            ty_config,
            &ctx.push_ty_var(name_expected, name_found, TyVar::Rec, TyVar::Rec),
        )
        .map(|result| {
            ctx.intern(Type::RecAbs {
                name: name_found,
                result,
            })
        })
        .try_wrap_error(|| {
            Ok(PlainContextError::new(format!(
                "assuming {name_expected} == {name_found}"
            )))
        }),
        (Type::TyVar(level_expected), Type::TyVar(level_found), _) => {
            let mapped_level_expected = ctx.ty_vars.map_expected_level(*level_expected)?;
            if mapped_level_expected == *level_found {
                // also covers the TyVar::Rec case
                Ok(found)
            } else if mapped_level_expected.deeper_than(*level_found) {
                // if levels are not equal (as above), we 'instantiate' the deeper ty_var first to avoid
                // cyclic dependency issues (as earlier ty_vars cannot reference later ones)
                handle_ty_var(*level_expected, false)
            } else {
                handle_ty_var(*level_found, true)
            }
        }
        (Type::TyVar(level_expected), _, _) => handle_ty_var(*level_expected, false),
        (_, Type::TyVar(level_found), _) => handle_ty_var(*level_found, true),
        (
            Type::Arr {
                arg: arg_expected,
                effects: effects_expected,
                result: res_expected,
            },
            Type::Arr {
                arg: arg_found,
                effects: effects_found,
                result: res_found,
            },
            _,
            // no try block :(
        ) => (|| {
            Ok(ctx.intern(Type::Arr {
                arg: expect_type_rec(
                    arg_expected,
                    arg_found,
                    !subtype,
                    ty_config.infer_ty_args(false),
                    ctx,
                )?,
                effects: {
                    let (effects_super, effects_sub) =
                        super_sub_of(effects_expected, effects_found, swapped);
                    effects_sub.try_map(|label, effect_sub| {
                        let check_effects = |effect_super, effect_sub| {
                            let (effect_expected, effect_found) =
                                exp_found_of(effect_super, effect_sub, swapped);
                            Effect::expect_effect_rec(effect_expected, effect_found, subtype, ctx)
                                .wrap_error(|| {
                                    PlainContextError::new(
                                        "from the perspective of subtyping, \
                                        effects are like arrow type parameters",
                                    )
                                })
                        };

                        if let Some(label) = label {
                            if let Some(effect_super) = effects_super.get_labelled(label) {
                                check_effects(effect_super, effect_sub).wrap_error(|| {
                                    PlainContextError::new(format!(
                                        "for effect with label '{label}'"
                                    ))
                                })
                            } else if let Some(effect_super) =
                                effects_super.get_anonymous(effect_sub.get_id())
                            {
                                check_effects(effect_super, effect_sub)
                            } else {
                                Err(PlainContextError::new(format!(
                                    "labelled effect '{label}' missing from supertype"
                                )))?
                            }
                        } else if let Some(effect_super) =
                            effects_super.get_anonymous(effect_sub.get_id())
                        {
                            check_effects(effect_super, effect_sub)
                        } else if effects_super.exhaustive {
                            Err(PlainContextError::new(format!(
                                "anonymous '{}' effect missing from supertype",
                                effect_sub.get_id()
                            )))?
                        } else {
                            // non-exhaustive super effects so an extra effect is valid
                            // should only occur when super == expected but we don't check for that
                            Ok(*effect_sub)
                        }
                    })?
                },
                result: expect_type_rec(res_expected, res_found, subtype, ty_config, ctx)?,
            }))
        })(),
        (Type::TyObj(expected), Type::TyObj(found), _) => expect_type_rec(
            expected,
            found,
            subtype,
            ty_config.infer_ty_args(false),
            ctx,
        )
        .map(|ty| ctx.intern(Type::TyObj(ty))),
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
                            expect_type_rec(ty_expected, ty_found, subtype, ty_config, ctx)?,
                        ))
                    } else {
                        let (ty_super, ctx_super) = if swapped {
                            (found, ctx.fnd_ctx())
                        } else {
                            (expected, ctx.exp_ctx())
                        };
                        Err(PlainContextError::new(format!(
                            "label '{l}' missing from supertype:\n\
                            | {}",
                            ty_super.display(ctx_super)?
                        ))
                        .into())
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
                            expect_type_rec(ty_expected, ty_found, subtype, ty_config, ctx)?,
                        ))
                    } else {
                        let (ty_sub, ctx_sub) = if swapped {
                            (expected, ctx.exp_ctx())
                        } else {
                            (found, ctx.fnd_ctx())
                        };
                        Err(PlainContextError::new(format!(
                            "label '{l}' missing from subtype:\n\
                            | {}",
                            ty_sub.display(ctx_sub)?
                        ))
                        .into())
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
                        expect_type_rec(elem_expected, elem_found, subtype, ty_config, ctx)
                    })
                    .try_collect()
                    .map(|elems| ctx.intern(Type::Tuple(elems)))
            } else {
                Err(PlainContextError::new(format!(
                    "tuples have different lengths\n\
                    expected tuple with length {len_expected}: {}\n\
                    found    tuple with length {len_found   }: {}",
                    expected.display(ctx.exp_ctx())?,
                    found.display(ctx.fnd_ctx())?
                ))
                .into())
            }
        }
        (_, Type::Any, true) | (Type::Any, _, false) => Err(PlainContextError::new(
            "_ is the any type: \
            it has no supertypes bar itself and cannot be constructed (directly)"
                .to_string(),
        )
        .into()),
        (Type::Never, _, true) | (_, Type::Never, false) => Err(PlainContextError::new(
            "! is the never type: \
            it has no subtypes bar itself and cannot be constructed"
                .to_string(),
        )
        .into()),
        // not using _ to avoid catching more cases than intended
        (
            Type::TyAbs { .. }
            | Type::RecAbs { .. }
            | Type::TyObj(_)
            | Type::Arr { .. }
            | Type::Enum(..)
            | Type::Record(..)
            | Type::Tuple(..)
            | Type::Bool,
            Type::RecAbs { .. }
            | Type::TyObj(_)
            | Type::Arr { .. }
            | Type::Enum(..)
            | Type::Record(..)
            | Type::Tuple(..)
            | Type::Bool,
            _,
        ) => Err(PlainContextError::new("types are incompatible".to_string()).into()),
    }
    .try_wrap_error(|| {
        Ok(PlainContextError::new(format!(
            "expected (or a {relation} of):\n\
            |   {}\n\
            found:\n\
            |   {}",
            expected.display(ctx.exp_ctx())?,
            found.display(ctx.fnd_ctx())?
        )))
    })
}

impl<'a> TyBounds<'a> {
    pub(super) fn expect_bounds<'inn>(
        expected: &Self,
        found: &Self,
        encloses: bool,
        ctx: &ctx!(arena 'inn; ty_var; eff_var),
    ) -> Result<(), ContextError<'static>>
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
    ) -> Result<(), ContextError<'static>> {
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

        // neither outer's upper or lower bounds should be Unknown but if they are we will ignore
        // them (for better or for worse)

        if let Some(upper_outer) = outer.get_upper(ctx).known_not_any() {
            let upper_inner = inner.get_upper(ctx);
            let (upper_expected, upper_found) = exp_found_of(upper_inner, upper_outer, swapped);
            expect_type_rec(
                upper_expected,
                upper_found,
                !encloses,
                TyConfig::ty_inference_disabled(),
                ctx,
            )
            .try_wrap_error(|| {
                Ok(PlainContextError::new(format!(
                    "expected upper bound (or {}):\n\
                    {}\n\
                    found upper bound:\n\
                    {}",
                    if encloses { "higher" } else { "lower" },
                    upper_expected.display(ctx.exp_ctx())?,
                    upper_found.display(ctx.fnd_ctx())?
                )))
            })?;
        }

        if let Some(lower_outer) = outer.get_lower(ctx).known_not_never() {
            let lower_inner = inner.get_lower(ctx);
            let (lower_expected, lower_found) = exp_found_of(lower_inner, lower_outer, swapped);
            expect_type_rec(
                lower_expected,
                lower_found,
                encloses,
                TyConfig::ty_inference_disabled(),
                ctx,
            )
            .try_wrap_error(|| {
                Ok(PlainContextError::new(format!(
                    "expected lower bound (or {}):\n\
                    {}\n\
                    found lower bound:\n\
                    {}",
                    if encloses { "lower" } else { "higher" },
                    lower_expected.display(ctx.exp_ctx())?,
                    lower_found.display(ctx.fnd_ctx())?
                )))
            })?;
        }
        Ok(())
    }
}

impl<'a> Effect<'a> {
    pub(super) fn expect_effect<'inn>(
        expected: &Self,
        found: &Self,
        subtype: bool,
        ctx: &ctx!(arena 'inn; ty_var; eff_var),
    ) -> Result<Self, ContextError<'static>>
    where
        'a: 'inn,
    {
        Self::expect_effect_rec(expected, found, subtype, &Context::from(ctx))
    }

    fn expect_effect_rec(
        expected: &Self,
        found: &Self,
        subtype: bool,
        ctx: &Context<'a, '_>,
    ) -> Result<Self, ContextError<'static>> {
        let handle_eff_var = |level, is_found| {
            let ((name, eff_var), var, other) = if is_found {
                (ctx.eff_vars.get_found_unwrap(level)?, found, expected)
            } else {
                (ctx.eff_vars.get_expected_unwrap(level)?, expected, found)
            };
            let effect = match eff_var {
                InferenceEffVar::EffVar(EffVar::Effect { effect, ty_lvl }) => {
                    if is_found {
                        let effect = effect.deepen(
                            TyEffLvl::new(level, *ty_lvl),
                            ctx.next_found_ty_eff_level(),
                            ctx,
                        );
                        Effect::expect_effect_rec(expected, &effect, subtype, ctx)
                    } else {
                        let effect = effect.deepen(
                            TyEffLvl::new(level, *ty_lvl),
                            ctx.next_expected_ty_eff_level(),
                            ctx,
                        );
                        Effect::expect_effect_rec(&effect, found, subtype, ctx)
                    }?
                }
                InferenceEffVar::EffVar(EffVar::Unbound) => Err(PlainContextError::new(
                    "unbound effect variables are only comparable to themselves".to_string(),
                ))?,
                InferenceEffVar::Inferred(eff_constraint) => {
                    eff_constraint
                        .constrain(level, other, subtype, ctx)
                        .try_wrap_error(|| {
                            Ok(PlainContextError::new(format!(
                                "failed to infer effect argument: {name}"
                            )))
                        })?;
                    *other
                }
            };
            Ok(effect)
        };

        let effect = match (expected, found) {
            (
                Effect::Def {
                    name: name_expected,
                    arg: arg_expected,
                    result: result_expected,
                },
                Effect::Def {
                    name: name_found,
                    arg: arg_found,
                    result: result_found,
                },
            ) => {
                if name_expected != name_found {
                    Err(PlainContextError::new(format!(
                        "expected effect: '{name_expected}'\n\
                        found effect: '{name_found}'"
                    )))?
                }
                Effect::Def {
                    name: *name_found,
                    arg: expect_type_rec(
                        arg_expected,
                        arg_found,
                        subtype,
                        TyConfig::ty_inference_disabled(),
                        ctx,
                    )?,
                    result: expect_type_rec(
                        result_expected,
                        result_found,
                        !subtype,
                        TyConfig::ty_inference_disabled(),
                        ctx,
                    )?,
                }
            }
            (Effect::Var(level_expected), Effect::Var(level_found)) => {
                let mapped_level_expected = ctx.eff_vars.map_expected_level(*level_expected)?;
                if mapped_level_expected == *level_found {
                    // also covers the EffVar::Unbound case
                    Ok(found)
                } else if mapped_level_expected.deeper_than(*level_found) {
                    // if levels are not equal (as above), we 'instantiate' the deeper eff_var first to avoid
                    // cyclic dependency issues (as earlier eff_vars cannot reference later ones)
                    handle_eff_var(*level_expected, false)
                } else {
                    handle_eff_var(*level_found, true)
                }
            }
            (Effect::Var(level_expected), _) => handle_eff_var(*level_expected, false),
            (_, Effect::Var(level_found)) => handle_eff_var(*level_found, true),
        };
        Ok(effect)
    }
}
