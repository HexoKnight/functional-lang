use std::{
    collections::HashMap,
    iter::{chain, once},
};

use itertools::{Either, Itertools};
use typed_arena::Arena;

use crate::{
    common::{IterExt, ResultOption, WithInfo, maybe_zip_eq},
    hashed_hashmap::HashedHashMap,
    importing::ImportId,
    reprs::{
        common::{Label, Lvl, Span},
        typed_ir::{self as tir},
        untyped_ir as uir,
    },
    typing::{
        InternedType, TyConfig, TyVar,
        context::{ContextInner, EffVarContext, TyArenaContext, TyVarContext},
        effects::{Effect, EffectGroup},
        error::{IllegalError, SpannedError, TypeCheckError, TypeCheckResult},
        eval::TyEval,
        merge::join,
        subtyping::expect_type,
        ty::{TyBounds, TyDisplay, Type},
    },
};

use self::context::Context;

mod context {
    use std::collections::HashMap;

    use crate::{
        importing::ImportId,
        reprs::common::{Idx, Label, Lvl},
        typing::{
            EffVar, InternedType, MapVars, TyEffLvl, TyVar,
            context::{ContextInner, EffVarContext, Stack, TyArenaContext, TyVarContext},
            effects::Effect,
            ty::Type,
        },
    };

    #[must_use]
    #[derive(Clone)]
    pub(super) struct Context<'a, 'inn> {
        inner: &'inn ContextInner<'a>,
        import_tys: &'inn HashMap<ImportId, InternedType<'a>>,
        var_ty_stack: Stack<(InternedType<'a>, TyEffLvl)>,
        ty_var_stack: Stack<(&'a str, TyVar<'a>)>,
        eff_ref_stack: Stack<(Label<'a>, Effect<'a>, TyEffLvl)>,
        eff_var_stack: Stack<(&'a str, EffVar<'a>)>,
    }

    impl<'a, 'inn> Context<'a, 'inn> {
        pub(super) fn new(
            inner: &'inn ContextInner<'a>,
            import_tys: &'inn HashMap<ImportId, InternedType<'a>>,
        ) -> Self {
            Self {
                inner,
                import_tys,
                var_ty_stack: Vec::new(),
                ty_var_stack: Vec::new(),
                eff_ref_stack: Vec::new(),
                eff_var_stack: Vec::new(),
            }
        }

        pub(super) fn push_var_tys(
            &self,
            vars: impl IntoIterator<Item = InternedType<'a>>,
        ) -> Self {
            let mut new = self.clone();

            let ty_eff_lvl = self.next_ty_eff_level();

            new.var_ty_stack
                .extend(vars.into_iter().map(|var_ty| (var_ty, ty_eff_lvl)));
            new
        }

        pub(super) fn get_var_ty(&self, index: Idx) -> Option<InternedType<'a>> {
            let (var_ty, ty_eff_lvl) = *index.get(&self.var_ty_stack)?;

            let cur_ty_eff_lvl = self.next_ty_eff_level();

            if ty_eff_lvl == cur_ty_eff_lvl {
                return Some(var_ty);
            }
            debug_assert!(cur_ty_eff_lvl.ty.deeper_than(ty_eff_lvl.ty));
            debug_assert!(cur_ty_eff_lvl.eff.deeper_than(ty_eff_lvl.eff));

            Some(var_ty.map_vars_no_level(
                |level| {
                    let level = if level.deeper_than(ty_eff_lvl.ty) {
                        level.translate(ty_eff_lvl.ty, cur_ty_eff_lvl.ty).expect(
                            "current ty_var_stack cannot be smaller than \
                            the ty_var_stack of a currently bound variable",
                        )
                    } else {
                        level
                    };
                    self.intern(Type::TyVar(level))
                },
                |level| {
                    let level = if level.deeper_than(ty_eff_lvl.eff) {
                        level.translate(ty_eff_lvl.eff, cur_ty_eff_lvl.eff).expect(
                            "current eff_var_stack cannot be smaller than \
                            the eff_var_stack of a currently bound variable",
                        )
                    } else {
                        level
                    };
                    Effect::Var(level)
                },
                self,
            ))
        }

        pub(super) fn get_import_ty(&self, import_id: ImportId) -> Option<InternedType<'a>> {
            self.import_tys.get(&import_id).copied()
        }

        pub(super) fn push_ty_vars(
            &self,
            ty_vars: impl IntoIterator<Item = (&'a str, <Self as TyVarContext<'a>>::TyVar)>,
        ) -> Self {
            let mut new = self.clone();
            new.ty_var_stack.extend(ty_vars);
            new
        }

        pub(super) fn next_eff_ref_level(&self) -> Lvl {
            Lvl::get_depth(&self.eff_ref_stack)
        }

        pub(super) fn push_eff_refs(
            &self,
            eff_vars: impl IntoIterator<Item = (Label<'a>, Effect<'a>, TyEffLvl)>,
        ) -> Self {
            let mut new = self.clone();
            new.eff_ref_stack.extend(eff_vars);
            new
        }

        pub(super) fn find_eff_ref(&self, label: Label<'a>) -> Option<Lvl> {
            Lvl::find(&self.eff_ref_stack, |(var_label, _, _)| *var_label == label)
        }

        pub(super) fn get_eff_ref(&self, level: Lvl) -> Option<(Label<'a>, Effect<'a>)> {
            let (label, effect, ty_eff_lvl) = *level.get(&self.eff_ref_stack)?;

            let cur_ty_eff_lvl = self.next_ty_eff_level();

            if ty_eff_lvl == cur_ty_eff_lvl {
                return Some((label, effect));
            }
            debug_assert!(cur_ty_eff_lvl.ty.deeper_than(ty_eff_lvl.ty));
            debug_assert!(cur_ty_eff_lvl.eff.deeper_than(ty_eff_lvl.eff));

            Some((label, effect.deepen(ty_eff_lvl, cur_ty_eff_lvl, self)))
        }
    }

    impl<'a, 'inn> TyArenaContext<'a> for Context<'a, 'inn> {
        type Inner = &'inn ContextInner<'a>;

        fn get_inner(&self) -> &'inn ContextInner<'a> {
            self.inner
        }
    }

    impl<'a> TyVarContext<'a> for Context<'a, '_> {
        type TyVar = TyVar<'a>;

        fn push_ty_var(&self, ty_var_name: &'a str, ty_var: Self::TyVar) -> Self {
            let mut new = self.clone();
            new.ty_var_stack.push((ty_var_name, ty_var));
            new
        }

        fn get_ty_var(&self, level: Lvl) -> Option<(&'a str, Self::TyVar)> {
            level.get(&self.ty_var_stack).copied()
        }

        fn next_ty_var_level(&self) -> Lvl {
            Lvl::get_depth(&self.ty_var_stack)
        }

        fn get_ty_vars(&self) -> impl Iterator<Item = (&'a str, Self::TyVar)> {
            self.ty_var_stack.iter().copied()
        }
    }

    impl<'a> EffVarContext<'a> for Context<'a, '_> {
        type EffVar = EffVar<'a>;

        fn push_eff_var(&self, eff_var_name: &'a str, eff_var: Self::EffVar) -> Self {
            let mut new = self.clone();
            new.eff_var_stack.push((eff_var_name, eff_var));
            new
        }

        fn get_eff_var(&self, level: Lvl) -> Option<(&'a str, Self::EffVar)> {
            level.get(&self.eff_var_stack).copied()
        }

        fn next_eff_var_level(&self) -> Lvl {
            Lvl::get_depth(&self.eff_var_stack)
        }

        fn get_eff_vars(&self) -> impl Iterator<Item = (&'a str, Self::EffVar)> {
            self.eff_var_stack.iter().copied()
        }
    }
}

/// Takes a series of [`ImportId`]s and [`untyped_ir::Term`][uir::Term]s and checks that they can be
/// typed, returning a series of [`typed_ir::Term`][tir::Term], which are entirely type erased,
/// along with strings representing the type of each term.
///
/// The terms are checked in order, so they must be toposorted without cycles.
///
/// # Errors
/// When type checking fails.
pub fn type_check<'i: 't, 't>(
    untyped_irs: impl IntoIterator<Item = (ImportId, &'t uir::Term<'i>)>,
) -> Result<Vec<(ImportId, tir::Term<'i>, String)>, TypeCheckError<'i>> {
    let arena = Arena::new();
    let inner = ContextInner::new(&arena);

    let mut import_tys = HashMap::new();

    untyped_irs
        .into_iter()
        .map(|(import_id, untyped_ir)| {
            let ctx = Context::new(&inner, &import_tys);

            let (term, ty, unhandled_effects) = untyped_ir.type_check(
                None,
                TyConfig {
                    infer_ty_args: false,
                    ty_infer_fail: false,
                },
                &ctx,
            )?;
            if !unhandled_effects.is_empty() {
                if let Some((level, span)) = unhandled_effects.labelled.into_iter().next() {
                    Err(IllegalError::new(
                        format!("unhandled labelled effect: {:?}", level),
                        Some(span),
                    ))?
                }

                Err(SpannedError::with_context(
                    "unhandled effects",
                    "",
                    "in this file",
                    untyped_ir.0,
                    unhandled_effects
                        .anonymous
                        .into_iter()
                        .map(|(e, span)| {
                            Ok((span, format!("effect used here: {}", e.display(&ctx)?)))
                        })
                        .collect::<Result<Vec<_>, TypeCheckError>>()?,
                ))?;
            }

            let ty_display = ty.display(&ctx)?;

            import_tys.insert(import_id, ty);

            Ok((import_id, term, ty_display))
        })
        .collect()
}

trait TypeCheck<'i, 'a, 'inn> {
    type TypeChecked;

    /// `check_type`: any type information known ahead of time
    /// `infer_ty_args`: whether to allow type arguments to be inferred
    ///
    /// should never return `Type::Unknown`
    fn type_check(
        &self,
        check_type: Option<InternedType<'a>>,
        ty_config: TyConfig,
        ctx: &Context<'a, 'inn>,
    ) -> Result<(Self::TypeChecked, InternedType<'a>, EffectUses<'i, 'a>), TypeCheckError<'i>>;
}

impl<'i, 'a, 'inn, T: TypeCheck<'i, 'a, 'inn>> TypeCheck<'i, 'a, 'inn> for Box<T> {
    type TypeChecked = Box<T::TypeChecked>;

    fn type_check(
        &self,
        check_type: Option<InternedType<'a>>,
        ty_config: TyConfig,
        ctx: &Context<'a, 'inn>,
    ) -> Result<(Self::TypeChecked, InternedType<'a>, EffectUses<'i, 'a>), TypeCheckError<'i>> {
        T::type_check(self, check_type, ty_config, ctx)
            .map(|(term, ty, effs)| (Box::new(term), ty, effs))
    }
}

impl<'i: 'a, 'a, 'inn> TypeCheck<'i, 'a, 'inn> for uir::Term<'i> {
    type TypeChecked = tir::Term<'i>;

    fn type_check(
        &self,
        check_type: Option<InternedType<'a>>,
        ty_config: TyConfig,
        ctx: &Context<'a, 'inn>,
    ) -> Result<(Self::TypeChecked, InternedType<'a>, EffectUses<'i, 'a>), TypeCheckError<'i>> {
        let WithInfo(info, term) = self;

        // mutable so it can be `take()`n when used then for cases that don't use it, it will be
        // checked afterwards
        let mut check_type = if let Some(ty) = check_type {
            // top or unknown type provides no information and is equivalent to no check_type at all
            ty.known_not_any()
        } else {
            None
        };

        let mut take_concrete_check_type = || {
            check_type
                .take()
                .map(|check_type| check_type.upper_concrete(ctx))
                .transpose()
        };

        // a sentinel value used as TyBounds::name to represent an applied (ie. concrete) bounds
        // notably it must not be nameable so cannot be a valid type var name
        const TY_APP_NAME: &str = "$";

        let (term, ty, effects) = match term {
            uir::RawTerm::Abs {
                arg_structure,
                arg_type: arg,
                effects,
                body,
            } => {
                let declared_effects = effects.eval(ctx)?;

                if let Some(arg) = arg {
                    let arg = arg.eval(ctx)?;

                    let (check_arg, check_effects, check_result) =
                        if let Some(check_type) = take_concrete_check_type()? {
                            let Type::Arr {
                                arg: check_arg,
                                effects: check_effects,
                                result: check_result,
                            } = check_type
                            else {
                                Err(SpannedError::ty_mismatch(
                                    check_type.display(ctx)?,
                                    "got function definition",
                                    *info,
                                ))?
                            };
                            (
                                check_arg.known_not_never(),
                                Some(check_effects),
                                check_result.known_not_any(),
                            )
                        } else {
                            (None, None, None)
                        };

                    if let Some(check_arg) = check_arg {
                        expect_type(check_arg, arg, false, ty_config.infer_ty_args(false), ctx)
                            .try_wrap_error(|| {
                                Ok(SpannedError::ty_ty_mismatch(
                                    Type::arr(check_arg, &Type::Unknown).display(ctx)?,
                                    Type::arr(arg, &Type::Unknown).display(ctx)?,
                                    *info,
                                ))
                            })?;
                    }

                    let (arg_structure, arg_types, ty_vars) =
                        arg.destructure(arg_structure, ctx)?;

                    let ctx_ = ctx
                        .push_var_tys(arg_types.into_iter().map(|(_, ty)| ty))
                        .push_ty_vars(ty_vars.iter().map(|(name, ty)| {
                            (
                                *name,
                                TyVar::Type {
                                    ty,
                                    eff_lvl: ctx.next_eff_var_level(),
                                },
                            )
                        }))
                        .push_eff_refs(
                            declared_effects
                                .labelled
                                .iter_unsorted()
                                .map(|(l, e)| (*l, *e, ctx.next_ty_eff_level())),
                        );
                    let (body, result, effects_used) = body.type_check(
                        check_result,
                        ty_config.infer_ty_args(true).ty_infer_fail(false),
                        &ctx_,
                    )?;

                    let result = result.substitute_ty_vars(
                        ctx.next_ty_eff_level(),
                        &ty_vars.into_iter().map(|(_, ty)| ty).collect::<Box<_>>(),
                        ctx,
                    );

                    let ty = Type::Arr {
                        arg,
                        effects: check_declared_effects(
                            declared_effects,
                            effects_used,
                            check_effects,
                            *info,
                            ctx,
                        )?,
                        result,
                    };

                    (
                        tir::RawTerm::Abs {
                            arg_structure: arg_structure.clone(),
                            body,
                        },
                        ctx.intern(ty),
                        EffectUses::default(),
                    )
                } else if let Some(check_type) = take_concrete_check_type()? {
                    let Type::Arr {
                        arg: check_arg,
                        effects: check_effects,
                        result: check_result,
                    } = check_type
                    else {
                        Err(SpannedError::ty_mismatch(
                            check_type.display(ctx)?,
                            "got function definition",
                            *info,
                        ))?
                    };

                    let Some(check_arg) = check_arg.known() else {
                        if ty_config.ty_infer_fail {
                            Err(TypeCheckError::NonTerminalTypeInference)?
                        } else {
                            Err(SpannedError::type_inference(
                                "cannot infer type of function argument",
                                *info,
                            ))?
                        }
                    };
                    let check_result = check_result.known_not_any();

                    let (arg_structure, check_args, ty_vars) =
                        check_arg.destructure(arg_structure, ctx)?;

                    let ctx_ = ctx
                        .push_var_tys(check_args.into_iter().map(|(_, ty)| ty))
                        .push_ty_vars(ty_vars.iter().map(|(name, ty)| {
                            (
                                *name,
                                TyVar::Type {
                                    ty,
                                    eff_lvl: ctx.next_eff_var_level(),
                                },
                            )
                        }))
                        .push_eff_refs(
                            declared_effects
                                .labelled
                                .iter_unsorted()
                                .map(|(l, e)| (*l, *e, ctx.next_ty_eff_level())),
                        );
                    let (body, result, effects_used) =
                        body.type_check(check_result, ty_config.infer_ty_args(true), &ctx_)?;

                    let result = result.substitute_ty_vars(
                        ctx.next_ty_eff_level(),
                        &ty_vars.into_iter().map(|(_, ty)| ty).collect::<Box<_>>(),
                        ctx,
                    );

                    let ty = Type::Arr {
                        arg: check_arg,
                        effects: check_declared_effects(
                            declared_effects,
                            effects_used,
                            Some(check_effects),
                            *info,
                            ctx,
                        )?,
                        result,
                    };

                    (
                        tir::RawTerm::Abs {
                            arg_structure: arg_structure.clone(),
                            body,
                        },
                        ctx.intern(ty),
                        EffectUses::default(),
                    )
                } else if ty_config.ty_infer_fail {
                    Err(TypeCheckError::NonTerminalTypeInference)?
                } else {
                    Err(SpannedError::type_inference(
                        "cannot infer type of function argument",
                        *info,
                    ))?
                }
            }
            uir::RawTerm::App {
                func: func_term,
                effects: app_effects,
                arg: arg_term,
            } => {
                let check_type = check_type.take();

                let app_effects = app_effects
                    .0
                    .iter()
                    .map(|(label, level)| {
                        ctx.get_eff_ref(*level)
                            .map(|(outer_label, effect)| (*label, *level, outer_label, effect))
                            .ok_or_else(|| {
                                IllegalError::new(
                                    format!("effect reference level not found: {level:?}"),
                                    None,
                                )
                            })
                    })
                    .collect::<Result<Vec<_>, _>>()?;

                let provided_effects = app_effects
                    .iter()
                    .map(|(label, _, _, effect)| (*label, *effect))
                    .collect::<EffectGroup>()
                    .non_exhaustive();

                let check_func_effects = |func_effects: &EffectGroup<'a>| {
                    let mut provided_labelled = HashMap::<_, _>::new();
                    let mut provided_anonymous = HashMap::<_, _>::new();

                    app_effects
                        .iter()
                        .try_for_each(|(label, level, outer_label, effect)| {
                            if let Some(label) = label {
                                let prev = provided_labelled.insert(*label, *level);
                                #[cfg(debug_assertions)]
                                if prev.is_some() {
                                    Err(IllegalError::new(
                                        "effect label appears twice (validation failure)",
                                        Some(*info),
                                    ))?
                                }
                            } else {
                                let name = effect.get_id();
                                if let Some((prev_label, _)) =
                                    provided_anonymous.insert(name, (*outer_label, *level))
                                {
                                    Err(SpannedError::new(
                                        "anonymous effect kind specified multiple times",
                                        format!(
                                            "'{name}' effects: '{}' vs '{}'",
                                            prev_label, outer_label
                                        ),
                                        "in this application",
                                        *info,
                                    ))?
                                }
                            }
                            Ok::<_, TypeCheckError>(())
                        })?;

                    let (labelled, anonymous) =
                        func_effects
                            .iter_unsorted()
                            .try_partition_map(|(label, effect)| {
                                Ok::<_, TypeCheckError>(if let Some(label) = label {
                                    if let Some(level) = provided_labelled
                                        .remove(&label)
                                        .or_else(|| ctx.find_eff_ref(label))
                                    {
                                        Either::Left((level, *info))
                                    } else {
                                        Err(SpannedError::new(
                                            format!(
                                                "no effect available: {}",
                                                effect.display(ctx)?
                                            ),
                                            "",
                                            "for this application",
                                            *info,
                                        ))?
                                    }
                                } else if let Some((_, level)) =
                                    provided_anonymous.remove(&effect.get_id())
                                {
                                    Either::Left((level, *info))
                                } else {
                                    Either::Right((*effect, *info))
                                })
                            })?;

                    if !provided_labelled.is_empty() {
                        let s = if provided_labelled.len() > 1 { "s" } else { "" };
                        Err(SpannedError::new(
                            format!("extra labelled effect{s} provided"),
                            format!(
                                "extra labelled effect{s}: {}",
                                provided_labelled
                                    .into_keys()
                                    .map(|label| format!("'{label}'"))
                                    .format(", ")
                            ),
                            "in this application",
                            *info,
                        ))?
                    }
                    if !provided_anonymous.is_empty() {
                        let s = if provided_anonymous.len() > 1 {
                            "s"
                        } else {
                            ""
                        };
                        Err(SpannedError::new(
                            format!("extra anonymous effect{s} provided"),
                            format!(
                                "extra anonymous effect{s}: {}",
                                provided_anonymous
                                    .into_values()
                                    .map(|(label, _)| format!("'{label}'"))
                                    .format(", ")
                            ),
                            "in this application",
                            *info,
                        ))?
                    }

                    Ok::<_, TypeCheckError>(EffectUses {
                        labelled,
                        anonymous,
                    })
                };

                // try infer but fall back if it fails
                if let Some((func_term, func, func_effects_used)) = func_term
                    .type_check(
                        Some(ctx.intern(Type::Arr {
                            arg: ctx.ty_unknown(),
                            // TODO: maybe try remove clone
                            effects: provided_effects.clone(),
                            result: check_type.unwrap_or(ctx.ty_unknown()),
                        })),
                        ty_config.infer_ty_args(true).ty_infer_fail(true),
                        ctx,
                    )
                    .catch_type_inference_error()
                    .some_or(|| {
                        func_term
                            .type_check(
                                None,
                                ty_config.infer_ty_args(false).ty_infer_fail(true),
                                ctx,
                            )
                            .catch_type_inference_error()
                    })?
                {
                    match func.upper_concrete(ctx)? {
                        Type::Arr {
                            arg: func_arg,
                            effects: func_effects,
                            result,
                        } => {
                            let (arg_term, arg, arg_effects_used) = arg_term.type_check(
                                Some(func_arg),
                                ty_config.infer_ty_args(true),
                                ctx,
                            )?;

                            // `type_check` should always return a
                            // subtype of `check_type` (ie. `func_arg`)
                            #[cfg(debug_assertions)]
                            expect_type(func_arg, arg, true, ty_config.infer_ty_args(false), ctx)
                                .try_wrap_error(|| {
                                Ok(IllegalError::new(
                                    "`type_check` result is not subtype of `check_type`",
                                    None,
                                ))
                            })?;

                            (
                                tir::RawTerm::App {
                                    func: func_term,
                                    arg: arg_term,
                                },
                                *result,
                                EffectUses::join([
                                    func_effects_used,
                                    arg_effects_used,
                                    check_func_effects(func_effects)?,
                                ])?,
                            )
                        }
                        ty_abs @ Type::TyAbs { .. } => {
                            // TODO: maybe try pass some check info into this
                            let (arg_term, arg, arg_effects_used) =
                                arg_term.type_check(None, ty_config.infer_ty_args(false), ctx)?;

                            let check_func = ctx.intern(Type::Arr {
                                arg,
                                effects: provided_effects,
                                result: check_type.unwrap_or(ctx.ty_unknown()),
                            });
                            let inferred_func = expect_type(
                                check_func,
                                ty_abs,
                                true,
                                ty_config.infer_ty_args(true),
                                ctx,
                            )
                            .try_wrap_error(|| {
                                Ok(SpannedError::ty_ty_mismatch(
                                    check_func.display(ctx)?,
                                    ty_abs.display(ctx)?,
                                    *info,
                                ))
                            })?;

                            let Type::Arr {
                                arg: _,
                                effects: func_effects,
                                result: inferred_result,
                            } = inferred_func
                            else {
                                Err(IllegalError::new(
                                    "`expect_type` result is not subtype of `expected`",
                                    None,
                                ))?
                            };
                            (
                                tir::RawTerm::App {
                                    func: func_term,
                                    arg: arg_term,
                                },
                                *inferred_result,
                                EffectUses::join([
                                    func_effects_used,
                                    arg_effects_used,
                                    check_func_effects(func_effects)?,
                                ])?,
                            )
                        }
                        _ => Err(SpannedError::ty_ty_mismatch(
                            Type::arr(&Type::Unknown, check_type.unwrap_or(&Type::Unknown))
                                .display(ctx)?,
                            func.display(ctx)?,
                            *info,
                        ))?,
                    }
                } else {
                    let (arg_term, arg, arg_effects_used) =
                        arg_term.type_check(None, ty_config, ctx)?;
                    let (func_term, func, func_effects_used) = func_term.type_check(
                        Some(ctx.intern(Type::Arr {
                            arg,
                            effects: provided_effects,
                            result: check_type.unwrap_or(ctx.ty_unknown()),
                        })),
                        ty_config.infer_ty_args(true),
                        ctx,
                    )?;

                    let Type::Arr {
                        arg: func_arg,
                        effects: func_effects,
                        result,
                    } = func
                    else {
                        Err(IllegalError::new(
                            "`type_check` result is not subtype of `check_type`",
                            None,
                        ))?
                    };

                    #[cfg(debug_assertions)]
                    expect_type(func_arg, arg, true, ty_config.infer_ty_args(false), ctx)
                        .try_wrap_error(|| {
                            Ok(IllegalError::new(
                                "`type_check` result is not subtype of `check_type`",
                                None,
                            ))
                        })?;

                    (
                        tir::RawTerm::App {
                            func: func_term,
                            arg: arg_term,
                        },
                        *result,
                        EffectUses::join([
                            func_effects_used,
                            arg_effects_used,
                            check_func_effects(func_effects)?,
                        ])?,
                    )
                }
            }
            uir::RawTerm::TyAbs { name, bounds, body } => {
                let bounds = bounds.eval(ctx)?;

                let (check_result, infer) = if let Some(check_type) = take_concrete_check_type()? {
                    if let Type::TyAbs {
                        name: check_name,
                        bounds: check_bounds,
                        result: check_result,
                    } = check_type
                    {
                        if *check_name != TY_APP_NAME {
                            // if check_name == TY_APP_NAME, the bounds will be checked afterwards
                            // so its fine to leave it until then
                            TyBounds::expect_bounds(check_bounds, &bounds, true, ctx)
                                .try_wrap_error(|| {
                                    Ok(SpannedError::new(
                                        "type bounds mismatch",
                                        format!(
                                            "expected bounds (or wider): `{}`\n\
                                            found:                      `{}`",
                                            check_bounds.display(ctx)?,
                                            bounds.display(ctx)?
                                        ),
                                        "",
                                        *info,
                                    ))
                                })?;
                        }

                        (check_result.known_not_any(), None)
                    } else if ty_config.infer_ty_args {
                        // expected something other than a type abstraction and we are allowed to
                        // infer ty_args so we attempt to do so
                        // we cannot pass down check_type as the ty_var contexts would diverge
                        (None, Some(check_type))
                    } else {
                        Err(SpannedError::ty_mismatch(
                            check_type.display(ctx)?,
                            "found a type abstraction (could not infer)",
                            *info,
                        ))?
                    }
                } else {
                    (None, None)
                };

                let ctx_ = ctx.push_ty_var(
                    name,
                    TyVar::Bounded {
                        bounds,
                        eff_lvl: ctx.next_eff_var_level(),
                    },
                );
                let (body, result, effects_used) =
                    body.type_check(check_result, ty_config, &ctx_)?;

                if !effects_used.is_empty() {
                    Err(SpannedError::with_context(
                        "type abstraction cannot capture effects",
                        "consider adding an intermediate abstraction",
                        "type abstraction here",
                        *info,
                        effects_used
                            .spans_iter()
                            .map(|span| (*span, "effect used here")),
                    ))?
                }

                let ty_abs = ctx.intern(Type::TyAbs {
                    name,
                    bounds,
                    result,
                });

                let WithInfo(_info, body) = *body;

                if let Some(check_type) = infer {
                    // we should only be here if we are allowed to infer
                    debug_assert!(ty_config.infer_ty_args);
                    let inferred =
                        expect_type(check_type, ty_abs, true, ty_config.infer_ty_args(true), ctx)
                            .try_wrap_error(|| {
                            Ok(SpannedError::ty_ty_mismatch(
                                check_type.display(ctx)?,
                                ty_abs.display(ctx)?,
                                *info,
                            ))
                        })?;
                    (body, inferred, effects_used)
                } else {
                    (body, ty_abs, effects_used)
                }
            }
            uir::RawTerm::TyApp {
                abs: abs_term,
                arg: arg_term,
            } => {
                let arg = arg_term.eval(ctx)?;

                let check_abs = ctx.intern(Type::TyAbs {
                    name: TY_APP_NAME,
                    bounds: TyBounds {
                        upper: Some(arg),
                        lower: Some(arg),
                    },
                    result: check_type.unwrap_or(ctx.ty_unknown()),
                });

                let (abs_term, abs, abs_effects_used) =
                    abs_term.type_check(Some(check_abs), ty_config, ctx)?;
                let WithInfo(abs_info, abs_term) = *abs_term;

                let ty = abs.apply_ty_arg(abs_info, arg, arg_term.0, ty_config, ctx)?;
                (abs_term, ty, abs_effects_used)
            }
            uir::RawTerm::EffAbs { name, body } => {
                //
                todo!()
            }
            uir::RawTerm::EffApp { abs, effects } => {
                //
                todo!()
            }
            uir::RawTerm::Var(index) => {
                let ty = ctx.get_var_ty(*index).ok_or_else(|| {
                    IllegalError::new(format!("variable index not found: {index:?}"), Some(*info))
                })?;

                let ty = if let Some(check_type) = check_type.take() {
                    expect_type(check_type, ty, true, ty_config, ctx).try_wrap_error(|| {
                        Ok(SpannedError::ty_ty_mismatch(
                            check_type.display(ctx)?,
                            ty.display(ctx)?,
                            *info,
                        ))
                    })?
                } else {
                    ty
                };

                (tir::RawTerm::Var(*index), ty, EffectUses::default())
            }
            uir::RawTerm::Type(ty) => (
                tir::RawTerm::Tuple(Box::new([])),
                ctx.intern(Type::TyObj(ty.eval(ctx)?)),
                EffectUses::default(),
            ),
            uir::RawTerm::Handle(effect) => (
                tir::RawTerm::Handle { name: todo!() },
                ctx.intern(todo!()),
                EffectUses::default(),
            ),
            uir::RawTerm::Trigger(effect_term) => {
                let effect = effect_term.eval(ctx)?;

                let (term, ty) = match effect.concrete(ctx)? {
                    Effect::Def { name, arg, result } => (
                        tir::RawTerm::Trigger {
                            // TODO
                            name: Label(name.0.to_string().leak()),
                        },
                        Type::Arr {
                            arg,
                            effects: [(None, effect)].into_iter().collect(),
                            result,
                        },
                    ),
                    Effect::Var(level) => Err(IllegalError::new(
                        format!(
                            "`Effect::concrete` produced non-concrete effect: var of level {level:?}"
                        ),
                        Some(effect_term.0),
                    ))?,
                };

                (term, ctx.intern(ty), EffectUses::default())
            }
            uir::RawTerm::Import(WithInfo(span, import_id)) => (
                tir::RawTerm::Import(*import_id),
                ctx.get_import_ty(*import_id).ok_or_else(|| {
                    IllegalError::new(
                        format!("import {import_id:?} not found during type checking"),
                        Some(*span),
                    )
                })?,
                EffectUses::default(),
            ),
            uir::RawTerm::Fold(rec) => {
                let rec = rec.eval(ctx)?;

                let (check_arg, check_rec) = if let Some(check_type) = take_concrete_check_type()? {
                    let Type::Arr {
                        arg: check_arg,
                        effects: _,
                        result: check_rec,
                    } = check_type
                    else {
                        Err(SpannedError::ty_mismatch(
                            check_type.display(ctx)?,
                            "found a fold (a function)",
                            *info,
                        ))?
                    };
                    (
                        check_arg.upper_concrete(ctx)?.known_not_never(),
                        check_rec.upper_concrete(ctx)?.known_not_any(),
                    )
                } else {
                    (None, None)
                };

                let rec = if let (Some(rec), Some(check_rec)) = (rec, check_rec) {
                    Some(
                        expect_type(check_rec, rec, true, ty_config.infer_ty_args(false), ctx)
                            .try_wrap_error(|| {
                                Ok(SpannedError::ty_ty_mismatch(
                                    Type::arr(&Type::Unknown, check_rec).display(ctx)?,
                                    Type::arr(&Type::Unknown, rec).display(ctx)?,
                                    *info,
                                ))
                            })?,
                    )
                } else {
                    rec.or(check_rec)
                };

                if let Some(rec) = rec {
                    let Type::RecAbs {
                        name: _,
                        result: rec_body,
                    } = rec.upper_concrete(ctx)?
                    else {
                        Err(SpannedError::new(
                            "type mismatch: expected recursive type",
                            format!(
                                "cannot fold into a non-recursive type: {}",
                                rec.display(ctx)?
                            ),
                            "",
                            *info,
                        ))?
                    };

                    let unfolded_rec =
                        rec_body.substitute_ty_var(ctx.next_ty_eff_level(), rec, ctx);
                    let arg = if let Some(check_arg) = check_arg {
                        expect_type(
                            check_arg,
                            unfolded_rec,
                            false,
                            ty_config.infer_ty_args(false),
                            ctx,
                        )
                        .try_wrap_error(|| {
                            Ok(SpannedError::ty_ty_mismatch(
                                Type::arr(check_arg, check_rec.unwrap_or(ctx.ty_unknown()))
                                    .display(ctx)?,
                                Type::arr(unfolded_rec, rec).display(ctx)?,
                                *info,
                            ))
                        })?
                    } else {
                        unfolded_rec
                    };

                    (
                        tir::RawTerm::Identity,
                        ctx.intern(Type::arr(arg, rec)),
                        EffectUses::default(),
                    )
                } else if ty_config.ty_infer_fail {
                    Err(TypeCheckError::NonTerminalTypeInference)?
                } else {
                    Err(SpannedError::type_inference(
                        "cannot infer type of fold".to_string(),
                        *info,
                    ))?
                }
            }
            uir::RawTerm::Unfold(rec) => {
                let rec = rec.eval(ctx)?;

                let (check_rec, check_result) =
                    if let Some(check_type) = take_concrete_check_type()? {
                        let Type::Arr {
                            arg: check_rec,
                            effects: _,
                            result: check_result,
                        } = check_type
                        else {
                            Err(SpannedError::ty_mismatch(
                                check_type.display(ctx)?,
                                "found an unfold (a function)",
                                *info,
                            ))?
                        };
                        (
                            check_rec.upper_concrete(ctx)?.known_not_never(),
                            check_result.upper_concrete(ctx)?.known_not_any(),
                        )
                    } else {
                        (None, None)
                    };

                let rec = if let (Some(rec), Some(check_rec)) = (rec, check_rec) {
                    Some(
                        expect_type(check_rec, rec, false, ty_config.infer_ty_args(false), ctx)
                            .try_wrap_error(|| {
                                Ok(SpannedError::ty_ty_mismatch(
                                    Type::arr(check_rec, &Type::Unknown).display(ctx)?,
                                    Type::arr(rec, &Type::Unknown).display(ctx)?,
                                    *info,
                                ))
                            })?,
                    )
                } else {
                    rec.or(check_rec)
                };

                if let Some(rec) = rec {
                    let Type::RecAbs {
                        name: _,
                        result: rec_body,
                    } = rec
                    else {
                        Err(SpannedError::new(
                            "type mismatch: expected recursive type",
                            format!("cannot unfold a non-recursive type: {}", rec.display(ctx)?),
                            "",
                            *info,
                        ))?
                    };

                    let unfolded_rec =
                        rec_body.substitute_ty_var(ctx.next_ty_eff_level(), rec, ctx);
                    let result = if let Some(check_result) = check_result {
                        expect_type(
                            check_result,
                            unfolded_rec,
                            true,
                            ty_config.infer_ty_args(false),
                            ctx,
                        )
                        .try_wrap_error(|| {
                            Ok(SpannedError::ty_ty_mismatch(
                                Type::arr(check_rec.unwrap_or(ctx.ty_unknown()), check_result)
                                    .display(ctx)?,
                                Type::arr(rec, unfolded_rec).display(ctx)?,
                                *info,
                            ))
                        })?
                    } else {
                        unfolded_rec
                    };

                    (
                        tir::RawTerm::Identity,
                        ctx.intern(Type::arr(rec, result)),
                        EffectUses::default(),
                    )
                } else if ty_config.ty_infer_fail {
                    Err(TypeCheckError::NonTerminalTypeInference)?
                } else {
                    Err(SpannedError::type_inference(
                        "cannot infer type of fold".to_string(),
                        *info,
                    ))?
                }
            }
            uir::RawTerm::Enum(arg, label) => {
                let arg = arg.eval(ctx)?;

                let (check_arg, check_enum) = if let Some(check_type) = take_concrete_check_type()?
                {
                    let Type::Arr {
                        arg: check_arg,
                        effects: _,
                        result: check_enum,
                    } = check_type
                    else {
                        Err(SpannedError::ty_mismatch(
                            check_type.display(ctx)?,
                            "found an enum constructor (a function)",
                            *info,
                        ))?
                    };
                    (
                        check_arg.upper_concrete(ctx)?.known_not_never(),
                        check_enum.upper_concrete(ctx)?.known_not_any(),
                    )
                } else {
                    (None, None)
                };

                let arg = if let (Some(arg), Some(check_arg)) = (arg, check_arg) {
                    Some(
                        expect_type(check_arg, arg, false, ty_config.infer_ty_args(false), ctx)
                            .try_wrap_error(|| {
                                Ok(SpannedError::ty_ty_mismatch(
                                    Type::arr(check_arg, &Type::Unknown).display(ctx)?,
                                    Type::arr(arg, &Type::Unknown).display(ctx)?,
                                    *info,
                                ))
                            })?,
                    )
                } else {
                    arg.or(check_arg)
                };

                if let Some(check_enum) = check_enum {
                    let result_err = |variant| -> Result<_, TypeCheckError> {
                        Ok(SpannedError::ty_ty_mismatch(
                            Type::arr(&Type::Unknown, check_enum).display(ctx)?,
                            Type::arr(
                                &Type::Unknown,
                                ctx.intern(Type::Enum(once((*label, variant)).collect())),
                            )
                            .display(ctx)?,
                            *info,
                        ))
                    };

                    let Type::Enum(check_variants) = check_enum else {
                        Err(result_err(ctx.ty_unknown())?)?
                    };

                    let Some(check_variant_type) = check_variants.0.get(label) else {
                        Err(result_err(ctx.ty_unknown())?)?
                    };

                    let arg = if let Some(arg) = arg {
                        expect_type(
                            check_variant_type,
                            arg,
                            true,
                            ty_config.infer_ty_args(false),
                            ctx,
                        )
                        .try_wrap_error(|| result_err(arg))?
                    } else {
                        check_variant_type
                    };

                    let result = ctx.intern(Type::Enum(once((*label, arg)).collect()));

                    let result = expect_type(check_enum, result, true, ty_config, ctx)
                        .try_wrap_error(|| result_err(arg))?;

                    (
                        tir::RawTerm::Enum(*label),
                        ctx.intern(Type::arr(arg, result)),
                        EffectUses::default(),
                    )
                } else if let Some(arg) = arg {
                    let result = ctx.intern(Type::Enum(once((*label, arg)).collect()));
                    (
                        tir::RawTerm::Enum(*label),
                        ctx.intern(Type::arr(arg, result)),
                        EffectUses::default(),
                    )
                } else if ty_config.ty_infer_fail {
                    Err(TypeCheckError::NonTerminalTypeInference)?
                } else {
                    Err(SpannedError::type_inference(
                        format!("cannot infer type of enum constructor with label: '{label}'",),
                        *info,
                    ))?
                }
            }
            uir::RawTerm::Match(enum_type, arms) => {
                let enum_type = enum_type.eval(ctx)?;

                let (enum_type, check_effects, check_result) =
                    if let Some(check_type) = take_concrete_check_type()? {
                        let Type::Arr {
                            arg: check_arg,
                            effects: check_effects,
                            result: check_result,
                        } = check_type
                        else {
                            Err(SpannedError::ty_mismatch(
                                check_type.display(ctx)?,
                                "found a match expression (a function)",
                                *info,
                            ))?
                        };

                        if let Some(enum_type) = enum_type {
                            expect_type(
                                check_arg,
                                enum_type,
                                false,
                                ty_config.infer_ty_args(false),
                                ctx,
                            )
                            .try_wrap_error(|| {
                                Ok(SpannedError::ty_ty_mismatch(
                                    Type::arr(check_arg, &Type::Unknown).display(ctx)?,
                                    Type::arr(enum_type, &Type::Unknown).display(ctx)?,
                                    *info,
                                ))
                            })?;
                        }

                        (
                            enum_type.or(check_arg.upper_concrete(ctx)?.known_not_never()),
                            Some(check_effects),
                            check_result.upper_concrete(ctx)?.known_not_any(),
                        )
                    } else {
                        (enum_type, None, None)
                    };

                if let Some(enum_type) = enum_type {
                    let Type::Enum(variants) = enum_type else {
                        Err(SpannedError::new(
                            "type mismatch: expected enum type",
                            format!(
                                "cannot match on a non-enum type: {}",
                                enum_type.display(ctx)?
                            ),
                            "",
                            *info,
                        ))?
                    };

                    let (arms, effects, results, effects_used): (
                        HashMap<_, _>,
                        Vec<_>,
                        Vec<_>,
                        Vec<_>,
                    ) = arms
                        .iter()
                        .map(|(label, func_term)| -> Result<_, TypeCheckError> {
                            // check dead branches
                            let Some(variant) = variants.0.get(label) else {
                                Err(SpannedError::new(
                                    "type mismatch: dead match branch",
                                    format!(
                                        "enum type does not contain label '{label}': `{}`",
                                        enum_type.display(ctx)?
                                    ),
                                    "",
                                    func_term.0,
                                ))?
                            };

                            let check_func = ctx.intern(Type::Arr {
                                arg: variant,
                                effects: check_effects
                                    .cloned()
                                    .unwrap_or(EffectGroup::new_non_exhaustive()),
                                result: check_result.unwrap_or(ctx.ty_unknown()),
                            });

                            let (func_term, func, effects_used) =
                                func_term.type_check(Some(check_func), ty_config, ctx)?;

                            let Type::Arr {
                                arg: func_arg,
                                effects: func_effects,
                                result: func_result,
                            } = func
                            else {
                                Err(SpannedError::ty_ty_mismatch(
                                    Type::arr(variant, &Type::Unknown).display(ctx)?,
                                    func.display(ctx)?,
                                    func_term.0,
                                ))?
                            };

                            #[cfg(debug_assertions)]
                            expect_type(
                                variant,
                                func_arg,
                                false,
                                ty_config.infer_ty_args(false),
                                ctx,
                            )
                            .try_wrap_error(|| {
                                Ok(IllegalError::new(
                                    "`type_check` result is not subtype of `check_type`",
                                    None,
                                ))
                            })?;

                            Ok(Some((
                                (*label, func_term),
                                // TODO: check effects
                                func_effects,
                                *func_result,
                                effects_used,
                            )))
                        })
                        .filter_map_ok(|o| o)
                        .try_collect()?;

                    variants.0.iter().try_for_each(|(label, _)| {
                        if arms.contains_key(label) {
                            Ok(())
                        } else {
                            Err(SpannedError::new(
                                "type mismatch: inexhaustive match",
                                format!("match missing arm with label '{label}'"),
                                "",
                                *info,
                            ))
                        }
                    })?;
                    (
                        tir::RawTerm::Match(arms),
                        ctx.intern(Type::Arr {
                            arg: enum_type,
                            // TODO: check effects
                            effects: join(effects, ctx).wrap_error(|| {
                                SpannedError::new(
                                    "mismatched effects: match arms have incompatible effects",
                                    "",
                                    "arms in this match",
                                    *info,
                                )
                            })?,
                            result: join(results, ctx).wrap_error(|| {
                                SpannedError::new(
                                    "mismatched types: match arms have incompatible types",
                                    "",
                                    "arms in this match",
                                    *info,
                                )
                            })?,
                        }),
                        EffectUses::join(effects_used)?,
                    )
                } else {
                    let (arms, variants, effects, results, effects_used): (
                        HashMap<_, _>,
                        _,
                        Vec<_>,
                        Vec<_>,
                        Vec<_>,
                    ) = arms
                        .iter()
                        .map(|(label, func_term)| -> Result<_, TypeCheckError> {
                            let (func_term, func, effects_used) = func_term.type_check(
                                Some(ctx.intern(Type::arr(
                                    ctx.ty_unknown(),
                                    check_result.unwrap_or(ctx.ty_unknown()),
                                ))),
                                ty_config.infer_ty_args(true),
                                ctx,
                            )?;

                            let Type::Arr {
                                arg: func_arg,
                                effects,
                                result: func_result,
                            } = func
                            else {
                                Err(SpannedError::ty_ty_mismatch(
                                    Type::arr(&Type::Unknown, &Type::Unknown).display(ctx)?,
                                    func.display(ctx)?,
                                    func_term.0,
                                ))?
                            };

                            Ok(Some((
                                (*label, func_term),
                                (*label, *func_arg),
                                // TODO: check effects
                                effects,
                                *func_result,
                                effects_used,
                            )))
                        })
                        .filter_map_ok(|o| o)
                        .try_collect()?;
                    (
                        tir::RawTerm::Match(arms),
                        ctx.intern(Type::Arr {
                            arg: ctx.intern(Type::Enum(variants)),
                            // TODO: check effects
                            effects: join(effects, ctx).wrap_error(|| {
                                SpannedError::new(
                                    "mismatched effects: match arms have incompatible effects",
                                    "",
                                    "arms in this match",
                                    *info,
                                )
                            })?,
                            result: join(results, ctx).wrap_error(|| {
                                SpannedError::new(
                                    "type mismatch: match arms have incompatible types",
                                    "",
                                    "arms in this match",
                                    *info,
                                )
                            })?,
                        }),
                        EffectUses::join(effects_used)?,
                    )
                }
            }
            uir::RawTerm::Record(field_terms) => {
                let check_fields = take_concrete_check_type()?
                    .map(|check_type| {
                        let Type::Record(check_fields) = check_type else {
                            Err(SpannedError::ty_mismatch(
                                check_type.display(ctx)?,
                                "found record",
                                *info,
                            ))?
                        };
                        for label in check_fields.0.keys() {
                            if !field_terms.iter().any(|(l, _)| l == label) {
                                Err(SpannedError::new(
                                    "type mismatch: record missing field",
                                    format!("record missing field with label '{label}'"),
                                    "",
                                    *info,
                                ))?;
                            }
                        }
                        Ok::<_, TypeCheckError>(check_fields)
                    })
                    .transpose()?;

                let (field_terms, fields, effects_used): (Vec<_>, _, Vec<_>) = field_terms
                    .iter()
                    .map(|(label, field_term)| {
                        let check_field = check_fields
                            .and_then(|check_fields| check_fields.0.get(label).copied());

                        field_term.type_check(check_field, ty_config, ctx).map(
                            |(field_term, field, effects_used)| {
                                ((*label, field_term), (*label, field), effects_used)
                            },
                        )
                    })
                    .try_collect()?;
                (
                    tir::RawTerm::Record(field_terms.into_boxed_slice()),
                    ctx.intern(Type::Record(fields)),
                    EffectUses::join(effects_used)?,
                )
            }
            uir::RawTerm::Tuple(elem_terms) => {
                let check_elems = take_concrete_check_type()?
                    .map(|check_type| {
                        let Type::Tuple(check_elems) = check_type else {
                            Err(SpannedError::ty_mismatch(
                                check_type.display(ctx)?,
                                "found tuple",
                                *info,
                            ))?
                        };
                        let len = elem_terms.len();
                        let check_len = check_elems.len();
                        if len != check_len {
                            Err(SpannedError::ty_mismatch(
                                check_type.display(ctx)?,
                                "found tuple with {len} elements",
                                *info,
                            ))?;
                        }
                        Ok::<_, TypeCheckError>(check_elems.iter().copied())
                    })
                    .transpose()?;
                let (elem_terms, elems, effects_used): (Vec<_>, Vec<_>, Vec<_>) =
                    maybe_zip_eq(elem_terms, check_elems)
                        .map(|(elem_term, check_elem)| {
                            elem_term.type_check(check_elem, ty_config, ctx)
                        })
                        .try_collect()?;
                (
                    tir::RawTerm::Tuple(elem_terms.into_boxed_slice()),
                    ctx.intern(Type::Tuple(elems.into_boxed_slice())),
                    EffectUses::join(effects_used)?,
                )
            }
            uir::RawTerm::Bool(b) => (
                tir::RawTerm::Bool(*b),
                ctx.intern(Type::Bool),
                EffectUses::default(),
            ),
        };

        debug_assert_ne!(ty.display(ctx)?, "?");

        // if we don't explicity check above (using `.take()`), we do a basic subtype check here
        let ty = if let Some(check_type) = check_type.take() {
            expect_type(check_type, ty, true, ty_config, ctx).try_wrap_error(|| {
                Ok(SpannedError::ty_ty_mismatch(
                    check_type.display(ctx)?,
                    ty.display(ctx)?,
                    *info,
                ))
            })?
        } else {
            ty
        };

        Ok((WithInfo(*info, term), ty, effects))
    }
}

fn check_declared_effects<'i: 'a, 'a>(
    declared_effects: EffectGroup<'a>,
    effects_used: EffectUses<'i, 'a>,
    check_effects: Option<&EffectGroup<'a>>,
    abs_span: Span<'i>,
    ctx: &Context<'a, '_>,
) -> Result<EffectGroup<'a>, TypeCheckError<'i>> {
    if let Some(check_effects) = check_effects {
        for (label, declared_effect) in declared_effects.iter_unsorted() {
            let Some(check_effect) = label
                .and_then(|label| check_effects.get_labelled(label))
                .or_else(|| check_effects.get_anonymous(declared_effect.get_id()))
            else {
                if check_effects.exhaustive {
                    Err(SpannedError::new(
                        format!("unexpected effect: {}", declared_effect.display(ctx)?),
                        "",
                        "in this abstraction",
                        abs_span,
                    ))?
                } else {
                    continue;
                }
            };
            Effect::expect_effect(check_effect, declared_effect, true, ctx).try_wrap_error(
                || {
                    Ok(SpannedError::eff_eff_mismatch(
                        check_effect.display(ctx)?,
                        declared_effect.display(ctx)?,
                        label,
                        abs_span,
                        None,
                    ))
                },
            )?;
        }
    }

    let labelled_effects: HashedHashMap<_, _> = effects_used
        .labelled
        .into_iter()
        // only effects not bound by this abstraction
        .filter(|(level, _)| !level.deeper_than(ctx.next_eff_ref_level()))
        // preferably we could find a way to not discard this span here
        .map(|(level, span)| {
            let (label, effect) = ctx.get_eff_ref(level).ok_or_else(|| {
                IllegalError::new(
                    format!("effect reference level not found: {level:?}"),
                    Some(span),
                )
            })?;
            if let Some(check_effects) = check_effects
                && let Some(check_effect) = check_effects.get_labelled(label)
            {
                Effect::expect_effect(check_effect, &effect, true, ctx).try_wrap_error(|| {
                    Ok(SpannedError::eff_eff_mismatch(
                        check_effect.display(ctx)?,
                        effect.display(ctx)?,
                        Some(label),
                        abs_span,
                        Some(span),
                    ))
                })?;
            }
            Ok::<_, TypeCheckError>((label, effect))
        })
        .chain(declared_effects.labelled.0.into_iter().map(Ok))
        .try_collect()?;

    let mut anonymous_effects: HashedHashMap<_, _> = effects_used
        .anonymous
        .into_iter()
        .into_group_map_by(|(e, _)| e.get_id())
        .into_iter()
        .map(|(name, anonymous_effects)| {
            let check_catching_effect = |catching_effect| {
                anonymous_effects
                    .iter()
                    .try_for_each(|(effect, span)| {
                        Effect::expect_effect(catching_effect, effect, true, ctx)
                            .try_wrap_error(|| {
                                Ok(SpannedError::eff_eff_mismatch(
                                    catching_effect.display(ctx)?,
                                    effect.display(ctx)?,
                                    None,
                                    abs_span,
                                    Some(*span),
                                ))
                            })
                            .map(|_| ())
                    })
                    .map(|()| *catching_effect)
            };

            // check all the effects that these anonymous_effects could infer to

            let effect = 'effect: {
                if let Some(declared_effect) = declared_effects.anonymous.0.get(&name) {
                    // declared effect (checked with check_effects previously)
                    break 'effect check_catching_effect(declared_effect)?;
                }
                if let Some(check_effects) = check_effects
                    && let Some(check_effect) = check_effects.get_anonymous(name)
                {
                    // check_type effect
                    break 'effect check_catching_effect(check_effect)?;
                }

                // any previous (maybe ambiguous) labelled effect
                let all_fallback_effects = labelled_effects
                    .iter_unsorted()
                    .filter(|(_, e): &(_, &Effect)| e.get_id() == name)
                    .unique_by(|(l, _)| *l)
                    .collect_vec();
                match all_fallback_effects[..] {
                    [] => {}
                    // fallback to unambiguous labelled effect
                    [(_, fallback_effect)] => {
                        check_catching_effect(fallback_effect)?;
                        return Ok(None);
                    }
                    _ => Err(SpannedError::with_context(
                        format!("'{name}' effect usage is ambiguous"),
                        format!(
                            "ambiguous between labels:\n{}",
                            all_fallback_effects
                                .into_iter()
                                .map(|(l, _)| format!("'{l}'"))
                                .join(", ")
                        ),
                        "in this abstraction",
                        abs_span,
                        anonymous_effects
                            .iter()
                            .map(|(_, span)| (*span, "effect used here")),
                    ))?,
                };

                if let Some(check_effects) = check_effects
                    && check_effects.exhaustive
                {
                    let possible_effects: String = check_effects
                        .labelled
                        .iter_unsorted()
                        .filter(|(_, e)| e.get_id() == name)
                        .unique_by(|(l, _)| *l)
                        .map(|(l, e)| e.display(ctx).map(|e| format!("\n  '{l}': {e}")))
                        .try_collect()?;
                    Err(SpannedError::with_context(
                        format!("unexpected '{name}' effect"),
                        if possible_effects.is_empty() {
                            "".to_string()
                        } else {
                            format!("other labelled effects could be declared:{possible_effects}")
                        },
                        "in this abstraction",
                        abs_span,
                        anonymous_effects
                            .iter()
                            .map(|(_, span)| (*span, "effect used here")),
                    ))?
                }
                // non-exhaustive so we just try to join everything
                join(anonymous_effects.iter().map(|(e, _)| *e), ctx).try_wrap_error(|| {
                    Ok(SpannedError::with_context(
                        format!(
                            "failed to join incompatible \
                            '{name}' effects"
                        ),
                        "",
                        "in the body of this abstraction",
                        abs_span,
                        anonymous_effects
                            .into_iter()
                            .map(|(e, span)| {
                                e.display(ctx)
                                    .map(|e| (span, format!("effect used here: `{e}`")))
                            })
                            .collect::<Result<Vec<_>, _>>()?,
                    ))
                })?
            };

            Ok::<_, TypeCheckError>(Some((name, effect)))
        })
        .filter_map_ok(|o| o)
        .try_collect()?;

    anonymous_effects.extend(declared_effects.anonymous.0);

    Ok::<_, TypeCheckError>(EffectGroup {
        labelled: labelled_effects,
        anonymous: anonymous_effects,
        exhaustive: false,
    })
}

#[derive(Default)]
struct EffectUses<'i, 'a> {
    labelled: HashMap<Lvl, Span<'i>>,
    anonymous: Vec<(Effect<'a>, Span<'i>)>,
}

impl<'i: 'a, 'a> EffectUses<'i, 'a> {
    fn is_empty(&self) -> bool {
        self.labelled.is_empty() && self.anonymous.is_empty()
    }

    fn spans_iter(&self) -> impl Iterator<Item = &Span<'i>> {
        chain(
            self.labelled.values(),
            self.anonymous.iter().map(|(_, span)| span),
        )
    }

    fn join(effects: impl IntoIterator<Item = Self>) -> Result<Self, TypeCheckError<'i>> {
        let (labelled, anonymous): (Vec<_>, Vec<_>) = effects
            .into_iter()
            .map(|e| (e.labelled, e.anonymous))
            .collect();

        Ok(Self {
            // labelled effects have been checked so we ignore duplicates
            labelled: labelled.into_iter().flatten().collect(),
            anonymous: anonymous.into_iter().flatten().collect(),
        })
    }
}
