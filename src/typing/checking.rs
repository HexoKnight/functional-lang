use std::collections::HashMap;

use itertools::Itertools;
use typed_arena::Arena;

use crate::{
    common::{WithInfo, maybe_zip_eq},
    reprs::{
        typed_ir::{self as tir},
        untyped_ir as uir,
    },
    typing::{
        InternedType, TypeCheckError,
        context::{ContextInner, TyArenaContext, TyVarContext},
        eval::TyEval,
        merge::join,
        prepend,
        subtyping::expect_type,
        try_prepend,
        ty::{TyBounds, TyDisplay, Type},
    },
};

use self::context::Context;

mod context {
    use crate::{
        reprs::common::{Idx, Lvl},
        typing::{
            InternedType,
            context::{ContextInner, Stack, TyArenaContext, TyVarContext},
            ty::{TyBounds, Type},
        },
    };

    #[must_use]
    #[derive(Clone)]
    pub(super) struct Context<'a, 'inn> {
        inner: &'inn ContextInner<'a>,
        var_ty_stack: Stack<(InternedType<'a>, Lvl)>,
        ty_var_stack: Stack<(&'a str, TyBounds<'a>)>,
    }

    impl<'a, 'inn> Context<'a, 'inn> {
        pub(super) fn with_inner(inner: &'inn ContextInner<'a>) -> Self {
            Self {
                inner,
                var_ty_stack: Vec::new(),
                ty_var_stack: Vec::new(),
            }
        }

        pub(super) fn push_var_tys(
            &self,
            vars: impl IntoIterator<Item = InternedType<'a>>,
        ) -> Self {
            let mut new = self.clone();

            let ty_var_level = self.next_ty_var_level();

            new.var_ty_stack
                .extend(vars.into_iter().map(|var_ty| (var_ty, ty_var_level)));
            new
        }

        pub(super) fn get_var_ty(&self, index: Idx) -> Option<&'a Type<'a>> {
            let (var_ty, ty_var_level) = *index.get(&self.var_ty_stack)?;
            let current_ty_var_level = self.next_ty_var_level();
            if ty_var_level == current_ty_var_level {
                return Some(var_ty);
            }
            debug_assert!(current_ty_var_level.deeper_than(ty_var_level));

            Some(var_ty.map_ty_vars(
                |level| {
                    let level = if level.deeper_than(ty_var_level) {
                        level.translate(ty_var_level, current_ty_var_level).expect(
                            "current ty_var_stack cannot be smaller than \
                            the ty_var_stack of a currently bound variable",
                        )
                    } else {
                        level
                    };
                    self.intern(Type::TyVar(level))
                },
                self,
            ))
        }
    }

    impl<'a, 'inn> TyArenaContext<'a> for Context<'a, 'inn> {
        type Inner = &'inn ContextInner<'a>;

        fn get_inner(&self) -> &'inn ContextInner<'a> {
            self.inner
        }
    }

    impl<'a> TyVarContext<'a> for Context<'a, '_> {
        type TyVar = TyBounds<'a>;

        fn push_ty_var(&self, ty_var_name: &'a str, ty_var: TyBounds<'a>) -> Self {
            let mut new = self.clone();
            new.ty_var_stack.push((ty_var_name, ty_var));
            new
        }

        fn get_ty_var(&self, level: Lvl) -> Option<(&'a str, TyBounds<'a>)> {
            level.get(&self.ty_var_stack).copied()
        }

        fn next_ty_var_level(&self) -> Lvl {
            Lvl::get_depth(&self.ty_var_stack)
        }

        fn get_ty_vars(&self) -> impl Iterator<Item = (&'a str, TyBounds<'a>)> {
            self.ty_var_stack.iter().copied()
        }
    }
}

/// Takes an [`untyped_ir::Term`][uir::Term] and checks that it can be typed, returning a
/// [`typed_ir::Term`][tir::Term], which is entirely type erased, along with a string
/// representing the type of the term.
///
/// # Errors
/// When type checking fails.
pub fn type_check<'i>(
    untyped_ir: &uir::Term<'i>,
) -> Result<(tir::Term<'i>, String), TypeCheckError> {
    let arena = Arena::new();
    let inner = ContextInner::new(&arena);
    let ctx = Context::with_inner(&inner);

    let (term, ty) = untyped_ir.type_check(None, false, &ctx)?;
    Ok((term, ty.display(&ctx)?))
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
        infer_ty_args: bool,
        ctx: &Context<'a, 'inn>,
    ) -> Result<(Self::TypeChecked, InternedType<'a>), TypeCheckError>;
}

impl<'i, 'a, 'inn, T: TypeCheck<'i, 'a, 'inn>> TypeCheck<'i, 'a, 'inn> for Box<T> {
    type TypeChecked = Box<T::TypeChecked>;

    fn type_check(
        &self,
        check_type: Option<InternedType<'a>>,
        infer_ty_args: bool,
        ctx: &Context<'a, 'inn>,
    ) -> Result<(Self::TypeChecked, InternedType<'a>), TypeCheckError> {
        T::type_check(self, check_type, infer_ty_args, ctx).map(|(term, ty)| (Box::new(term), ty))
    }
}

impl<'i: 'a, 'a, 'inn> TypeCheck<'i, 'a, 'inn> for uir::Term<'i> {
    type TypeChecked = tir::Term<'i>;

    fn type_check(
        &self,
        check_type: Option<InternedType<'a>>,
        infer_ty_args: bool,
        ctx: &Context<'a, 'inn>,
    ) -> Result<(Self::TypeChecked, InternedType<'a>), TypeCheckError> {
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

        let (term, ty) = match term {
            uir::RawTerm::Abs {
                arg_structure,
                arg_type: arg,
                body,
            } => {
                if let Some(arg) = arg {
                    let arg = arg.eval(ctx)?;

                    let (check_arg, check_result) =
                        if let Some(check_type) = take_concrete_check_type()? {
                            let Type::Arr {
                                arg: check_arg,
                                result: check_result,
                            } = check_type
                            else {
                                return Err(format!(
                                    "expected: {}\n\
                                got function definition",
                                    check_type.display(ctx)?
                                ));
                            };
                            (check_arg.known_not_never(), check_result.known_not_any())
                        } else {
                            (None, None)
                        };

                    if let Some(check_arg) = check_arg {
                        expect_type(check_arg, arg, false, false, ctx)?;
                    }

                    let destructured_arg_types = arg.destructure(arg_structure, ctx)?;
                    let ctx_ = ctx.push_var_tys(destructured_arg_types);
                    let (body, result) = body.type_check(check_result, true, &ctx_)?;

                    let ty = Type::Arr { arg, result };

                    (
                        tir::RawTerm::Abs {
                            arg_structure: arg_structure.clone(),
                            body,
                        },
                        ctx.intern(ty),
                    )
                } else if let Some(check_type) = take_concrete_check_type()? {
                    let Type::Arr {
                        arg: check_arg,
                        result: check_result,
                    } = check_type
                    else {
                        return Err(format!(
                            "expected: {}\n\
                            got function definition",
                            check_type.display(ctx)?
                        ));
                    };

                    let Some(check_arg) = check_arg.known() else {
                        return Err(format!(
                            "type inference error: cannot infer type of argument: {}",
                            "TODO"
                        ));
                    };
                    let check_result = check_result.known_not_any();

                    let check_destructured_args = check_arg.destructure(arg_structure, ctx)?;

                    let ctx_ = ctx.push_var_tys(check_destructured_args);
                    let (body, result) = body.type_check(check_result, true, &ctx_)?;

                    let ty = Type::Arr {
                        arg: check_arg,
                        result,
                    };

                    (
                        tir::RawTerm::Abs {
                            arg_structure: arg_structure.clone(),
                            body,
                        },
                        ctx.intern(ty),
                    )
                } else {
                    return Err(format!(
                        "type inference error: cannot infer type of argument: {}",
                        "TODO"
                    ));
                }
            }
            uir::RawTerm::App {
                func: func_term,
                arg: arg_term,
            } => {
                let check_type = check_type.take();
                let check_func = ctx.intern(Type::Arr {
                    arg: ctx.ty_unknown(),
                    result: check_type.unwrap_or(ctx.ty_unknown()),
                });

                // try infer but fall back if it fails
                let (func_term, func) =
                    func_term
                        .type_check(Some(check_func), true, ctx)
                        .or_else(|e| {
                            // TODO(errors): make this better :(
                            if e.contains("failed to infer") | e.contains("type inference error") {
                                func_term.type_check(None, false, ctx)
                            } else {
                                Err(e)
                            }
                        })?;

                match func.upper_concrete(ctx)? {
                    Type::Arr {
                        arg: func_arg,
                        result,
                    } => {
                        let (arg_term, arg) = arg_term.type_check(Some(func_arg), true, ctx)?;

                        // `type_check` should always return a
                        // subtype of `check_type` (ie. `func_arg`)
                        debug_assert_eq!(
                            expect_type(func_arg, arg, true, false, ctx)
                                .map_err(prepend(|| "incorrect argument type:"))
                                .map(|_| ()),
                            Ok(())
                        );

                        (
                            tir::RawTerm::App {
                                func: func_term,
                                arg: arg_term,
                            },
                            *result,
                        )
                    }
                    ty_abs @ Type::TyAbs { .. } => {
                        // TODO: maybe try pass some check info into this
                        let (arg_term, arg) = arg_term.type_check(None, false, ctx)?;

                        let check_func = ctx.intern(Type::Arr {
                            arg,
                            result: check_type.unwrap_or(ctx.ty_unknown()),
                        });
                        let inferred_func = expect_type(check_func, ty_abs, true, true, ctx)?;

                        let Type::Arr {
                            arg: _,
                            result: inferred_result,
                        } = inferred_func
                        else {
                            return Err("illegal failure: `expect_type` result is not subtype of `expected`".to_string());
                        };
                        (
                            tir::RawTerm::App {
                                func: func_term,
                                arg: arg_term,
                            },
                            *inferred_result,
                        )
                    }
                    _ => {
                        return Err(if let Some(check_type) = check_type {
                            format!(
                                "expected: {}\n\
                                got:      {}",
                                check_type.display(ctx)?,
                                func.display(ctx)?
                            )
                        } else {
                            format!(
                                "expected function\n\
                                got: {}",
                                func.display(ctx)?
                            )
                        });
                    }
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
                            // if check_name == TY_APP_NAME, the bounds will be checked afterwarss
                            // so its fine to leave it until then
                            TyBounds::expect_bounds(check_bounds, &bounds, true, ctx).map_err(
                                try_prepend(|| {
                                    Ok(format!(
                                        "expected bounds (or wider): {}\n\
                                        but found:                  {}",
                                        check_bounds.display(ctx)?,
                                        bounds.display(ctx)?
                                    ))
                                }),
                            )?;
                        }

                        (check_result.known_not_any(), None)
                    } else if infer_ty_args {
                        // expected something other than a type abstraction and we are allowed to
                        // infer ty_args so we attempt to do so
                        // we cannot pass down check_type as the ty_var contexts would diverge
                        (None, Some(check_type))
                    } else {
                        return Err(format!(
                            "expected: {}\n\
                            found a type abstraction",
                            check_type.display(ctx)?
                        ));
                    }
                } else {
                    (None, None)
                };

                let ctx_ = ctx.push_ty_var(name, bounds);
                let (body, result) = body.type_check(check_result, infer_ty_args, &ctx_)?;

                let ty_abs = ctx.intern(Type::TyAbs {
                    name,
                    bounds,
                    result,
                });

                let WithInfo(_info, body) = *body;

                if let Some(check_type) = infer {
                    // we should only be here if we are allowed to infer
                    debug_assert!(infer_ty_args);
                    let inferred = expect_type(check_type, ty_abs, true, true, ctx)?;
                    (body, inferred)
                } else {
                    (body, ty_abs)
                }
            }
            uir::RawTerm::TyApp { abs: abs_term, arg } => {
                let arg = arg.eval(ctx)?;

                let check_abs = ctx.intern(Type::TyAbs {
                    name: TY_APP_NAME,
                    bounds: TyBounds {
                        upper: Some(arg),
                        lower: Some(arg),
                    },
                    result: check_type.unwrap_or(ctx.ty_unknown()),
                });

                let (abs_term, abs) = abs_term.type_check(Some(check_abs), infer_ty_args, ctx)?;
                let WithInfo(_info, abs_term) = *abs_term;

                let Type::TyAbs {
                    name: _,
                    bounds,
                    result,
                } = abs
                else {
                    return Err(format!(
                        "cannot apply a type argument to type: {abs}",
                        abs = abs.display(ctx)?
                    ));
                };
                // bounds can't be unknown but anyway
                if let Some(upper) = bounds.get_upper(ctx).known_not_any() {
                    expect_type(upper, arg, true, false, ctx)
                        .map_err(prepend(|| "unsatisfied type arg upper bound:\n"))?;
                }
                if let Some(lower) = bounds.get_lower(ctx).known_not_never() {
                    expect_type(lower, arg, false, false, ctx)
                        .map_err(prepend(|| "unsatisfied type arg lower bound:\n"))?;
                }
                let ty = result.substitute_ty_var(ctx.next_ty_var_level(), arg, ctx);
                (abs_term, ty)
            }
            uir::RawTerm::Var(index) => {
                let ty = ctx.get_var_ty(*index).ok_or_else(|| {
                    format!("illegal failure: variable index not found: {index:?}\n")
                })?;

                let ty = if let Some(check_type) = check_type.take() {
                    expect_type(check_type, ty, true, infer_ty_args, ctx).map_err(try_prepend(
                        || {
                            Ok(format!(
                                "expected:     {}\n\
                                got var type: {}",
                                check_type.display(ctx)?,
                                ty.display(ctx)?,
                            ))
                        },
                    ))?
                } else {
                    ty
                };

                (tir::RawTerm::Var(*index), ty)
            }
            uir::RawTerm::Enum(arg, label) => {
                let arg = arg.eval(ctx)?;

                let (check_arg, check_enum) = if let Some(check_type) = take_concrete_check_type()?
                {
                    let Type::Arr {
                        arg: check_arg,
                        result: check_enum,
                    } = check_type
                    else {
                        return Err(format!(
                            "expected: {}\n\
                            found an enum constructor (a function)",
                            check_type.display(ctx)?
                        ));
                    };
                    (
                        check_arg.upper_concrete(ctx)?.known_not_never(),
                        check_enum.upper_concrete(ctx)?.known_not_any(),
                    )
                } else {
                    (None, None)
                };

                let arg = if let (Some(arg), Some(check_arg)) = (arg, check_arg) {
                    Some(expect_type(check_arg, arg, false, false, ctx)?)
                } else {
                    arg.or(check_arg)
                };

                if let Some(check_enum) = check_enum {
                    let Type::Enum(check_variants) = check_enum else {
                        return Err(format!(
                            "expected a function that returns: {}\n\
                            found an enum constructor (a function that returns an enum)",
                            check_enum.display(ctx)?
                        ));
                    };

                    let Some(check_variant_type) = check_variants.0.get(label) else {
                        return Err(format!(
                            "expected enum type does not contain label '{label}': {}",
                            check_enum.display(ctx)?
                        ));
                    };

                    let arg = if let Some(arg) = arg {
                        expect_type(check_variant_type, arg, true, false, ctx)?
                    } else {
                        check_variant_type
                    };

                    let result = ctx.intern(Type::Enum(
                        std::iter::once((*label, *check_variant_type)).collect(),
                    ));

                    let result = expect_type(check_enum, result, true, infer_ty_args, ctx)
                        .map_err(prepend(|| "incorrect enum result type:\n"))?;

                    (
                        tir::RawTerm::Enum(*label),
                        ctx.intern(Type::Arr { arg, result }),
                    )
                } else if let Some(arg) = arg {
                    let result = ctx.intern(Type::Enum(std::iter::once((*label, arg)).collect()));
                    (
                        tir::RawTerm::Enum(*label),
                        ctx.intern(Type::Arr { arg, result }),
                    )
                } else {
                    return Err(format!(
                        "type inference error: cannot infer type of enum constructor with label: '{label}'",
                    ));
                }
            }
            uir::RawTerm::Match(enum_type, arms) => {
                let enum_type = enum_type.eval(ctx)?;

                let (enum_type, check_result) =
                    if let Some(check_type) = take_concrete_check_type()? {
                        let Type::Arr {
                            arg: check_arg,
                            result: check_result,
                        } = check_type
                        else {
                            return Err(format!(
                                "expected: {}\n\
                            found a match expression (a function)",
                                check_type.display(ctx)?
                            ));
                        };

                        if let Some(enum_type) = enum_type {
                            expect_type(check_arg, enum_type, false, false, ctx)
                                .map_err(prepend(|| "incorrect match arg type:\n"))?;
                        }

                        (
                            enum_type.or(check_arg.upper_concrete(ctx)?.known_not_never()),
                            check_result.upper_concrete(ctx)?.known_not_any(),
                        )
                    } else {
                        (enum_type, None)
                    };

                if let Some(enum_type) = enum_type {
                    let Type::Enum(variants) = enum_type else {
                        return Err(format!(
                            "cannot match on a non-enum type: {enum_type}",
                            enum_type = enum_type.display(ctx)?
                        ));
                    };

                    let (arms, results): (HashMap<_, _>, Vec<_>) = arms
                        .iter()
                        .map(|(label, func_term)| -> Result<_, TypeCheckError> {
                            // check dead branches
                            let Some(variant) = variants.0.get(label) else {
                                return Err(format!(
                                    "enum type does not contain label '{label}': {enum_type}",
                                    enum_type = enum_type.display(ctx)?
                                ));
                            };

                            let check_func = ctx.intern(Type::Arr {
                                arg: variant,
                                result: check_result.unwrap_or(ctx.ty_unknown()),
                            });

                            let (func_term, func) =
                                func_term.type_check(Some(check_func), infer_ty_args, ctx)?;

                            let Type::Arr {
                                arg: func_arg,
                                result: func_result,
                            } = func
                            else {
                                return Err(format!(
                                    "match arm must be a function type: {func}",
                                    func = func.display(ctx)?
                                ));
                            };
                            expect_type(variant, func_arg, false, false, ctx)
                                .map_err(prepend(|| "incorrect match arm type:\n"))?;

                            Ok(Some(((*label, func_term), *func_result)))
                        })
                        .filter_map_ok(|o| o)
                        .try_collect()?;

                    variants.0.iter().try_for_each(|(label, _)| {
                        if arms.contains_key(label) {
                            Ok(())
                        } else {
                            Err(format!("match missing arm with label '{label}'"))
                        }
                    })?;
                    (
                        tir::RawTerm::Match(arms),
                        ctx.intern(Type::Arr {
                            arg: enum_type,
                            result: join(results, ctx)?,
                        }),
                    )
                } else {
                    let (arms, variants, results): (HashMap<_, _>, _, Vec<_>) = arms
                        .iter()
                        .map(|(label, func_term)| -> Result<_, TypeCheckError> {
                            let (func_term, func) = func_term.type_check(
                                Some(ctx.intern(Type::Arr {
                                    arg: ctx.ty_unknown(),
                                    result: ctx.ty_unknown(),
                                })),
                                true,
                                ctx,
                            )?;

                            let Type::Arr {
                                arg: func_arg,
                                result: func_result,
                            } = func
                            else {
                                return Err(format!(
                                    "match arm must be a function type: {func}",
                                    func = func.display(ctx)?
                                ));
                            };

                            Ok(Some((
                                (*label, func_term),
                                (*label, *func_arg),
                                *func_result,
                            )))
                        })
                        .filter_map_ok(|o| o)
                        .try_collect()?;
                    (
                        tir::RawTerm::Match(arms),
                        ctx.intern(Type::Arr {
                            arg: ctx.intern(Type::Enum(variants)),
                            result: join(results, ctx)?,
                        }),
                    )
                }
            }
            uir::RawTerm::Record(field_terms) => {
                let check_fields = take_concrete_check_type()?
                    .map(|check_type| {
                        let Type::Record(check_fields) = check_type else {
                            return Err(format!(
                                "expected: {}\n\
                                got a record type",
                                check_type.display(ctx)?
                            ));
                        };
                        for label in check_fields.0.keys() {
                            if !field_terms.iter().any(|(l, _)| l == label) {
                                return Err(format!("record missing field with label '{label}'"));
                            }
                        }
                        Ok(check_fields)
                    })
                    .transpose()?;

                let (field_terms, fields): (Vec<_>, _) = field_terms
                    .iter()
                    .map(|(label, field_term)| {
                        let check_field = check_fields
                            .and_then(|check_fields| check_fields.0.get(label).copied());

                        field_term
                            .type_check(check_field, infer_ty_args, ctx)
                            .map(|(field_term, field)| ((*label, field_term), (*label, field)))
                    })
                    .try_collect()?;
                (
                    tir::RawTerm::Record(field_terms.into_boxed_slice()),
                    ctx.intern(Type::Record(fields)),
                )
            }
            uir::RawTerm::Tuple(elem_terms) => {
                let check_elems = take_concrete_check_type()?
                    .map(|check_type| {
                        let Type::Tuple(check_elems) = check_type else {
                            return Err(format!(
                                "expected: {}\n\
                                got a tuple type",
                                check_type.display(ctx)?
                            ));
                        };
                        let len = elem_terms.len();
                        let check_len = check_elems.len();
                        if len != check_len {
                            return Err(format!(
                                "expected: {}\n\
                                got tuple with {len} elements",
                                check_type.display(ctx)?
                            ));
                        }
                        Ok(check_elems.iter().copied())
                    })
                    .transpose()?;
                let (elem_terms, elems): (Vec<_>, Vec<_>) = maybe_zip_eq(elem_terms, check_elems)
                    .map(|(elem_term, check_elem)| {
                        elem_term.type_check(check_elem, infer_ty_args, ctx)
                    })
                    .try_collect()?;
                (
                    tir::RawTerm::Tuple(elem_terms.into_boxed_slice()),
                    ctx.intern(Type::Tuple(elems.into_boxed_slice())),
                )
            }
            uir::RawTerm::Bool(b) => (tir::RawTerm::Bool(*b), ctx.intern(Type::Bool)),
        };

        debug_assert_ne!(ty.display(ctx), Ok("?".to_string()));

        // if we don't explicity check above (using `.take()`), we do a basic subtype check here
        let ty = if let Some(check_type) = check_type.take() {
            expect_type(check_type, ty, true, infer_ty_args, ctx).map_err(try_prepend(|| {
                Ok(format!(
                    "expected: {}\n\
                    got:      {}",
                    check_type.display(ctx)?,
                    ty.display(ctx)?,
                ))
            }))?
        } else {
            ty
        };

        Ok((WithInfo(*info, term), ty))
    }
}
