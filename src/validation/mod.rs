use std::cell::RefCell;
use std::collections::HashMap;
use std::iter::once;

use itertools::Itertools;

use crate::common::WithInfo;
use crate::importing::{ImportError, ImportId, ImportResolver};
use crate::reprs::ast::{self, RawAssignee, RawTermAssignee};
use crate::reprs::common::{
    ArgStructure, ArgTypeStructure, Label, Lvl, RawArgStructure, RawArgTermStructure,
    RawArgTypeStructure, Span,
};
use crate::reprs::untyped_ir as ir;

use self::context::{Context, ContextInner};
pub use self::error::{ValidationError, VarKind};

mod context {
    use std::{cell::RefCell, collections::HashMap};

    use derive_where::derive_where;

    use crate::{
        importing::{ImportError, ImportId, ImportResolver},
        reprs::common::{Idx, Lvl, Span},
        validation::ImportTermInfo,
    };

    /// Cheaply cloneable (hopefully) append-only stack
    type Stack<T> = Vec<T>;

    pub(super) struct ContextInner<'i> {
        import_id: ImportId,
        imports_resolved: RefCell<HashMap<ImportId, ImportTermInfo<'i>>>,
    }

    impl<'i> ContextInner<'i> {
        pub(super) fn new(import_id: ImportId) -> Self {
            Self {
                import_id,
                imports_resolved: RefCell::new(HashMap::new()),
            }
        }

        pub(super) fn into_imports_resolved(self) -> HashMap<ImportId, ImportTermInfo<'i>> {
            self.imports_resolved.into_inner()
        }
    }

    #[must_use]
    #[derive_where(Clone)]
    pub(super) struct Context<'i, 'inn, IR: ImportResolver> {
        inner: &'inn ContextInner<'i>,
        import_resolver: &'inn RefCell<&'inn mut IR>,

        var_stack: Stack<&'i str>,
        ty_var_stack: Stack<&'i str>,
        effect_stack: Stack<&'i str>,
    }

    impl<'i, 'inn, IR: ImportResolver> Context<'i, 'inn, IR> {
        pub(super) fn new(
            inner: &'inn ContextInner<'i>,
            import_resolver: &'inn RefCell<&'inn mut IR>,
        ) -> Self {
            Self {
                inner,
                import_resolver,

                var_stack: Vec::new(),
                ty_var_stack: Vec::new(),
                effect_stack: Vec::new(),
            }
        }

        pub(super) fn push_vars(&self, vars: impl IntoIterator<Item = &'i str>) -> Self {
            let mut new = self.clone();
            new.var_stack.extend(vars);
            new
        }

        pub(super) fn find_var(&self, name: &'i str) -> Option<Idx> {
            Idx::find(&self.var_stack, |var| *var == name)
        }

        pub(super) fn push_ty_vars(&self, ty_vars: impl IntoIterator<Item = &'i str>) -> Self {
            let mut new = self.clone();
            new.ty_var_stack.extend(ty_vars);
            new
        }

        pub(super) fn find_ty_var(&self, name: &'i str) -> Option<Lvl> {
            Lvl::find(&self.ty_var_stack, |ty_var| *ty_var == name)
        }

        pub(super) fn push_eff_vars(&self, effects: impl IntoIterator<Item = &'i str>) -> Self {
            let mut new = self.clone();
            new.effect_stack.extend(effects);
            new
        }

        pub(super) fn find_eff_var(&self, name: &'i str) -> Option<Lvl> {
            Lvl::find(&self.effect_stack, |effect| *effect == name)
        }

        pub(super) fn resolve_relative_import(
            &self,
            path: &'i str,
            span: Span<'i>,
        ) -> Result<ImportId, ImportError> {
            let import_id = self
                .import_resolver
                .borrow_mut()
                .resolve_relative(self.inner.import_id, path)?;
            self.inner
                .imports_resolved
                .borrow_mut()
                .entry(import_id)
                .or_insert(ImportTermInfo { path, span });
            Ok(import_id)
        }

        pub(super) fn resolve_package_import(
            &self,
            package: &'i str,
            path: &'i str,
            span: Span<'i>,
        ) -> Result<ImportId, ImportError> {
            let import_id = self
                .import_resolver
                .borrow_mut()
                .resolve_package(package, path)?;
            self.inner
                .imports_resolved
                .borrow_mut()
                .entry(import_id)
                .or_insert(ImportTermInfo { path, span });
            Ok(import_id)
        }
    }
}

mod error {
    use std::borrow::Cow;

    use annotate_snippets::{AnnotationKind, Group, Level};

    use crate::{error::RenderError, reprs::common::Span, validation::ImportTermInfo};

    pub enum VarKind {
        Normal,
        Type,
        Effect,
    }

    pub enum ValidationError<'i> {
        VarNotFound {
            var_kind: VarKind,
            name: &'i str,
            span: Span<'i>,
        },
        SameLabel {
            name: &'i str,
            first_span: Span<'i>,
            second_span: Span<'i>,
        },
        FailedImport {
            path: &'i str,
            info: Cow<'i, str>,
            span: Span<'i>,
        },
        CyclicImport {
            cycle: Box<[ImportTermInfo<'i>]>,
            last: ImportTermInfo<'i>,
        },
    }

    impl<'i> RenderError<'i> for ValidationError<'i> {
        fn push_groups(self, buf: &mut Vec<Group<'i>>) {
            let group = match self {
                ValidationError::VarNotFound {
                    var_kind,
                    name,
                    span,
                } => Level::ERROR
                    .primary_title(format!(
                        "{}variable '{name}' not found",
                        match var_kind {
                            VarKind::Normal => "",
                            VarKind::Type => "type ",
                            VarKind::Effect => "effect ",
                        }
                    ))
                    .element(
                        span.snippet()
                            .annotation(span.annotation(AnnotationKind::Primary)),
                    ),
                ValidationError::SameLabel {
                    name,
                    first_span,
                    second_span,
                } => Level::ERROR
                    .primary_title(format!("label '{name}' appears multiple times"))
                    .element(
                        // we assume the same file
                        first_span
                            .snippet()
                            .annotation(
                                first_span
                                    .annotation(AnnotationKind::Context)
                                    .label("initially appears here"),
                            )
                            .annotation(
                                second_span
                                    .annotation(AnnotationKind::Primary)
                                    .label("appears here again"),
                            ),
                    ),
                ValidationError::FailedImport { path, info, span } => Level::ERROR
                    .primary_title(format!("failed to import path '{path}'"))
                    .element(
                        span.snippet()
                            .annotation(span.annotation(AnnotationKind::Primary)),
                    )
                    .elements(if info.is_empty() {
                        None
                    } else {
                        Some(Level::INFO.message(info))
                    }),
                ValidationError::CyclicImport {
                    cycle,
                    last:
                        ImportTermInfo {
                            path: last_path,
                            span: last_span,
                        },
                } => Level::ERROR
                    .primary_title("cyclic import detected".to_string())
                    .elements(cycle.iter().map(|ImportTermInfo { path, span }| {
                        span.snippet().annotation(
                            span.annotation(AnnotationKind::Primary)
                                .label(format!("while importing '{path}'...")),
                        )
                    }))
                    .element(last_span.snippet().annotation(
                        last_span.annotation(AnnotationKind::Primary).label(format!(
                            "imported a path already being imported: '{last_path}'"
                        )),
                    )),
            };

            buf.push(group);
        }
    }
}

type Result<'i, T> = std::result::Result<T, ValidationError<'i>>;

#[derive(Copy, Clone)]
pub struct ImportTermInfo<'i> {
    pub path: &'i str,
    pub span: Span<'i>,
}

/// Takes an [`ast::Term`] and checks that it is 'valid', returning an
/// [`untyped_ir::Term`][ir::Term], which contains this encoded information
/// Also resolves any imports and returns them.
///
/// The actual validated and/or encoded information includes:
/// - (type) variable name resolution (encoded in de Bruijn indexes/levels)
/// - import resolution
/// - enum type and match label uniqueness
///
/// # Errors
/// When validation fails.
pub fn validate<'i>(
    import_id: ImportId,
    ast: &ast::Term<'i>,
    import_resolver: &mut impl ImportResolver,
) -> Result<'i, (ir::Term<'i>, HashMap<ImportId, ImportTermInfo<'i>>)> {
    let inner = ContextInner::new(import_id);
    let import_resolver = RefCell::new(import_resolver);
    let ctx = Context::new(&inner, &import_resolver);
    let untyped_ir = ast.validate(&ctx)?;
    Ok((untyped_ir, inner.into_imports_resolved()))
}

trait Validate<'i> {
    type Validated;
    fn validate(&self, ctx: &Context<'i, '_, impl ImportResolver>) -> Result<'i, Self::Validated>;
}

impl<'i, T: Validate<'i>> Validate<'i> for Box<T> {
    type Validated = Box<T::Validated>;

    fn validate(&self, ctx: &Context<'i, '_, impl ImportResolver>) -> Result<'i, Self::Validated> {
        T::validate(self, ctx).map(Box::new)
    }
}

impl<'i, T: Validate<'i>> Validate<'i> for Option<T> {
    type Validated = Option<T::Validated>;

    fn validate(&self, ctx: &Context<'i, '_, impl ImportResolver>) -> Result<'i, Self::Validated> {
        self.as_ref().map(|t| t.validate(ctx)).transpose()
    }
}

impl<'i> Validate<'i> for ast::Term<'i> {
    type Validated = ir::Term<'i>;

    fn validate(&self, ctx: &Context<'i, '_, impl ImportResolver>) -> Result<'i, Self::Validated> {
        let WithInfo(info, term) = self;

        let term = match term {
            ast::RawTerm::Abs {
                arg,
                arg_type,
                effects,
                body,
            } => {
                let (arg_structure, arg_vars, ty_vars) = extract_idents(arg)?;
                let effects = effects.validate(ctx)?.unwrap_or_default();
                ir::RawTerm::Abs {
                    arg_structure,
                    arg_type: arg_type.validate(ctx)?,
                    body: body.validate(
                        &ctx.push_vars(arg_vars.map(|i| i.0.text()))
                            .push_ty_vars(ty_vars.map(|i| i.0.text()))
                            .push_eff_vars(effects.0.iter().filter_map(|(n, _)| n.map(|n| n.0))),
                    )?,
                    effects,
                }
            }
            ast::RawTerm::App { func, effects, arg } => ir::RawTerm::App {
                func: func.validate(ctx)?,
                effects: effects.validate(ctx)?.unwrap_or_default(),
                arg: arg.validate(ctx)?,
            },
            ast::RawTerm::TyAbs { arg, bounds, body } => ir::RawTerm::TyAbs {
                name: arg.0.text(),
                bounds: bounds.validate(ctx)?,
                body: body.validate(&ctx.push_ty_vars(once(arg.0.text())))?,
            },
            ast::RawTerm::TyApp { func, arg } => ir::RawTerm::TyApp {
                abs: func.validate(ctx)?,
                arg: arg.validate(ctx)?,
            },
            ast::RawTerm::EffAbs { arg, body } => ir::RawTerm::EffAbs {
                name: Label(arg.0.text()),
                body: body.validate(&ctx.push_eff_vars(once(arg.0.text())))?,
            },
            ast::RawTerm::EffApp { abs, effects } => ir::RawTerm::EffApp {
                abs: abs.validate(ctx)?,
                effects: effects.validate(ctx)?,
            },
            ast::RawTerm::Var(ident) => {
                let Some(index) = ctx.find_var(ident.0.text()) else {
                    return Err(ValidationError::VarNotFound {
                        var_kind: VarKind::Normal,
                        name: ident.0.text(),
                        span: ident.0,
                    });
                };
                ir::RawTerm::Var(index)
            }
            ast::RawTerm::Type(ty) => ir::RawTerm::Type(ty.validate(ctx)?),
            ast::RawTerm::Handle(effect) => ir::RawTerm::Handle(effect.validate(ctx)?),
            ast::RawTerm::Trigger(effect) => ir::RawTerm::Trigger(effect.validate(ctx)?),
            ast::RawTerm::Import(path) => ir::RawTerm::Import(match path {
                ast::ImportPath::Relative { span } => WithInfo(
                    *span,
                    ctx.resolve_relative_import(span.text(), *span)
                        .map_err(|err| match err {
                            ImportError::Path(msg) | ImportError::Package(msg) => {
                                ValidationError::FailedImport {
                                    path: span.text(),
                                    info: msg.into(),
                                    span: *span,
                                }
                            }
                            ImportError::Other(msg) => ValidationError::FailedImport {
                                path: span.text(),
                                info: msg.into(),
                                span: *info,
                            },
                        })?,
                ),
                ast::ImportPath::Package {
                    span,
                    package,
                    path,
                } => WithInfo(
                    *path,
                    ctx.resolve_package_import(package.text(), path.text(), *span)
                        .map_err(|err| {
                            let span = *match err {
                                ImportError::Path(_) => path,
                                ImportError::Package(_) => package,
                                ImportError::Other(_) => span,
                            };
                            ValidationError::FailedImport {
                                path: span.text(),
                                info: err.into_msg().into(),
                                span,
                            }
                        })?,
                ),
            }),
            ast::RawTerm::Fold(rec_type) => ir::RawTerm::Fold(rec_type.validate(ctx)?),
            ast::RawTerm::Unfold(rec_type) => ir::RawTerm::Unfold(rec_type.validate(ctx)?),
            ast::RawTerm::Enum(enum_type, variant) => {
                ir::RawTerm::Enum(enum_type.validate(ctx)?, Label(variant.0.text()))
            }
            ast::RawTerm::Match(enum_type, arms) => ir::RawTerm::Match(
                enum_type.validate(ctx)?,
                check_unique_labels(arms)
                    .map_ok(|(_, l, t)| t.validate(ctx).map(|t| (l, t)))
                    .map(Result::flatten)
                    .try_collect()?,
            ),
            ast::RawTerm::Record(fields) => ir::RawTerm::Record(
                check_unique_labels(fields)
                    .map_ok(|(i, l, t)| {
                        (t.as_ref()
                            .unwrap_or(&WithInfo(i.0, ast::RawTerm::Var(ast::Ident(i.0)))))
                        .validate(ctx)
                        .map(|t| (l, t))
                    })
                    .map(Result::flatten)
                    .try_collect()?,
            ),
            ast::RawTerm::Tuple(elements) => {
                ir::RawTerm::Tuple(elements.iter().map(|t| t.validate(ctx)).try_collect()?)
            }
            ast::RawTerm::Bool(b) => ir::RawTerm::Bool(*b),
        };

        Ok(WithInfo(*info, term))
    }
}

impl<'i> Validate<'i> for ast::Type<'i> {
    type Validated = ir::Type<'i>;

    fn validate(&self, ctx: &Context<'i, '_, impl ImportResolver>) -> Result<'i, Self::Validated> {
        let WithInfo(info, ty) = self;

        let ty = match ty {
            ast::RawType::TyAbs {
                arg,
                bounds,
                result,
            } => ir::RawType::TyAbs {
                name: arg.0.text(),
                bounds: bounds.validate(ctx)?,
                result: result.validate(&ctx.push_ty_vars(once(arg.0.text())))?,
            },
            ast::RawType::TyApp { abs, arg } => ir::RawType::TyApp {
                abs: abs.validate(ctx)?,
                arg: arg.validate(ctx)?,
            },
            ast::RawType::RecAbs { arg, result } => ir::RawType::RecAbs {
                name: arg.0.text(),
                result: result.validate(&ctx.push_ty_vars(once(arg.0.text())))?,
            },
            ast::RawType::TyVar(ident) => {
                let Some(level) = ctx.find_ty_var(ident.0.text()) else {
                    return Err(ValidationError::VarNotFound {
                        var_kind: VarKind::Type,
                        name: ident.0.text(),
                        span: ident.0,
                    });
                };
                ir::RawType::TyVar(level)
            }
            ast::RawType::Arr {
                arg,
                effects,
                result,
            } => ir::RawType::Arr {
                arg: arg.validate(ctx)?,
                effects: effects.validate(ctx)?.unwrap_or_default(),
                result: result.validate(ctx)?,
            },
            ast::RawType::Enum(variants) => ir::RawType::Enum(
                check_unique_labels(variants)
                    .map_ok(|(_, l, t)| t.validate(ctx).map(|t| (l, t)))
                    .map(Result::flatten)
                    .try_collect()?,
            ),
            ast::RawType::Record(fields) => ir::RawType::Record(
                check_unique_labels(fields)
                    .map_ok(|(i, l, t)| {
                        (t.as_ref()
                            .unwrap_or(&WithInfo(i.0, ast::RawType::TyVar(ast::Ident(i.0)))))
                        .validate(ctx)
                        .map(|t| (l, t))
                    })
                    .map(Result::flatten)
                    .try_collect()?,
            ),
            ast::RawType::Tuple(elements) => {
                ir::RawType::Tuple(elements.iter().map(|t| t.validate(ctx)).try_collect()?)
            }
            ast::RawType::Bool => ir::RawType::Bool,
            ast::RawType::Any => ir::RawType::Any,
            ast::RawType::Never => ir::RawType::Never,
        };
        Ok(WithInfo(*info, ty))
    }
}

impl<'i> Validate<'i> for ast::TyBounds<'i> {
    type Validated = ir::TyBounds<'i>;

    fn validate(&self, ctx: &Context<'i, '_, impl ImportResolver>) -> Result<'i, Self::Validated> {
        let ast::TyBounds { upper, lower } = self;
        Ok(ir::TyBounds {
            upper: upper.as_ref().map(|ty| ty.validate(ctx)).transpose()?,
            lower: lower.as_ref().map(|ty| ty.validate(ctx)).transpose()?,
        })
    }
}

impl<'i> Validate<'i> for ast::Effect<'i> {
    type Validated = ir::Effect<'i>;

    fn validate(&self, ctx: &Context<'i, '_, impl ImportResolver>) -> Result<'i, Self::Validated> {
        let WithInfo(info, effect) = self;

        let effect = match effect {
            ast::RawEffect::Def { name, arg, result } => ir::RawEffect::Def {
                name: Label(name.0.text()),
                arg: arg.validate(ctx)?,
                result: result.validate(ctx)?,
            },
        };
        Ok(WithInfo(*info, effect))
    }
}

impl<'i> Validate<'i> for ast::EffectGroup<'i, ast::Effect<'i>> {
    type Validated = ir::EffectGroup<'i, ir::Effect<'i>>;

    fn validate(&self, ctx: &Context<'i, '_, impl ImportResolver>) -> Result<'i, Self::Validated> {
        let ast::EffectGroup(effects) = self;
        let effects = check_unique_optional_labels(effects)
            .map_ok(|(label, e)| e.validate(ctx).map(|e| (label.map(|(_, l)| l), e)))
            .map(Result::flatten)
            .try_collect()?;
        Ok(ir::EffectGroup(effects))
    }
}
impl<'i> Validate<'i> for ast::EffectGroup<'i, ast::Ident<'i>> {
    type Validated = ir::EffectGroup<'i, Lvl>;

    fn validate(&self, ctx: &Context<'i, '_, impl ImportResolver>) -> Result<'i, Self::Validated> {
        let ast::EffectGroup(effects) = self;
        let effects = check_unique_optional_labels(effects)
            .map_ok(|(label, ident)| {
                let Some(level) = ctx.find_eff_var(ident.0.text()) else {
                    Err(ValidationError::VarNotFound {
                        var_kind: VarKind::Effect,
                        name: ident.0.text(),
                        span: ident.0,
                    })?
                };
                Ok((label.map(|(_, l)| l), level))
            })
            .map(Result::flatten)
            .try_collect()?;
        Ok(ir::EffectGroup(effects))
    }
}

/// # Returns
/// (`arg_structure`, `var_idents`, `ty_var_idents`)
fn extract_idents<'a, 'i>(
    assignee: &'a ast::Assignee<'i>,
) -> Result<
    'i,
    (
        ArgStructure<'i>,
        impl Iterator<Item = &'a ast::Ident<'i>>,
        impl Iterator<Item = &'a ast::Ident<'i>>,
    ),
> {
    fn extract_idents_inner<'i, 'a, A1, A2>(
        assignee: &'a ast::RawAssignee<'i, A1>,
        idents: &mut Vec<&'a ast::Ident<'i>>,
        mut inner: impl FnMut(
            &'a A1,
            &mut Vec<&'a ast::Ident<'i>>,
        ) -> Result<'i, WithInfo<Span<'i>, A2>>,
        wrap: impl Fn(RawArgStructure<'i, WithInfo<Span<'i>, A2>>) -> A2,
    ) -> Result<'i, A2> {
        let st = match assignee {
            RawAssignee::Record(fields) => RawArgStructure::Record(
                check_unique_labels(fields)
                    .map_ok(|(ident, label, assignee)| {
                        Ok((
                            label,
                            if let Some(assignee) = assignee {
                                inner(assignee, idents)?
                            } else {
                                idents.push(ident);
                                WithInfo(ident.0, wrap(RawArgStructure::Var))
                            },
                        ))
                    })
                    .map(Result::flatten)
                    .try_collect()?,
            ),
            RawAssignee::Tuple(elements) => RawArgStructure::Tuple(
                elements
                    .iter()
                    .map(|assignee| inner(assignee, idents))
                    .try_collect()?,
            ),
            RawAssignee::Ident(ident) => {
                idents.push(ident);
                RawArgStructure::Var
            }
        };
        Ok(wrap(st))
    }

    fn extract_term_idents_inner<'i, 'a>(
        assignee: &'a ast::Assignee<'i>,
        term_idents: &mut Vec<&'a ast::Ident<'i>>,
        type_idents: &mut Vec<&'a ast::Ident<'i>>,
    ) -> Result<'i, ArgStructure<'i>> {
        let WithInfo(span, assignee) = assignee;

        let st = match assignee {
            RawTermAssignee::Term(assignee) => extract_idents_inner(
                assignee,
                term_idents,
                |assignee, term_idents| {
                    extract_term_idents_inner(assignee, term_idents, type_idents)
                },
                RawArgTermStructure::Term,
            )?,
            RawTermAssignee::Type(assignee) => {
                RawArgTermStructure::Type(extract_type_idents_inner(assignee, type_idents)?)
            }
        };

        Ok(WithInfo(*span, st))
    }

    fn extract_type_idents_inner<'i, 'a>(
        assignee: &'a ast::TypeAssignee<'i>,
        idents: &mut Vec<&'a ast::Ident<'i>>,
    ) -> Result<'i, ArgTypeStructure<'i>> {
        let WithInfo(span, assignee) = assignee;

        let st = extract_idents_inner(
            &assignee.0,
            idents,
            extract_type_idents_inner,
            RawArgTypeStructure,
        )?;

        Ok(WithInfo(*span, st))
    }
    let mut term_idents = Vec::new();
    let mut type_idents = Vec::new();
    Ok((
        extract_term_idents_inner(assignee, &mut term_idents, &mut type_idents)?,
        term_idents.into_iter(),
        type_idents.into_iter(),
    ))
}

fn check_unique_labels<'i, 'a, I>(
    labelled_items: &'a [(ast::Ident<'i>, I)],
) -> impl Iterator<Item = Result<'i, (&'a ast::Ident<'i>, Label<'i>, &'a I)>> {
    let mut labels = HashMap::new();
    labelled_items.iter().map(move |(ident, i)| {
        let label = Label(ident.0.text());
        if let Some(prev_ident) = labels.insert(label, ident) {
            return Err(ValidationError::SameLabel {
                name: label.0,
                first_span: prev_ident.0,
                second_span: ident.0,
            });
        }
        Ok((ident, label, i))
    })
}
fn check_unique_optional_labels<'i, 'a, I>(
    labelled_items: &'a [(Option<ast::Ident<'i>>, I)],
) -> impl Iterator<Item = Result<'i, (Option<(&'a ast::Ident<'i>, Label<'i>)>, &'a I)>> {
    let mut labels = HashMap::new();
    labelled_items.iter().map(move |(ident, i)| {
        if let Some(ident) = ident {
            let label = Label(ident.0.text());
            if let Some(prev_ident) = labels.insert(label, ident) {
                return Err(ValidationError::SameLabel {
                    name: label.0,
                    first_span: prev_ident.0,
                    second_span: ident.0,
                });
            }
            Ok((Some((ident, label)), i))
        } else {
            Ok((None, i))
        }
    })
}
