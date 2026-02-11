use std::collections::HashMap;

use itertools::Itertools;

use crate::common::WithInfo;
use crate::reprs::ast;
use crate::reprs::common::{ArgStructure, Label, RawArgStructure};
use crate::reprs::untyped_ir as ir;

use self::context::Context;
pub use self::error::ValidationError;

mod context {
    use crate::reprs::common::{Idx, Lvl};

    /// Cheaply cloneable (hopefully) append-only stack
    type Stack<T> = Vec<T>;

    #[must_use]
    #[derive(Clone)]
    pub(super) struct Context<'i> {
        var_stack: Stack<&'i str>,
        ty_var_stack: Stack<&'i str>,
    }

    impl<'i> Context<'i> {
        pub(super) fn new() -> Self {
            Self {
                var_stack: Vec::new(),
                ty_var_stack: Vec::new(),
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

        pub(super) fn push_ty_var(&self, ty_var: &'i str) -> Self {
            let mut new = self.clone();
            new.ty_var_stack.push(ty_var);
            new
        }

        pub(super) fn find_ty_var(&self, name: &'i str) -> Option<Lvl> {
            Lvl::find(&self.ty_var_stack, |ty_var| *ty_var == name)
        }
    }
}

mod error {
    use std::{borrow::Cow, ops::Range};

    use annotate_snippets::{AnnotationKind, Group, Level, Snippet};

    pub enum ValidationError<'i> {
        VarNotFound {
            ty_var: bool,
            name: &'i str,
            span: Range<usize>,
        },
        SameLabel {
            name: &'i str,
            first_span: Range<usize>,
            second_span: Range<usize>,
        },
    }

    impl<'i> ValidationError<'i> {
        pub fn into_record(
            self,
            source: &'i str,
            origin: impl Into<Cow<'i, str>>,
        ) -> Vec<Group<'i>> {
            let snippet = Snippet::source(source).path(origin.into());

            let group = match self {
                ValidationError::VarNotFound { ty_var, name, span } => Level::ERROR
                    .primary_title(format!(
                        "{}variable '{name}' not found",
                        if ty_var { "type " } else { "" }
                    ))
                    .element(snippet.annotation(AnnotationKind::Primary.span(span))),
                ValidationError::SameLabel {
                    name,
                    first_span,
                    second_span,
                } => Level::ERROR
                    .primary_title(format!("label '{name}' appears multiple times"))
                    .element(
                        snippet
                            .annotation(
                                AnnotationKind::Context
                                    .span(first_span)
                                    .label("initially appears here"),
                            )
                            .annotation(
                                AnnotationKind::Primary
                                    .span(second_span)
                                    .label("appears here again"),
                            ),
                    ),
            };

            vec![group]
        }
    }
}

type Result<'i, T> = std::result::Result<T, ValidationError<'i>>;

trait Validate<'i> {
    type Validated;
    fn validate(&self, ctx: &Context<'i>) -> Result<'i, Self::Validated>;
}

/// Takes an [`ast::Term`] and checks that it is 'valid', returning an
/// [`untyped_ir::Term`][ir::Term], which contains this encoded information.
///
/// The actual validated and/or encoded information includes:
/// - (type) variable name resolution (encoded in de Bruijn indexes/levels)
/// - enum type and match label uniqueness
///
/// # Errors
/// When validation fails.
pub fn validate<'i>(ast: &ast::Term<'i>) -> Result<'i, ir::Term<'i>> {
    let ctx = Context::new();
    ast.validate(&ctx)
}

impl<'i, T: Validate<'i>> Validate<'i> for Box<T> {
    type Validated = Box<T::Validated>;

    fn validate(&self, ctx: &Context<'i>) -> Result<'i, Self::Validated> {
        T::validate(self, ctx).map(Box::new)
    }
}

impl<'i, T: Validate<'i>> Validate<'i> for Option<T> {
    type Validated = Option<T::Validated>;

    fn validate(&self, ctx: &Context<'i>) -> Result<'i, Self::Validated> {
        self.as_ref().map(|t| t.validate(ctx)).transpose()
    }
}

impl<'i> Validate<'i> for ast::Term<'i> {
    type Validated = ir::Term<'i>;

    fn validate(&self, ctx: &Context<'i>) -> Result<'i, Self::Validated> {
        let WithInfo(info, term) = self;

        let term = match term {
            ast::RawTerm::Abs {
                arg,
                arg_type,
                body,
            } => {
                let (arg_structure, arg_vars) = extract_idents(arg)?;
                ir::RawTerm::Abs {
                    arg_structure,
                    arg_type: arg_type.validate(ctx)?,
                    body: body.validate(&ctx.push_vars(arg_vars.map(|i| i.0.text)))?,
                }
            }
            ast::RawTerm::App { func, arg } => ir::RawTerm::App {
                func: func.validate(ctx)?,
                arg: arg.validate(ctx)?,
            },
            ast::RawTerm::TyAbs { arg, bounds, body } => ir::RawTerm::TyAbs {
                name: arg.0.text,
                bounds: bounds.validate(ctx)?,
                body: body.validate(&ctx.push_ty_var(arg.0.text))?,
            },
            ast::RawTerm::TyApp { func, arg } => ir::RawTerm::TyApp {
                abs: func.validate(ctx)?,
                arg: arg.validate(ctx)?,
            },
            ast::RawTerm::Var(ident) => {
                let Some(index) = ctx.find_var(ident.0.text) else {
                    return Err(ValidationError::VarNotFound {
                        ty_var: false,
                        name: ident.0.text,
                        span: ident.0.range(),
                    });
                };
                ir::RawTerm::Var(index)
            }
            ast::RawTerm::Enum(enum_type, variant) => {
                ir::RawTerm::Enum(enum_type.validate(ctx)?, Label(variant.0.text))
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
                    .map_ok(|(_, l, t)| t.validate(ctx).map(|t| (l, t)))
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

    fn validate(&self, ctx: &Context<'i>) -> Result<'i, Self::Validated> {
        let WithInfo(info, ty) = self;

        let ty = match ty {
            ast::RawType::TyAbs {
                arg,
                bounds,
                result,
            } => ir::RawType::TyAbs {
                name: arg.0.text,
                bounds: bounds.validate(ctx)?,
                result: result.validate(&ctx.push_ty_var(arg.0.text))?,
            },
            ast::RawType::TyVar(ident) => {
                let Some(level) = ctx.find_ty_var(ident.0.text) else {
                    return Err(ValidationError::VarNotFound {
                        ty_var: true,
                        name: ident.0.text,
                        span: ident.0.range(),
                    });
                };
                ir::RawType::TyVar(level)
            }
            ast::RawType::Arr { arg, result } => ir::RawType::Arr {
                arg: arg.validate(ctx)?,
                result: result.validate(ctx)?,
            },
            ast::RawType::Enum(variants) => ir::RawType::Enum(
                check_unique_labels(variants)
                    .map_ok(|(_, l, t)| t.validate(ctx).map(|t| (l, t)))
                    .flatten_ok()
                    .try_collect()?,
            ),
            ast::RawType::Record(fields) => ir::RawType::Record(
                check_unique_labels(fields)
                    .map_ok(|(_, l, t)| t.validate(ctx).map(|t| (l, t)))
                    .flatten_ok()
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

    fn validate(&self, ctx: &Context<'i>) -> Result<'i, Self::Validated> {
        let ast::TyBounds { upper, lower } = self;
        Ok(ir::TyBounds {
            upper: upper.as_ref().map(|ty| ty.validate(ctx)).transpose()?,
            lower: lower.as_ref().map(|ty| ty.validate(ctx)).transpose()?,
        })
    }
}

fn extract_idents<'a, 'i>(
    assignee: &'a ast::Assignee<'i>,
) -> Result<'i, (ArgStructure<'i>, impl Iterator<Item = &'a ast::Ident<'i>>)> {
    fn extract_idents_inner<'a, 'i>(
        assignee: &'a ast::Assignee<'i>,
        idents: &mut Vec<&'a ast::Ident<'i>>,
    ) -> Result<'i, ArgStructure<'i>> {
        let WithInfo(span, assignee) = assignee;

        let st = match assignee {
            ast::RawAssignee::Record(fields) => RawArgStructure::Record(
                check_unique_labels(fields)
                    .map_ok(|(ident, label, assignee)| {
                        Ok((
                            label,
                            if let Some(assignee) = assignee {
                                extract_idents_inner(assignee, idents)?
                            } else {
                                idents.push(ident);
                                WithInfo(ident.0, RawArgStructure::Var)
                            },
                        ))
                    })
                    .map(Result::flatten)
                    .try_collect()?,
            ),
            ast::RawAssignee::Tuple(elements) => RawArgStructure::Tuple(
                elements
                    .iter()
                    .map(|assignee| extract_idents_inner(assignee, idents))
                    .try_collect()?,
            ),
            ast::RawAssignee::Ident(ident) => {
                idents.push(ident);
                RawArgStructure::Var
            }
        };

        Ok(WithInfo(*span, st))
    }
    let mut idents = Vec::new();
    Ok((
        extract_idents_inner(assignee, &mut idents)?,
        idents.into_iter(),
    ))
}

fn check_unique_labels<'i, 'a, I>(
    labelled_items: &'a [(ast::Ident<'i>, I)],
) -> impl Iterator<Item = Result<'i, (&'a ast::Ident<'i>, Label<'i>, &'a I)>> {
    let mut labels = HashMap::new();
    labelled_items.iter().map(move |(ident, i)| {
        let label = Label(ident.0.text);
        if let Some(prev_ident) = labels.insert(label, ident) {
            return Err(ValidationError::SameLabel {
                name: label.0,
                first_span: prev_ident.0.range(),
                second_span: ident.0.range(),
            });
        }
        Ok((ident, label, i))
    })
}
