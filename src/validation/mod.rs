use itertools::Itertools;

use crate::common::WithInfo;
use crate::reprs::ast;
use crate::reprs::common::{ArgStructure, EnumLabel};
use crate::reprs::untyped_ir as ir;

use self::context::Context;

mod context {
    /// Cheaply cloneable (hopefully) append-only stack
    type Stack<T> = Vec<T>;

    #[must_use]
    #[derive(Clone)]
    pub(super) struct Context<'i> {
        var_stack: Stack<&'i str>,
    }

    impl<'i> Context<'i> {
        pub(super) fn new() -> Self {
            Self {
                var_stack: Vec::new(),
            }
        }

        pub(super) fn push_vars(&self, vars: impl IntoIterator<Item = &'i str>) -> Self {
            let mut new = self.clone();
            new.var_stack.extend(vars);
            new
        }

        pub(super) fn find_var(&self, name: &'i str) -> Option<usize> {
            self.var_stack
                .iter()
                .copied::<&_>()
                .rev()
                .position(|var| var == name)
        }
    }
}

pub type ValidationError = String;

trait Validate<'i> {
    type Validated;
    fn validate(&self, ctx: &Context<'i>) -> Result<Self::Validated, ValidationError>;
}

pub fn validate<'i>(ast: &ast::Term<'i>) -> Result<ir::Term<'i>, ValidationError> {
    let ctx = Context::new();
    ast.validate(&ctx)
}

impl<'i, T: Validate<'i>> Validate<'i> for Box<T> {
    type Validated = Box<T::Validated>;

    fn validate(&self, ctx: &Context<'i>) -> Result<Self::Validated, ValidationError> {
        T::validate(self, ctx).map(Box::new)
    }
}

impl<'i> Validate<'i> for ast::Term<'i> {
    type Validated = ir::Term<'i>;

    fn validate(&self, ctx: &Context<'i>) -> Result<Self::Validated, ValidationError> {
        let WithInfo(info, term) = self;

        let term = match term {
            ast::RawTerm::Abs {
                arg,
                arg_type,
                body,
            } => {
                let (arg_structure, arg_vars) = extract_idents(arg);
                ir::RawTerm::Abs {
                    arg_structure,
                    arg_type: arg_type.validate(ctx)?,
                    body: body.validate(&ctx.push_vars(arg_vars.map(|i| i.name)))?,
                }
            }
            ast::RawTerm::App { func, arg } => ir::RawTerm::App {
                func: func.validate(ctx)?,
                arg: arg.validate(ctx)?,
            },
            ast::RawTerm::Var { ident } => {
                let Some(index) = ctx.find_var(ident.name) else {
                    return Err(format!("variable '{}' not found", ident.name));
                };
                ir::RawTerm::Var {
                    name: ident.name,
                    index,
                }
            }
            ast::RawTerm::Enum(enum_type, variant) => {
                ir::RawTerm::Enum(enum_type.validate(ctx)?, EnumLabel(variant.name))
            }
            ast::RawTerm::Tuple(elements) => {
                ir::RawTerm::Tuple(elements.iter().map(|t| t.validate(ctx)).try_collect()?)
            }
            ast::RawTerm::Bool(b) => ir::RawTerm::Bool(*b),
        };

        Ok(WithInfo(*info, term))
    }
}

impl<'i> Validate<'_> for ast::Type<'i> {
    type Validated = ir::Type<'i>;

    fn validate(&self, ctx: &Context) -> Result<Self::Validated, ValidationError> {
        let WithInfo(info, ty) = self;

        let ty = match ty {
            ast::RawType::Arr { arg, result } => ir::RawType::Arr {
                arg: arg.validate(ctx)?,
                result: result.validate(ctx)?,
            },
            ast::RawType::Tuple(elements) => {
                ir::RawType::Tuple(elements.iter().map(|t| t.validate(ctx)).try_collect()?)
            }
            ast::RawType::Enum(variants) => ir::RawType::Enum(
                variants
                    .iter()
                    .map(|(i, t)| t.validate(ctx).map(|t| (i.name, t)))
                    .try_collect()?,
            ),
            ast::RawType::Bool => ir::RawType::Bool,
        };
        Ok(WithInfo(*info, ty))
    }
}

pub fn extract_idents<'a, 'i>(
    assignee: &'a ast::Assignee<'i>,
) -> (ArgStructure, impl Iterator<Item = &'a ast::Ident<'i>>) {
    fn extract_idents_inner<'a, 'i>(
        assignee: &'a ast::Assignee<'i>,
        idents: &mut Vec<&'a ast::Ident<'i>>,
    ) -> ArgStructure {
        match assignee {
            ast::Assignee::Tuple(elements) => ArgStructure::Tuple(
                elements
                    .iter()
                    .map(|assignee| extract_idents_inner(assignee, idents))
                    .collect(),
            ),
            ast::Assignee::Ident(ident) => {
                idents.push(ident);
                ArgStructure::Var
            }
        }
    }
    let mut idents = Vec::new();
    (
        extract_idents_inner(assignee, &mut idents),
        idents.into_iter(),
    )
}
