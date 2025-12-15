use crate::reprs::ast;
use crate::reprs::untyped_ir as ir;

type ValidationError = String;

struct Context<'i> {
    var_stack: Vec<&'i str>,
}

trait Validate<'i> {
    type Validated;
    fn validate(&self, ctx: &mut Context<'i>) -> Result<Self::Validated, ValidationError>;
}

pub fn validate<'i>(ast: &ast::Term<'i>) -> Result<ir::Term<'i>, ValidationError> {
    ast.validate(&mut Context {
        var_stack: Vec::new(),
    })
}

impl<'i, T: Validate<'i>> Validate<'i> for Box<T> {
    type Validated = Box<T::Validated>;

    fn validate(&self, ctx: &mut Context<'i>) -> Result<Self::Validated, ValidationError> {
        T::validate(&self, ctx).map(Box::new)
    }
}

impl<'i> Validate<'i> for ast::Term<'i> {
    type Validated = ir::Term<'i>;

    fn validate(&self, ctx: &mut Context<'i>) -> Result<Self::Validated, ValidationError> {
        Ok(match self {
            ast::Term::Abs(ast::Abs {
                arg,
                arg_type,
                body,
            }) => ir::Term::Abs(ir::Abs {
                arg_type: arg_type.validate(ctx)?,
                body: {
                    ctx.var_stack.push(arg.name);
                    let body = body.validate(ctx)?;
                    ctx.var_stack.pop();
                    body
                },
            }),
            ast::Term::App(ast::App { func, arg }) => ir::Term::App(ir::App {
                func: func.validate(ctx)?,
                arg: arg.validate(ctx)?,
            }),
            ast::Term::Var(ast::Var { ident }) => {
                let Some(index) = ctx
                    .var_stack
                    .iter()
                    .rev()
                    .position(|arg| arg == &ident.name)
                else {
                    return Err(format!("variable '{}' not found", ident.name));
                };
                ir::Term::Var(ir::Var {
                    name: ident.name,
                    index,
                })
            }
            ast::Term::Bool(b) => ir::Term::Bool(*b),
        })
    }
}

impl Validate<'_> for ast::Type {
    type Validated = ir::Type;

    fn validate(&self, ctx: &mut Context) -> Result<Self::Validated, ValidationError> {
        Ok(match self {
            ast::Type::Arr(ast::Arr { arg, result }) => ir::Type::Arr(ir::Arr {
                arg: arg.validate(ctx)?,
                result: result.validate(ctx)?,
            }),
            ast::Type::Bool => ir::Type::Bool,
        })
    }
}

#[cfg(test)]
pub mod tests {
    use pretty_assertions::assert_eq;

    use crate::parsing::tests::parse_success;

    use super::*;

    #[track_caller]
    pub fn validate_success(src: &str) -> ir::Term<'_> {
        let ast = parse_success(src);
        match validate(&ast) {
            Ok(o) => o,
            Err(e) => panic!("validate failure:\n'{}'\n{}", src, e),
        }
    }

    #[track_caller]
    pub fn validate_failure(src: &str) -> ValidationError {
        let ast = parse_success(src);
        match validate(&ast) {
            Ok(o) => panic!("validate success:\n'{}'\n{:#?}", src, o),
            Err(e) => e,
        }
    }

    #[track_caller]
    pub fn validate_eq(src1: &str, src2: &str) {
        assert_eq!(validate_success(src1), validate_success(src2))
    }

    #[test]
    fn parsing() {
        validate_success(r"\x:bool x");
        validate_success(r"(\x:bool x)");
        validate_success(r"\x:bool \ y : bool x");
        validate_failure(r"\x:bool y");

        validate_success(r"\x:bool x x");

        validate_success(r"(\x:bool x) true");
        validate_success(r"(\x: bool -> bool x) (\y: bool false)");
    }
}
