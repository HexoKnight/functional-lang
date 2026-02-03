use itertools::Itertools;

use crate::{
    hashed_hashmap::HashedHashMap,
    reprs::common::{Label, Lvl},
    typing::{
        TypeCheckError,
        context::{TyArenaContext, TyVarContext, TyVarStack},
    },
};

type TypeRef<'ctx> = &'ctx Type<'ctx>;

// TODO: manual Hash / *Eq impls for more complex types
// TODO: impl Display for nicer output
#[derive(Hash, Eq, PartialEq)]
pub enum Type<'ctx> {
    TyAbs {
        // disables some type interning but comparing type abstractions is uncommon and displaying
        // useful type information is more important
        name: &'ctx str,
        bounds: TyBounds<'ctx>,
        result: TypeRef<'ctx>,
    },

    TyVar(Lvl),

    Arr {
        arg: TypeRef<'ctx>,
        result: TypeRef<'ctx>,
    },

    Enum(HashedHashMap<Label<'ctx>, TypeRef<'ctx>>),
    Record(HashedHashMap<Label<'ctx>, TypeRef<'ctx>>),
    Tuple(Box<[TypeRef<'ctx>]>),

    Bool,
    Any,
    Never,
}

#[derive(Copy, Clone, Hash, Eq, PartialEq)]
pub struct TyBounds<'ctx> {
    pub upper: Option<TypeRef<'ctx>>,
    pub lower: Option<TypeRef<'ctx>>,
}

impl<'ctx> TyBounds<'ctx> {
    pub(super) fn get_upper(&self, ctx: &impl TyArenaContext<'ctx>) -> TypeRef<'ctx> {
        self.upper.unwrap_or_else(|| ctx.intern(Type::Any))
    }
    pub(super) fn get_lower(&self, ctx: &impl TyArenaContext<'ctx>) -> TypeRef<'ctx> {
        self.lower.unwrap_or_else(|| ctx.intern(Type::Never))
    }
}

pub trait TyDisplay<'ctx> {
    fn write_display(
        &self,
        ctx: &TyVarStack<'ctx, ()>,
        w: &mut String,
    ) -> Result<(), TypeCheckError>;

    fn display(&self, ctx: impl Into<TyVarStack<'ctx, ()>>) -> Result<String, TypeCheckError> {
        let mut string = String::new();
        self.write_display(&ctx.into(), &mut string)?;
        Ok(string)
    }

    fn is_empty(&self, ctx: &TyVarStack<'ctx, ()>) -> Result<bool, TypeCheckError>;
}

impl<'ctx> TyDisplay<'ctx> for Type<'ctx> {
    fn write_display(
        &self,
        ctx: &TyVarStack<'ctx, ()>,
        w: &mut String,
    ) -> Result<(), TypeCheckError> {
        match self {
            Type::TyAbs {
                name,
                bounds,
                result,
            } => {
                w.push('[');
                w.push_str(name);
                if !bounds.is_empty(ctx)? {
                    w.push(' ');
                    bounds.write_display(ctx, w)?;
                }
                w.push_str("] ");
                result.write_display(&ctx.push_ty_var(name, ()), w)?;
            }
            Type::TyVar(level) => {
                w.push_str(ctx.get_ty_var_unwrap(*level)?.0);
            }
            Type::Arr { arg, result } => {
                if matches!(arg, Type::TyAbs { .. } | Type::Arr { .. }) {
                    w.push('(');
                    arg.write_display(ctx, w)?;
                    w.push_str(") -> ");
                    result.write_display(ctx, w)?;
                } else {
                    arg.write_display(ctx, w)?;
                    w.push_str(" -> ");
                    result.write_display(ctx, w)?;
                }
            }
            Type::Enum(variants) => {
                w.push_str("enum {");
                let mut iter = variants.0.iter().sorted_unstable_by_key(|(l, _)| *l);
                if let Some((l, ty)) = iter.next() {
                    w.push_str(l.0);
                    w.push_str(": ");
                    ty.write_display(ctx, w)?;
                    for (l, ty) in iter {
                        w.push_str(", ");
                        w.push_str(l.0);
                        w.push_str(": ");
                        ty.write_display(ctx, w)?;
                    }
                }
                w.push('}');
            }
            Type::Record(fields) => {
                w.push('{');
                let mut iter = fields.0.iter().sorted_unstable_by_key(|(l, _)| *l);
                if let Some((l, ty)) = iter.next() {
                    w.push_str(l.0);
                    w.push_str(": ");
                    ty.write_display(ctx, w)?;
                    for (l, ty) in iter {
                        w.push_str(", ");
                        w.push_str(l.0);
                        w.push_str(": ");
                        ty.write_display(ctx, w)?;
                    }
                }
                w.push('}');
            }
            Type::Tuple(elems) => {
                w.push('(');
                let mut iter = elems.iter();
                if let Some(first) = iter.next() {
                    first.write_display(ctx, w)?;
                    w.push(',');
                    if let Some(second) = iter.next() {
                        w.push(' ');
                        second.write_display(ctx, w)?;
                        for ty in iter {
                            w.push_str(", ");
                            ty.write_display(ctx, w)?;
                        }
                    }
                }
                w.push(')');
            }
            Type::Bool => w.push_str("bool"),
            Type::Any => w.push('_'),
            Type::Never => w.push('!'),
        }
        Ok(())
    }

    fn is_empty(&self, _ctx: &TyVarStack<'ctx, ()>) -> Result<bool, TypeCheckError> {
        Ok(false)
    }
}

impl<'ctx> TyDisplay<'ctx> for TyBounds<'ctx> {
    fn write_display(
        &self,
        ctx: &TyVarStack<'ctx, ()>,
        w: &mut String,
    ) -> Result<(), TypeCheckError> {
        let Self { upper, lower } = self;

        if let Some(upper) = upper {
            w.push('<');
            upper.write_display(ctx, w)?;
        }
        if let Some(lower) = lower {
            if upper.is_some() {
                w.push(' ');
            }
            w.push('>');
            lower.write_display(ctx, w)?;
        }
        Ok(())
    }

    fn is_empty(&self, _ctx: &TyVarStack<'ctx, ()>) -> Result<bool, TypeCheckError> {
        let Self { upper, lower } = self;

        Ok(upper.is_none() && lower.is_none())
    }
}
