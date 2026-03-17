use std::hash::Hash;

use itertools::{Itertools, Position};

use crate::{
    hashed_hashmap::HashedHashMap,
    reprs::common::{Label, Lvl},
    typing::{
        context::{EffVarContext, TyArenaContext, TyEffVarStack, TyVarContext},
        effects::{Effect, EffectGroup},
        error::IllegalError,
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
    RecAbs {
        name: &'ctx str,
        result: TypeRef<'ctx>,
    },
    EffAbs {
        // disables some type interning but comparing type abstractions is uncommon and displaying
        // useful type information is more important
        name: Label<'ctx>,
        result: TypeRef<'ctx>,
    },

    TyVar(Lvl),

    TyObj(TypeRef<'ctx>),

    Arr {
        arg: TypeRef<'ctx>,
        effects: EffectGroup<'ctx>,
        result: TypeRef<'ctx>,
    },

    Enum(HashedHashMap<Label<'ctx>, TypeRef<'ctx>>),
    Record(HashedHashMap<Label<'ctx>, TypeRef<'ctx>>),
    Tuple(Box<[TypeRef<'ctx>]>),

    Bool,
    Any,
    Never,

    /// used specifically for type inference
    /// while Any represents a statically unknown type
    /// Unknown represents a type that will be statically known
    /// but just hasn't been determined yet
    /// should not appear in the result of any type checking operation
    ///
    /// a future refactor could make `check_type` and `expected` use some `UnknownOrType` instead
    Unknown,
}

// a sentinel value used as TyAbs::name to represent an applied (ie. concrete) bounds
// notably it must not be nameable so cannot be a valid type var name
pub(super) const CONCRETE_TY_APP_NAME: &str = "$";

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

type VarStack<'ctx> = TyEffVarStack<'ctx, (), ()>;

pub trait TyDisplay<'ctx> {
    fn write_display(
        &self,
        ctx: &VarStack<'ctx>,
        w: &mut String,
    ) -> Result<(), IllegalError<'static>>;

    #[track_caller]
    fn display(&self, ctx: impl Into<VarStack<'ctx>>) -> Result<String, IllegalError<'static>> {
        let mut string = String::new();
        self.write_display(&ctx.into(), &mut string)?;
        Ok(string)
    }

    fn is_empty(&self, ctx: &VarStack<'ctx>) -> Result<bool, IllegalError<'static>>;
}

impl<'ctx> TyDisplay<'ctx> for Type<'ctx> {
    #[track_caller]
    fn write_display(
        &self,
        ctx: &VarStack<'ctx>,
        w: &mut String,
    ) -> Result<(), IllegalError<'static>> {
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
            Type::RecAbs { name, result } => {
                w.push_str("rec ");
                w.push_str(name);
                w.push(' ');
                result.write_display(&ctx.push_ty_var(name, ()), w)?;
            }
            Type::EffAbs { name, result } => {
                w.push_str("[%");
                w.push_str(name.0);
                w.push_str("] ");
                result.write_display(&ctx.push_eff_var(name.0, ()), w)?;
            }
            Type::TyVar(level) => {
                w.push_str(ctx.get_ty_var_unwrap(*level)?.0);
            }
            Type::TyObj(ty) => {
                w.push_str("type ");
                ty.write_display(ctx, w)?;
            }
            Type::Arr {
                arg,
                effects,
                result,
            } => {
                if matches!(
                    arg,
                    Type::TyAbs { .. } | Type::RecAbs { .. } | Type::TyObj(_) | Type::Arr { .. }
                ) {
                    w.push('(');
                    arg.write_display(ctx, w)?;
                    w.push_str(") -> ");
                } else {
                    arg.write_display(ctx, w)?;
                    w.push_str(" -> ");
                }

                if !effects.is_empty() {
                    effects.write_display(ctx, w)?;
                    w.push(' ');
                }
                result.write_display(ctx, w)?;
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
            Type::Unknown => w.push('?'),
        }
        Ok(())
    }

    fn is_empty(&self, _ctx: &VarStack<'ctx>) -> Result<bool, IllegalError<'static>> {
        Ok(false)
    }
}

impl<'ctx> TyDisplay<'ctx> for TyBounds<'ctx> {
    fn write_display(
        &self,
        ctx: &VarStack<'ctx>,
        w: &mut String,
    ) -> Result<(), IllegalError<'static>> {
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

    fn is_empty(&self, _ctx: &VarStack<'ctx>) -> Result<bool, IllegalError<'static>> {
        let Self { upper, lower } = self;

        Ok(upper.is_none() && lower.is_none())
    }
}

impl<'ctx> TyDisplay<'ctx> for Effect<'ctx> {
    #[track_caller]
    fn write_display(
        &self,
        ctx: &VarStack<'ctx>,
        w: &mut String,
    ) -> Result<(), IllegalError<'static>> {
        match self {
            Effect::Def { name, arg, result } => {
                w.push_str("effect ");
                w.push_str(name.0);
                w.push(' ');
                arg.write_display(ctx, w)?;
                w.push_str(" -> ");
                result.write_display(ctx, w)?;
            }
            Effect::Var(level, _) => {
                w.push_str(ctx.get_eff_var_unwrap(*level)?.0);
            }
        }
        Ok(())
    }

    fn is_empty(&self, _ctx: &VarStack<'ctx>) -> Result<bool, IllegalError<'static>> {
        Ok(false)
    }
}

impl<'ctx> TyDisplay<'ctx> for EffectGroup<'ctx> {
    #[track_caller]
    fn write_display(
        &self,
        ctx: &VarStack<'ctx>,
        w: &mut String,
    ) -> Result<(), IllegalError<'static>> {
        w.push_str("%{");
        for (pos, (name, effect)) in self.iter_sorted().with_position() {
            if let Some(name) = name {
                w.push_str(name.0);
                w.push_str(": ");
            }
            effect.write_display(ctx, w)?;
            if !self.exhaustive || matches!(pos, Position::First | Position::Middle) {
                w.push_str(", ");
            }
        }
        if !self.exhaustive {
            w.push_str("..");
        }
        w.push('}');
        Ok(())
    }

    fn is_empty(&self, _ctx: &VarStack<'ctx>) -> Result<bool, IllegalError<'static>> {
        Ok(false)
    }
}
