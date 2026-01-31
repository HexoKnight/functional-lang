use std::borrow::Borrow;

use typed_arena::Arena;

use crate::{
    intern::InternedArena,
    reprs::common::Lvl,
    typing::{InternedType, TypeCheckError, ty::Type},
};

// doesn't suffer from the same dropck issues as self references
// do not (currently) pass through this type
/// Cheaply cloneable (hopefully) append-only stack
pub(super) type Stack<T> = Vec<T>;

pub(super) struct ContextInner<'a> {
    ty_arena: InternedArena<'a, Type<'a>>,
}
impl<'a> ContextInner<'a> {
    pub(super) fn new(arena: &'a Arena<Type<'a>>) -> Self {
        Self {
            ty_arena: InternedArena::with_arena(arena),
        }
    }
}
impl<'a, 'inn> TyArenaContext<'a> for &'inn ContextInner<'a> {
    type Inner = Self;

    fn intern(&self, var: Type<'a>) -> InternedType<'a> {
        self.ty_arena.intern(var)
    }

    fn get_inner(&self) -> &'inn ContextInner<'a> {
        self
    }
}

pub(super) trait TyArenaContext<'a> {
    type Inner: Borrow<ContextInner<'a>>;

    fn intern(&self, var: Type<'a>) -> InternedType<'a> {
        self.get_inner().borrow().intern(var)
    }

    fn get_inner(&self) -> Self::Inner;
}

pub(super) trait TyVarContext<'a> {
    type TyVar;

    fn push_ty_var(&self, ty_var_name: &'a str, ty_var: Self::TyVar) -> Self;

    fn get_ty_var(&self, level: Lvl) -> Option<(&'a str, Self::TyVar)>;

    fn get_ty_var_unwrap(&self, level: Lvl) -> Result<(&'a str, Self::TyVar), TypeCheckError> {
        self.get_ty_var(level)
            .ok_or_else(|| format!("illegal failure: type variable level not found: {level:?}"))
    }

    fn next_ty_var_level(&self) -> Lvl;

    fn get_ty_vars(&self) -> impl Iterator<Item = (&'a str, Self::TyVar)>;
}

pub(super) struct MultiContext<TyArena = (), TyVar = ()>(pub TyArena, pub TyVar);

impl<'a, TyArena, TyVar> TyArenaContext<'a> for MultiContext<TyArena, TyVar>
where
    TyArena: TyArenaContext<'a>,
{
    type Inner = TyArena::Inner;

    fn get_inner(&self) -> Self::Inner {
        self.0.get_inner()
    }
}
impl<'a, TyArena, TyVar> TyVarContext<'a> for MultiContext<TyArena, TyVar>
where
    TyArena: Clone,
    TyVar: TyVarContext<'a>,
{
    type TyVar = TyVar::TyVar;

    fn push_ty_var(&self, ty_var_name: &'a str, ty_var: Self::TyVar) -> Self {
        Self(self.0.clone(), self.1.push_ty_var(ty_var_name, ty_var))
    }

    fn get_ty_var(&self, level: Lvl) -> Option<(&'a str, Self::TyVar)> {
        self.1.get_ty_var(level)
    }

    fn next_ty_var_level(&self) -> Lvl {
        self.1.next_ty_var_level()
    }

    fn get_ty_vars(&self) -> impl Iterator<Item = (&'a str, Self::TyVar)> {
        self.1.get_ty_vars()
    }

    fn get_ty_var_unwrap(&self, level: Lvl) -> Result<(&'a str, Self::TyVar), TypeCheckError> {
        self.1.get_ty_var_unwrap(level)
    }
}

#[must_use]
#[derive(Clone)]
pub(super) struct TyVarStack<'a, T>(Stack<(&'a str, T)>);

impl<'a, T> FromIterator<(&'a str, T)> for TyVarStack<'a, T> {
    fn from_iter<I: IntoIterator<Item = (&'a str, T)>>(iter: I) -> Self {
        Self(iter.into_iter().collect())
    }
}

impl<'a, Ctx: TyVarContext<'a>> From<&Ctx> for TyVarStack<'a, ()> {
    fn from(value: &Ctx) -> Self {
        value.get_ty_vars().map(|(name, _)| (name, ())).collect()
    }
}

impl<'a, T: Copy> TyVarContext<'a> for TyVarStack<'a, T> {
    type TyVar = T;

    fn push_ty_var(&self, ty_var_name: &'a str, ty_var: Self::TyVar) -> Self {
        let mut new = self.clone();
        new.0.push((ty_var_name, ty_var));
        new
    }

    fn get_ty_var(&self, level: Lvl) -> Option<(&'a str, Self::TyVar)> {
        level.get(&self.0).copied()
    }

    fn next_ty_var_level(&self) -> Lvl {
        Lvl::get_depth(&self.0)
    }

    fn get_ty_vars(&self) -> impl Iterator<Item = (&'a str, Self::TyVar)> {
        self.0.iter().copied()
    }
}
