use std::borrow::Borrow;

use typed_arena::Arena;

use crate::{
    intern::InternedArena,
    reprs::common::Lvl,
    typing::{InternedType, TyEffLvl, error::IllegalError, ty::Type},
};

// unfortunately no trait aliases
macro_rules! ctx {
    ($([$($bounds:tt)*])* | arena $($inn:lifetime)? $(; $($rest:tt)+)?) => {
        ctx!($([$($bounds)*])* [
            $crate::typing::context::TyArenaContext<'a $(, Inner = &$inn $crate::typing::context::ContextInner<'a>)?>
        ] | $($($rest)+)?)
    };
    ($([$($bounds:tt)*])* | ty_var $(; $($rest:tt)+)?) => {
        ctx!($([$($bounds)*])* [
            $crate::typing::context::TyVarContext<'a, TyVar = $crate::typing::TyVar<'a>>
        ] | $($($rest)+)?)
    };
    ($([$($bounds:tt)*])* | eff_var $(; $($rest:tt)+)?) => {
        ctx!($([$($bounds)*])* [
            $crate::typing::context::EffVarContext<'a, EffVar = $crate::typing::EffVar<'a>>
        ] | $($($rest)+)?)
    };
    ($([$($bounds:tt)*])* |) => {
        impl $($($bounds)* +)*
    };
    ($([$($bounds:tt)*])* | $($invalid:tt)+) => {
    };
    ($($args:tt)*) => {
        ctx!(| $($args)*)
    };
}

#[track_caller]
pub(super) fn unwrap_get<T>(
    op: Option<T>,
    kind: &str,
    level: Lvl,
) -> Result<T, IllegalError<'static>> {
    // explicit match to allow `#[track_caller]`
    match op {
        Some(t) => Ok(t),
        None => Err(IllegalError::new(
            format!("{kind} level not found: {level:?}"),
            None,
        )),
    }
}

// doesn't suffer from the same dropck issues as self references
// do not (currently) pass through this type
/// Cheaply cloneable (hopefully) append-only stack
pub(super) type Stack<T> = Vec<T>;

pub(super) struct ContextInner<'a> {
    ty_arena: InternedArena<'a, Type<'a>>,

    ty_unknown: InternedType<'a>,
}
impl<'a> ContextInner<'a> {
    pub(super) fn new(arena: &'a Arena<Type<'a>>) -> Self {
        let ty_arena = InternedArena::with_arena(arena);
        let ty_unknown = ty_arena.intern(Type::Unknown);

        Self {
            ty_arena,
            ty_unknown,
        }
    }
}
impl<'a, 'inn> TyArenaContext<'a> for &'inn ContextInner<'a> {
    type Inner = Self;

    fn get_inner(&self) -> &'inn ContextInner<'a> {
        self
    }

    fn intern(&self, var: Type<'a>) -> InternedType<'a> {
        self.ty_arena.intern(var)
    }
}

pub(super) trait TyArenaContext<'a> {
    type Inner: Borrow<ContextInner<'a>>;

    fn get_inner(&self) -> Self::Inner;

    fn intern(&self, var: Type<'a>) -> InternedType<'a> {
        self.get_inner().borrow().intern(var)
    }

    fn ty_unknown(&self) -> InternedType<'a> {
        self.get_inner().borrow().ty_unknown
    }
}

pub(super) trait TyVarContext<'a> {
    type TyVar;

    fn push_ty_var(&self, ty_var_name: &'a str, ty_var: Self::TyVar) -> Self;

    fn get_ty_var(&self, level: Lvl) -> Option<(&'a str, Self::TyVar)>;

    #[track_caller]
    fn get_ty_var_unwrap(
        &self,
        level: Lvl,
    ) -> Result<(&'a str, Self::TyVar), IllegalError<'static>> {
        unwrap_get(self.get_ty_var(level), "type variable", level)
    }

    fn next_ty_var_level(&self) -> Lvl;

    fn get_ty_vars(&self) -> impl Iterator<Item = (&'a str, Self::TyVar)>;

    fn next_ty_eff_level(&self) -> TyEffLvl
    where
        Self: EffVarContext<'a>,
    {
        TyEffLvl {
            ty: self.next_ty_var_level(),
            eff: self.next_eff_var_level(),
        }
    }
}

pub(super) trait EffVarContext<'a> {
    type EffVar;

    fn push_eff_var(&self, eff_var_label: &'a str, eff_var: Self::EffVar) -> Self;

    fn get_eff_var(&self, level: Lvl) -> Option<(&'a str, Self::EffVar)>;

    #[track_caller]
    fn get_eff_var_unwrap(
        &self,
        level: Lvl,
    ) -> Result<(&'a str, Self::EffVar), IllegalError<'static>> {
        unwrap_get(self.get_eff_var(level), "effect variable", level)
    }

    fn next_eff_var_level(&self) -> Lvl;

    fn get_eff_vars(&self) -> impl Iterator<Item = (&'a str, Self::EffVar)>;
}

pub(super) struct MultiContext<TyArena = (), TyVar = (), EffVar = ()>(TyArena, TyVar, EffVar);

impl MultiContext {
    pub(super) fn new() -> Self {
        Self((), (), ())
    }
}
impl<'a, TyArena, TyVar, EffVar> MultiContext<TyArena, TyVar, EffVar> {
    pub(super) fn with_ty_arena<NewTyArena: TyArenaContext<'a>>(
        self,
        new_ty_arena: NewTyArena,
    ) -> MultiContext<NewTyArena, TyVar, EffVar> {
        MultiContext(new_ty_arena, self.1, self.2)
    }
    pub(super) fn with_ty_var<NewTyVar: TyVarContext<'a>>(
        self,
        new_ty_var: NewTyVar,
    ) -> MultiContext<TyArena, NewTyVar, EffVar> {
        MultiContext(self.0, new_ty_var, self.2)
    }
    pub(super) fn with_eff_var<NewEffVar: EffVarContext<'a>>(
        self,
        new_eff_var: NewEffVar,
    ) -> MultiContext<TyArena, TyVar, NewEffVar> {
        MultiContext(self.0, self.1, new_eff_var)
    }
}

impl<'a, TyArena, TyVar, EffVar> TyArenaContext<'a> for MultiContext<TyArena, TyVar, EffVar>
where
    TyArena: TyArenaContext<'a>,
{
    type Inner = TyArena::Inner;

    fn get_inner(&self) -> Self::Inner {
        self.0.get_inner()
    }
}
impl<'a, TyArena, TyVar, EffVar> TyVarContext<'a> for MultiContext<TyArena, TyVar, EffVar>
where
    TyArena: Clone,
    TyVar: TyVarContext<'a>,
    EffVar: Clone,
{
    type TyVar = TyVar::TyVar;

    fn push_ty_var(&self, ty_var_name: &'a str, ty_var: Self::TyVar) -> Self {
        Self(
            self.0.clone(),
            self.1.push_ty_var(ty_var_name, ty_var),
            self.2.clone(),
        )
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

    fn get_ty_var_unwrap(
        &self,
        level: Lvl,
    ) -> Result<(&'a str, Self::TyVar), IllegalError<'static>> {
        self.1.get_ty_var_unwrap(level)
    }
}
impl<'a, TyArena, TyVar, EffVar> EffVarContext<'a> for MultiContext<TyArena, TyVar, EffVar>
where
    TyArena: Clone,
    TyVar: Clone,
    EffVar: EffVarContext<'a>,
{
    type EffVar = EffVar::EffVar;

    fn push_eff_var(&self, eff_var_name: &'a str, eff_var: Self::EffVar) -> Self {
        Self(
            self.0.clone(),
            self.1.clone(),
            self.2.push_eff_var(eff_var_name, eff_var),
        )
    }

    fn get_eff_var(&self, level: Lvl) -> Option<(&'a str, Self::EffVar)> {
        self.2.get_eff_var(level)
    }

    fn next_eff_var_level(&self) -> Lvl {
        self.2.next_eff_var_level()
    }

    fn get_eff_vars(&self) -> impl Iterator<Item = (&'a str, Self::EffVar)> {
        self.2.get_eff_vars()
    }

    fn get_eff_var_unwrap(
        &self,
        level: Lvl,
    ) -> Result<(&'a str, Self::EffVar), IllegalError<'static>> {
        self.2.get_eff_var_unwrap(level)
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

#[must_use]
#[derive(Clone)]
pub(super) struct EffVarStack<'a, T>(Stack<(&'a str, T)>);

impl<'a, T> FromIterator<(&'a str, T)> for EffVarStack<'a, T> {
    fn from_iter<I: IntoIterator<Item = (&'a str, T)>>(iter: I) -> Self {
        Self(iter.into_iter().collect())
    }
}

impl<'a, Ctx: EffVarContext<'a>> From<&Ctx> for EffVarStack<'a, ()> {
    fn from(value: &Ctx) -> Self {
        value.get_eff_vars().map(|(name, _)| (name, ())).collect()
    }
}

impl<'a, T: Copy> EffVarContext<'a> for EffVarStack<'a, T> {
    type EffVar = T;

    fn push_eff_var(&self, eff_var_name: &'a str, eff_var: Self::EffVar) -> Self {
        let mut new = self.clone();
        new.0.push((eff_var_name, eff_var));
        new
    }

    fn get_eff_var(&self, level: Lvl) -> Option<(&'a str, Self::EffVar)> {
        level.get(&self.0).copied()
    }

    fn next_eff_var_level(&self) -> Lvl {
        Lvl::get_depth(&self.0)
    }

    fn get_eff_vars(&self) -> impl Iterator<Item = (&'a str, Self::EffVar)> {
        self.0.iter().copied()
    }
}
