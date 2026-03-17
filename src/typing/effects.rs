use std::fmt;

use itertools::{Either, Itertools};

use crate::{
    hashed_hashmap::HashedHashMap,
    reprs::common::{Label, Lvl},
    typing::{EffVar, InternedType, MapVars, TyEffLvl, error::IllegalError},
};

#[derive(Hash, Copy, Clone, Eq, PartialEq)]
pub enum EffKind<'a> {
    Named(Label<'a>),
    Unbound,
}

impl<'a> EffKind<'a> {
    pub(super) fn to_id(self, level: Lvl) -> EffId<'a> {
        match self {
            EffKind::Named(label) => EffId::Name(label),
            // `level` *should* refer to the level of the final concrete var,
            // not for example any intermediate indirections, it currently does not
            //
            // I believe this solution then breaks down for indirect unbound effect
            // vars but they are not supported currently so it is left here regardless
            EffKind::Unbound => EffId::Unbound(level),
        }
    }
}

#[derive(Hash, Copy, Clone, Eq, PartialEq, Ord, PartialOrd)]
pub enum EffId<'a> {
    Name(Label<'a>),
    Unbound(Lvl),
}

impl<'a> EffId<'a> {
    pub fn to_kind(self) -> EffKind<'a> {
        match self {
            EffId::Name(name) => EffKind::Named(name),
            EffId::Unbound(_) => EffKind::Unbound,
        }
    }
}

impl<'a> fmt::Display for EffId<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            EffId::Name(label) => label.fmt(f),
            EffId::Unbound(lvl) => write!(f, "<effvar:{lvl:?}>"),
        }
    }
}

/// we take effect subtyping to be akin to arrow type parameter subtyping:
/// ie. the opposite of arrow type subtyping
/// ie. `effect name A -> B` < `effect name C -> D`
///     iff `A` < `B` && `D` < `C`
#[derive(Copy, Clone, Hash, Eq, PartialEq)]
pub enum Effect<'a> {
    Def {
        name: Label<'a>,
        arg: InternedType<'a>,
        result: InternedType<'a>,
    },
    Var(Lvl, EffKind<'a>),
}

impl<'a> Effect<'a> {
    pub fn get_id(&self) -> EffId<'a> {
        match self {
            Self::Def { name, .. } => EffId::Name(*name),
            Self::Var(level, eff_kind) => eff_kind.to_id(*level),
        }
    }

    /// Resolves the effect as much as possible
    pub fn concrete(
        &self,
        ty_eff_level: TyEffLvl,
        ctx: &ctx!(arena; eff_var),
    ) -> Result<Self, IllegalError<'static>> {
        match self {
            Effect::Var(level, _) => {
                let (_, eff_var) = ctx.get_eff_var_unwrap(*level)?;
                match eff_var {
                    EffVar::Effect { effect, ty_lvl } => effect
                        .deepen(TyEffLvl::new(ty_lvl, *level), ty_eff_level, ctx)
                        .concrete(ty_eff_level, ctx),
                    EffVar::Unbound => Ok(*self),
                }
            }
            Effect::Def { .. } => Ok(*self),
        }
    }
}

#[derive(Clone, Hash, Eq, PartialEq)]
pub struct EffectGroup<'a> {
    pub labelled: HashedHashMap<Label<'a>, Effect<'a>>,
    pub anonymous: HashedHashMap<EffId<'a>, Effect<'a>>,
    /// equivalent to `Type::Unknown`
    /// should only be `false` for `check_type` or `EffConstraint::upper`
    pub exhaustive: bool,
}

impl<'a> Default for EffectGroup<'a> {
    fn default() -> Self {
        Self {
            labelled: HashedHashMap::default(),
            anonymous: HashedHashMap::default(),
            // should only be `false` in select situations so this is the only good default
            exhaustive: true,
        }
    }
}

impl<'a> FromIterator<Either<(Label<'a>, Effect<'a>), (EffId<'a>, Effect<'a>)>>
    for EffectGroup<'a>
{
    fn from_iter<
        I: IntoIterator<Item = Either<(Label<'a>, Effect<'a>), (EffId<'a>, Effect<'a>)>>,
    >(
        iter: I,
    ) -> Self {
        let (labelled, anonymous) = iter.into_iter().partition_map(|e| e);

        Self {
            labelled,
            anonymous,
            ..Default::default()
        }
    }
}
impl<'a> FromIterator<(Option<Label<'a>>, Effect<'a>)> for EffectGroup<'a> {
    fn from_iter<I: IntoIterator<Item = (Option<Label<'a>>, Effect<'a>)>>(iter: I) -> Self {
        let (labelled, anonymous) = iter.into_iter().partition_map(|(label, effect)| {
            if let Some(label) = label {
                Either::Left((label, effect))
            } else {
                Either::Right((effect.get_id(), effect))
            }
        });

        Self {
            labelled,
            anonymous,
            ..Default::default()
        }
    }
}

impl<'a> EffectGroup<'a> {
    pub fn new_non_exhaustive() -> Self {
        Self::default().non_exhaustive()
    }

    /// should only be used for `check_type`
    pub fn non_exhaustive(mut self) -> Self {
        self.exhaustive = false;
        self
    }

    pub fn exhaustive(mut self) -> Self {
        self.exhaustive = true;
        self
    }

    /// mapping must be injective
    pub fn try_map<E>(
        &self,
        mut f: impl FnMut(Option<Label<'a>>, &Effect<'a>) -> Result<Effect<'a>, E>,
    ) -> Result<EffectGroup<'a>, E> {
        Ok(EffectGroup {
            labelled: self
                .labelled
                .iter_unsorted()
                .map(|(l, e)| f(Some(*l), e).map(|e| (*l, e)))
                .try_collect()?,
            anonymous: self
                .anonymous
                .iter_unsorted()
                .map(|(_, e)| f(None, e).map(|e| (e.get_id(), e)))
                .try_collect()?,
            ..*self
        })
    }

    pub fn iter_sorted(&self) -> impl Iterator<Item = (Option<Label<'a>>, &Effect<'a>)> {
        std::iter::chain(
            self.labelled.iter_sorted().map(|(l, e)| (Some(*l), e)),
            self.anonymous.iter_sorted().map(|(_, e)| (None, e)),
        )
    }
    pub fn iter_unsorted(&self) -> impl Iterator<Item = (Option<Label<'a>>, &Effect<'a>)> {
        std::iter::chain(
            self.labelled.iter_unsorted().map(|(l, e)| (Some(*l), e)),
            self.anonymous.iter_unsorted().map(|(_, e)| (None, e)),
        )
    }

    pub fn get_labelled(&self, label: Label<'a>) -> Option<&Effect<'a>> {
        self.labelled.0.get(&label)
    }

    pub fn get_anonymous(&self, eff_id: EffId<'a>) -> Option<&Effect<'a>> {
        self.anonymous.0.get(&eff_id)
    }

    pub fn is_empty(&self) -> bool {
        self.labelled.0.is_empty() && self.anonymous.0.is_empty()
    }
}
