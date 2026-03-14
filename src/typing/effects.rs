use itertools::{Either, Itertools};

use crate::{
    hashed_hashmap::HashedHashMap,
    reprs::common::{Label, Lvl},
    typing::{InternedType, TyArenaContext},
};

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
}

impl<'a> Effect<'a> {
    pub fn get_name(&self) -> Label<'a> {
        match self {
            Effect::Def { name, .. } => *name,
        }
    }

    pub fn deepen(&self, prev_level: Lvl, new_level: Lvl, ctx: &impl TyArenaContext<'a>) -> Self {
        if prev_level == new_level {
            return *self;
        }
        match self {
            Effect::Def { name, arg, result } => Effect::Def {
                name: *name,
                arg: arg.deepen(prev_level, new_level, ctx),
                result: result.deepen(prev_level, new_level, ctx),
            },
        }
    }
}

#[derive(Clone, Hash, Eq, PartialEq)]
pub struct EffectGroup<'a> {
    pub labelled: HashedHashMap<Label<'a>, Effect<'a>>,
    pub anonymous: HashedHashMap<Label<'a>, Effect<'a>>,
    /// equivalent to `Type::Unknown`
    /// should only be `false` for `check_type`
    pub exhaustive: bool,
}

impl<'a> Default for EffectGroup<'a> {
    fn default() -> Self {
        Self {
            labelled: HashedHashMap::default(),
            anonymous: HashedHashMap::default(),
            // should only be `false` for `check_type` so this is the only good default
            exhaustive: true,
        }
    }
}

impl<'i> FromIterator<(Option<Label<'i>>, Effect<'i>)> for EffectGroup<'i> {
    fn from_iter<I: IntoIterator<Item = (Option<Label<'i>>, Effect<'i>)>>(iter: I) -> Self {
        let (labelled, anonymous) = iter.into_iter().partition_map(|(name, effect)| {
            if let Some(name) = name {
                Either::Left((name, effect))
            } else {
                Either::Right((effect.get_name(), effect))
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

    /// mapping should be injective (at least when `None` label)
    pub fn try_map<E>(
        &self,
        mut f: impl FnMut(Option<Label<'a>>, &Effect<'a>) -> Result<Effect<'a>, E>,
    ) -> Result<EffectGroup<'a>, E> {
        Ok(EffectGroup {
            labelled: self
                .labelled
                .iter_unsorted()
                .map(|(l, t)| f(Some(*l), t).map(|u| (*l, u)))
                .try_collect()?,
            anonymous: self
                .anonymous
                .iter_unsorted()
                .map(|(_, e)| f(None, e).map(|e| (e.get_name(), e)))
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

    pub fn get_anonymous(&self, name: Label<'a>) -> Option<&Effect<'a>> {
        self.anonymous.0.get(&name)
    }
}
