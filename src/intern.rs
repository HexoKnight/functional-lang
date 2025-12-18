use std::hash::{BuildHasher, Hash};

use hashbrown::{DefaultHashBuilder, HashTable, hash_table::Entry};
use typed_arena::Arena;

pub struct InternedArena<'a, T> {
    hash_builder: DefaultHashBuilder,
    hash_table: HashTable<&'a T>,

    // would prefer to be able to own this but that'd require self reference,
    // which becomes real complex real quick
    arena: &'a Arena<T>,
}
impl<'a, T> InternedArena<'a, T>
where
    T: Hash + Eq,
{
    pub fn with_arena(arena: &'a Arena<T>) -> Self {
        Self {
            hash_builder: DefaultHashBuilder::default(),
            hash_table: HashTable::new(),

            arena,
        }
    }

    pub fn intern(&'_ mut self, val: T) -> &'a T {
        let hasher = |v: &&T| self.hash_builder.hash_one(v);

        match self
            .hash_table
            .entry(hasher(&&val), |k: &&'a T| k == &&val, hasher)
        {
            Entry::Occupied(occupied) => occupied.into_mut(),
            Entry::Vacant(vacant) => {
                let arena_ref: &'a T = self.arena.alloc(val);
                vacant.insert(arena_ref).into_mut()
            }
        }
    }
}
