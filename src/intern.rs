use std::{
    cell::RefCell,
    hash::{BuildHasher, Hash},
};

use hashbrown::{DefaultHashBuilder, HashTable, hash_table::Entry};
use typed_arena::Arena;

pub struct InternedArena<'a, T> {
    intern_table: RefCell<InternTable<'a, T>>,

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
            intern_table: RefCell::new(InternTable::default()),
            arena,
        }
    }

    pub fn intern<'s>(&'s self, val: T) -> &'a T {
        self.intern_table
            // same call is used during `Arena::alloc`
            .borrow_mut()
            .intern(val, |v| self.arena.alloc(v))
    }
}

// derive_where to remove `T: Default` bound
#[derive_where::derive_where(Default)]
pub struct InternTable<'a, T> {
    hash_builder: DefaultHashBuilder,
    hash_table: HashTable<&'a T>,
}
impl<'a, T> InternTable<'a, T>
where
    T: Hash + Eq,
{
    pub fn intern<'s>(&'s mut self, val: T, alloc: impl FnOnce(T) -> &'a T) -> &'a T {
        let hasher = |v: &&T| self.hash_builder.hash_one(v);

        match self
            .hash_table
            .entry(hasher(&&val), |k: &&'a T| k == &&val, hasher)
        {
            Entry::Occupied(occupied) => occupied.into_mut(),
            Entry::Vacant(vacant) => {
                let val_ref: &'a T = alloc(val);
                vacant.insert(val_ref).into_mut()
            }
        }
    }
}
