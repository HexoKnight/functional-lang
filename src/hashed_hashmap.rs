use std::{
    collections::HashMap,
    hash::{Hash, Hasher},
};

use derive_where::derive_where;
use itertools::Itertools;

#[derive_where(Eq, PartialEq; HashMap<K, V>)]
pub struct HashedHashMap<K, V>(pub HashMap<K, V>);

crate::newtype_derive!([HashedHashMap<K, V>(HashMap<K, V>)] Debug);

impl<K, V> FromIterator<(K, V)> for HashedHashMap<K, V>
where
    HashMap<K, V>: FromIterator<(K, V)>,
{
    fn from_iter<T: IntoIterator<Item = (K, V)>>(iter: T) -> Self {
        Self(HashMap::from_iter(iter))
    }
}

impl<K: Hash + Ord, V: Hash> Hash for HashedHashMap<K, V> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        for kv in self.0.iter().sorted_unstable_by_key(|(k, _)| *k) {
            kv.hash(state);
        }
    }
}
