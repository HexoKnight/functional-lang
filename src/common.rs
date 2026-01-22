use std::{collections::HashMap, fmt::Debug, hash::Hash};

use itertools::{Either, zip_eq};

#[derive(Clone)]
pub struct WithInfo<I, T>(pub I, pub T);

impl<I, T: Debug> Debug for WithInfo<I, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.1.fmt(f)
    }
}
impl<I, T: Eq> Eq for WithInfo<I, T> {}
impl<I, T: PartialEq> PartialEq for WithInfo<I, T> {
    fn eq(&self, other: &Self) -> bool {
        self.1 == other.1
    }
}

pub(crate) fn hashmap_union<'a, K, V1, V2, R>(
    hashmap1: &'a HashMap<K, V1>,
    hashmap2: &'a HashMap<K, V2>,
    mut single1: impl FnMut(&V1) -> R,
    mut single2: impl FnMut(&V2) -> R,
    mut merge: impl FnMut(&V1, &V2) -> R,
) -> impl Iterator<Item = (&'a K, R)>
where
    K: Hash + Eq,
{
    hashmap1
        .iter()
        .map(move |(k, v1)| {
            (
                k,
                hashmap2
                    .get(k)
                    // merge intersection
                    .map(|v2| merge(v1, v2))
                    // passthru pairs only in hashmap1
                    .unwrap_or(single1(v1)),
            )
        })
        .chain(
            hashmap2
                .iter()
                // passthru pairs only in hashmap2
                .filter(|(k, _)| !hashmap1.contains_key(*k))
                .map(move |(k, v2)| (k, single2(v2))),
        )
}

pub(crate) fn hashmap_intersection<'a, K, V1, V2, R>(
    hashmap1: &'a HashMap<K, V1>,
    hashmap2: &'a HashMap<K, V2>,
    mut merge: impl FnMut(&V1, &V2) -> R,
) -> impl Iterator<Item = (&'a K, R)>
where
    K: Hash + Eq,
{
    hashmap1
        .iter()
        .filter_map(move |(k, v1)| hashmap2.get(k).map(|v2| (k, merge(v1, v2))))
}

pub(crate) fn maybe_zip_eq<T1, T2>(
    iter1: impl IntoIterator<Item = T1>,
    iter2: Option<impl IntoIterator<Item = T2>>,
) -> impl Iterator<Item = (T1, Option<T2>)> {
    if let Some(iter2) = iter2 {
        Either::Left(zip_eq(iter1, iter2.into_iter().map(Some)))
    } else {
        Either::Right(iter1.into_iter().map(|t1| (t1, None)))
    }
}
