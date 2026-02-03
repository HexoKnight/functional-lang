use crate::newtype_derive;

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub struct Span<'i> {
    pub text: &'i str,
    pub start: usize,
}

#[derive(Clone, Eq, PartialEq, Debug)]
pub enum ArgStructure<'i> {
    Record(Box<[(Label<'i>, ArgStructure<'i>)]>),
    Tuple(Box<[ArgStructure<'i>]>),
    Var,
}

#[derive(Hash, Copy, Clone, Eq, PartialEq, Ord, PartialOrd)]
pub struct Label<'i>(pub &'i str);

newtype_derive!([Label<'i>(&'i str)] Debug, Display);

/// de Bruijn index
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub struct Idx(usize);

impl Idx {
    pub fn get<'s, T>(&'_ self, stack: &'s [T]) -> Option<&'s T> {
        stack.iter().nth_back(self.0)
    }

    pub fn find<T>(stack: &[T], f: impl FnMut(&T) -> bool) -> Option<Self> {
        stack.iter().rev().position(f).map(Self)
    }
}

/// de Bruijn level
#[derive(Hash, Copy, Clone, Eq, PartialEq, Debug)]
pub struct Lvl(usize);

impl Lvl {
    /// get total depth of stack
    pub fn get_depth<T>(stack: &[T]) -> Self {
        Self(stack.len())
    }

    /// get item at level in stack
    pub fn get<T>(self, stack: &[T]) -> Option<&T> {
        stack.get(self.0)
    }

    /// find level of item in stack
    pub fn find<T>(stack: &[T], f: impl FnMut(&T) -> bool) -> Option<Self> {
        stack.iter().position(f).map(Self)
    }

    /// deeper than or equal to
    #[must_use]
    pub fn deeper_than(self, other: Self) -> bool {
        self.0 >= other.0
    }

    /// shallow level by one level (None if already shallow as possible)
    pub fn shallower(self) -> Option<Self> {
        self.0.checked_sub(1).map(Self)
    }

    /// deepen level by one level (shouldn't reach maximum)
    #[must_use]
    pub fn deeper(self) -> Self {
        Self(self.0 + 1)
    }

    /// translate level by difference between other levels (shouldn't reach maximum)
    /// returns None if the result is invalid (ie. negative level)
    #[must_use]
    pub fn translate(self, before: Self, after: Self) -> Option<Self> {
        (self.0 + after.0).checked_sub(before.0).map(Self)
    }
}
