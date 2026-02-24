use std::{
    borrow::Cow,
    ops::{Index, Range},
};

use crate::{common::WithInfo, newtype_derive};

/// `text` must be a subslice of `file_info.text` or weird stuff happens
#[derive(Copy, Clone, Debug)]
pub struct Span<'i> {
    text: &'i str,

    file_info: &'i FileInfo<'i>,
}

impl<'i> Span<'i> {
    pub fn new(file_info: &'i FileInfo<'i>, range: Range<usize>) -> Self {
        Self {
            text: file_info.text.index(range),
            file_info,
        }
    }

    pub fn text(self) -> &'i str {
        self.text
    }
    pub fn file_info(self) -> &'i FileInfo<'i> {
        self.file_info
    }

    pub fn start(self) -> usize {
        self.text
            .as_ptr()
            .addr()
            .checked_sub(self.file_info.text.as_ptr().addr())
            .expect("`Span::text` not a subslice of `Span::file_info::text`")
    }
    pub fn end(self) -> usize {
        self.start() + self.text.len()
    }

    pub fn range(self) -> Range<usize> {
        self.start()..self.end()
    }

    // for<> should help ensure that the result is a substring
    pub fn map_text(&self, f: impl for<'t> FnOnce(&'t str) -> &'t str) -> Self {
        Self {
            text: f(self.text()),
            file_info: self.file_info,
        }
        .debug_check_valid()
    }

    pub fn map_text_array<F, const N: usize>(&self, f: F) -> [Self; N]
    where
        F: for<'t> FnOnce(&'t str) -> [&'t str; N],
    {
        f(self.text()).map(|text| {
            Self {
                text,
                file_info: self.file_info,
            }
            .debug_check_valid()
        })
    }

    fn debug_check_valid(self) -> Self {
        debug_assert!(
            self.text.as_ptr().addr() >= self.file_info.text.as_ptr().addr()
                && self.end() <= self.file_info.text.len()
        );
        self
    }
}

/// Represents a 'file' or more specifically a source string and an identifying name
#[derive(Debug)]
pub struct FileInfo<'i> {
    name: Cow<'i, str>,
    // this may need to be a slice
    text: Cow<'i, str>,
}

impl<'i> FileInfo<'i> {
    pub fn new(name: impl Into<Cow<'i, str>>, text: impl Into<Cow<'i, str>>) -> Self {
        Self {
            name: name.into(),
            text: text.into(),
        }
    }

    pub fn name(&self) -> &str {
        &self.name
    }
    pub fn text(&self) -> &str {
        &self.text
    }
}

pub type ArgStructure<'i> = WithInfo<Span<'i>, RawArgStructure<'i>>;

#[derive(Clone, Eq, PartialEq, Debug)]
pub enum RawArgStructure<'i> {
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
    pub fn deeper_than(self, other: Self) -> bool {
        self.0 >= other.0
    }

    /// shallow level by one level (None if already shallow as possible)
    pub fn shallower(self) -> Option<Self> {
        self.0.checked_sub(1).map(Self)
    }

    /// deepen level by one level (shouldn't reach maximum)
    pub fn deeper(self) -> Self {
        Self(self.0 + 1)
    }

    /// translate level by difference between other levels (shouldn't reach maximum)
    /// returns None if the result is invalid (ie. negative level)
    pub fn translate(self, before: Self, after: Self) -> Option<Self> {
        (self.0 + after.0).checked_sub(before.0).map(Self)
    }
}
