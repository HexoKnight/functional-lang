use crate::newtype_derive;

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub struct Span<'i> {
    pub text: &'i str,
    pub start: usize,
}

#[derive(Clone, Eq, PartialEq, Debug)]
pub enum ArgStructure {
    Tuple(Box<[ArgStructure]>),
    Var,
}

#[derive(Copy, Clone, Eq, PartialEq)]
pub struct EnumLabel<'i>(pub &'i str);

newtype_derive!([EnumLabel<'i>(&'i str)] Debug);
