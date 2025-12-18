type TypeRef<'ctx> = &'ctx Type<'ctx>;

// TODO: manual Hash / *Eq impls for more complex types
// TODO: impl Display for nicer output
#[derive(Hash, Eq, PartialEq, Debug)]
pub enum Type<'ctx> {
    Arr(Arr<'ctx>),

    Bool,
}

#[derive(Hash, Eq, PartialEq, Debug)]
pub struct Arr<'ctx> {
    pub arg: TypeRef<'ctx>,
    pub result: TypeRef<'ctx>,
}
