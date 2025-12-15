#[derive(Eq, PartialEq, Debug)]
pub enum Term<'i> {
    Abs(Abs<'i>),
    App(App<'i>),

    Var(Var<'i>),

    Bool(bool),
}

#[derive(Eq, PartialEq, Debug)]
pub struct Abs<'i> {
    pub arg_type: Type,

    pub body: Box<Term<'i>>,
}

#[derive(Eq, PartialEq, Debug)]
pub struct App<'i> {
    pub func: Box<Term<'i>>,
    pub arg: Box<Term<'i>>,
}

#[derive(Eq, PartialEq, Debug)]
pub struct Var<'i> {
    pub name: &'i str,
    pub index: usize,
}

#[derive(Eq, PartialEq, Debug)]
pub enum Type {
    Arr(Arr),

    Bool,
}

#[derive(Eq, PartialEq, Debug)]
pub struct Arr {
    pub arg: Box<Type>,
    pub result: Box<Type>,
}
