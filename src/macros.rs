#[macro_export]
macro_rules! newtype_derive_single {
    ($newtype:ident<$($generics:tt),*> ($inner:ty); Debug) => {
        impl<$($generics),*> std::fmt::Debug for $newtype<$($generics),*>
        where
            $inner: std::fmt::Debug,
        {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                self.0.fmt(f)
            }
        }
    };
}

#[macro_export]
macro_rules! newtype_derive {
    ([$($args:tt)*]) => {};
    ([$($args:tt)*] $trait:ident $(,$rest:ident)* $(,)?) => {
            $crate::newtype_derive_single!($($args)*; $trait);
            $crate::newtype_derive!([$($args)*] $($rest),*);
    };
}
