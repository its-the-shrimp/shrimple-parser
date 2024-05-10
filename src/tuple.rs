//! This module contains utilities for working with generic tuples, such as:
//! - Extracting & transforming the N-th element of a tuple;
//! - Extracting N first elements of a tuple or splitting it;
//! - Extending a tuple from both ends;
//! - Reversing a tuple.
//!
//! See the [`Tuple`] trait or the free-standing functions.

/// The trait for a tuple that has the N-th element, the backbone of the [`nth`] function.
/// The associated functions are not to be used directly, instead use the equivalent functions
/// or methods of the [`Tuple`] trait.
#[diagnostic::on_unimplemented(
    message = "`{Self}` is not a tuple, doesn't have an element #{N}, or is too long",
    note = "At the moment, the trait is implemented only for tuples up to length 8"
)]
pub trait IndexTuple<const N: usize>: Sized + Tuple {
    /// The N-th element of the tuple.
    type Nth;
    /// The tuple with its N-th element mapped to `U`.
    type NthMapped<U>;

    /// Returns the N-th element of the tuple.
    fn nth(this: Self) -> Self::Nth;

    /// Returns a reference to the N-th element of the tuple.
    fn nth_ref(this: &Self) -> &Self::Nth;

    /// Returns the tuple with the N-th element transformed by `f`
    fn map_nth<U>(this: Self, f: impl FnOnce(Self::Nth) -> U) -> Self::NthMapped<U>;
}

/// The trait for a tuple that has at least N elements, the backbone of the [`first_n`] function.
/// The associated functions are not to be used directly, instead use the equivalent functions
/// or methods of the [`Tuple`] trait.
#[diagnostic::on_unimplemented(
    message = "`{Self}` is not tuple, has less than {N} elements, or is too long",
    note = "At the moment, the trait is implemented only for tuples up to length 8",
)]
pub trait SliceTuple<const N: usize>: Sized + Tuple {
    /// A tuple containing the first N elements of the original tuple. 
    type FirstN;

    /// A tuple with the first N elements of the original tuple.
    type FirstNStripped;

    /// Return the first N elements of the tuple as a tuple.
    fn first_n(this: Self) -> Self::FirstN;

    /// Returns the tuple without the first N elements
    fn strip_first_n(this: Self) -> Self::FirstNStripped;

    /// Splits the tuple into 2, with the 1st tuple having the 1st N element,
    /// and the 2nd tuple having the rest.
    fn split(this: Self) -> (Self::FirstN, Self::FirstNStripped);
}

macro_rules! impl_nth_methods {
    ($n:literal, $name:ident, $ref_name:ident, $map_name:ident) => {
        #[doc = concat!("Returns the ", stringify!($name), " element of the tuple.")]
        #[doc = "For a more generic function, see [`Tuple::nth`]"]
        fn $name(self) -> Self::Nth where Self: IndexTuple<$n> {
            IndexTuple::nth(self)
        }

        #[doc = concat!("Returns a reference to the ", stringify!($name), " element of the tuple.")]
        #[doc = "For a more generic function, see [`Tuple::nth_ref`]"]
        fn $ref_name(&self) -> &Self::Nth where Self: IndexTuple<$n> {
            IndexTuple::nth_ref(self)
        }

        #[doc = concat!("Transforms the ", stringify!($name), " element of the tuple with `f`.")]
        #[doc = "For a more generic function, see [`Tuple::map_nth`]"]
        fn $map_name<U>(self, f: impl FnOnce(Self::Nth) -> U) -> Self::NthMapped<U>
        where
            Self: IndexTuple<$n>
        {
            IndexTuple::map_nth(self, f)
        }
    };
}

/// Trait for a generic tuple.
/// Most methods in the trait have equivalents in the form of free-standing functions.
#[diagnostic::on_unimplemented(
    message = "`{Self}` is not a tuple or is too long",
    note = "At the moment, the trait is implemented only for tuples up to length 8"
)]
pub trait Tuple: Sized {
    /// The tuple + a new element at the end.
    type Appended<NewElement>;

    /// The tuple + a new element at the start.
    type Prepended<NewElement>;

    /// The tuple with its elements in reverse order.
    type Reversed;

    /// Adds `new_element` to the end of the tuple.
    fn append<NewElement>(self, new_element: NewElement) -> Self::Appended<NewElement>;

    /// Adds `new_element` to the start of the tuple.
    fn prepend<NewElement>(self, new_element: NewElement) -> Self::Prepended<NewElement>;

    /// Returns the tuple with its elements in reverse order.
    fn rev(self) -> Self::Reversed;

    /// Returns the `N`-th element of the tuple.
    /// For shortcuts see [`Tuple::first`], [`Tuple::second`], [`Tuple::third`]
    fn nth<const N: usize>(self) -> Self::Nth where Self: IndexTuple<N> {
        IndexTuple::nth(self)
    }

    /// Returns a reference to the `N`-th element of the tuple.
    /// For shortcuts see [`Tuple::first_ref`], [`Tuple::second_ref`], [`Tuple::third_ref`]
    fn nth_ref<const N: usize>(&self) -> &Self::Nth where Self: IndexTuple<N> {
        IndexTuple::nth_ref(self)
    }

    /// Returns a function that transforms the N-th element of a tuple with `f`.
    /// For common shortcuts, see [`Tuple::map_first`], [`Tuple::map_second`], [`Tuple::map_third`]
    fn map_nth<const N: usize, U>(self, f: impl FnOnce(Self::Nth) -> U) -> Self::NthMapped<U>
    where
        Self: IndexTuple<N>
    {
        IndexTuple::map_nth(self, f)
    }

    impl_nth_methods!(0, first, first_ref, map_first);
    impl_nth_methods!(1, second, second_ref, map_second);
    impl_nth_methods!(2, third, third_ref, map_third);

    /// Returns a tuple that containing the first N elements of the original tuple.
    /// The other elements are discarded.
    fn first_n<const N: usize>(self) -> Self::FirstN where Self: SliceTuple<N> {
        SliceTuple::first_n(self)
    }

    /// Returns the original tuple with its first N elements discarded.
    /// Logical complement of [`Tuple::first_n`]
    fn strip_first_n<const N: usize>(self) -> Self::FirstNStripped where Self: SliceTuple<N> {
        SliceTuple::strip_first_n(self)
    }

    /// Splits the tuple into one with the first N elements and one with the rest.
    fn split<const N: usize>(self) -> (Self::FirstN, Self::FirstNStripped)
    where
        Self: SliceTuple<N>
    {
        SliceTuple::split(self)
    }
}

macro_rules! rev {
    ($($x:ident,)*) => { rev!(| $($x,)* |) };
    (| $x:ident, $($rest:ident,)* | $($rev:ident,)*) => { rev!(| $($rest,)* | $x, $($rev,)*) };
    (| | $($rev:ident,)*) => { ($($rev,)*) };
}

macro_rules! impl_tuple_traits {
    ($length:literal - $($n:literal : $t:ident),*) => {
        impl_tuple_traits!([] [$($n:$t,)*] [$($t),*]);

        impl<$($t),*> SliceTuple<$length> for ($($t,)*) {
            type FirstN = Self;
            type FirstNStripped = ();

            fn first_n(this: Self) -> Self::FirstN { this }
            fn strip_first_n(_: Self) -> Self::FirstNStripped {}
            fn split(this: Self) -> (Self::FirstN, Self::FirstNStripped) { (this, ()) }
        }

        #[allow(non_snake_case)]
        impl<$($t),*> Tuple for ($($t,)*) {
            type Appended<NewElement> = ($($t,)* NewElement,);
            type Prepended<NewElement> = (NewElement, $($t,)*);
            type Reversed = rev!($($t,)*);

            fn append<NewElement>(self, new_element: NewElement) -> Self::Appended<NewElement> {
                let ($($t,)*) = self;
                ($($t,)* new_element,)
            }

            fn prepend<NewElement>(self, new_element: NewElement) -> Self::Prepended<NewElement> {
                let ($($t,)*) = self;
                (new_element, $($t,)*)
            }

            fn rev(self) -> Self::Reversed {
                let ($($t,)*) = self;
                rev!($($t,)*)
            }
        }

    };

    ($prev:tt [] $t:tt) => {};

    ([$($prev:ident),*] [$id:literal : $nth:ident, $($next_id:literal : $next:ident,)*] [$($t:ident),+]) => {
        #[allow(non_snake_case)]
        impl<$($t),+> IndexTuple<$id> for ($($t,)+) {
            type Nth = $nth;
            type NthMapped<U> = ($($prev,)* U, $($next,)*);

            #[allow(unused)]
            fn nth(this: Self) -> Self::Nth {
                let ($($t,)+) = this;
                $nth
            }

            #[allow(unused)]
            fn nth_ref(this: &Self) -> &Self::Nth {
                let ($($t,)+) = this;
                $nth
            }

            fn map_nth<U>(this: Self, f: impl FnOnce(Self::Nth) -> U) -> Self::NthMapped<U> {
                let ($($t,)+) = this;
                ($($prev,)* f($nth), $($next,)*)
            }
        }

        #[allow(non_snake_case)]
        impl<$($t),+> SliceTuple<$id> for ($($t,)+) {
            type FirstN = ($($prev,)*);
            type FirstNStripped = ($nth, $($next,)*);

            #[allow(unused, clippy::unused_unit)]
            fn first_n(this: Self) -> Self::FirstN {
                let ($($t,)+) = this;
                ($($prev,)*)
            }

            #[allow(unused)]
            fn strip_first_n(this: Self) -> Self::FirstNStripped {
                let ($($t,)+) = this;
                ($nth, $($next,)*)
            }

            fn split(this: Self) -> (Self::FirstN, Self::FirstNStripped) {
                let ($($t,)+) = this;
                (($($prev,)*), ($nth, $($next,)*))
            }
        }

        impl_tuple_traits!([$($prev,)* $nth] [$($next_id:$next,)*] [$($t),+]);
    };
}

impl_tuple_traits!(0 -);
impl_tuple_traits!(1 - 0: T0);
impl_tuple_traits!(2 - 0: T0, 1: T1);
impl_tuple_traits!(3 - 0: T0, 1: T1, 2: T2);
impl_tuple_traits!(4 - 0: T0, 1: T1, 2: T2, 3: T3);
impl_tuple_traits!(5 - 0: T0, 1: T1, 2: T2, 3: T3, 4: T4);
impl_tuple_traits!(6 - 0: T0, 1: T1, 2: T2, 3: T3, 4: T4, 5: T5);
impl_tuple_traits!(7 - 0: T0, 1: T1, 2: T2, 3: T3, 4: T4, 5: T5, 6: T6);
impl_tuple_traits!(8 - 0: T0, 1: T1, 2: T2, 3: T3, 4: T4, 5: T5, 6: T6, 7: T7);

macro_rules! impl_nth_fn {
    ($n:literal, $name:ident, $ref_name:ident, $map_name:ident) => {
        #[doc = concat!("Returns the ", stringify!($name), " element of the tuple.")]
        #[doc = "For a more generic function, see [`Tuple::nth`]"]
        pub fn $name<T: IndexTuple<$n>>(tuple: T) -> T::Nth {
            IndexTuple::nth(tuple)
        }

        #[doc = concat!("Returns a reference to the ", stringify!($name), " element of the tuple.")]
        #[doc = "For a more generic function, see [`Tuple::nth_ref`]"]
        pub fn $ref_name<T: IndexTuple<$n>>(tuple: &T) -> &T::Nth {
            IndexTuple::nth_ref(tuple)
        }

        #[doc = concat!(
            "Returns a function that transforms the ",
            stringify!($name),
            " element of a tuple with `f`."
        )]
        #[doc = "For a more generic function, see [`Tuple::map_nth`]"]
        pub fn $map_name<T: IndexTuple<$n>, U>(f: impl FnOnce(T::Nth) -> U)
            -> impl FnOnce(T)
            -> T::NthMapped<U>
        {
            move |tuple| IndexTuple::map_nth(tuple, f)
        }
    };
}

impl_nth_fn!(0, first, first_ref, map_first);
impl_nth_fn!(1, second, second_ref, map_second);
impl_nth_fn!(2, third, third_ref, map_third);

/// Adds `new_element` to the end of a tuple and returns the resulting new tuple.
pub fn append<T: Tuple, U>(new_element: U) -> impl FnOnce(T) -> T::Appended<U> {
    move |tuple| tuple.append(new_element)
}

/// Adds `new_element` to the beginning of a tuple and returns the resulting new tuple.
pub fn prepend<U, T: Tuple>(new_element: U) -> impl FnOnce(T) -> T::Prepended<U> {
    move |tuple| tuple.prepend(new_element)
}

/// Turns `T` into a tuple with 1 element, `T`
pub const fn tuple<T>(x: T) -> (T,) { (x,) }

/// Reverses the tuple.
pub fn rev<T: Tuple>(x: T) -> T::Reversed {
    x.rev()
}
