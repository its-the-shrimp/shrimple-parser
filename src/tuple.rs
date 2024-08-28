//! This module contains utilities for working with generic tuples, such as:
//! - Extracting & transforming the N-th element of a tuple;
//! - Extracting N first elements of a tuple or splitting it;
//! - Extending a tuple from both ends;
//! - Reversing a tuple.
//! - Copying/cloning a tuple element per element. (i.e. turn `(&T, &U)` into `(T, U)`
//!
//! See the [`Tuple`] trait or the free-standing functions.

/// The trait for a tuple that has the N-th element, the backbone of the [`Tuple::nth`] function.
/// The associated functions are not to be used directly, instead use the equivalent functions
/// or methods of the [`Tuple`] trait.
#[diagnostic::on_unimplemented(
    message = "`{Self}` is not a tuple, doesn't have an element #{N}, or is too long",
    note = "At the moment, the trait is implemented only for tuples up to length 8"
)]
pub trait Index<const N: usize>: Tuple {
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

/// The trait for a tuple that has at least N elements, the backbone of the
/// [`Tuple::first_n`] function.
/// The associated functions are not to be used directly, instead use the equivalent functions
/// or methods of the [`Tuple`] trait.
#[diagnostic::on_unimplemented(
    message = "`{Self}` is not tuple, has less than {N} elements, or is too long",
    note = "At the moment, the trait is implemented only for tuples up to length 8",
)]
pub trait Slice<const N: usize>: Tuple {
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

/// The trait for a tuple, all elements of which are references to [`Clone`]-able values,
/// the backbone of the [`Tuple::cloned`] function.
/// The associated functions are not to be used directly, instead use the equivalent free-standing
/// functions or methods of the [`Tuple`] trait.
pub trait CloneableRefs: Tuple {
    /// The result of [`CloneableRefs::cloned`]
    type Cloned;

    /// Clone the tuple element-wise, e.g. turn `(&T, &U)` into `(T, U)`
    fn cloned(this: Self) -> Self::Cloned;
}

/// The trait for a tuple, all elements of which are references to [`Copy`]-able values,
/// the backbone of the [`Tuple::copied`] function.
/// The associated functions are not to be used directly, instead use the equivalent free-standing
/// functions or methods of the [`Tuple`] trait.
pub trait CopiableRefs: Tuple {
    /// The result of [`CopiableRefs::copied`]
    type Copied;

    /// Copy the tuple element-wise, e.g. turn `(&T, &U)` into `(T, U)`
    fn copied(this: Self) -> Self::Copied;
}

macro_rules! impl_nth_methods {
    ($n:literal, $name:ident, $ref_name:ident, $map_name:ident) => {
        #[doc = concat!("Returns the ", stringify!($name), " element of the tuple.")]
        #[doc = "For a more generic function, see [`Tuple::nth`]"]
        fn $name(self) -> Self::Nth where Self: Index<$n> {
            Index::nth(self)
        }

        #[doc = concat!("Returns a reference to the ", stringify!($name), " element of the tuple.")]
        #[doc = "For a more generic function, see [`Tuple::nth_ref`]"]
        fn $ref_name(&self) -> &Self::Nth where Self: Index<$n> {
            Index::nth_ref(self)
        }

        #[doc = concat!("Transforms the ", stringify!($name), " element of the tuple with `f`.")]
        #[doc = "For a more generic function, see [`Tuple::map_nth`]"]
        fn $map_name<U>(self, f: impl FnOnce(Self::Nth) -> U) -> Self::NthMapped<U>
        where
            Self: Index<$n>
        {
            Index::map_nth(self, f)
        }
    };
}

/// Trait for a generic tuple.
#[diagnostic::on_unimplemented(
    message = "`{Self}` is not a tuple or is too long",
    note = "At the moment, the trait is implemented only for tuples up to length 8"
)]
pub trait Tuple: Sized {
    /// The tuple + a new element at the end, the result of [`Tuple::append`]
    type Appended<NewElement>;

    /// The tuple + a new element at the start, the result of [`Tuple::prepend`]
    type Prepended<NewElement>;

    /// The tuple with its elements in reverse order, the result of [`Tuple::rev`]
    type Reversed;

    /// Adds `new_element` to the end of the tuple.
    /// Also see [`append`]
    fn append<NewElement>(self, new_element: NewElement) -> Self::Appended<NewElement>;

    /// Adds `new_element` to the start of the tuple.
    /// Also see [`prepend`]
    fn prepend<NewElement>(self, new_element: NewElement) -> Self::Prepended<NewElement>;

    /// Returns the tuple with its elements in reverse order.
    /// Also see [`rev`]
    fn rev(self) -> Self::Reversed;

    /// Clones the tuple element-wise, e.g. turn `(&T, &U)` into `(T, U)`
    /// Also see [`cloned`]
    fn cloned(self) -> Self::Cloned where Self: CloneableRefs {
        CloneableRefs::cloned(self)
    }

    /// Copies the tuple element-wise, e.g. turn `(&T, &U)` into `(T, U)`
    /// Also see [`copied`]
    fn copied(self) -> Self::Copied where Self: CopiableRefs {
        CopiableRefs::copied(self)
    }

    /// Returns the `N`-th element of the tuple.
    /// For shortcuts see [`Tuple::first`], [`Tuple::second`], [`Tuple::third`]
    fn nth<const N: usize>(self) -> Self::Nth where Self: Index<N> {
        Index::nth(self)
    }

    /// Returns a reference to the `N`-th element of the tuple.
    /// For shortcuts see [`Tuple::first_ref`], [`Tuple::second_ref`], [`Tuple::third_ref`]
    fn nth_ref<const N: usize>(&self) -> &Self::Nth where Self: Index<N> {
        Index::nth_ref(self)
    }

    /// Returns a function that transforms the N-th element of a tuple with `f`.
    /// For common shortcuts, see [`Tuple::map_first`], [`Tuple::map_second`], [`Tuple::map_third`]
    fn map_nth<const N: usize, U>(self, f: impl FnOnce(Self::Nth) -> U) -> Self::NthMapped<U>
    where
        Self: Index<N>
    {
        Index::map_nth(self, f)
    }

    impl_nth_methods!(0, first, first_ref, map_first);
    impl_nth_methods!(1, second, second_ref, map_second);
    impl_nth_methods!(2, third, third_ref, map_third);

    /// Returns a tuple that containing the first N elements of the original tuple.
    /// The other elements are discarded.
    fn first_n<const N: usize>(self) -> Self::FirstN where Self: Slice<N> {
        Slice::first_n(self)
    }

    /// Returns the original tuple with its first N elements discarded.
    /// Logical complement of [`Tuple::first_n`]
    fn strip_first_n<const N: usize>(self) -> Self::FirstNStripped where Self: Slice<N> {
        Slice::strip_first_n(self)
    }

    /// Splits the tuple into one with the first N elements and one with the rest.
    fn split<const N: usize>(self) -> (Self::FirstN, Self::FirstNStripped)
    where
        Self: Slice<N>
    {
        Slice::split(self)
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

        impl<$($t),*> Slice<$length> for ($($t,)*) {
            type FirstN = Self;
            type FirstNStripped = ();

            fn first_n(this: Self) -> Self::FirstN { this }
            fn strip_first_n(_: Self) -> Self::FirstNStripped {}
            fn split(this: Self) -> (Self::FirstN, Self::FirstNStripped) { (this, ()) }
        }

        #[allow(non_snake_case)]
        impl<$($t: Clone),*> CloneableRefs for ($(&$t,)*) {
            type Cloned = ($($t,)*);

            #[allow(clippy::unused_unit)]
            fn cloned(this: Self) -> Self::Cloned {
                let ($($t,)*) = this;
                ($($t.clone(),)*)
            }
        }

        #[allow(non_snake_case)]
        impl<$($t: Copy),*> CopiableRefs for ($(&$t,)*) {
            type Copied = ($($t,)*);

            #[allow(clippy::unused_unit)]
            fn copied(this: Self) -> Self::Copied {
                let ($($t,)*) = this;
                ($(*$t,)*)
            }
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
        impl<$($t),+> Index<$id> for ($($t,)+) {
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
        impl<$($t),+> Slice<$id> for ($($t,)+) {
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
        pub fn $name<T: Index<$n>>(tuple: T) -> T::Nth {
            Index::nth(tuple)
        }

        #[doc = concat!("Returns a reference to the ", stringify!($name), " element of the tuple.")]
        #[doc = "For a more generic function, see [`Tuple::nth_ref`]"]
        pub fn $ref_name<T: Index<$n>>(tuple: &T) -> &T::Nth {
            Index::nth_ref(tuple)
        }

        #[doc = concat!(
            "Returns a function that transforms the ",
            stringify!($name),
            " element of a tuple with `f`."
        )]
        #[doc = "For a more generic function, see [`Tuple::map_nth`]"]
        pub fn $map_name<T: Index<$n>, U>(mut f: impl FnMut(T::Nth) -> U)
            -> impl FnMut(T)
            -> T::NthMapped<U>
        {
            move |tuple| Index::map_nth(tuple, &mut f)
        }
    };
}

impl_nth_fn!(0, first, first_ref, map_first);
impl_nth_fn!(1, second, second_ref, map_second);
impl_nth_fn!(2, third, third_ref, map_third);

/// Adds `new_element` to the end of a tuple and returns the resulting new tuple.
pub fn append<T: Tuple, U: Clone>(new_element: U) -> impl Fn(T) -> T::Appended<U> {
    move |tuple| tuple.append(new_element.clone())
}

/// Adds `new_element` to the beginning of a tuple and returns the resulting new tuple.
pub fn prepend<U: Clone, T: Tuple>(new_element: U) -> impl Fn(T) -> T::Prepended<U> {
    move |tuple| tuple.prepend(new_element.clone())
}

/// Turns `T` into a tuple with 1 element, `T`
pub const fn tuple<T>(x: T) -> (T,) { (x,) }

/// Reverses the tuple.
pub fn rev<T: Tuple>(x: T) -> T::Reversed {
    x.rev()
}

/// Clones the tuple element-wise, e.g. turns `(&T, &U)` into `(T, U)`
pub fn cloned<T: CloneableRefs>(x: T) -> T::Cloned {
    CloneableRefs::cloned(x)
}

/// Copies the tuple element-wise, e.g. turns `(&T, &U)` into `(T, U)`
pub fn copied<T: CopiableRefs>(x: T) -> T::Copied {
    CopiableRefs::copied(x)
}

/// Generates a closure that constructs a struct from a tuple.
/// The struct fields must be exactly in the order in which they're expected to be in the tuple.
/// ```rust
/// # fn main() {
/// use shrimple_parser::{Parser, pattern::parse_until_ex, from_tuple};
///
/// #[derive(Debug, PartialEq, Eq)]
/// struct Example<'src> { a: &'src str, b: &'src str }
///
/// let input = "abc|def|";
/// let res = parse_until_ex("|")
///     .and(parse_until_ex("|"))
///     .map(from_tuple!(Example { a, b }))
///     .parse(input);
/// assert_eq!(res, Ok(("", Example { a: "abc", b: "def" })))
/// # }
/// ```
#[macro_export]
macro_rules! from_tuple {
    ($name:ident { $($field:ident),* $(,)? }) => { |($($field,)*)| $name { $($field),* } };
}

#[macro_export]
#[doc(hidden)]
macro_rules! last {
    ($_:tt $($rest:tt)+) => { $($rest)+ };
    ($last:tt) => { $last };
}

/// Generates a closure that calls a function with a tuple's contents as it arguments.
/// The input can be anything as long as the last token contains all the arguments parenthesized.
/// ```rust
/// # fn main() {
/// use shrimple_parser::{Parser, pattern::parse_until_ex, call};
///
/// fn len_sum(a: &str, b: &str) -> usize {
///     a.len() + b.len()
/// }
///
/// let input = "abc|def|";
/// let res = parse_until_ex("|")
///     .and(parse_until_ex("|"))
///     .map(call!(len_sum(a, b)))
///     .parse(input);
/// assert_eq!(res, Ok(("", 6)))
/// # }
/// ```
#[macro_export]
macro_rules! call {
    ($($args:tt)*) => { |$crate::last!($($args)*)| $($args)* };
}
