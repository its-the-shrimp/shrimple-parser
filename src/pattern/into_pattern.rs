use super::Pattern;

/// A trait for converting values into patterns. It exists to bridge the gap between an easy to use
/// library & a more performant, lean implementation.
///
/// All parsers that accept patterns for matching should accept `IntoPattern` values for better
/// ergonomics
pub trait IntoPattern {
    /// The pattern that this value converts to.
    type Pattern: Pattern;

    /// Converts the value into a pattern.
    fn into_pattern(self) -> Self::Pattern;
}

impl<T: Pattern> IntoPattern for T {
    type Pattern = Self;

    fn into_pattern(self) -> Self::Pattern {
        self
    }
}

macro_rules! tuple_into_cons_list {
    ($first:ident, $($next:ident),*) => { ($first, tuple_into_cons_list!($($next),+)) };
    ($only:ident) => { $only }
}

macro_rules! impl_into_pattern_for_tuple {
    ($($typename:ident),+) => {
        impl<$($typename: Pattern),+> IntoPattern for ($($typename),+) {
            type Pattern = tuple_into_cons_list!($($typename),+);

            #[expect(non_snake_case)]
            fn into_pattern(self) -> Self::Pattern {
                let ($($typename),+) = self;
                tuple_into_cons_list!($($typename),+)
            }
        }

        impl_into_pattern_for_tuple!(continue $($typename),+);
    };

    (continue $_dropped:ident, $new_first:ident, $new_second:ident, $($more:ident),+) => {
        impl_into_pattern_for_tuple!($new_first, $new_second, $($more),+);
    };

    (continue $_dropped:ident, $_new_first:ident, $_new_second:ident) => {};
}

impl_into_pattern_for_tuple!(T0, T1, T2, T3, T4, T5, T6, T7, T8, T9);

