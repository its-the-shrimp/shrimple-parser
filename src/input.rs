/// This trait represents input that can be parsed by a [Parser] and/or matched by a [Pattern]
///
/// Its [`Default`] impl of the type should return a value that represents empty input, akin to an
/// empty string, `""`
///
/// [Parser]: crate::Parser
/// [Pattern]: crate::pattern::Pattern
pub trait Input: Sized + Clone + core::fmt::Debug + Default + core::ops::Deref<Target = str> {
    /// A generalisation of [`str::split_at`]
    #[must_use]
    fn split_at(self, mid: usize) -> (Self, Self);

    /// Equivalent to `self.split_at(mid).0`, but can be overridden to provide a more optimal
    /// implementation
    #[must_use]
    fn before(self, index: usize) -> Self {
        self.split_at(index).0
    }

    /// Equivalent to `self.split_at(mid).1`, but can be overriden to provide a more optimal
    /// implementation
    #[must_use]
    fn after(self, index: usize) -> Self {
        self.split_at(index).1
    }
}

impl Input for &str {
    fn split_at(self, mid: usize) -> (Self, Self) {
        str::split_at(self, mid)
    }

    fn before(self, index: usize) -> Self {
        &self[..index]
    }

    fn after(self, index: usize) -> Self {
        &self[index..]
    }
}
