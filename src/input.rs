/// This trait represents input that can be parsed by a [Parser] and/or matched by a [Pattern].
///
/// An [`Input`] must be cheaply cloneable, which is why types like `Box<str>` or `String` don't
/// implement this trait.
///
/// If you want to create an
/// empty span of the input of a parser, better carve it out of the input to keep the pointer
/// inside it. Even an empty string can provide info on its location in the source code.
/// [`Input::start`] & [`Input::end`] methods will help you with that.
///
/// [Parser]: crate::Parser
/// [Pattern]: crate::pattern::Pattern
pub trait Input:
    Sized + Clone + core::fmt::Debug + core::ops::Deref<Target = str>
{
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

    /// Returns an empty string that points to the start of the input
    fn start(self) -> Self {
        self.before(0)
    }
    
    /// Returns an empty string that points to the end of the input
    fn end(self) -> Self {
        let len = self.len();
        self.after(len)
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
