use creusot_contracts::ghost_ptr::GhostPtrToken;
use creusot_contracts::{ensures, ghost, open, predicate, requires, ShallowModel};

pub(super) struct MyBox<T> {
    ptr: *const T,
    token: GhostPtrToken<T>,
}

impl<T> MyBox<T> {
    #[open(self)]
    #[predicate]
    pub fn invariant(self) -> bool {
        self.token.shallow_model().contains(self.ptr) && self.token.shallow_model().len() == 1
    }

    #[open(self)]
    #[ghost]
    #[requires(self.invariant())]
    pub fn model(self) -> T {
        self.token.shallow_model().lookup(self.ptr)
    }

    #[ensures(result.invariant())]
    #[ensures(result.model() == val)]
    pub fn new(val: T) -> Self {
        let mut token = GhostPtrToken::new();
        let ptr = token.ptr_from_box(Box::new(val));
        MyBox { ptr, token }
    }

    #[requires(self.invariant())]
    #[ensures(result == self.model())]
    pub fn into_inner(self) -> T {
        let MyBox { ptr, mut token } = self;
        let res = token.ptr_to_box(ptr);
        token.drop();
        *res
    }

    #[requires((*self).invariant())]
    #[ensures(*result == (*self).model())]
    pub fn deref(&self) -> &T {
        self.token.ptr_as_ref(self.ptr)
    }

    #[requires((*self).invariant())]
    #[ensures(*result == (*self).model())]
    #[ensures((^self).invariant())]
    #[ensures(^result == (^self).model())]
    pub fn deref_mut(&mut self) -> &mut T {
        self.token.ptr_as_mut(self.ptr)
    }
}
