use creusot_contracts::{requires, ensures, ghost, open, predicate};
use crate::inv::*;
use crate::my_box::MyBox as MyBoxInner;

struct MyBoxInv;

impl<T> Inv<MyBoxInner<T>> for MyBoxInv {
    #[predicate]
    #[open(self)]
    fn inv(t: MyBoxInner<T>) -> bool {
        t.invariant()
    }
}

struct MyBox<T>(InvS<'static, MyBoxInner<T>, MyBoxInv>);

impl<T> MyBox<T> {
    #[open(self)]
    #[ghost]
    pub fn model(self) -> T {
        self.0.inner().model()
    }

    #[ensures(result.model() == val)]
    pub fn new(val: T) -> Self {
        MyBox(InvS::new(MyBoxInner::new(val)))
    }
    #[ensures(result == self.model())]
    pub fn into_inner(self) -> T {
        self.0.open().into_inner()
    }

    #[ensures(*result == (*self).model())]
    pub fn deref(&self) -> &T {
        self.0.deref().deref()
    }

    #[ensures(*result == (*self).model())]
    #[ensures(^result == (^self).model())]
    pub fn deref_mut<'a>(&'a mut self) -> &'a mut T {
        self.0.with_mut(
            #[requires((*x).invariant())]
            #[ensures(*result == (*x).model())]
            #[ensures((^x).invariant())]
            #[ensures(^result == (^x).model())]
                |x| MyBoxInner::deref_mut(x)
        )
    }
}
