use std::marker::PhantomData;
use creusot_contracts::{ensures, ghost, open, predicate, requires, trusted, Resolve, pearlite};
use creusot_contracts::std::ops::FnOnceExt;

pub trait Inv<T> {
    #[predicate]
    fn inv(t: T) -> bool;

    #[open]
    #[predicate]
    #[ensures(Self::inv(t) && t.resolve() ==> result)]
    fn co_inv(t: T) -> bool {
        true
    }
}

/// Ensures that I::inv(data) is true now
/// Has proof obligation that I::co_inv(data) will be true when 'a expires
/// Since this obligation burden is stronger for shorter lifetimes 'a is coinvariant
#[trusted]
pub struct InvS<'a, T, I: Inv<T>>{
    data: T,
    inv: PhantomData<(&'a (), I)>
}

pub struct LiftedInv<I>(I);

impl<T, I: Inv<T>> Inv<&mut T> for LiftedInv<I> {

    #[open]
    #[predicate]
    fn inv(t: &mut T) -> bool {
        I::inv(*t)
    }

    #[open]
    #[predicate]
    #[ensures(Self::inv(t) && t.resolve() ==> result)]
    // Leaking a T that satisifies its invariant must ensures its coinvariant
    fn co_inv(t: &mut T) -> bool {
        pearlite!{I::inv(^t) && (I::co_inv(^t) ==> I::co_inv(*t))}
    }
}

pub struct NopInv;

impl<T> Inv<T> for NopInv {
    #[open]
    #[predicate]
    fn inv(_: T) -> bool {
        true
    }
}

#[trusted]
impl<'a, T, I: Inv<T>> Resolve for InvS<'a, T, I> {

    #[open]
    #[predicate]
    fn resolve(self) -> bool {
        self.inner().resolve() && I::inv(self.inner())
    }
}

impl<'a, T, I: Inv<T>> InvS<'a, T, I> {
    #[trusted]
    #[open(self)]
    #[ghost]
    pub fn inner(self) -> T {
        self.data
    }

    #[trusted]
    #[requires(I::inv(data))]
    #[ensures(result.inner() == data)]
    pub fn new(data: T) -> Self {
        InvS{data, inv: PhantomData}
    }

    #[trusted]
    #[requires(I::inv(self.inner()) ==> I::co_inv(self.inner()))]
    #[ensures(result == self.inner())]
    #[ensures(I::inv(self.inner()))]
    pub fn open(self) -> T {
        self.data
    }

    #[trusted]
    #[ensures(I::inv((*self).inner()))]
    #[ensures(*result == (*self).inner())]
    pub fn deref(&self) -> &T {
        &self.data
    }

    #[trusted]
    #[ensures(*result.inner() == (*self).inner())]
    #[ensures(^result.inner() == (^self).inner())]
    pub fn lift(&mut self) -> InvS<'_, &mut T, LiftedInv<I>> {
        InvS::new(&mut self.data)
    }

    #[trusted]
    #[requires(I::inv(self.inner()) ==> f.precondition((self.inner(),)))]
    #[requires(forall<res: U> I::inv(self.inner()) ==> f.postcondition_once((self.inner(),), res) ==>
        I2::inv(res) && (I2::co_inv(res) ==> I::co_inv(self.inner())))]
    #[ensures(I::inv(self.inner()) && f.postcondition_once((self.inner(),), result.inner()))]
    pub fn map<U, F: FnOnce(T) -> U, I2: Inv<U>>(self, f: F) -> InvS<'a, U, I2> {
        InvS::new(f(self.data))
    }

    #[requires(I::inv(self.inner()) ==> f.precondition((self.inner(),)))]
    #[requires(forall<res: U> I::inv(self.inner()) ==> f.postcondition_once((self.inner(),), res) ==>
        I::co_inv(self.inner()))]
    #[ensures(I::inv(self.inner()) && f.postcondition_once((self.inner(),), result))]
    pub fn open_with<U, F: FnOnce(T) -> U>(self, f: F) -> U {
        let res: InvS<U, NopInv> = self.map(f);
        res.open()
    }

    #[requires(forall<m: &mut T> *m == (*self).inner() ==> I::inv(*m) ==> f.precondition((m,)))]
    #[requires(forall<m: &mut T, res: U> *m == (*self).inner() ==> I::inv(*m) ==> f.postcondition_once((m,), res)
      ==> I::inv(^m) && (I::co_inv(^m) ==> I::co_inv(*m)))]
    #[ensures(exists<m: &mut T> *m == (*self).inner() && I::inv(*m) && ^m == (^self).inner() && f.postcondition_once((m,), result))]
    pub fn with_mut<'b, U, F: FnOnce(&'b mut T) -> U>(&'b mut self, f: F) -> U {
        self.lift().open_with(f)
    }

    #[requires(forall<m: &mut T> *m == (*self).inner() ==> I::inv(*m) ==> f.precondition((m,)))]
    #[requires(forall<m: &mut T, res: U> *m == (*self).inner() ==> I::inv(*m) ==> f.postcondition_once((m,), res)
      ==> I2::inv(res) && (I2::co_inv(res) ==> I::inv(^m) && (I::co_inv(^m) ==> I::co_inv(*m))))]
    #[ensures(exists<m: &mut T> *m == (*self).inner() && I::inv(*m) && ^m == (^self).inner() && f.postcondition_once((m,), result.inner()))]
    pub fn map_mut<'b, U, F: FnOnce(&'b mut T) -> U, I2: Inv<U>>(&'b mut self, f: F) -> InvS<'b, U, I2> {
        self.lift().map(f)
    }
}