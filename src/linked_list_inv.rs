use creusot_contracts::{ensures, ghost, open, predicate, ShallowModel, Seq, logic, Resolve};
use crate::inv::*;
use crate::linked_list::{LinkedList as LinkedListInner, Iter as IterInner, IterMut as IterMutInner};

struct LinkedListInv;

impl<T> Inv<LinkedListInner<T>> for LinkedListInv {
    #[predicate]
    #[open(self)]
    fn inv(t: LinkedListInner<T>) -> bool {
        t.invariant()
    }
}

struct LinkedList<T>(InvS<'static, LinkedListInner<T>, LinkedListInv>);

impl<T> ShallowModel for LinkedList<T> {
    type ShallowModelTy = Seq<T>;

    #[ghost]
    #[open(self)]
    fn shallow_model(self) -> Self::ShallowModelTy {
        self.0.inner().model()
    }
}
impl<T> LinkedList<T> {

    #[ensures(result@ == Seq::new())]
    pub fn new() -> Self {
        LinkedList(InvS::new(LinkedListInner::new()))
    }

    #[ensures(result@ == Seq::singleton(v))]
    pub fn singleton(v: T) -> Self {
        LinkedList(InvS::new(LinkedListInner::singleton(v)))
    }

    #[ensures(match result {
        Some(val) => Seq::singleton(val).concat((^self)@) == (*self)@,
        None => ^self == *self && (*self)@ == Seq::new()
    })]
    pub fn dequeue(&mut self) -> Option<T> {
        self.0.with_mut(|x| x.dequeue())
    }

    #[ensures(result@ == self@)]
    pub fn iter(&self) -> Iter<'_, T> {
        Iter(InvS::new(self.0.deref().iter()))
    }

    #[ensures(result.seq() == (*self)@)]
    #[ensures((^self)@ == result.fin_seq())]
    pub fn iter_mut(&mut self) -> IterMut<'_, T> {
        IterMut(self.0.map_mut(LinkedListInner::iter_mut))
    }
}

struct IterInv;

impl<'a, T> Inv<IterInner<'a, T>> for IterInv {
    #[predicate]
    #[open(self)]
    fn inv(t: IterInner<T>) -> bool {
        t.invariant()
    }
}

pub struct Iter<'a, T>(InvS<'a, IterInner<'a, T>, IterInv>);

impl<'a, T> ShallowModel for Iter<'a, T> {
    type ShallowModelTy = Seq<T>;

    #[ghost]
    #[open(self)]
    fn shallow_model(self) -> Self::ShallowModelTy {
        self.0.inner().model()
    }
}

impl<'a, T> Iter<'a, T> {
    #[ensures(match result {
        Some(val) => Seq::singleton(*val).concat((^self)@) == (*self)@,
        None => ^self == *self && (*self)@ == Seq::new()
    })]
    pub fn next(&mut self) -> Option<&'a T> {
        self.0.with_mut(IterInner::next)
    }
}

struct IterMutInv;

impl<'a, T> Inv<IterMutInner<'a, T>> for IterMutInv {
    #[predicate]
    #[open(self)]
    fn inv(t: IterMutInner<'a, T>) -> bool {
        t.invariant()
    }

    #[predicate]
    #[open(self)]
    #[ensures(Self::inv(t) && t.resolve() ==> result)]
    fn co_inv(t: IterMutInner<'a, T>) -> bool {
        t.fin_invariant()
    }
}

pub struct IterMut<'a, T>(InvS<'a, IterMutInner<'a, T>, IterMutInv>);

impl<'a, T> IterMut<'a, T> {

    #[ghost]
    #[open(self)]
    pub fn seq(self) -> Seq<T> {
        self.0.inner().model()
    }

    #[logic]
    #[open(self)]
    pub fn fin_seq(self) -> Seq<T> {
        self.0.inner().fin_model()
    }

    #[ensures(match result {
        Some(val) => Seq::singleton(*val).concat((^self).seq()) == (*self).seq(),
        None => ^self == *self && (*self).seq() == Seq::new()
    })]
    #[ensures(match result {
        Some(val) => Seq::singleton(^val).concat((^self).fin_seq()) == (*self).fin_seq(),
        None => ^self == *self
    })]
    fn next(&mut self) -> Option<&'a mut T> {
        self.0.with_mut(IterMutInner::next)
    }
}
