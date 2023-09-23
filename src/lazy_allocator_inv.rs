use creusot_contracts::*;
use crate::inv::*;
use crate::lazy_allocator::{LazyAllocatorData as LazyAllocatorDataInner, LazyAllocator as LazyAllocatorInner};

struct LazyAllocatorDataInv;

impl<T: ?Sized> Inv<LazyAllocatorDataInner<T>> for LazyAllocatorDataInv {
    #[predicate]
    #[open(self)]
    fn inv(t: LazyAllocatorDataInner<T>) -> bool {
        t.invariant()
    }
}

struct LazyAllocatorData<T: ?Sized>(InvS<'static, LazyAllocatorDataInner<T>, LazyAllocatorDataInv>);
impl<T: ?Sized> LazyAllocatorData<T> {

    #[ensures(result.0.inner().is_empty())]
    pub(super) fn new() -> Self {
        LazyAllocatorData(InvS::new(LazyAllocatorDataInner::new()))
    }

    // ensures no memory leaks
    pub(super) fn drop(self) {
        self.0.open().drop()
    }
}

struct LazyAllocatorInv;

impl<'a, T: ?Sized> Inv<LazyAllocatorInner<'a, T>> for LazyAllocatorInv {
    #[predicate]
    #[open(self)]
    fn inv(t: LazyAllocatorInner<'a, T>) -> bool {
        t.invariant()
    }

    #[predicate]
    #[open(self)]
    #[ensures(t.resolve() && t.invariant() ==> result)]
    fn co_inv(t: LazyAllocatorInner<'a, T>) -> bool {
        t.fin_invariant()
    }
}

pub struct LazyAllocator<'a, T: ?Sized>(InvS<'a, LazyAllocatorInner<'a, T>, LazyAllocatorInv>);

impl<'a, T: ?Sized> LazyAllocator<'a, T> {

    #[requires((*x).0.inner().is_empty())]
    fn new(x: &'a mut LazyAllocatorData<T>) -> Self {
        LazyAllocator(x.0.map_mut(
            #[requires((*x).is_empty())]
            #[ensures(result.invariant())]
            #[ensures(result.fin_invariant() ==> (^x).invariant())]
                |x| LazyAllocatorInner::new(x)))
    }

    #[ensures(*result == *memory)]
    pub fn accept_box(&mut self, memory: Box<T>) -> &'a mut T {
        self.0.with_mut(
            #[requires((*x).invariant())]
            #[ensures((^x).invariant())]
            #[ensures((^x).fin_invariant() ==> (*x).fin_invariant())]
            // #[ensures(*result == *memory)]
                |x| x.accept_box(memory)
        )
    }

    #[ensures(*result == data)]
    pub fn alloc(&mut self, data: T) -> &'a mut T
    where
        T: Sized,
    {
        self.accept_box(Box::new(data))
    }

    pub fn allocations(&self) -> usize {
        self.0.deref().allocations()
    }
}

#[requires(forall<x: LazyAllocator<'_, T>> f.precondition((x,)))]
#[ensures(exists<x: LazyAllocator<'_, T>> f.postcondition_once((x,), result))]
pub fn with_lazy_allocator<T, U, F: FnOnce(LazyAllocator<'_, T>) -> U>(f: F) -> U {
    let mut data = LazyAllocatorData::new();
    let allocator = LazyAllocator::new(&mut data);
    let res = f(allocator);
    data.drop();
    res
}
