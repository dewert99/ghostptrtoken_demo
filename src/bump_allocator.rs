use super::lazy_allocator::LazyAllocator;
use ::std::alloc::Allocator;
use ::std::default::Default;
use ::std::{iter, mem};
use creusot_contracts::std::default::Default as CDefault;
use creusot_contracts::util::unwrap;
use creusot_contracts::Iterator as _;
use creusot_contracts::*;
use iter::Iterator;

const BASE: usize = 8;

pub struct BumpAllocator<'a, T> {
    allocator: LazyAllocator<'a, [T]>,
    current: &'a mut [T],
}

#[trusted] // This is just the structural resolve Creusot should have inferred
impl<'a, T> Resolve for BumpAllocator<'a, T> {
    #[open(self)]
    #[predicate(prophetic)]
    fn resolve(self) -> bool {
        Resolve::resolve(self.allocator) && Resolve::resolve(self.current)
    }
}

#[trusted] // Cruesot doesn't support shl and I also can avoid overflow
fn shl(x: usize, y: usize) -> usize {
    x << y
}

extern_spec! {
    mod std {
        mod vec {
            impl<T, A: Allocator> Vec<T, A> {
                #[ensures(result@ == self@)]
                fn into_boxed_slice(self) -> Box<[T], A>;
            }
        }
    }
}

impl<'a, T: CDefault> BumpAllocator<'a, T> {
    #[open(self)]
    #[predicate(prophetic)]
    pub fn invariant(self) -> bool {
        self.allocator.invariant()
            && pearlite! {forall<i: Int> 0 <= i && i < (*self.current)@.len() ==> (*self.current)@[i].is_default()}
    }

    #[open(self)]
    #[predicate(prophetic)]
    #[ensures(self.resolve() && self.invariant() ==> result)]
    pub fn fin_invariant(self) -> bool {
        self.allocator.fin_invariant()
    }

    #[requires(allocator.invariant())]
    #[ensures(result.invariant())]
    #[ensures(result.fin_invariant() ==> allocator.fin_invariant())]
    pub fn new(allocator: LazyAllocator<'a, [T]>) -> Self {
        BumpAllocator {
            allocator,
            current: Default::default(),
        }
    }

    #[requires((*self).invariant())]
    #[ensures((^self).invariant())]
    #[ensures((^self).fin_invariant() ==> (^self).fin_invariant())]
    #[ensures(result@.len() == len@)]
    #[ensures(forall<i: Int> 0 <= i && i < len@ ==> (*result)@[i].is_default())]
    pub fn alloc_default_slice(&mut self, len: usize) -> &'a mut [T] {
        let mut current = mem::replace(&mut self.current, Default::default());
        if current.len() < len {
            let new_size = len.max(shl(BASE, self.allocator.allocations()));
            let memory: Vec<_> = iter::repeat(())
                .map_inv(
                    #[ensures(result.is_default())]
                    |(), _| T::default(),
                )
                .take(new_size)
                .collect();
            current = self.allocator.accept_box(memory.into_boxed_slice());
        }
        let (res, rest) = current.split_at_mut(len);
        self.current = rest;
        return res;
    }

    #[requires((*self).invariant())]
    #[ensures((^self).invariant())]
    #[ensures((^self).fin_invariant() ==> (^self).fin_invariant())]
    #[ensures((*result).is_default())]
    pub fn alloc_default(&mut self) -> &'a mut T {
        &mut self.alloc_default_slice(1)[0]
    }

    #[requires((*self).invariant())]
    #[ensures((^self).invariant())]
    #[ensures((^self).fin_invariant() ==> (^self).fin_invariant())]
    #[ensures(*result == val)]
    pub fn alloc(&mut self, val: T) -> &'a mut T {
        let res = self.alloc_default();
        *res = val;
        res
    }
}

// TODO replace once Creusot gets MaybeUninit support
type MaybeUninit<T> = Option<T>;

struct BumpBox<'a, T> {
    data: &'a mut MaybeUninit<T>,
}

impl<'a, T> BumpBox<'a, T> {
    #[open(self)]
    #[predicate]
    pub fn invariant(self) -> bool {
        *self.data != None
    }

    #[open(self)]
    #[logic]
    pub fn data(self) -> T {
        unwrap(*self.data)
    }

    #[requires(self.invariant())]
    pub fn drop(self) {
        let x = self.data;
        drop(x.take().unwrap())
    }

    #[requires((*self).invariant())]
    #[ensures(*result == self.data())]
    fn deref(&self) -> &T {
        self.data.as_ref().unwrap()
    }

    #[requires((*self).invariant())]
    #[requires((^self).invariant())]
    #[ensures(^result == (^self).data())]
    #[ensures(*result == (*self).data())]
    fn deref_mut(&mut self) -> &mut T {
        self.data.as_mut().unwrap()
    }
}

impl<'a, T> BumpAllocator<'a, MaybeUninit<T>> {
    #[requires((*self).invariant())]
    #[ensures((^self).invariant())]
    #[ensures((^self).fin_invariant() ==> (^self).fin_invariant())]
    #[ensures(result.invariant())]
    #[ensures(result.data() == t)]
    fn alloc_box(&mut self, t: T) -> BumpBox<'a, T> {
        BumpBox {
            data: self.alloc(Some(t)),
        }
    }
}
