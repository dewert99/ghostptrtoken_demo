use ::std::{mem, iter};
use creusot_contracts::*;
use iter::Iterator;
use ::std::default::Default;
use ::std::alloc::Allocator;
use creusot_contracts::Iterator as _;
use creusot_contracts::std::default::Default as CDefault;
use super::lazy_allocator::LazyAllocator;

const BASE: usize = 8;

struct BumpAllocator<'a, T>{
    allocator: LazyAllocator<'a, [T]>,
    current: &'a mut [T]
}

#[trusted] // This is just the structural resolve Creusot should have inferred
impl<'a, T> Resolve for BumpAllocator<'a, T> {
    #[open(self)]
    #[predicate]
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
    #[predicate]
    pub fn invariant(self) -> bool {
        self.allocator.invariant()
    }

    #[open(self)]
    #[predicate]
    #[ensures(self.resolve() && self.invariant() ==> result)]
    pub fn coinvariant(self) -> bool {
        self.allocator.coinvariant()
    }

    #[requires(allocator.invariant())]
    #[ensures(result.invariant())]
    #[ensures(result.coinvariant() ==> allocator.coinvariant())]
    pub fn new(allocator: LazyAllocator<'a, [T]>) -> Self {
        BumpAllocator{allocator, current: Default::default()}
    }

    #[requires((*self).invariant())]
    #[ensures((^self).invariant())]
    #[ensures((^self).coinvariant() ==> (^self).coinvariant())]
    #[ensures(result@.len() == len@)]
    pub fn alloc_default_slice(&mut self, len: usize) -> &'a mut [T] {
        let mut current = mem::replace(&mut self.current , Default::default());
        if current.len() < len {
            let new_size = len.max(shl(BASE, self.allocator.allocations()));
            let memory: Vec<_> = iter::repeat(()).map_inv(|(), _| T::default()).take(new_size).collect();
            current = self.allocator.accept_box(memory.into_boxed_slice());
        }
        let (res, rest) = current.split_at_mut(len);
        self.current = rest;
        return res
    }

    #[requires((*self).invariant())]
    #[ensures((^self).invariant())]
    #[ensures((^self).coinvariant() ==> (^self).coinvariant())]
    pub fn alloc_default(&mut self) -> &'a mut T {
        match self.alloc_default_slice(1).split_first_mut() {
            Some((x, _)) => x,
            _ => unreachable!()
        }
    }

    #[requires((*self).invariant())]
    #[ensures((^self).invariant())]
    #[ensures((^self).coinvariant() ==> (^self).coinvariant())]
    #[ensures(*result == val)]
    pub fn alloc(&mut self, val: T) -> &'a mut T {
        let res = self.alloc_default();
        *res = val;
        res
    }
}