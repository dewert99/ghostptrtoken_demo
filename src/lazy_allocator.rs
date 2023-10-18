use crate::lemmas::*;
use creusot_contracts::ghost_ptr::GhostPtrToken;
use creusot_contracts::logic::Mapping;
use creusot_contracts::util::SizedW;
use creusot_contracts::*;

type TokenM<T> = <GhostPtrToken<T> as ShallowModel>::ShallowModelTy;

trait SeqExt {
    #[ghost]
    #[why3::attr = "inline:trivial"]
    fn tail2(self) -> Self;
}

impl<T> SeqExt for Seq<T> {
    #[ghost]
    #[open]
    #[why3::attr = "inline:trivial"]
    fn tail2(self) -> Self {
        self.subsequence(1, self.len())
    }
}

pub(super) struct LazyAllocatorData<T: ?Sized> {
    token: GhostPtrToken<T>,
    allocated: Vec<*const T>,
}

#[predicate]
#[variant(allocated.len())]
fn alloc_invariant<T: ?Sized>(token: TokenM<T>, allocated: Seq<*const T>) -> bool {
    match allocated.get(0) {
        None => token == TokenM::empty(),
        Some(head) => {
            token.contains(head) && alloc_invariant(token.remove(head), allocated.tail2())
        }
    }
}

impl<T: ?Sized> LazyAllocatorData<T> {
    #[predicate]
    #[open(self)]
    pub(super) fn invariant(self) -> bool {
        pearlite! {alloc_invariant(self.token@, self.allocated@)}
    }

    #[predicate]
    #[open(self)]
    pub(super) fn is_empty(self) -> bool {
        pearlite! {self.token@ == TokenM::empty() && self.allocated@.ext_eq(Seq::EMPTY)}
    }

    #[ensures(result.is_empty())]
    #[ensures(result.invariant())]
    pub(super) fn new() -> Self {
        LazyAllocatorData {
            token: GhostPtrToken::new(),
            allocated: Vec::new(),
        }
    }

    #[requires(self.invariant())]
    // ensures no memory leaks
    pub(super) fn drop(self) {
        subseq_concat::<*const T>;
        let mut token = self.token;
        #[invariant(alloc_invariant(token@, iter@))]
        for ptr in self.allocated {
            let _ = token.ptr_to_box(ptr);
        }
        token.drop();
    }
}

#[derive(Resolve)]
pub struct LazyAllocator<'a, T: ?Sized> {
    token: &'a mut GhostPtrToken<T>,
    allocated: &'a mut Vec<*const T>,
}

impl<'a, T: ?Sized> LazyAllocator<'a, T> {
    #[open(self)]
    #[predicate]
    pub fn invariant(self) -> bool {
        pearlite! {self.token@.view() == Mapping::cst(None)}
    }

    #[logic]
    #[why3::attr = "inline:trivial"]
    fn will_add_later(self) -> Seq<*const T> {
        pearlite! {(^self.allocated)@.subsequence((*self.allocated)@.len(), (^self.allocated)@.len())}
    }

    #[open(self)]
    #[predicate]
    #[ensures(self.resolve() && self.invariant() ==> result)]
    #[why3::attr = "inline:trivial"]
    pub fn fin_invariant(self) -> bool {
        pearlite! {(^self.allocated)@.len() >= (*self.allocated)@.len() &&
        (^self.allocated)@.subsequence(0, (*self.allocated)@.len()).ext_eq((*self.allocated)@) &&
        alloc_invariant((^self.token)@, self.will_add_later())}
    }

    #[requires((*x).is_empty())]
    #[ensures(result.invariant())]
    #[ensures(result.fin_invariant() ==> (^x).invariant())]
    pub(super) fn new(x: &'a mut LazyAllocatorData<T>) -> Self {
        subseq_full::<*const T>;
        LazyAllocator {
            token: &mut x.token,
            allocated: &mut x.allocated,
        }
    }

    #[requires((*self).invariant())]
    #[ensures((^self).invariant())]
    #[ensures((^self).fin_invariant() ==> (*self).fin_invariant())]
    #[ensures(*result == *memory)]
    pub fn accept_box(&mut self, memory: Box<T>) -> &'a mut T {
        let old_self = gh!(*self);
        let ptr = self.token.ptr_from_box(memory);
        self.allocated.push(ptr);
        let res = self.token.take_mut(ptr);
        proof_assert!((^old_self.token)@.remove(ptr).ext_eq((^self.token)@));
        proof_assert!(^self.allocated == ^old_self.allocated);
        proof_assert!((*self.allocated)@.len() ==(*old_self.allocated)@.len() + 1);
        proof_assert!((^self.allocated)@.len() >= (*self.allocated)@.len() ==> old_self.will_add_later().tail2().ext_eq(self.will_add_later()));
        res
    }

    pub fn allocations(&self) -> usize {
        self.allocated.len()
    }
}

#[requires(forall<x: LazyAllocator<'_, T>> x.invariant() ==> f.precondition((x,)) && (forall<u: U> f.postcondition_once((x,), u) ==> x.fin_invariant()))]
#[ensures(exists<x: LazyAllocator<'_, T>> x.invariant() && f.postcondition_once((x,), result))]
pub fn with_lazy_allocator<T, U, F>(f: F) -> U
where
    F: FnOnce(LazyAllocator<'_, T>) -> U,
{
    let mut data = LazyAllocatorData::new();
    let allocator = LazyAllocator::new(&mut data);
    let res = f(allocator);
    data.drop();
    res
}
