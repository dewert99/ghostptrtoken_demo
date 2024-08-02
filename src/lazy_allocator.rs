use creusot_contracts::ghost_ptr::*;
use creusot_contracts::logic::Mapping;
use creusot_contracts::*;

type TokenM<T> = <GhostPtrToken<T> as ShallowModel>::ShallowModelTy;

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
            token.contains(head) && alloc_invariant(token.remove(head), allocated.tail())
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
    token: GhostPtrTokenMut<'a, T>,
    allocated: &'a mut Vec<*const T>,
}

impl<'a, T: ?Sized> LazyAllocator<'a, T> {
    #[open(self)]
    #[predicate]
    pub fn invariant(self) -> bool {
        pearlite! {self.token.cur().view() == Mapping::cst(None)}
    }

    #[logic(prophetic)]
    #[why3::attr = "inline:trivial"]
    fn will_add_later(self) -> Seq<*const T> {
        pearlite! {(^self.allocated)@.subsequence((*self.allocated)@.len(), (^self.allocated)@.len())}
    }

    #[open(self)]
    #[predicate(prophetic)]
    #[ensures(self.resolve() && self.invariant() ==> result)]
    pub fn fin_invariant(self) -> bool {
        pearlite! {(^self.allocated)@.len() >= (*self.allocated)@.len() &&
        (forall<i: Int> 0 <= i && i < (*self.allocated)@.len() ==> (^self.allocated)@[i] == (*self.allocated)@[i]) &&
        alloc_invariant(self.token.fin(), self.will_add_later())}
    }

    #[requires((*x).is_empty())]
    #[ensures(result.invariant())]
    #[ensures((^x).allocated@.ext_eq(result.will_add_later()))]
    #[ensures(result.fin_invariant() ==> (^x).invariant())]
    pub(super) fn new(x: &'a mut LazyAllocatorData<T>) -> Self {
        LazyAllocator {
            token: x.token.borrow_mut(),
            allocated: &mut x.allocated,
        }
    }

    #[requires((*self).invariant())]
    #[ensures((^self).invariant())]
    #[ensures((^self).fin_invariant() ==> (*self).fin_invariant())]
    #[ensures(*result == *memory)]
    pub fn accept_box(&mut self, memory: Box<T>) -> &'a mut T {
        let old_self = snapshot!(*self);
        let ptr = self.token.ptr_from_box(memory);
        self.allocated.push(ptr);
        let res = self.token.take_mut(ptr);
        proof_assert!(old_self.token.fin().remove(ptr).ext_eq(self.token.fin()));
        proof_assert!(^self.allocated == ^old_self.allocated);
        proof_assert!((*self.allocated)@.len() ==(*old_self.allocated)@.len() + 1);
        proof_assert!((^self.allocated)@.len() >= (*self.allocated)@.len() ==> old_self.will_add_later().tail().ext_eq(self.will_add_later()));
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
