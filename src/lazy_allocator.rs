use crate::lemmas::*;
use creusot_contracts::ghost_ptr::GhostPtrToken;
use creusot_contracts::logic::Mapping;
use creusot_contracts::util::SizedW;
use creusot_contracts::*;

type TokenM<T> = <GhostPtrToken<T> as ShallowModel>::ShallowModelTy;

#[logic]
#[ensures(s.ext_eq(match result {None => Seq::new(), Some((rest, last)) => rest.push(last)}))]
fn split_last<T>(s: Seq<T>) -> Option<(Seq<T>, T)> {
    match s.get(s.len() - 1) {
        None => None,
        Some(l) => Some((s.subsequence(0, s.len() - 1), l)),
    }
}

#[logic]
#[ensures(s.ext_eq(match result {None => Seq::new(), Some((first, rest)) => Seq::singleton(first).concat(rest)}))]
fn split_first<T>(s: Seq<T>) -> Option<(T, Seq<T>)> {
    match s.get(0) {
        None => None,
        Some(f) => Some((f, s.subsequence(1, s.len()))),
    }
}

pub(super) struct LazyAllocatorData<T: ?Sized> {
    token: GhostPtrToken<T>,
    allocated: Vec<*const T>,
}

#[predicate]
#[variant(allocated.len())]
fn alloc_invariant<T: ?Sized>(token: TokenM<T>, allocated: Seq<*const T>) -> bool {
    match split_first(allocated) {
        None => token == TokenM::empty(),
        Some((first, rest)) => token.contains(first) && alloc_invariant(token.remove(first), rest),
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
        pearlite! {self.token@ == TokenM::empty() && self.allocated@.ext_eq(Seq::new())}
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

pub struct LazyAllocator<'a, T: ?Sized> {
    token: &'a mut GhostPtrToken<T>,
    allocated: &'a mut Vec<*const T>,
}

#[trusted] // This is just the structural resolve Creusot should have inferred
impl<'a, T: ?Sized> Resolve for LazyAllocator<'a, T> {
    #[open(self)]
    #[predicate]
    fn resolve(self) -> bool {
        Resolve::resolve(self.token) && Resolve::resolve(self.allocated)
    }
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
    pub fn fin_invariant(self) -> bool {
        subseq_full::<*const T>;
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
        subseq_singleton::<*const T>;
        concat_subseq::<*const T>;
        subseq_subseq::<*const T>;
        map_set_commute::<*const T, Option<SizedW<T>>>;
        map_set_id::<*const T, Option<SizedW<T>>>;
        map_set_overwrite::<*const T, Option<SizedW<T>>>;
        let old_self = gh!(*self);
        let ptr = self.token.ptr_from_box(memory);
        self.allocated.push(ptr);
        let res = self.token.take_mut(ptr);
        proof_assert!((^old_self.token)@.remove(ptr).view() == (^self.token)@.view());
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
