use creusot_contracts::*;
use creusot_contracts::logic::Set;
use creusot_contracts::ghost_ptr::*;
use ::std::collections::HashSet;


pub struct PtrHashSet<T>(HashSet<*const T>);


impl<T> ShallowModel for PtrHashSet<T> {
    type ShallowModelTy = Set<Int>;

    #[logic]
    #[trusted]
    #[open(self)]
    fn shallow_model(self) -> Set<Int> {
        absurd
    }
}

impl<T> PtrHashSet<T> {

    #[trusted]
    #[ensures(result@ == Set::EMPTY)]
    pub fn new() -> Self {
        PtrHashSet(HashSet::new())
    }

    #[trusted]
    #[ensures((^self)@ == (*self)@.insert(x.addr_logic()))]
    #[ensures(result == !(*self)@.contains(x.addr_logic()))]
    pub fn insert(&mut self, x: *const T) -> bool {
        self.0.insert(x)
    }
}