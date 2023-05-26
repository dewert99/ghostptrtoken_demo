use creusot_contracts::__stubs::fin;
use ::std::ptr;
use creusot_contracts::ghost_ptr::{GhostPtrExt, GhostPtrToken};
use creusot_contracts::logic::{FMap, Mapping};
use creusot_contracts::*;

pub struct Node<T> {
    pub data: T,
    pub next: *const Node<T>,
}

#[law]
#[ensures(x.set(k, v1).set(k, v2) == x.set(k, v2))]
fn map_set_overwrite<K, V>(x: Mapping<K, V>, k: K, v1: V, v2: V) {}

#[law]
#[requires(k1 != k2)]
#[ensures(x.set(k1, v1).set(k2, v2) == x.set(k2, v2).set(k1, v1))]
fn map_set_commute<K, V>(x: Mapping<K, V>, k1: K, k2: K, v1: V, v2: V) {}

#[law]
#[requires(x.get(k) == v)]
#[ensures(x.set(k, v) == x)]
fn map_set_id<K, V>(x: Mapping<K, V>, k: K, v: V) {}

#[law]
#[requires(x1.disjoint(x2))]
#[ensures(x1.union(x2) == x2.union(x1))]
fn union_commute<K, V>(x1: FMap<K, V>, x2: FMap<K, V>) {}

#[law]
#[requires(x1.disjoint(x2))]
#[requires(x1.contains(k))]
#[ensures(x1.union(x2).remove(k).ext_eq(x1.remove(k).union(x2)))]
fn union_remove<K, V>(x1: FMap<K, V>, x2: FMap<K, V>, k: K) {}

#[law]
#[requires(x1.insert(k,v).disjoint(x2))]
#[ensures(x1.union(x2).insert(k, v).ext_eq(x1.insert(k, v).union(x2)))]
fn union_insert<K, V>(x1: FMap<K, V>, x2: FMap<K, V>, k: K, v: V) {}


#[law]
#[ensures(FMap::empty().union(x).ext_eq(x))]
fn union_empty<K, V>(x: FMap<K, V>) {}



/// Is there a linked list segment from ptr to other
#[predicate]
#[variant(token.len())]
#[ensures(ptr == other ==> result == (token == FMap::empty()))]
#[ensures(result && ptr != other ==> token.contains(ptr))]
fn lseg<T>(ptr: *const Node<T>, other: *const Node<T>, token: FMap<*const Node<T>, Node<T>>) -> bool {
    if ptr == other {
        token == FMap::empty()
    } else {
        match token.get(ptr) {
            None => false,
            Some(node) => lseg(node.next, other, token.remove(ptr)),
        }
    }
}

#[logic]
#[variant(token.len())]
#[requires(lseg(ptr, other, token))]
#[ensures(ptr == other ==> result == Seq::new())]
fn lseg_seq<T>(ptr: *const Node<T>, other: *const Node<T>, token: FMap<*const Node<T>, Node<T>>) -> Seq<T> {
    if ptr == other {
        Seq::new()
    } else {
        let node = token.lookup(ptr);
        Seq::singleton(node.data).concat(lseg_seq(node.next, other, token.remove(ptr)))
    }
}

/// Lemma for concatenating 2 segments
#[logic]
#[variant(token12.len())]
#[requires(token12.disjoint(token23))]
#[requires(lseg(ptr1, ptr2, token12))]
#[requires(lseg(ptr2, ptr3, token23))]
#[requires(!token12.contains(ptr3))]
#[ensures(result)]
#[ensures(lseg(ptr1, ptr3, token12.union(token23)))]
#[ensures(lseg_seq(ptr1, ptr3, token12.union(token23)).ext_eq(lseg_seq(ptr1, ptr2, token12).concat(lseg_seq(ptr2, ptr3, token23))))]
fn lseg_trans<T>(
    ptr1: *const Node<T>,
    ptr2: *const Node<T>,
    ptr3: *const Node<T>,
    token12: FMap<*const Node<T>, Node<T>>,
    token23: FMap<*const Node<T>, Node<T>>,
) -> bool {
    union_remove::<*const Node<T>, Node<T>>;
    union_empty::<*const Node<T>, Node<T>>;
    if ptr1 != ptr2 {
        let next = token12.lookup(ptr1).next;
        lseg_trans(next, ptr2, ptr3, token12.remove(ptr1), token23)
    } else {
        true
    }
}

pub struct LinkedList<T> {
    head: *const Node<T>,
    tail: *const Node<T>,
    token: GhostPtrToken<Node<T>>,
}

impl<T> ShallowModel for LinkedList<T> {
    type ShallowModelTy = Seq<T>;

    #[logic]
    fn shallow_model(self) -> Self::ShallowModelTy {
        if self.head == <*const Node<T>>::null_logic() {
            Seq::new()
        } else {
            lseg_seq(self.head, self.tail, self.token.shallow_model().remove(self.tail))
                .concat(Seq::singleton(self.token.shallow_model().lookup(self.tail).data))
        }
    }
}

impl<T> LinkedList<T> {
    #[predicate]
    pub fn invariant(self) -> bool {
        if self.head == <*const Node<T>>::null_logic() {
            self.token.shallow_model() == FMap::empty()
        } else {
            lseg(self.head, self.tail, self.token.shallow_model().remove(self.tail))
                && (match self.token.shallow_model().get(self.tail) {
                None => false,
                Some(node) => node.next == <*const Node<T>>::null_logic()
            })
        }
    }

    #[ensures(result.invariant())]
    #[ensures(result@ == Seq::new())]
    pub fn new() -> Self {
        LinkedList {
            head: ptr::null(),
            tail: ptr::null(),
            token: GhostPtrToken::new(),
        }
    }

    #[ensures(result.invariant())]
    #[ensures(result@.ext_eq(Seq::singleton(v)))]
    pub fn singleton(v: T) -> Self {
        map_set_commute::<*const Node<T>, Option<Node<T>>>;
        let mut token = GhostPtrToken::new();
        let node = Box::new(Node{data:v, next: ptr::null()});
        let ptr = token.ptr_from_box(node);
        LinkedList {
            head: ptr,
            tail: ptr,
            token
        }
    }

    #[requires((*self).invariant())]
    #[ensures((^self).invariant())]
    #[ensures(match result {
        Some(val) => Seq::singleton(val).concat((^self)@).ext_eq((*self)@),
        None => ^self == *self
    })]
    pub fn dequeue(&mut self) -> Option<T> {
        map_set_commute::<*const Node<T>, Option<Node<T>>>;
        if self.head.is_null() {
            None
        } else {
            let node = self.token.ptr_to_box(self.head);
            self.head = node.next;
            Some(node.data)
        }
    }

    #[requires((*self).invariant())]
    #[requires(other.invariant())]
    #[ensures((^self).invariant())]
    #[ensures((*self).head != <*const Node<T>>::null_logic() ==>  (*self).head == (^self).head)]
    #[ensures((*self).head != <*const Node<T>>::null_logic() ==> other.head != <*const Node<T>>::null_logic() ==>
       lseg_seq((^self).head, (^self).tail, (^self).token@.remove((^self).tail)).ext_eq(
       lseg_seq((*self).head, (*self).tail, (*self).token@.remove((*self).tail)).concat(Seq::singleton((*self).token@.lookup((*self).tail).data)).concat(lseg_seq(other.head, other.tail, other.token@.remove(other.tail)))))]
    #[ensures((*self).head != <*const Node<T>>::null_logic() ==> other.head != <*const Node<T>>::null_logic() ==> (^self)@.ext_eq((*self)@.concat(other@)))]
    #[ensures((^self)@.ext_eq((*self)@.concat(other@)))]
    pub fn append(&mut self, other: Self) {
        map_set_commute::<*const Node<T>, Option<Node<T>>>;
        map_set_overwrite::<*const Node<T>, Option<Node<T>>>;
        map_set_id::<*const Node<T>, Option<Node<T>>>;
        union_remove::<*const Node<T>, Node<T>>;
        union_empty::<*const Node<T>, Node<T>>;
        union_commute::<*const Node<T>, Node<T>>;
        union_insert::<*const Node<T>, Node<T>>;
        if self.head.is_null() {
            *self = other
        } else if !other.head.is_null() {
            let older_self = ghost!(self);
            let tail = self.token.ptr_as_mut(self.tail);
            tail.next = other.head;
            let old_self = ghost!(self);
            let old_other = ghost!(other);
            let tok1 = ghost!(old_self.token.shallow_model().remove(self.tail));
            let tok2 = ghost!(old_other.token.shallow_model().remove(old_other.tail).insert(self.tail, self.token.shallow_model().lookup(self.tail)));
            proof_assert!(*tok1 == older_self.token.shallow_model().remove(self.tail));
            self.token.merge(other.token);
            proof_assert!(lseg(self.tail, old_other.tail, *tok2));
            proof_assert!(tok1.disjoint(*tok2));
            proof_assert!(lseg_trans(self.head, self.tail, old_other.tail, *tok1, *tok2));
            proof_assert!(lseg_seq(older_self.tail, old_other.tail, *tok2) ==
                Seq::singleton(older_self.token@.lookup(older_self.tail).data).concat(lseg_seq(old_other.head, old_other.tail, old_other.token@.remove(old_other.tail))));
            proof_assert!(tok1.union(*tok2).ext_eq(self.token@.remove(old_other.tail)));
            self.tail = other.tail;
        }
    }

    #[requires((*self).invariant())]
    #[ensures((^self).invariant())]
    #[ensures((^self)@.ext_eq((*self)@.concat(Seq::singleton(val))))]
    fn enqueue(&mut self, val: T) {
        self.append(Self::singleton(val))
    }

    #[requires((*self).invariant())]
    #[ensures(result.invariant())]
    #[ensures(result@ == self@)]
    pub fn iter(&self) -> Iter<'_, T> {
        Iter{curr: self.head, token: &self.token, tail: ghost!(self.tail)}
    }

    #[requires((*self).invariant())]
    #[ensures(result.invariant())]
    #[ensures(result.seq() == (*self)@)]
    #[ensures(result.fin_invariant() ==> (^self).invariant())]
    #[ensures(result.fin_invariant() ==> (^self)@ == result.fin_seq())]
    pub fn iter_mut(&mut self) -> IterMut<'_, T> {
        IterMut{curr: self.head, token: &mut self.token, tail: ghost!(self.tail)}
    }
}

impl<'a, T> ShallowModel for Iter<'a, T> {
    type ShallowModelTy = Seq<T>;

    #[logic]
    fn shallow_model(self) -> Self::ShallowModelTy {
        LinkedList{head: self.curr, tail: *self.tail, token: *self.token}.shallow_model()
    }
}

pub struct Iter<'a, T> {
    curr: *const Node<T>,
    token: &'a GhostPtrToken<Node<T>>,
    tail: Ghost<*const Node<T>>,
}

impl<'a, T> Iter<'a, T> {

    #[predicate]
    pub fn invariant(self) -> bool {
        LinkedList{head: self.curr, tail: *self.tail, token: *self.token}.invariant()
    }

    #[requires((*self).invariant())]
    #[ensures((^self).invariant())]
    #[ensures(match result {
        Some(val) => Seq::singleton(*val).concat((^self)@).ext_eq((*self)@),
        None => ^self == *self
    })]
    fn next(&mut self) -> Option<&'a T> {
        map_set_commute::<*const Node<T>, Option<Node<T>>>;
        if self.curr.is_null() {
            None
        } else {
            let node = self.token.ptr_as_ref(self.curr);
            self.token = self.token.shrink_token_ref(ghost!((self.token.shallow_model()).remove(self.curr)));
            self.curr = node.next;
            Some(&node.data)
        }
    }
}


pub struct IterMut<'a, T> {
    curr: *const Node<T>,
    token: &'a mut GhostPtrToken<Node<T>>,
    tail: Ghost<*const Node<T>>,
}

impl<'a, T> IterMut<'a, T> {

    #[predicate]
    pub fn invariant(self) -> bool {
        LinkedList{head: self.curr, tail: *self.tail, token: *self.token}.invariant()
    }

    #[predicate]
    pub fn fin_invariant(self) -> bool {
        LinkedList{head: self.curr, tail: *self.tail, token: *fin(self.token)}.invariant() &&
            pearlite!{forall<k: *const Node<T>> self.token@.contains(k) == (^self.token)@.contains(k)}
    }

    #[logic]
    pub fn seq(self) -> Seq<T> {
        LinkedList{head: self.curr, tail: *self.tail, token: *self.token}.shallow_model()
    }

    #[logic]
    pub fn fin_seq(self) -> Seq<T> {
        LinkedList{head: self.curr, tail: *self.tail, token: *fin(self.token)}.shallow_model()
    }

    #[requires((*self).invariant())]
    #[ensures((^self).invariant())]
    #[ensures(match result {
        Some(val) => Seq::singleton(*val).concat((^self).seq()).ext_eq((*self).seq()),
        None => ^self == *self
    })]
    #[ensures((^self).fin_invariant() ==> (*self).fin_invariant())]
    #[ensures((^self).fin_invariant() ==> match result {
        Some(_) => (^(^self).token)@.remove(*self.tail) == (^(*self).token)@.remove(*self.tail).remove(self.curr),
        None => true
    })]
    #[ensures((^self).fin_invariant() ==> match result {
        Some(val) => Seq::singleton(^val).concat((^self).fin_seq()).ext_eq((*self).fin_seq()),
        None => ^self == *self
    })]
    fn next(&mut self) -> Option<&'a mut T> {
        map_set_commute::<*const Node<T>, Option<Node<T>>>;
        map_set_overwrite::<*const Node<T>, Option<Node<T>>>;
        map_set_id::<*const Node<T>, Option<Node<T>>>;
        if self.curr.is_null() {
            None
        } else {
            let node = self.token.take_mut(self.curr);
            self.curr = node.next;
            Some(&mut node.data)
        }
    }
}