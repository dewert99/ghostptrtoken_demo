use crate::lemmas::*;
use ::std::ptr;
use creusot_contracts::__stubs::fin;
use creusot_contracts::ghost_ptr::{GhostPtrExt, GhostPtrToken};
use creusot_contracts::logic::FMap;
use creusot_contracts::*;

struct Node<T> {
    data: T,
    next: *const Node<T>,
}

/// Is there a linked list segment from ptr to other
#[predicate]
#[variant(token.len())]
#[ensures(ptr == other ==> result == (token == FMap::empty()))]
#[ensures(result && ptr != other ==> token.contains(ptr))]
fn lseg<T>(
    ptr: *const Node<T>,
    other: *const Node<T>,
    token: FMap<*const Node<T>, Node<T>>,
) -> bool {
    if ptr == other {
        token == FMap::empty()
    } else {
        match token.get(ptr) {
            None => false,
            Some(node) => lseg(node.next, other, token.remove(ptr)),
        }
    }
}

#[ghost]
#[variant(token.len())]
#[ensures(ptr == other ==> result == Seq::EMPTY)]
fn lseg_seq<T>(
    ptr: *const Node<T>,
    other: *const Node<T>,
    token: FMap<*const Node<T>, Node<T>>,
) -> Seq<T> {
    if ptr == other {
        Seq::EMPTY
    } else {
        match token.get(ptr) {
            None => Seq::EMPTY,
            Some(node) => {
                Seq::singleton(node.data).concat(lseg_seq(node.next, other, token.remove(ptr)))
            }
        }
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

impl<T> LinkedList<T> {
    #[predicate]
    #[open(self)]
    pub fn invariant(self) -> bool {
        if self.head == <*const Node<T>>::null_logic() {
            self.token.shallow_model() == FMap::empty()
        } else {
            lseg(
                self.head,
                self.tail,
                self.token.shallow_model().remove(self.tail),
            ) && (match self.token.shallow_model().get(self.tail) {
                None => false,
                Some(node) => node.next == <*const Node<T>>::null_logic(),
            })
        }
    }

    #[ghost]
    #[open(self)]
    pub fn model(self) -> Seq<T> {
        if self.head == <*const Node<T>>::null_logic() {
            Seq::EMPTY
        } else {
            lseg_seq(
                self.head,
                self.tail,
                self.token.shallow_model().remove(self.tail),
            )
            .concat(Seq::singleton(
                self.token.shallow_model().lookup(self.tail).data,
            ))
        }
    }

    #[ensures(result.invariant())]
    #[ensures(result.model() == Seq::EMPTY)]
    pub fn new() -> Self {
        LinkedList {
            head: ptr::null(),
            tail: ptr::null(),
            token: GhostPtrToken::new(),
        }
    }

    #[ensures(result.invariant())]
    #[ensures(result.model().ext_eq(Seq::singleton(v)))]
    pub fn singleton(v: T) -> Self {
        map_set_commute::<*const Node<T>, Option<Node<T>>>;
        let mut token = GhostPtrToken::new();
        let node = Node {
            data: v,
            next: ptr::null(),
        };
        let ptr = token.ptr_from_box(Box::new(node));
        LinkedList {
            head: ptr,
            tail: ptr,
            token,
        }
    }

    #[requires((*self).invariant())]
    #[ensures((^self).invariant())]
    #[ensures(match result {
        Some(val) => Seq::singleton(val).concat((^self).model()).ext_eq((*self).model()),
        None => ^self == *self && (*self).model() == Seq::EMPTY
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
    #[ensures((^self).model().ext_eq((*self).model().concat(other.model())))]
    pub fn append(&mut self, other: Self) {
        if self.head.is_null() {
            *self = other
        } else if !other.head.is_null() {
            let older_self = gh!(self);
            let tail = self.token.ptr_as_mut(self.tail);
            tail.next = other.head;
            let old_self = gh!(self);
            let old_other = gh!(other);
            let tok1 = gh!(old_self.token.shallow_model().remove(self.tail));
            let tok2 = gh!(old_other
                .token
                .shallow_model()
                .remove(old_other.tail)
                .insert(self.tail, self.token.shallow_model().lookup(self.tail)));
            proof_assert!(tok1.view() == older_self.token.shallow_model().remove(self.tail).view());
            self.token.merge(other.token);
            proof_assert!(old_other.token@.remove(old_other.tail).view() == tok2.remove(self.tail).view());
            proof_assert!(lseg(self.tail, old_other.tail, *tok2));
            proof_assert!(tok1.disjoint(*tok2));
            proof_assert!(lseg_trans(
                self.head,
                self.tail,
                old_other.tail,
                *tok1,
                *tok2
            ));
            proof_assert!(lseg_seq(older_self.tail, old_other.tail, *tok2) ==
                Seq::singleton(older_self.token@.lookup(older_self.tail).data).concat(lseg_seq(old_other.head, old_other.tail, old_other.token@.remove(old_other.tail))));
            proof_assert!(tok1.union(*tok2).ext_eq(self.token@.remove(old_other.tail)));
            self.tail = other.tail;
            proof_assert!(
               lseg_seq(self.head, self.tail, self.token@.remove(self.tail)).ext_eq(
               lseg_seq(old_self.head, old_self.tail, old_self.token@.remove(old_self.tail)).concat(
                        Seq::singleton(old_self.token@.lookup(old_self.tail).data)).concat(lseg_seq(old_other.head, old_other.tail, old_other.token@.remove(old_other.tail)))));
            proof_assert!(self
                .model()
                .ext_eq(old_self.model().concat(old_other.model())));
        }
    }

    #[requires((*self).invariant())]
    #[ensures((^self).invariant())]
    #[ensures((^self).model().ext_eq((*self).model().concat(Seq::singleton(val))))]
    pub fn enqueue(&mut self, val: T) {
        self.append(Self::singleton(val))
    }

    #[requires((*self).invariant())]
    #[ensures(result.invariant())]
    #[ensures(result.model() == self.model())]
    pub fn iter(&self) -> Iter<'_, T> {
        Iter {
            curr: self.head,
            token: &self.token,
            tail: gh!(self.tail),
        }
    }

    #[requires((*self).invariant())]
    #[ensures(result.invariant())]
    #[ensures(result.model() == (*self).model())]
    #[ensures(result.fin_invariant() ==> (^self).invariant())]
    #[ensures((^self).model() == result.fin_model())]
    pub fn iter_mut(&mut self) -> IterMut<'_, T> {
        IterMut {
            curr: self.head,
            token: &mut self.token,
            tail: gh!(self.tail),
        }
    }
}

pub struct Iter<'a, T> {
    curr: *const Node<T>,
    token: &'a GhostPtrToken<Node<T>>,
    tail: Ghost<*const Node<T>>,
}

impl<'a, T> Iter<'a, T> {
    #[predicate]
    #[open(self)]
    pub fn invariant(self) -> bool {
        LinkedList {
            head: self.curr,
            tail: *self.tail,
            token: *self.token,
        }
        .invariant()
    }

    #[ghost]
    #[open(self)]
    pub fn model(self) -> Seq<T> {
        LinkedList {
            head: self.curr,
            tail: *self.tail,
            token: *self.token,
        }
        .model()
    }

    #[requires((*self).invariant())]
    #[ensures((^self).invariant())]
    #[ensures(match result {
        Some(val) => Seq::singleton(*val).concat((^self).model()).ext_eq((*self).model()),
        None => ^self == *self && (*self).model() == Seq::EMPTY
    })]
    pub fn next(&mut self) -> Option<&'a T> {
        map_set_commute::<*const Node<T>, Option<Node<T>>>;
        if self.curr.is_null() {
            None
        } else {
            let node = self.token.ptr_as_ref(self.curr);
            let g = gh!(self.token.shallow_model().remove(self.curr));
            self.curr = node.next;
            self.token = self.token.shrink_token_ref(g);
            Some(&node.data)
        }
    }
}

pub struct IterMut<'a, T> {
    curr: *const Node<T>,
    token: &'a mut GhostPtrToken<Node<T>>,
    tail: Ghost<*const Node<T>>,
}

// Safety this is just the structural resolve
#[trusted]
impl<'a, T> Resolve for IterMut<'a, T> {
    #[predicate]
    #[open(self)]
    fn resolve(self) -> bool {
        self.curr.resolve() && self.token.resolve() && self.tail.resolve()
    }
}

impl<'a, T> IterMut<'a, T> {
    #[predicate]
    #[open(self)]
    pub fn invariant(self) -> bool {
        LinkedList {
            head: self.curr,
            tail: *self.tail,
            token: *self.token,
        }
        .invariant()
    }

    #[predicate]
    #[open(self)]
    #[ensures(self.resolve() && self.invariant() ==> result)]
    pub fn fin_invariant(self) -> bool {
        LinkedList {
            head: self.curr,
            tail: *self.tail,
            token: *fin(self.token),
        }
        .invariant()
    }

    #[ghost]
    #[open(self)]
    pub fn model(self) -> Seq<T> {
        LinkedList {
            head: self.curr,
            tail: *self.tail,
            token: *self.token,
        }
        .model()
    }

    #[logic]
    #[open(self)]
    #[ensures(self.resolve() ==> result == self.model())]
    pub fn fin_model(self) -> Seq<T> {
        LinkedList {
            head: self.curr,
            tail: *self.tail,
            token: *fin(self.token),
        }
        .model()
    }

    #[requires((*self).invariant())]
    #[ensures((^self).invariant())]
    #[ensures(match result {
        Some(val) => Seq::singleton(*val).concat((^self).model()) == (*self).model(),
        None => ^self == *self && (*self).model() == Seq::EMPTY
    })]
    #[ensures((^self).fin_invariant() ==> (*self).fin_invariant())]
    #[ensures(match result {
        Some(val) => Seq::singleton(^val).concat((^self).fin_model()) == (*self).fin_model(),
        None => ^self == *self
    })]
    pub fn next(&mut self) -> Option<&'a mut T> {
        map_set_commute::<*const Node<T>, Option<Node<T>>>;
        map_set_id::<*const Node<T>, Option<Node<T>>>;
        let old_self = gh!(*self);
        if self.curr.is_null() {
            None
        } else {
            let node = self.token.take_mut(self.curr);
            self.curr = node.next;
            let res = &mut node.data;
            proof_assert!(node.resolve() ==> self.fin_invariant() ==> old_self.fin_invariant());
            proof_assert!(node.resolve() ==> (^self.token)@.remove(*old_self.tail).view() == (^old_self.token)@.remove(*old_self.tail).remove(old_self.curr).view());
            proof_assert!(node.resolve() ==> Seq::singleton(^res).concat(self.fin_model()).ext_eq(old_self.fin_model()));
            proof_assert!(node.resolve() ==> Seq::singleton(*res).concat(self.model()).ext_eq(old_self.model()));
            Some(res)
        }
    }
}
