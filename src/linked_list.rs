use crate::ghost_ptr::*;
use crate::p_map::PMap;
use creusot_contracts::*;
use creusot_contracts::__stubs::fin;
use ::std::ptr;

pub struct Node<T> {
    pub data: T,
    pub next: *const Node<T>,
}


/// Is there a linked list segment from ptr to other
#[predicate]
#[variant(token.len())]
#[ensures(ptr == other ==> result == (token == PMap::empty()))]
#[ensures(result && ptr != other ==> token.contains(ptr))]
fn lseg<T>(ptr: *const Node<T>, other: *const Node<T>, token: PMap<*const Node<T>, Node<T>>) -> bool {
    if ptr == other {
        token == PMap::empty()
    } else {
        match token.get(ptr) {
            None => false,
            Some(node) => lseg(node.next, other, token.remove(ptr)),
        }
    }
}

// /// Lemma for concatenating 2 segments
// #[logic(('_, '_, '_, '_, '_) -> '_)]
// #[variant(token12.len())]
// #[requires(token12.disjoint(token23))]
// #[requires(lseg(ptr1, ptr2, token12))]
// #[requires(lseg(ptr2, ptr3, token23))]
// #[requires(!token12.contains(ptr3))]
// #[ensures(result)]
// #[ensures(lseg(ptr1, ptr3, token12.union(token23)))]
// // TODO clean up once why3 gets a better discriminate transformation
// fn lseg_trans<T>(
//     ptr1: Ptr<T>,
//     ptr2: Ptr<T>,
//     ptr3: Ptr<T>,
//     token12: TokenM<T>,
//     token23: TokenM<T>,
// ) -> bool {
//     if ptr1 != ptr2 {
//         let Node { data, next } = token12.lookup(ptr1);
//         lseg_trans(next, ptr2, ptr3, token12.remove(ptr1), token23)
//             && token12.union(token23).remove(ptr1).ext_eq(token12.remove(ptr1).union(token23))
//     } else {
//         true
//     }
// }


pub struct LinkedList<T> {
    head: *const Node<T>,
    tail: *const Node<T>,
    token: GhostPtrToken<Node<T>>,
}

impl<T> LinkedList<T> {
    #[predicate]
    pub fn invariant(self) -> bool {
        if self.head == <*const Node<T>>::null_logic() {
            self.token.shallow_model() == PMap::empty()
        } else {
            lseg(self.head, self.tail, self.token.shallow_model().remove(self.tail))
                && (match self.token.shallow_model().get(self.tail) {
                None => false,
                Some(node) => node.next == <*const Node<T>>::null_logic()
            })
        }
    }

    #[ensures(result.invariant())]
    pub fn new() -> Self {
        LinkedList {
            head: ptr::null(),
            tail: ptr::null(),
            token: GhostPtrToken::new(),
        }
    }

    #[requires((*self).invariant())]
    #[ensures((^self).invariant())]
    pub fn push(&mut self, v: T) {
        let old_self = ghost!(self);
        let node = Box::new(Node{data:v, next: self.head});
        let ptr = ptr_from_box(node, &mut self.token);
        proof_assert!((@self.token).remove(self.tail).remove(ptr).ext_eq((@old_self.token).remove(self.tail)));
        if self.head.is_null() {
            self.tail = ptr;
            proof_assert!(self.token.shallow_model().remove(self.tail).ext_eq(PMap::empty()));
        }
        self.head = ptr;
    }

    #[requires((*self).invariant())]
    #[ensures((^self).invariant())]
    pub fn dequeue(&mut self) -> Option<T> {
        let old_self = ghost!(self);
        if self.head.is_null() {
            None
        } else {
            let node = *ptr_to_box(self.head, &mut self.token);
            proof_assert!((@self.token).remove(self.tail).ext_eq((@old_self.token).remove(self.tail).remove(old_self.head)));
            self.head = node.next;
            Some(node.data)
        }
    }

    #[requires((*self).invariant())]
    #[ensures(result.invariant())]
    #[ensures(result.fin_invariant() ==> (^self).invariant())]
    pub fn iter_mut(&mut self) -> IterMut<'_, T> {
        IterMut{curr: self.head, token: &mut self.token, tail: ghost!(self.tail)}
    }

    // #[requires((*self).invariant())]
    // #[requires(other.invariant())]
    // #[ensures(result.invariant())]
    // pub fn append(&mut self, other: Self) {
    //     if self.head.is_null() {
    //         *self = other
    //     } else {
    //         let old_self = ghost!(self);
    //         let tail = ptr_as_mut(self.tail, &mut self.token);
    //         tail.next = other.head;
    //         proof_assert!((@self.token).remove(self.tail).ext_eq((@old_self.token).remove(self.tail)));
    //         proof_assert!(lseg_trans(self.head, self.tail, other.tail, (@self.token).remove(self.tail), (@other.token).remove(self.tail)))
    //         self.token.absorb(other.token);
    //         proof_assert!((@self.token).remove(other.tail).ext_eq())
    //         self.tail = other.tail;
    //     }
    // }
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
    fn next(&mut self) -> Option<&'a T> {
        let old_self = ghost!(self);
        if self.curr.is_null() {
            None
        } else {
            let node = ptr_as_ref(self.curr, self.token);
            self.token = shrink_token_ref(self.token, ghost!((self.token.shallow_model()).remove(self.curr)));
            proof_assert!((@self.token).remove(*self.tail).ext_eq((@old_self.token).remove(*self.tail).remove(old_self.curr)));
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
        LinkedList{head: self.curr, tail: *self.tail, token: *fin(self.token)}.invariant()
    }

    #[requires((*self).invariant())]
    #[ensures((^self).invariant())]
    fn next(&mut self) -> Option<&'a mut T> {
        let old_self = ghost!(self);
        if self.curr.is_null() {
            None
        } else {
            let node = ptr_as_mut2(self.curr, &mut self.token);
            proof_assert!((@self.token).remove(*self.tail).ext_eq((@old_self.token).remove(*self.tail).remove(old_self.curr)));
            self.curr = node.next;
            Some(&mut node.data)
        }
    }
}