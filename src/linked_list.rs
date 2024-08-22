use ::std::ptr;
use creusot_contracts::ghost_ptr::*;
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

#[logic]
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

#[predicate]
fn inv<T>(
    head: *const Node<T>,
    tail: *const Node<T>,
    token: FMap<*const Node<T>, Node<T>>,
) -> bool {
    if head == <*const Node<T>>::null_logic() {
        token == FMap::empty()
    } else {
        lseg(head, tail, token.remove(tail))
            && (match token.get(tail) {
                None => false,
                Some(node) => node.next == <*const Node<T>>::null_logic(),
            })
    }
}

#[logic]
fn model<T>(
    head: *const Node<T>,
    tail: *const Node<T>,
    token: FMap<*const Node<T>, Node<T>>,
) -> Seq<T> {
    if head == <*const Node<T>>::null_logic() {
        Seq::EMPTY
    } else {
        lseg_seq(head, tail, token.remove(tail)).concat(Seq::singleton(token.lookup(tail).data))
    }
}

impl<T> LinkedList<T> {
    #[predicate]
    #[open(self)]
    pub fn invariant(self) -> bool {
        inv(self.head, self.tail, self.token.shallow_model())
    }

    #[logic]
    #[open(self)]
    pub fn model(self) -> Seq<T> {
        model(self.head, self.tail, self.token.shallow_model())
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
            let tail = self.token.ptr_as_mut(self.tail);
            tail.next = other.head;
            let tok1 = snapshot!(self.token@.remove(self.tail));
            let tok2 = snapshot!(
                other
                    .token@
                    .remove(other.tail)
                    .insert(self.tail, self.token@.lookup(self.tail))
            );
            self.token.merge(other.token);
            proof_assert!(lseg_trans(self.head, self.tail, other.tail, *tok1, *tok2));
            self.tail = other.tail;
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
            token: self.token.borrow(),
            tail: snapshot!(self.tail),
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
            token: self.token.borrow_mut(),
            tail: {
                let x = self.tail;
                snapshot!(x)
            },
        }
    }
}

pub struct Iter<'a, T> {
    curr: *const Node<T>,
    token: GhostPtrTokenRef<'a, Node<T>>,
    tail: Snapshot<*const Node<T>>,
}

impl<'a, T> Iter<'a, T> {
    #[predicate]
    #[open(self)]
    pub fn invariant(self) -> bool {
        inv(self.curr, *self.tail, self.token.shallow_model())
    }

    #[logic]
    #[open(self)]
    pub fn model(self) -> Seq<T> {
        model(self.curr, *self.tail, self.token.shallow_model())
    }

    #[requires((*self).invariant())]
    #[ensures((^self).invariant())]
    #[ensures(match result {
        Some(val) => Seq::singleton(*val).concat((^self).model()).ext_eq((*self).model()),
        None => ^self == *self && (*self).model() == Seq::EMPTY
    })]
    pub fn next(&mut self) -> Option<&'a T> {
        if self.curr.is_null() {
            None
        } else {
            let node = self.token.to_ref().ptr_as_ref(self.curr);
            let g = snapshot!(self.token.shallow_model().remove(self.curr));
            self.curr = node.next;
            self.token = self.token.shrink_token_ref(g);
            Some(&node.data)
        }
    }
}

#[derive(Resolve)]
pub struct IterMut<'a, T> {
    curr: *const Node<T>,
    token: GhostPtrTokenMut<'a, Node<T>>,
    tail: Snapshot<*const Node<T>>,
}

impl<'a, T> IterMut<'a, T> {
    #[predicate]
    #[open(self)]
    pub fn invariant(self) -> bool {
        inv(self.curr, *self.tail, self.token.cur())
    }

    #[predicate(prophetic)]
    #[open(self)]
    #[ensures(self.resolve() && self.invariant() ==> result)]
    pub fn fin_invariant(self) -> bool {
        inv(self.curr, *self.tail, self.token.fin())
    }

    #[logic]
    #[open(self)]
    pub fn model(self) -> Seq<T> {
        model(self.curr, *self.tail, self.token.cur())
    }

    #[logic(prophetic)]
    #[open(self)]
    #[ensures(self.resolve() ==> result == self.model())]
    pub fn fin_model(self) -> Seq<T> {
        model(self.curr, *self.tail, self.token.fin())
    }

    #[requires((*self).invariant())]
    #[ensures((^self).invariant())]
    #[ensures(match result {
        Some(val) => Seq::singleton(*val).concat((^self).model()).ext_eq((*self).model()),
        None => ^self == *self && (*self).model() == Seq::EMPTY
    })]
    #[ensures((^self).fin_invariant() ==> (*self).fin_invariant())]
    #[ensures(match result {
        Some(val) => Seq::singleton(^val).concat((^self).fin_model()).ext_eq((*self).fin_model()),
        None => ^self == *self
    })]
    pub fn next(&mut self) -> Option<&'a mut T> {
        if self.curr.is_null() {
            None
        } else {
            let node = self.token.take_mut(self.curr);
            self.curr = node.next;
            let res = &mut node.data;
            Some(res)
        }
    }
}
