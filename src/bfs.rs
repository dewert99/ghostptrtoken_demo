use crate::hashset::PtrHashSet;
use ::std::collections::VecDeque;
use creusot_contracts::ghost_ptr::*;
use creusot_contracts::logic::{FMap, Set};
use creusot_contracts::*;

pub struct Node<T> {
    data: T,
    edges: VecDeque<*const Node<T>>,
}

pub struct Graph<T>(GhostPtrToken<Node<T>>);

#[predicate]
fn node_inv<T>(node: Node<T>, token: FMap<*const Node<T>, Node<T>>) -> bool {
    pearlite! {
        forall<i: Int> 0 <= i && i < node.edges@.len() ==> token.contains(node.edges@[i])
    }
}

#[predicate]
fn closed<T>(token: FMap<*const Node<T>, Node<T>>) -> bool {
    pearlite! {
        forall<ptr: *const Node<T>> match token.get(ptr) {
            None => true,
            Some(node) => node_inv(*node, token)
        }
    }
}

impl<T> Graph<T> {
    #[predicate]
    #[open(self)]
    pub fn inv(self) -> bool {
        closed(self.0.shallow_model())
    }

    #[predicate]
    #[open(self)]
    pub fn contains(self, ptr: *const Node<T>) -> bool {
        self.0.shallow_model().contains(ptr)
    }

    #[requires(self.inv())]
    #[requires((*self).contains(start))]
    #[ensures(result.inv())]
    #[ensures(result.fin_inv() ==> (^self).inv())]
    pub fn bfs_mut(&mut self, start: *const Node<T>) -> BFS<T> {
        let original = snapshot!(self.0@);
        let mut token = self.0.borrow_mut();
        let m = token.take_mut(start);
        let mut todo = VecDeque::new();
        todo.push_back(m);
        let mut done = PtrHashSet::new();
        done.insert(start);
        BFS {
            original,
            todo,
            token,
            done,
        }
    }
}

#[derive(Resolve)]
pub struct BFS<'a, T> {
    original: Snapshot<FMap<*const Node<T>, Node<T>>>,
    token: GhostPtrTokenMut<'a, Node<T>>,
    todo: VecDeque<&'a mut Node<T>>,
    done: PtrHashSet<Node<T>>,
}

#[predicate]
fn tracked_subset<T>(
    token: FMap<*const T, T>,
    original: FMap<*const T, T>,
    done: Set<Int>,
) -> bool {
    pearlite! {
        forall<ptr: *const T> match token.get(ptr) {
            Some(x) => original.get(ptr) == Some(x),
            None => original.get(ptr) == None || done.contains(ptr.addr_logic())
        }
    }
}

#[predicate]
fn todo_inv<T>(todo: Seq<&mut Node<T>>, original: FMap<*const Node<T>, Node<T>>) -> bool {
    pearlite! {
        forall<i: Int> 0 <= i && i < todo.len() ==>
            node_inv(*todo[i], original)
    }
}

#[predicate]
fn same_edges<T>(
    token1: FMap<*const Node<T>, Node<T>>,
    token2: FMap<*const Node<T>, Node<T>>,
) -> bool {
    pearlite! {
        forall<ptr: *const Node<T>> match (token1.get(ptr), token2.get(ptr)) {
            (Some(node1), Some(node2)) => node1.edges@ == node2.edges@,
            (None, None) => true,
            (Some(_x), None) => false,
            (None, Some(_x)) => false,
        }
    }
}

#[predicate(prophetic)]
fn resolve_todo_edges<T>(todo: Seq<&mut Node<T>>) -> bool {
    pearlite! {
        forall<i: Int> 0 <= i && i < todo.len() ==>
            (*todo[i]).edges@ == (^todo[i]).edges@
    }
}

impl<'a, T> BFS<'a, T> {
    #[predicate]
    #[open(self)]
    pub fn inv(self) -> bool {
        closed(*self.original)
            && tracked_subset(self.token.cur(), *self.original, self.done.shallow_model())
            && todo_inv(self.todo.shallow_model(), *self.original)
    }

    #[predicate(prophetic)]
    #[open(self)]
    #[ensures(self.resolve() ==> result)]
    pub fn fin_inv(self) -> bool {
        same_edges(self.token.cur(), self.token.fin())
            && resolve_todo_edges(self.todo.shallow_model())
    }

    #[requires((*self).inv())]
    #[ensures((^self).inv())]
    #[ensures((^self).fin_inv() ==> (*self).fin_inv())]
    pub fn next(&mut self) -> Option<&'a mut T> {
        let r = self.todo.pop_front();
        match r {
            None => None,
            Some(node) => {
                let edges = &node.edges;
                let old_self = snapshot!(self);
                #[invariant(self.inv())]
                #[invariant(self.fin_inv() ==> old_self.fin_inv())]
                #[invariant(*self.original == *old_self.original)]
                #[invariant(^self == ^*old_self)]
                for i in 0..edges.len() {
                    let ptr = edges[i];
                    if self.done.insert(ptr) {
                        self.todo.push_back(self.token.take_mut(ptr))
                    }
                }
                Some(&mut node.data)
            }
        }
    }
}