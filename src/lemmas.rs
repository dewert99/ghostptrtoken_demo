use creusot_contracts::*;
use creusot_contracts::logic::{Seq, Mapping, Int, FMap};

#[law]
#[open(self)]
#[ensures(x.set(k, v1).set(k, v2) == x.set(k, v2))]
pub fn map_set_overwrite<K, V>(x: Mapping<K, V>, k: K, v1: V, v2: V) {}

#[law]
#[open(self)]
#[requires(k1 != k2)]
#[ensures(x.set(k1, v1).set(k2, v2) == x.set(k2, v2).set(k1, v1))]
pub fn map_set_commute<K, V>(x: Mapping<K, V>, k1: K, k2: K, v1: V, v2: V) {}

#[law]
#[open(self)]
#[requires(x.get(k) == v)]
#[ensures(x.set(k, v) == x)]
pub fn map_set_id<K, V>(x: Mapping<K, V>, k: K, v: V) {}

#[law]
#[open(self)]
#[requires(x1.disjoint(x2))]
#[ensures(x1.union(x2) == x2.union(x1))]
pub fn union_commute<K, V>(x1: FMap<K, V>, x2: FMap<K, V>) {}

#[law]
#[open(self)]
#[requires(x1.disjoint(x2))]
#[requires(x1.contains(k))]
#[ensures(x1.union(x2).remove(k).ext_eq(x1.remove(k).union(x2)))]
pub fn union_remove<K, V>(x1: FMap<K, V>, x2: FMap<K, V>, k: K) {}

#[law]
#[open(self)]
#[requires(x1.insert(k,v).disjoint(x2))]
#[ensures(x1.union(x2).insert(k, v).ext_eq(x1.insert(k, v).union(x2)))]
pub fn union_insert<K, V>(x1: FMap<K, V>, x2: FMap<K, V>, k: K, v: V) {}


#[law]
#[open(self)]
#[ensures(FMap::empty().union(x).ext_eq(x))]
pub fn union_empty<K, V>(x: FMap<K, V>) {}

#[law]
#[open(self)]
#[ensures(s.subsequence(0, s.len()) == s)]
pub fn subseq_full<T>(s: Seq<T>) {
    s.subsequence(0, s.len()).ext_eq(s);
}

#[law]
#[open(self)]
#[requires(0 <= i && i < s.len())]
#[ensures(s.subsequence(i, i+1) == Seq::singleton(s[i]))]
pub fn subseq_singleton<T>(s: Seq<T>, i: Int) {
    s.subsequence(i, i+1).ext_eq(Seq::singleton(s[i]));
}

#[law]
#[open(self)]
#[requires(0 <= i && i <= j && j <= k && k <= s.len())]
#[ensures(s.subsequence(i, j).concat(s.subsequence(j, k)) == s.subsequence(i, k))]
pub fn concat_subseq<T>(s: Seq<T>, i: Int, j: Int, k: Int) {
    s.subsequence(i, k).ext_eq(s.subsequence(i, j).concat(s.subsequence(j, k)));
}

#[law]
#[open(self)]
#[ensures(s1.concat(s2).subsequence(0, s1.len()) == s1)]
#[ensures(s1.concat(s2).subsequence(s1.len(), s1.len() + s2.len()) == s2)]
pub fn subseq_concat<T>(s1: Seq<T>, s2: Seq<T>) {
    s1.ext_eq(s1.concat(s2).subsequence(0, s1.len()));
    s2.ext_eq(s1.concat(s2).subsequence(s1.len(), s1.len() + s2.len()));
}

#[law]
#[open(self)]
#[requires(0 <= i && i <= j && j <= s.len() && 0 <= k && k <= l && i + l <= j)]
#[ensures(s.subsequence(i, j).subsequence(k, l) == s.subsequence(i + k, i + l))]
pub fn subseq_subseq<T>(s: Seq<T>, i: Int, j: Int, k: Int, l: Int) {
    s.subsequence(i + k, i + l).ext_eq(s.subsequence(i, j).subsequence(k, l));
}
