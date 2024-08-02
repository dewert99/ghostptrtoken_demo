use creusot_contracts::logic::IndexLogic;
use creusot_contracts::prelude::*;
use creusot_contracts::util::*;
enum BaseSeq<T> {
    Empty,
    Cons(T, SizedW<BaseSeq<T>>)
}

impl<T> BaseSeq<T> {
    #[logic]
    #[ensures(result >= 0)]
    fn len(self) -> Int {
        match self {
            BaseSeq::Empty => 0,
            BaseSeq::Cons(_, rest) => rest.len() + 1
        }
    }

    #[logic]
    #[requires(i >= 0)]
    #[requires(i < self.len())]
    fn get(self, i: Int) -> T {
        match self {
            BaseSeq::Empty => unreachable(),
            BaseSeq::Cons(x, rest) => if i == 0 {
                x
            } else {
                rest.get(i - 1)
            }
        }
    }

    #[logic]
    #[ensures(result.len() == self.len() + other.len())]
    #[ensures(forall<i: Int> i >= 0 && i < self.len() ==> result.get(i) == self.get(i))]
    #[ensures(forall<i: Int> i >= self.len() && i - self.len() < other.len() ==> result.get(i) == other.get(i - self.len()))]
    fn concat(self, other: Self) -> Self {
        match self {
            BaseSeq::Empty => other,
            BaseSeq::Cons(y, rest) => BaseSeq::Cons(y, rest.concat(other).make_sized())
        }
    }
}

pub struct Seq<T>(BaseSeq<T>);

impl<T> IndexLogic<Int> for Seq<T> {
    type Item = T;

    #[logic]
    #[open(self)]
    fn index_logic(self, i: Int) -> T {
        self.0.get(i)
    }
}

impl<T> Seq<T> {

    #[logic]
    #[open(self)]
    fn len(self) -> Int {
        self.0.len()
    }

    #[logic]
    #[open(self)]
    #[ensures(result.len() == self.len() + other.len())]
    #[ensures(forall<i: Int> i >= 0 && i < self.len() ==> result[i] == self[i])]
    #[ensures(forall<i: Int> i >= self.len() && i - self.len() < other.len() ==> result[i] == other[i - self.len()])]
    fn concat(self, other: Self) -> Self {
        Seq(self.0.concat(other.0))
    }
}