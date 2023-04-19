use creusot_contracts::*;

pub type SizedW<T> = Box<T>;

pub trait MakeSized {
    #[logic]
    #[why3::attr = "inline:trivial"]
    fn make_sized(self) -> SizedW<Self>;
}

impl<T: ?Sized> MakeSized for T {
    #[trusted]
    #[logic]
    #[ensures(*result == self)]
    fn make_sized(self) -> SizedW<Self> {
        absurd
    }
}


#[allow(unconditional_recursion)]
#[logic(() -> '_)]
#[requires(false)]
#[ensures(false)]
#[variant(0)]
pub fn unreachable<T>() -> T {
    unreachable()
}

#[creusot_contracts::logic]
#[requires(b)]
pub fn assert(b: bool) {}

#[logic(('x) -> 'x)]
#[requires(op != None)]
#[ensures(Some(result) == op)]
pub fn unwrap<T>(op: Option<T>) -> T {
    match op {
        Some(t) => t,
        None => unreachable()
    }
}
