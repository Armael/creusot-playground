use creusot_contracts::*;
use crate::{constptr, gptr, ghost_vec};

struct Cell<T> {
    v: T,
    next: RawPtr<Cell<T>>,
}

struct List<T> {
    // actual data
    first: RawPtr<Cell<T>>,
    last: RawPtr<Cell<T>>,
    // ghost
    region: GhostPtrToken<Cell<T>>,
    seq: GhostBox<GhostVec<RawPtr<Cell<T>>>>,
    // this duplicates ownership of the elements
    // model: GhostBox<Seq<T>>, // cannot construct Seqs in ghost code? -> indeed, would duplicate ownership
    // model: GhostBox<GhostVec<T>>,
}

#[open(self)]
#[predicate]
fn seq_invariant<T>(region: GhostPtrToken<Cell<T>>, seq: GhostVec<RawPtr<Cell<T>>>) -> bool { pearlite!{
    forall<i:Int> 0 <= i && i < seq@.len() ==>
      match region@.get(seq@[i]) {
          Some(cell) => {
              (cell.next == seq@[i+1] && i < seq@.len() - 1) ||
              (cell.next == RawPtr::null_logic() && i == seq@.len() - 1)
          },
          None => false
      }
}}

impl<T> Invariant for List<T> {
    #[open(self)]
    #[predicate]
    fn invariant(self) -> bool { pearlite!{
        ( // first and last are correct
            (self.seq@ == Seq::EMPTY && self.first == RawPtr::null_logic() && self.last == RawPtr::null_logic()) ||
            (self.seq@.get(0) == Some(self.first) && self.seq@.get(self.seq@.len() - 1) == Some(self.last))
        ) && seq_invariant(self.region, self.seq.inner())
    }}
}

impl<T> List<T> {
    #[logic]
    #[open(self)]
    fn shallow_model_rec(self, from: RawPtr<Cell<T>>) -> Seq<T> { pearlite!{
        if from == RawPtr::null_logic() {
            Seq::EMPTY
        } else {
            // cannot call Option::unwrap() in logic context
            match self.region@.get(from) {
                Some(cell) => Seq::concat(Seq::singleton(cell.v), self.shallow_model_rec(cell.next)),
                None => absurd
            }
        }
    }}
}

impl<T> ShallowModel for List<T> {
    type ShallowModelTy = Seq<T>;

    #[logic]
    #[open(self)]
    fn shallow_model(self) -> Self::ShallowModelTy {
        self.shallow_model_rec(self.first)
    }
}

// could we automatically have pearlite!{} for #[logic] functions?

// impl<T> ShallowModel for List<T> {
//     type ShallowModelTy = Seq<T>;

//     #[logic]
//     #[open(self)]
//     fn shallow_model(self) -> Self::ShallowModelTy {
//         pearlite!{ self.model@ }
//     }
// }



impl<T> List<T> {
    #[ensures(result@ == Seq::EMPTY)]
    fn new() -> List<T> {
        List {
            first: std::ptr::null(),
            last: std::ptr::null(),
            region: GhostPtrToken::new(),
            seq: GhostVec::new(),
            // model: GhostVec::new(),
        }
    }

    #[ensures((^self)@ == Seq::concat(Seq::singleton(x), (*self)@))]
    fn cons(&mut self, x: T) {
        let cell = Box::new(Cell { v: x, next: self.first });
        let cell_ptr = self.region.ptr_from_box(cell);
        self.first = cell_ptr;
        if self.last == std::ptr::null() {
            self.last = cell_ptr;
        }
        ghost!{ GhostVec::push_front(&mut self.seq, cell_ptr) };
        ghost!{ GhostVec::push_front(&mut self.model, x) };
    }
}
