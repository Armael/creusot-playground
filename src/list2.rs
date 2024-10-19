use creusot_contracts::{logic::Seq, *};
use crate::rawptr::{RawPtr,RawPtrExt};
use crate::gptr::GhostPtrOwn;
use crate::gptr;

struct Cell<T> {
    v: T,
    next: RawPtr<Cell<T>>,
}

pub struct List<T> {
    // actual data
    first: RawPtr<Cell<T>>,
    last: RawPtr<Cell<T>>,
    // ghost
    seq: GhostBox<Seq<GhostPtrOwn<Cell<T>>>>,
}

impl<T> Invariant for List<T> {
    #[open]
    #[predicate]
    fn invariant(self) -> bool { pearlite! {
        ( // `first` and `last` are correct
          (*self.seq == Seq::EMPTY &&
           self.first.is_null_logic() &&
           self.last.is_null_logic())    // xxx ".first."
          ||
          (self.seq.len() > 0 &&
           self.seq.inner_logic()[0].ptr == self.first &&
           self.seq.inner_logic()[self.seq.inner_logic().len() - 1].ptr == self.last)
        ) && (
          // the cells in `seq` are chained properly
          forall<i:Int> 0 <= i && i < self.seq.inner_logic().len() ==> {
            let cell_i /* Cell<T> */ = self.seq.inner_logic()[i].val;
            (i == self.seq.inner_logic().len() - 1 && cell_i.next.is_null_logic()) ||
            (i <  self.seq.inner_logic().len() - 1 && cell_i.next == self.seq.inner_logic()[i+1].ptr)
          }
        )
    }}
}

#[logic]
#[open(self)]
pub fn seq_map<T,U>(s: Seq<T>, f: logic::Mapping<T,U>) -> Seq<U> {
    Seq::new(s.len(), |i| f.get(s[i]))
}

impl<T> View for List<T> {
    type ViewTy = Seq<T>;

    #[logic]
    #[open(self)]
    fn view(self) -> Self::ViewTy { pearlite! {
        seq_map(self.seq.inner_logic(), |ptr_own: GhostPtrOwn<Cell<T>>| ptr_own.val.v)
    }}
}

// #[trusted]
// #[pure]
// #[ensures(*result == 1)]
// fn one() -> GhostBox<Int> { #[allow(unreachable_code)] { ghost!{loop{}} } }

#[trusted]
#[pure]
#[ensures(result == x - 1)]
fn minus_one(x: Int) -> Int { #[allow(unreachable_code)] { loop{} } }

impl<T> List<T> {
    #[ensures(result@ == Seq::EMPTY)]
    pub fn new() -> List<T> {
        List {
            first: std::ptr::null(),
            last: std::ptr::null(),
            seq: Seq::new_ghost(),
        }
    }

    #[ensures((^self)@ == (*self)@.push(x))]
    pub fn push_back(&mut self, x: T) {
        let cell = Box::new(Cell { v: x, next: std::ptr::null() });
        let (cell_ptr, cell_own) = gptr::from_box(cell);
        if self.last.is_null() {
            self.first = cell_ptr;
            self.last = cell_ptr;

            // ghost!{ self.seq.push_ghost(*cell_own) };
            //
            // error[E0507]: cannot move out of dereference of `creusot_contracts::GhostBox<gptr::GhostPtrOwn<list2::Cell<T>>>`
            //  --> src/list2.rs:83:41
            //   |
            //83 |             ghost!{ self.seq.push_ghost(*cell_own) };
            //   |                                         ^^^^^^^^^ move occurs because value has type `gptr::GhostPtrOwn<list2::Cell<T>>`, which does not implement the `Copy` trait

            //error: not a ghost variable: self
            //  --> src/list2.rs:83:21
            //   |
            //83 |             ghost!{ self.seq.push_ghost(*cell_own) };
            //   |                     ^^^^^^^^
            //   |

            // alternativement:

            // self.seq = ghost!{
            //     let mut s = *Seq::<GhostPtrOwn<Cell<T>>>::new_ghost();
            //     s.push_ghost(*cell_own);
            //     s
            // };

            // error[E0507]: cannot move out of dereference of `creusot_contracts::GhostBox<creusot_contracts::Seq<gptr::GhostPtrOwn<list2::Cell<T>>>>`
            //    --> src/list2.rs:101:29
            //     |
            // 101 |                 let mut s = *Seq::<GhostPtrOwn<Cell<T>>>::new_ghost();
            //     |                             ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ move occurs because value has type `creusot_contracts::Seq<gptr::GhostPtrOwn<list2::Cell<T>>>`, which does not implement the `Copy` trait
            //     |
            //
            // error[E0507]: cannot move out of dereference of `creusot_contracts::GhostBox<gptr::GhostPtrOwn<list2::Cell<T>>>`
            //    --> src/list2.rs:102:30
            //     |
            // 102 |                 s.push_ghost(*cell_own);
            //     |                              ^^^^^^^^^ move occurs because value has type `gptr::GhostPtrOwn<list2::Cell<T>>`, which does not implement the `Copy` trait
            //
            // error: internal compiler error: compiler/rustc_borrowck/src/places_conflict.rs:227:21: Tracking borrow behind shared reference.
            //
            // thread 'rustc' panicked at compiler/rustc_borrowck/src/places_conflict.rs:227:21:
            // Box<dyn Any>

            // self.seq = ghost!{
            //     let mut s = Seq::<GhostPtrOwn<Cell<T>>>::new_ghost().into_inner();
            //     s.push_ghost(cell_own.into_inner());
            //     s
            // };

            let mut seq = self.seq.borrow_mut();
            ghost!{ seq.push_ghost(cell_own.into_inner()) };
        } else {
            let seq = self.seq.borrow_mut();
            // proof_assert!{ (*self).invariant() }; // why?
            // proof_assert!(seq.len() > 0); // not needed
            let cell_last = gptr::as_mut(self.last, ghost!{
                // seq.into_inner().get_mut_ghost(seq.len_ghost() - 1).unwrap()
                // -> no Int literals

                // let len = seq.len_ghost();
                // seq.into_inner().get_mut_ghost(len - one().into_inner()).unwrap()
                // -> crash because of "-"

                let off = minus_one(seq.len_ghost());
                seq.into_inner().get_mut_ghost(off).unwrap()
            });
            cell_last.next = cell_ptr;
            self.last = cell_ptr;
        }
    }

    #[ensures((^self)@ == Seq::push_front(x, (*self)@))]
    pub fn push_front(&mut self, x: T) {
        let cell = Box::new(Cell { v: x, next: self.first });
        let cell_s = snapshot!{ *cell };
        let (cell_ptr, cell_own) = gptr::from_box(cell);
        proof_assert!{ *cell_s == cell_own.val };
        self.first = cell_ptr;
        if self.last.is_null() {
            self.last = cell_ptr;
        }
        let mut seq = self.seq.borrow_mut();
        let seq0 = snapshot!{ *seq.inner_logic() };
        ghost!{ seq.push_ghost(cell_own.into_inner()) };
        proof_assert!{ **seq == Seq::push_front(GhostPtrOwn { val: *cell_s, ptr: cell_ptr }, *seq0) };
    }
}
