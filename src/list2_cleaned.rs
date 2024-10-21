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
        (*self.seq == Seq::EMPTY &&
         self.first.is_null_logic() &&
         self.last.is_null_logic())
        ||
        (self.seq.len() > 0 &&
         self.first == self.seq[0].ptr &&
         self.last  == self.seq[self.seq.len() - 1].ptr &&
         // the cells in `seq` are chained properly
         (forall<i:Int> 0 <= i && i < self.seq.len() - 1 ==>
             self.seq[i].val.next == self.seq[i+1].ptr) &&
         self.seq[self.seq.len() - 1].val.next.is_null_logic())
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
        seq_map(*self.seq, |ptr_own: GhostPtrOwn<Cell<T>>| ptr_own.val.v)
    }}
}

#[trusted]
#[pure]
#[ensures(result == x - 1)]
fn minus_one(x: Int) -> Int { #[allow(unreachable_code)] { loop{} } }

#[pure]
#[ensures(forall<y: T, s: Seq<T>, f: logic::Mapping<T,U>>
    seq_map(Seq::push_front(y, s), f) == Seq::push_front(f.get(y), seq_map(s, f)))]
fn seq_map_cons<T,U>() {}

#[pure]
#[ensures(forall<y: T, s: Seq<T>, f: logic::Mapping<T,U>>
    seq_map(s.push(y), f) == seq_map(s, f).push(f.get(y)))]
fn seq_map_snoc<T,U>() {}

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
            let mut seq = self.seq.borrow_mut();
            ghost!{ seq.push_ghost(cell_own.into_inner()) };
        } else {
            let seq = self.seq.borrow_mut();
            let cell_last = gptr::as_mut(self.last, ghost!{
                let off = minus_one(seq.len_ghost());
                seq.into_inner().get_mut_ghost(off).unwrap()
            });
            cell_last.next = cell_ptr;
            self.last = cell_ptr;
        }
        seq_map_snoc::<GhostPtrOwn<Cell<T>>, T>();
    }

    #[ensures((^self)@ == Seq::push_front(x, (*self)@))]
    pub fn push_front(&mut self, x: T) {
        let cell = Box::new(Cell { v: x, next: self.first });
        let (cell_ptr, cell_own) = gptr::from_box(cell);
        self.first = cell_ptr;
        if self.last.is_null() {
            self.last = cell_ptr;
        }
        let mut seq = self.seq.borrow_mut();
        ghost!{ seq.push_front_ghost(cell_own.into_inner()) };
        seq_map_cons::<GhostPtrOwn<Cell<T>>, T>();
    }
}

impl<T: core::fmt::Debug> List<T> {
    #[trusted]
    pub fn print(&self) {
        let mut cur = self.first;
        while !cur.is_null() {
            let cell: Box<Cell<T>> = unsafe { Box::from_raw(cur as *mut _) };
            println!("{:?}", cell.v);
            cur = cell.next;
            Box::into_raw(cell); // avoid deallocating the cell
        }
    }
}
