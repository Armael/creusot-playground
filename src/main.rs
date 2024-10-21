use creusot_contracts::*;
use creusot_playground::list2_cleaned::*;

fn main() {
    let mut l: List<i32> = List::new();
    l.push_front(1);
    l.push_back(2);
    l.push_back(3);
    proof_assert!{ l@.len() == 3 && l@[0]@ == 1 && l@[1]@ == 2 && l@[2]@ == 3 };
    l.print();
}
