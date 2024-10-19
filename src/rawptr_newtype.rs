use creusot_contracts::*;

// can we avoid the Thin bound?

#[trusted]
pub struct RawPtr<T: ?Sized + std::ptr::Thin>(pub *const T);

impl<T: ?Sized + std::ptr::Thin> RawPtr<T> {
    #[trusted]
    #[open(self)]
    #[logic]
    pub fn addr_logic(self) -> Int {
        absurd
    }

    #[open(self)]
    #[predicate]
    pub fn is_null_logic(self) -> bool { pearlite! {
        self.addr_logic() == 0
    }}

    #[trusted]
    #[ensures(result == (self.addr_logic() == 0))]
    pub fn is_null(self) -> bool {
        self.0.is_null()
    }

    #[trusted]
    #[ensures(result.addr_logic() == 0)]
    pub fn null() -> Self {
        RawPtr(std::ptr::null())
    }
}
