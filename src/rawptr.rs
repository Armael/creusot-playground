use creusot_contracts::*;

pub type RawPtr<T> = *const T;

pub trait RawPtrExt<T: ?Sized>: Sized {
    #[logic]
    fn addr_logic(self) -> Int;
    #[predicate]
    fn is_null_logic(self) -> bool;
}

impl<T: ?Sized> RawPtrExt<T> for RawPtr<T> {
    #[trusted]
    #[logic]
    #[open(self)]
    fn addr_logic(self) -> Int {
        absurd
    }

    #[predicate]
    // NB: not #[open(self)]!
    #[open]
    fn is_null_logic(self) -> bool {
        self.addr_logic() == 0
    }
}

extern_spec!{
    impl<T> *const T {
        #[trusted]
        #[ensures(result == self.is_null_logic())]
        fn is_null(self) -> bool;
    }

    mod std {
        mod ptr {
            #[trusted]
            #[ensures(result.is_null_logic())]
            fn null<T>() -> *const T
            where
                T: Sized;
        }
    }
}
