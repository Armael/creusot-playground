use creusot_contracts::*;
use crate::rawptr::{RawPtr,RawPtrExt};
use ::std::ptr::Thin;

// we inherit "+ Thin" from RawPtr; could we get rid of it?
// TODO: relax to unsized Ts

pub struct GhostPtrOwn<T: Thin> {
    pub ptr: RawPtr<T>,
    pub val: T,
}

impl<T: Thin> Invariant for GhostPtrOwn<T> {
    #[predicate(prophetic)]
    #[open]
    #[creusot::trusted_ignore_structural_inv]
    #[creusot::trusted_is_tyinv_trivial_if_param_trivial]
    fn invariant(self) -> bool {
        pearlite! { !self.ptr.is_null_logic() && inv(self.val) }
    }
}

// TODO: make these methods of RawPtr when we can make it a newtype?

#[trusted]
#[ensures(result.1.ptr == result.0 && result.1.val == *val)]
pub fn from_box<T>(val: Box<T>) -> (RawPtr<T>, GhostBox<GhostPtrOwn<T>>) {
    assert!(core::mem::size_of_val::<T>(&*val) > 0, "GhostPtrOwn doesn't support ZSTs");
    (Box::into_raw(val), #[allow(unreachable_code)] { ghost!(loop{}) })
}

#[trusted]
#[requires(ptr == own.ptr)]
#[ensures(*result == own.val)]
pub fn as_ref<T>(ptr: RawPtr<T>, own: GhostBox<&GhostPtrOwn<T>>) -> &T {
    unsafe { &*ptr }
}

#[trusted]
#[requires(ptr == (own.inner_logic()).ptr)]
#[ensures(*result == (own.inner_logic()).val)]
// TODO: why is .inner_logic() needed instead of *?
#[ensures((^own.inner_logic()).ptr == (own.inner_logic()).ptr)]
#[ensures((^own.inner_logic()).val == ^result)]
pub fn as_mut<T>(ptr: RawPtr<T>, own: GhostBox<&mut GhostPtrOwn<T>>) -> &mut T {
    unsafe { &mut *(ptr as *mut _) }
}

#[trusted]
#[requires(ptr == own.ptr)]
#[ensures(*result == own.val)]
pub fn to_box<T>(ptr: RawPtr<T>, own: GhostBox<GhostPtrOwn<T>>) -> Box<T> {
    unsafe { Box::from_raw(ptr as *mut _) }
}
