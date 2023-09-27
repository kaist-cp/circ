use core::mem;
use std::{
    hash::Hash,
    mem::ManuallyDrop,
    ptr::null_mut,
    sync::atomic::{AtomicU32, Ordering},
};

use crate::Cs;

/// An instance of an object of type T with an atomic reference count.
pub struct RcInner<T> {
    storage: ManuallyDrop<T>,
    pub(crate) strong: AtomicU32,
    pub(crate) weak: AtomicU32,
}

impl<T> RcInner<T> {
    pub const DESTRUCTED: u32 = 1 << (u32::BITS - 1);
    pub const WEAK_EXISTS: u32 = 1 << (u32::BITS - 1);

    pub(crate) fn new(val: T) -> Self {
        Self {
            storage: ManuallyDrop::new(val),
            strong: AtomicU32::new(1),
            weak: AtomicU32::new(1),
        }
    }

    pub fn data(&self) -> &T {
        &self.storage
    }

    pub fn data_mut(&mut self) -> &mut T {
        &mut self.storage
    }

    pub unsafe fn dispose(&mut self) {
        ManuallyDrop::drop(&mut self.storage)
    }

    pub fn into_inner(self) -> T {
        ManuallyDrop::into_inner(self.storage)
    }

    pub(crate) fn increment_strong(&self) -> bool {
        let val = self.strong.fetch_add(1, Ordering::SeqCst);
        if (val & Self::DESTRUCTED) != 0 {
            return false;
        }
        if val == 0 {
            // The previous fetch_add created a permission to run decrement again.
            // Now create an actual reference.
            self.strong.fetch_add(1, Ordering::SeqCst);
        }
        return true;
    }

    pub(crate) unsafe fn decrement_strong<C: Cs>(&mut self, cs: Option<&C>) {
        if self.strong.fetch_sub(1, Ordering::SeqCst) == 1 {
            if let Some(cs) = cs {
                cs.defer(self, |inner| unsafe { inner.try_destruct::<C>() })
            } else {
                C::new().defer(self, |inner| unsafe { inner.try_destruct::<C>() })
            }
        }
    }

    pub(crate) unsafe fn try_destruct<C: Cs>(&mut self) {
        if self
            .strong
            .compare_exchange(0, Self::DESTRUCTED, Ordering::SeqCst, Ordering::SeqCst)
            .is_ok()
        {
            self.dispose();
            if self.weak.load(Ordering::SeqCst) & Self::WEAK_EXISTS == 0 {
                drop(C::own_object(self));
            } else {
                self.decrement_weak::<C>(None);
            }
        } else {
            self.decrement_strong::<C>(None);
        }
    }

    pub(crate) fn increment_weak(&self) {
        let old_weak = self.weak.fetch_add(1, Ordering::SeqCst);
        if old_weak & !Self::WEAK_EXISTS == 0 {
            // The previous fetch_add created a permission to run decrement again.
            // Now create an actual reference.
            self.weak.fetch_add(1, Ordering::SeqCst);
        }
        if old_weak & Self::WEAK_EXISTS == 0 {
            self.weak.fetch_or(Self::WEAK_EXISTS, Ordering::SeqCst);
        }
    }

    pub(crate) unsafe fn decrement_weak<C: Cs>(&mut self, cs: Option<&C>) {
        if self.weak.fetch_sub(1, Ordering::SeqCst) & !Self::WEAK_EXISTS == 1 {
            if let Some(cs) = cs {
                cs.defer(self, |inner| unsafe { inner.try_free::<C>() })
            } else {
                C::new().defer(self, |inner| unsafe { inner.try_free::<C>() })
            }
        }
    }

    pub(crate) unsafe fn try_free<C: Cs>(&mut self) {
        if self.weak.load(Ordering::SeqCst) & !Self::WEAK_EXISTS == 0 {
            drop(C::own_object(self));
        } else {
            self.decrement_weak::<C>(None);
        }
    }

    pub(crate) fn non_zero(&self) -> bool {
        let mut curr = self.strong.load(Ordering::SeqCst);
        if curr == 0 {
            curr = self
                .strong
                .compare_exchange(0, 1, Ordering::SeqCst, Ordering::SeqCst)
                .err()
                .unwrap_or(1);
        }
        (curr & Self::DESTRUCTED) == 0
    }
}

pub struct Tagged<T> {
    ptr: *mut T,
}

impl<T> Default for Tagged<T> {
    fn default() -> Self {
        Self { ptr: null_mut() }
    }
}

impl<T> Clone for Tagged<T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T> Copy for Tagged<T> {}

impl<T> PartialEq for Tagged<T> {
    fn eq(&self, other: &Self) -> bool {
        self.ptr == other.ptr
    }
}

impl<T> Eq for Tagged<T> {}

impl<T> Hash for Tagged<T> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.ptr.hash(state)
    }
}

impl<T> Tagged<T> {
    pub fn new(ptr: *mut T) -> Self {
        Self { ptr }
    }

    pub fn null() -> Self {
        Self { ptr: null_mut() }
    }

    pub fn is_null(&self) -> bool {
        self.as_raw().is_null()
    }

    pub fn tag(&self) -> usize {
        let ptr = self.ptr as usize;
        ptr & low_bits::<T>()
    }

    /// Converts the pointer to a raw pointer (without the tag).
    pub fn as_raw(&self) -> *mut T {
        let ptr = self.ptr as usize;
        (ptr & !low_bits::<T>()) as *mut T
    }

    pub fn with_tag(&self, tag: usize) -> Self {
        Self::new(with_tag(self.ptr, tag))
    }

    pub unsafe fn deref<'g>(&self) -> &'g T {
        &*self.as_raw()
    }

    pub unsafe fn deref_mut<'g>(&mut self) -> &'g mut T {
        &mut *self.as_raw()
    }

    pub unsafe fn as_ref<'g>(&self) -> Option<&'g T> {
        if self.is_null() {
            None
        } else {
            Some(self.deref())
        }
    }

    pub unsafe fn as_mut<'g>(&mut self) -> Option<&'g mut T> {
        if self.is_null() {
            None
        } else {
            Some(self.deref_mut())
        }
    }
}

/// Returns a bitmask containing the unused least significant bits of an aligned pointer to `T`.
const fn low_bits<T>() -> usize {
    (1 << mem::align_of::<T>().trailing_zeros()) - 1
}

/// Returns the pointer with the given tag
fn with_tag<T>(ptr: *mut T, tag: usize) -> *mut T {
    ((ptr as usize & !low_bits::<T>()) | (tag & low_bits::<T>())) as *mut T
}

pub type TaggedCnt<T> = Tagged<RcInner<T>>;

pub trait Pointer<T> {
    fn as_ptr(&self) -> TaggedCnt<T>;
    fn is_null(&self) -> bool {
        self.as_ptr().is_null()
    }
}
