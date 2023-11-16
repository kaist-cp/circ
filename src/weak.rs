use std::{
    marker::PhantomData,
    mem::{self, forget},
    sync::atomic::AtomicUsize,
};

use atomic::{Atomic, Ordering};
use static_assertions::const_assert;

use crate::{Cs, Pointer, Snapshot, StrongPtr, Tagged, TaggedCnt};

/// A result of unsuccessful `compare_exchange`.
///
/// It returns the ownership of [`Weak`] pointer which was given as a parameter.
pub struct CompareExchangeErrorWeak<T, P> {
    /// The `desired` which was given as a parameter of `compare_exchange`.
    pub desired: P,
    /// The current pointer value inside the atomic pointer.
    pub current: TaggedCnt<T>,
}

pub struct AtomicWeak<T, C: Cs> {
    pub(crate) link: Atomic<TaggedCnt<T>>,
    _marker: PhantomData<*const C>,
}

unsafe impl<T: Send + Sync, C: Cs> Send for AtomicWeak<T, C> {}
unsafe impl<T: Send + Sync, C: Cs> Sync for AtomicWeak<T, C> {}

// Ensure that TaggedPtr<T> is 8-byte long,
// so that lock-free atomic operations are possible.
const_assert!(Atomic::<TaggedCnt<u8>>::is_lock_free());
const_assert!(mem::size_of::<TaggedCnt<u8>>() == mem::size_of::<usize>());
const_assert!(mem::size_of::<Atomic<TaggedCnt<u8>>>() == mem::size_of::<AtomicUsize>());

impl<T, C: Cs> AtomicWeak<T, C> {
    #[inline(always)]
    pub fn null() -> Self {
        Self {
            link: Atomic::new(Tagged::null()),
            _marker: PhantomData,
        }
    }

    /// Loads a raw tagged pointer from this atomic pointer.
    ///
    /// Note that the returned pointer cannot be dereferenced safely, becuase it is protected by
    /// neither a SMR nor a reference count. To dereference, use `load_from_weak` method of
    /// [`Snapshot`] instead.
    #[inline]
    pub fn load(&self, order: Ordering) -> TaggedCnt<T> {
        self.link.load(order)
    }

    #[inline]
    pub fn load_ss(&self, cs: &C) -> Option<Snapshot<T, C>> {
        let mut result = Snapshot::new();
        if result.load_from_weak(self, cs) {
            Some(result)
        } else {
            None
        }
    }

    #[inline]
    pub fn store(&self, ptr: Weak<T, C>, order: Ordering, cs: &C) {
        let new_ptr = ptr.as_ptr();
        forget(ptr);
        let old_ptr = self.link.swap(new_ptr, order);
        unsafe {
            if let Some(cnt) = old_ptr.as_raw().as_mut() {
                C::decrement_weak(cnt, Some(cs));
            }
        }
    }

    /// Atomically compares the underlying pointer with expected, and if they refer to
    /// the same managed object, replaces the current pointer with a copy of desired
    /// (incrementing its reference count) and returns true. Otherwise, returns false.
    #[inline(always)]
    pub fn compare_exchange(
        &self,
        expected: TaggedCnt<T>,
        desired: Weak<T, C>,
        success: Ordering,
        failure: Ordering,
        _: &C,
    ) -> Result<Weak<T, C>, CompareExchangeErrorWeak<T, Weak<T, C>>> {
        match self
            .link
            .compare_exchange(expected, desired.as_ptr(), success, failure)
        {
            Ok(_) => {
                // Skip decrementing a strong count of the inserted pointer.
                forget(desired);
                let weak = Weak::from_raw(expected);
                return Ok(weak);
            }
            Err(current) => Err(CompareExchangeErrorWeak { desired, current }),
        }
    }

    #[inline]
    pub fn compare_exchange_tag<P>(
        &self,
        expected: &P,
        desired_tag: usize,
        success: Ordering,
        failure: Ordering,
        _: &C,
    ) -> Result<TaggedCnt<T>, CompareExchangeErrorWeak<T, TaggedCnt<T>>>
    where
        P: StrongPtr<T, C>,
    {
        let desired = expected.as_ptr().with_tag(desired_tag);
        match self
            .link
            .compare_exchange(expected.as_ptr(), desired, success, failure)
        {
            Ok(current) => Ok(current),
            Err(current) => Err(CompareExchangeErrorWeak { desired, current }),
        }
    }

    #[inline(always)]
    pub fn fetch_or(&self, tag: usize, order: Ordering, _: &C) -> TaggedCnt<T> {
        // HACK: The size and alignment of `Atomic<TaggedCnt<T>>` will be same with `AtomicUsize`.
        // The equality of the sizes is checked by `const_assert!`.
        let link = unsafe { &*(&self.link as *const _ as *const AtomicUsize) };
        let prev = link.fetch_or(tag, order);
        TaggedCnt::new(prev as *mut _)
    }
}

impl<T, C: Cs> From<Weak<T, C>> for AtomicWeak<T, C> {
    #[inline]
    fn from(value: Weak<T, C>) -> Self {
        let init_ptr = value.into_raw();
        Self {
            link: Atomic::new(init_ptr),
            _marker: PhantomData,
        }
    }
}

impl<T, C: Cs> Drop for AtomicWeak<T, C> {
    #[inline(always)]
    fn drop(&mut self) {
        let ptr = self.link.load(Ordering::SeqCst);
        unsafe {
            if let Some(cnt) = ptr.as_raw().as_mut() {
                C::decrement_weak(cnt, None);
            }
        }
    }
}

impl<T, C: Cs> Default for AtomicWeak<T, C> {
    #[inline(always)]
    fn default() -> Self {
        Self::null()
    }
}

pub struct Weak<T, C: Cs> {
    ptr: TaggedCnt<T>,
    _marker: PhantomData<*const C>,
}

unsafe impl<T: Send + Sync, C: Cs> Send for Weak<T, C> {}
unsafe impl<T: Send + Sync, C: Cs> Sync for Weak<T, C> {}

impl<T, C: Cs> Weak<T, C> {
    #[inline(always)]
    pub fn null() -> Self {
        Self::from_raw(TaggedCnt::null())
    }

    #[inline(always)]
    pub(crate) fn from_raw(ptr: TaggedCnt<T>) -> Self {
        Self {
            ptr,
            _marker: PhantomData,
        }
    }

    #[inline(always)]
    pub fn clone(&self) -> Self {
        let weak = Self {
            ptr: self.ptr,
            _marker: PhantomData,
        };
        unsafe {
            if let Some(cnt) = weak.ptr.as_raw().as_ref() {
                C::increment_weak(cnt, 1);
            }
        }
        weak
    }

    #[inline(always)]
    pub fn is_null(&self) -> bool {
        self.ptr.is_null()
    }

    #[inline(always)]
    pub fn tag(&self) -> usize {
        self.ptr.tag()
    }

    #[inline(always)]
    pub fn untagged(mut self) -> Self {
        self.ptr = TaggedCnt::new(self.ptr.as_raw());
        self
    }

    #[inline(always)]
    pub fn with_tag(mut self, tag: usize) -> Self {
        self.ptr = self.ptr.with_tag(tag);
        self
    }

    #[inline]
    pub(crate) fn into_raw(self) -> TaggedCnt<T> {
        let new_ptr = self.as_ptr();
        // Skip decrementing the ref count.
        forget(self);
        new_ptr
    }

    #[inline]
    pub(crate) fn increment_weak(&self) {
        if let Some(ptr) = unsafe { self.ptr.as_raw().as_ref() } {
            C::increment_weak(ptr, 1);
        }
    }
}

impl<T, C: Cs> Drop for Weak<T, C> {
    #[inline(always)]
    fn drop(&mut self) {
        unsafe {
            if let Some(cnt) = self.ptr.as_raw().as_mut() {
                C::decrement_weak(cnt, None);
            }
        }
    }
}

impl<T, C: Cs> PartialEq for Weak<T, C> {
    #[inline(always)]
    fn eq(&self, other: &Self) -> bool {
        self.ptr == other.ptr
    }
}

impl<T, C: Cs> Pointer<T> for Weak<T, C> {
    #[inline]
    fn as_ptr(&self) -> TaggedCnt<T> {
        self.ptr
    }
}
