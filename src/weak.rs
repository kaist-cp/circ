use std::{
    mem::{forget, size_of},
    sync::atomic::{AtomicUsize, Ordering},
};
use Ordering::*;

use atomic::Atomic;
use static_assertions::const_assert;

use crate::ebr_impl::{Cs, Tagged};
use crate::{Pointer, RcInner, Snapshot, TaggedCnt};

/// A result of unsuccessful [`AtomicWeak::compare_exchange`].
///
/// It returns the ownership of the pointer which was given as a parameter `desired`.
pub struct CompareExchangeErrorWeak<T, P> {
    /// The `desired` which was given as a parameter of [`AtomicWeak::compare_exchange`].
    pub desired: P,
    /// The current pointer value inside the atomic pointer.
    pub current: TaggedCnt<T>,
}

/// A atomically mutable field that contains an [`Weak<T>`].
///
/// The pointer must be properly aligned. Since it is aligned, a tag can be stored into the unused
/// least significant bits of the address. For example, the tag for a pointer to a sized type `T`
/// should be less than `(1 << align_of::<T>().trailing_zeros())`.
pub struct AtomicWeak<T> {
    pub(crate) link: Atomic<TaggedCnt<T>>,
}

unsafe impl<T: Send + Sync> Send for AtomicWeak<T> {}
unsafe impl<T: Send + Sync> Sync for AtomicWeak<T> {}

// Ensure that TaggedPtr<T> is 8-byte long,
// so that lock-free atomic operations are possible.
const_assert!(Atomic::<TaggedCnt<u8>>::is_lock_free());
const_assert!(size_of::<TaggedCnt<u8>>() == size_of::<usize>());
const_assert!(size_of::<Atomic<TaggedCnt<u8>>>() == size_of::<AtomicUsize>());

impl<T> AtomicWeak<T> {
    /// Constructs a new `AtomicWeak` containing a null pointer.
    #[inline(always)]
    pub fn null() -> Self {
        Self {
            link: Atomic::new(Tagged::null()),
        }
    }

    /// Loads a raw tagged pointer from this `AtomicWeak`.
    ///
    /// This method takes an [`Ordering`] argument which describes the memory ordering of this
    /// operation. Possible values are [`SeqCst`], [`Acquire`] and [`Relaxed`].
    ///
    /// Note that the returned pointer cannot be dereferenced safely, becuase it is protected by
    /// neither a SMR nor a reference count. To dereference, use [`AtomicWeak::load`] method
    /// instead.
    ///
    /// # Panics
    ///
    /// Panics if `order` is [`Release`] or [`AcqRel`].
    #[inline]
    pub fn load_raw(&self, order: Ordering) -> TaggedCnt<T> {
        self.link.load(order)
    }

    /// Tries loading a [`Snapshot`] pointer from this `AtomicWeak`.
    ///
    /// This method checks the strong reference counter of the object and returns the [`Snapshot`]
    /// pointer if the pointer is a null pointer or the object is not destructed yet.
    #[inline]
    pub fn load<'g>(&self, cs: &'g Cs) -> Option<Snapshot<'g, T>> {
        loop {
            let acquired = self.load_raw(Acquire);

            if acquired.is_null() || unsafe { acquired.deref().non_zero() } {
                return Some(Snapshot::from_raw(acquired, cs));
            } else if acquired == self.load_raw(Acquire) {
                return None;
            }
        }
    }

    /// Stores a [`Weak`] pointer into this `AtomicWeak`.
    ///
    /// This method takes an [`Ordering`] argument which describes the memory ordering of
    /// this operation.
    #[inline]
    pub fn store(&self, ptr: Weak<T>, order: Ordering, cs: &Cs) {
        let new_ptr = ptr.as_ptr();
        forget(ptr);
        let old_ptr = self.link.swap(new_ptr, order);
        unsafe {
            if let Some(cnt) = old_ptr.as_raw().as_mut() {
                RcInner::decrement_weak(cnt, Some(cs));
            }
        }
    }

    /// Stores a [`Weak`] pointer into this `AtomicWeak`, returning the previous [`Weak`].
    ///
    /// This method takes an [`Ordering`] argument which describes the memory ordering of
    /// this operation.
    #[inline(always)]
    pub fn swap(&self, new: Weak<T>, order: Ordering) -> Weak<T> {
        let new_ptr = new.into_raw();
        let old_ptr = self.link.swap(new_ptr, order);
        Weak::from_raw(old_ptr)
    }

    /// Stores the [`Weak`] pointer `desired` into the atomic pointer if the current value is the
    /// same as `expected` (either [`Snapshot`], [`crate::Rc`] or [`Weak`]). The tag is also taken
    /// into account, so two pointers to the same object, but with different tags, will not be
    /// considered equal.
    ///
    /// The return value is a result indicating whether the desired pointer was written.
    /// On success the pointer that was in this `AtomicWeak` is returned.
    /// On failure the actual current value and `desired` are returned.
    ///
    /// This method takes two [`Ordering`] arguments to describe the memory
    /// ordering of this operation. `success` describes the required ordering for the
    /// read-modify-write operation that takes place if the comparison with `expected` succeeds.
    /// `failure` describes the required ordering for the load operation that takes place when
    /// the comparison fails. Using [`Acquire`] as success ordering makes the store part
    /// of this operation [`Relaxed`], and using [`Release`] makes the successful load
    /// [`Relaxed`]. The failure ordering can only be [`SeqCst`], [`Acquire`] or [`Relaxed`]
    /// and must be equivalent to or weaker than the success ordering.
    #[inline(always)]
    pub fn compare_exchange(
        &self,
        expected: impl Pointer<T>,
        desired: Weak<T>,
        success: Ordering,
        failure: Ordering,
        _: &Cs,
    ) -> Result<Weak<T>, CompareExchangeErrorWeak<T, Weak<T>>> {
        match self
            .link
            .compare_exchange(expected.as_ptr(), desired.as_ptr(), success, failure)
        {
            Ok(_) => {
                // Skip decrementing a weak count of the inserted pointer.
                forget(desired);
                let weak = Weak::from_raw(expected.as_ptr());
                Ok(weak)
            }
            Err(current) => Err(CompareExchangeErrorWeak { desired, current }),
        }
    }

    /// Stores the [`Weak`] pointer `desired` into the atomic pointer if the current value is the
    /// same as `expected` (either [`Snapshot`], [`crate::Rc`] or [`Weak`]). The tag is also taken
    /// into account, so two pointers to the same object, but with different tags, will not be
    /// considered equal.
    ///
    /// Unlike [`AtomicWeak::compare_exchange`], this method is allowed to spuriously fail
    /// even when comparison succeeds, which can result in more efficient code on some platforms.
    /// The return value is a result indicating whether the desired pointer was written.
    /// On success the pointer that was in this `AtomicWeak` is returned.
    /// On failure the actual current value and `desired` are returned.
    ///
    /// This method takes two [`Ordering`] arguments to describe the memory
    /// ordering of this operation. `success` describes the required ordering for the
    /// read-modify-write operation that takes place if the comparison with `expected` succeeds.
    /// `failure` describes the required ordering for the load operation that takes place when
    /// the comparison fails. Using [`Acquire`] as success ordering makes the store part
    /// of this operation [`Relaxed`], and using [`Release`] makes the successful load
    /// [`Relaxed`]. The failure ordering can only be [`SeqCst`], [`Acquire`] or [`Relaxed`]
    /// and must be equivalent to or weaker than the success ordering.
    #[inline(always)]
    pub fn compare_exchange_weak(
        &self,
        expected: impl Pointer<T>,
        desired: Weak<T>,
        success: Ordering,
        failure: Ordering,
        _: &Cs,
    ) -> Result<Weak<T>, CompareExchangeErrorWeak<T, Weak<T>>> {
        match self
            .link
            .compare_exchange_weak(expected.as_ptr(), desired.as_ptr(), success, failure)
        {
            Ok(_) => {
                // Skip decrementing a weak count of the inserted pointer.
                forget(desired);
                let weak = Weak::from_raw(expected.as_ptr());
                Ok(weak)
            }
            Err(current) => Err(CompareExchangeErrorWeak { desired, current }),
        }
    }

    /// Overwrites the tag value `desired_tag` to the atomic pointer if the current value is the
    /// same as `expected` (either [`Snapshot`], [`crate::Rc`] or [`Weak`]). The tag is also taken
    /// into account, so two pointers to the same object, but with different tags, will not be
    /// considered equal.
    ///
    /// If the `desired_tag` uses more bits than the unused least significant bits of the pointer
    /// to `T`, it will be truncated to be fit.
    ///
    /// The return value is a result indicating whether the desired pointer was written.
    /// On success the pointer that was in this `AtomicWeak` is returned.
    /// On failure the actual current value and `desired` are returned.
    ///
    /// This method takes two [`Ordering`] arguments to describe the memory
    /// ordering of this operation. `success` describes the required ordering for the
    /// read-modify-write operation that takes place if the comparison with `expected` succeeds.
    /// `failure` describes the required ordering for the load operation that takes place when
    /// the comparison fails. Using [`Acquire`] as success ordering makes the store part
    /// of this operation [`Relaxed`], and using [`Release`] makes the successful load
    /// [`Relaxed`]. The failure ordering can only be [`SeqCst`], [`Acquire`] or [`Relaxed`]
    /// and must be equivalent to or weaker than the success ordering.
    #[inline]
    pub fn compare_exchange_tag(
        &self,
        expected: impl Pointer<T>,
        desired_tag: usize,
        success: Ordering,
        failure: Ordering,
        _: &Cs,
    ) -> Result<TaggedCnt<T>, CompareExchangeErrorWeak<T, TaggedCnt<T>>> {
        let desired = expected.as_ptr().with_tag(desired_tag);
        match self
            .link
            .compare_exchange(expected.as_ptr(), desired, success, failure)
        {
            Ok(current) => Ok(current),
            Err(current) => Err(CompareExchangeErrorWeak { desired, current }),
        }
    }
}

impl<T> From<Weak<T>> for AtomicWeak<T> {
    #[inline]
    fn from(value: Weak<T>) -> Self {
        let init_ptr = value.into_raw();
        Self {
            link: Atomic::new(init_ptr),
        }
    }
}

impl<T> Drop for AtomicWeak<T> {
    #[inline(always)]
    fn drop(&mut self) {
        let ptr = self.link.load(SeqCst);
        unsafe {
            if let Some(cnt) = ptr.as_raw().as_mut() {
                RcInner::decrement_weak(cnt, None);
            }
        }
    }
}

impl<T> Default for AtomicWeak<T> {
    #[inline(always)]
    fn default() -> Self {
        Self::null()
    }
}

/// A weak pointer for reference-counted pointer to an object of type `T`.
///
/// Unlike [`crate::Rc`] pointer, This pointer does not own a strong reference count but own a weak reference count.
/// It allows a destruction of the object `T` when the strong count reaches zero, but the allocation of the counters
/// remains due to the weak count. To create a strong pointer such as [`Snapshot`], it must first check the counter
/// and make sure the object is not destructed yet.
///
/// When `T` implements [`Send`] and [`Sync`], [`Weak<T>`] also implements these traits.
///
/// The pointer must be properly aligned. Since it is aligned, a tag can be stored into the unused
/// least significant bits of the address. For example, the tag for a pointer to a sized type `T`
/// should be less than `(1 << align_of::<T>().trailing_zeros())`.
pub struct Weak<T> {
    ptr: TaggedCnt<T>,
}

unsafe impl<T: Send + Sync> Send for Weak<T> {}
unsafe impl<T: Send + Sync> Sync for Weak<T> {}

impl<T> Clone for Weak<T> {
    fn clone(&self) -> Self {
        let weak = Self { ptr: self.ptr };
        unsafe {
            if let Some(cnt) = weak.ptr.as_raw().as_ref() {
                cnt.increment_weak(1);
            }
        }
        weak
    }
}

impl<T> Weak<T> {
    /// Constructs a new `Rc` representing a null pointer.
    #[inline(always)]
    pub fn null() -> Self {
        Self::from_raw(TaggedCnt::null())
    }

    #[inline(always)]
    pub(crate) fn from_raw(ptr: TaggedCnt<T>) -> Self {
        Self { ptr }
    }

    /// Returns the tag stored within the pointer.
    #[inline(always)]
    pub fn tag(&self) -> usize {
        self.ptr.tag()
    }

    /// Returns the same pointer, but tagged with `tag`. `tag` is truncated to be fit into the
    /// unused bits of the pointer to `T`.
    #[inline(always)]
    pub fn with_tag(mut self, tag: usize) -> Self {
        self.ptr = self.ptr.with_tag(tag);
        self
    }

    /// Tries creating a [`Snapshot`] pointer to the same object.
    ///
    /// This method checks the strong reference counter of the object and returns the [`Snapshot`]
    /// pointer if the pointer is a null pointer or the object is not destructed yet.
    #[inline]
    pub fn as_snapshot<'g>(&self, cs: &'g Cs) -> Option<Snapshot<'g, T>> {
        let acquired = self.as_ptr();
        if !acquired.is_null() && !unsafe { acquired.deref() }.non_zero() {
            return None;
        }
        Some(Snapshot::from_raw(acquired, cs))
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
            ptr.increment_weak(1);
        }
    }
}

impl<T> Drop for Weak<T> {
    #[inline(always)]
    fn drop(&mut self) {
        unsafe {
            if let Some(cnt) = self.ptr.as_raw().as_mut() {
                RcInner::decrement_weak(cnt, None);
            }
        }
    }
}

impl<T> PartialEq for Weak<T> {
    #[inline(always)]
    fn eq(&self, other: &Self) -> bool {
        self.ptr == other.ptr
    }
}

impl<T> Pointer<T> for Weak<T> {
    #[inline]
    fn as_ptr(&self) -> TaggedCnt<T> {
        self.ptr
    }
}
