use std::{
    marker::PhantomData,
    mem::{forget, size_of},
    sync::atomic::{AtomicUsize, Ordering},
};

use atomic::Atomic;
use static_assertions::const_assert;

use crate::ebr_impl::{Guard, Tagged};
use crate::utils::{Raw, RcInner};
use crate::{CompareExchangeError, Rc, RcObject, Snapshot};

/// A thread-safe (atomic) mutable memory location that contains a [`Weak<T>`].
///
/// The pointer must be properly aligned. Since it is aligned, a tag can be stored into the unused
/// least significant bits of the address. For example, the tag for a pointer to a sized type `T`
/// should be less than `(1 << align_of::<T>().trailing_zeros())`.
pub struct AtomicWeak<T> {
    pub(crate) link: Atomic<Raw<T>>,
}

unsafe impl<T: Send + Sync> Send for AtomicWeak<T> {}
unsafe impl<T: Send + Sync> Sync for AtomicWeak<T> {}

// Ensure that TaggedPtr<T> is 8-byte long,
// so that lock-free atomic operations are possible.
const_assert!(Atomic::<Raw<u8>>::is_lock_free());
const_assert!(size_of::<Raw<u8>>() == size_of::<usize>());
const_assert!(size_of::<Atomic<Raw<u8>>>() == size_of::<AtomicUsize>());

impl<T> AtomicWeak<T> {
    /// Constructs a new `AtomicWeak` containing a null pointer.
    #[inline(always)]
    pub fn null() -> Self {
        Self {
            link: Atomic::new(Tagged::null()),
        }
    }

    /// Loads a [`WeakSnapshot`] pointer from this `AtomicWeak`.
    ///
    /// This method takes an [`Ordering`] argument which describes the memory ordering of this
    /// operation. Possible values are `SeqCst`, `Acquire` and `Relaxed`.
    ///
    /// # Panics
    ///
    /// Panics if `order` is `Release` or `AcqRel`.
    #[inline]
    pub fn load<'g>(&self, order: Ordering, guard: &'g Guard) -> WeakSnapshot<'g, T> {
        WeakSnapshot::from_raw(self.link.load(order), guard)
    }

    /// Stores a [`Weak`] pointer into this `AtomicWeak`.
    ///
    /// This method takes an [`Ordering`] argument which describes the memory ordering of
    /// this operation.
    #[inline]
    pub fn store(&self, ptr: Weak<T>, order: Ordering, guard: &Guard) {
        let new_ptr = ptr.ptr;
        forget(ptr);
        let old_ptr = self.link.swap(new_ptr, order);
        unsafe {
            if let Some(cnt) = old_ptr.as_raw().as_mut() {
                RcInner::decrement_weak(cnt, Some(guard));
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
    /// the comparison fails. Using `Acquire` as success ordering makes the store part
    /// of this operation `Relaxed`, and using `Release` makes the successful load
    /// `Relaxed`. The failure ordering can only be `SeqCst`, `Acquire` or `Relaxed`
    /// and must be equivalent to or weaker than the success ordering.
    #[inline(always)]
    pub fn compare_exchange<'g>(
        &self,
        expected: WeakSnapshot<'g, T>,
        desired: Weak<T>,
        success: Ordering,
        failure: Ordering,
        guard: &'g Guard,
    ) -> Result<Weak<T>, CompareExchangeError<Weak<T>, WeakSnapshot<'g, T>>> {
        match self
            .link
            .compare_exchange(expected.ptr, desired.ptr, success, failure)
        {
            Ok(_) => {
                // Skip decrementing a weak count of the inserted pointer.
                forget(desired);
                let weak = Weak::from_raw(expected.ptr);
                Ok(weak)
            }
            Err(current) => {
                let current = WeakSnapshot::from_raw(current, guard);
                Err(CompareExchangeError { desired, current })
            }
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
    /// the comparison fails. Using `Acquire` as success ordering makes the store part
    /// of this operation `Relaxed`, and using `Release` makes the successful load
    /// `Relaxed`. The failure ordering can only be `SeqCst`, `Acquire` or `Relaxed`
    /// and must be equivalent to or weaker than the success ordering.
    #[inline(always)]
    pub fn compare_exchange_weak<'g>(
        &self,
        expected: WeakSnapshot<'g, T>,
        desired: Weak<T>,
        success: Ordering,
        failure: Ordering,
        guard: &'g Guard,
    ) -> Result<Weak<T>, CompareExchangeError<Weak<T>, WeakSnapshot<'g, T>>> {
        match self
            .link
            .compare_exchange_weak(expected.ptr, desired.ptr, success, failure)
        {
            Ok(_) => {
                // Skip decrementing a weak count of the inserted pointer.
                forget(desired);
                let weak = Weak::from_raw(expected.ptr);
                Ok(weak)
            }
            Err(current) => {
                let current = WeakSnapshot::from_raw(current, guard);
                Err(CompareExchangeError { desired, current })
            }
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
    /// For both cases, the ownership of `expected` is returned by a dedicated field.
    ///
    /// This method takes two [`Ordering`] arguments to describe the memory
    /// ordering of this operation. `success` describes the required ordering for the
    /// read-modify-write operation that takes place if the comparison with `expected` succeeds.
    /// `failure` describes the required ordering for the load operation that takes place when
    /// the comparison fails. Using `Acquire` as success ordering makes the store part
    /// of this operation `Relaxed`, and using `Release` makes the successful load
    /// `Relaxed`. The failure ordering can only be `SeqCst`, `Acquire` or `Relaxed`
    /// and must be equivalent to or weaker than the success ordering.
    #[inline]
    pub fn compare_exchange_tag<'g>(
        &self,
        expected: WeakSnapshot<'g, T>,
        desired_tag: usize,
        success: Ordering,
        failure: Ordering,
        guard: &'g Guard,
    ) -> Result<WeakSnapshot<'g, T>, CompareExchangeError<WeakSnapshot<'g, T>, WeakSnapshot<'g, T>>>
    {
        let desired_raw = expected.ptr.with_tag(desired_tag);
        match self
            .link
            .compare_exchange(expected.ptr, desired_raw, success, failure)
        {
            Ok(current) => Ok(WeakSnapshot::from_raw(current, guard)),
            Err(current) => Err(CompareExchangeError {
                desired: WeakSnapshot::from_raw(desired_raw, guard),
                current: WeakSnapshot::from_raw(current, guard),
            }),
        }
    }

    /// Returns a mutable reference to the stored `Weak`.
    ///
    /// This is safe because the mutable reference guarantees that no other threads are
    /// concurrently accessing.
    pub fn get_mut(&mut self) -> &mut Weak<T> {
        unsafe { core::mem::transmute(self.link.get_mut()) }
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
        let ptr = (*self.link.get_mut()).as_raw();
        unsafe {
            if let Some(cnt) = ptr.as_mut() {
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
/// Unlike [`crate::Rc`] pointer, this pointer does not own a strong reference count
/// but own a weak reference count.
/// It allows a destruction of the object `T` when the strong count reaches zero,
/// but the allocation of the counters remains due to the weak count.
/// To create a strong pointer such as [`Snapshot`], it must first check the counter
/// and make sure the object is not destructed yet.
///
/// When `T` implements [`Send`] and [`Sync`], [`Weak<T>`] also implements these traits.
///
/// The pointer must be properly aligned. Since it is aligned, a tag can be stored into the unused
/// least significant bits of the address. For example, the tag for a pointer to a sized type `T`
/// should be less than `(1 << align_of::<T>().trailing_zeros())`.
pub struct Weak<T> {
    ptr: Raw<T>,
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
    /// Constructs a null `Weak` pointer.
    #[inline(always)]
    pub fn null() -> Self {
        Self::from_raw(Raw::null())
    }

    /// Returns `true` if the pointer is null ignoring the tag.
    #[inline(always)]
    pub fn is_null(&self) -> bool {
        self.ptr.is_null()
    }

    #[inline(always)]
    pub(crate) fn from_raw(ptr: Raw<T>) -> Self {
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

    #[inline]
    pub fn snapshot<'g>(&self, guard: &'g Guard) -> WeakSnapshot<'g, T> {
        WeakSnapshot::from_raw(self.ptr, guard)
    }

    #[inline]
    pub(crate) fn into_raw(self) -> Raw<T> {
        let new_ptr = self.ptr;
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

impl<T: RcObject> Weak<T> {
    /// Attempts to upgrade the `Weak` pointer to an `Rc`.
    /// Returns `None` if the referent has been destructed.
    #[inline]
    pub fn upgrade(&self) -> Option<Rc<T>> {
        let Some(obj) = (unsafe { self.ptr.as_raw().as_ref() }) else {
            return Some(Rc::from_raw(self.ptr));
        };
        if obj.increment_strong() {
            return Some(Rc::from_raw(self.ptr));
        }
        None
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

/// A local weak pointer protected by the backend EBR.
///
/// Unlike [`Weak`] pointer, this pointer does not own a weak reference count by itself.
/// This pointer is valid for use only during the lifetime of EBR guard `'g`.
pub struct WeakSnapshot<'g, T> {
    pub(crate) ptr: Raw<T>,
    pub(crate) _marker: PhantomData<&'g T>,
}

impl<'g, T> Clone for WeakSnapshot<'g, T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<'g, T> Copy for WeakSnapshot<'g, T> {}

impl<'g, T> WeakSnapshot<'g, T> {
    /// Returns `true` if the pointer is null ignoring the tag.
    #[inline(always)]
    pub fn is_null(&self) -> bool {
        self.ptr.is_null()
    }

    /// Creates an [`Weak`] pointer by incrementing the weak reference counter.
    #[inline]
    pub fn counted(self) -> Weak<T> {
        let weak = Weak::from_raw(self.ptr);
        weak.increment_weak();
        weak
    }

    /// Tries creating a [`Snapshot`] pointer to the same object.
    ///
    /// This method checks the strong reference counter of the object and returns the [`Snapshot`]
    /// pointer if the pointer is a null pointer or the object is not destructed yet.
    pub fn upgrade(self) -> Option<Snapshot<'g, T>> {
        let ptr = self.ptr;
        if !ptr.is_null() && !unsafe { ptr.deref() }.is_not_destructed() {
            return None;
        }
        Some(Snapshot {
            ptr,
            _marker: PhantomData,
        })
    }

    /// Returns the tag stored within the pointer.
    #[inline(always)]
    pub fn tag(self) -> usize {
        self.ptr.tag()
    }

    /// Returns the same pointer, but tagged with `tag`. `tag` is truncated to be fit into the
    /// unused bits of the pointer to `T`.
    #[inline]
    pub fn with_tag(self, tag: usize) -> Self {
        let mut result = self;
        result.ptr = result.ptr.with_tag(tag);
        result
    }
}

impl<'g, T> WeakSnapshot<'g, T> {
    /// Constructs a new `WeakSnapshot` representing a null pointer.
    #[inline(always)]
    pub fn null() -> Self {
        Self {
            ptr: Tagged::null(),
            _marker: PhantomData,
        }
    }

    #[inline]
    pub(crate) fn from_raw(acquired: Raw<T>, _: &'g Guard) -> Self {
        Self {
            ptr: acquired,
            _marker: PhantomData,
        }
    }
}

impl<'g, T> Default for WeakSnapshot<'g, T> {
    #[inline]
    fn default() -> Self {
        Self::null()
    }
}

impl<'g, T> PartialEq for WeakSnapshot<'g, T> {
    #[inline(always)]
    fn eq(&self, other: &Self) -> bool {
        self.ptr.eq(&other.ptr)
    }
}
