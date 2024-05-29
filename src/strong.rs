use std::{
    array,
    marker::PhantomData,
    mem::{forget, size_of},
    sync::atomic::{AtomicUsize, Ordering},
};
use Ordering::*;

use atomic::Atomic;
use static_assertions::const_assert;

use crate::ebr_impl::{global_epoch, Cs, Tagged};
use crate::{Pointer, RcInner, TaggedCnt, Weak};

/// A common trait for reference-counted object types.
///
/// This trait enables *immediate recursive destruction*,
/// which identifies the outgoing edges of the reclaiming nodes and
/// recursively destructs the subsequent chain of unreachable nodes.
///
/// # Examples
///
/// ```
/// use circ::{AtomicRc, RcObject, Rc};
///
/// // A simple singly linked list node.
/// struct ListNode {
///     item: usize,
///     next: AtomicRc<Self>,
/// }
///
/// impl RcObject for ListNode {
///     fn pop_edges(&mut self, out: &mut Vec<Rc<Self>>) {
///         out.push(self.next.take());
///     }
/// }
///
/// // A tree node with two children.
/// struct TreeNode {
///     item: usize,
///     left: AtomicRc<Self>,
///     right: AtomicRc<Self>,
/// }
///
/// impl RcObject for TreeNode {
///     fn pop_edges(&mut self, out: &mut Vec<Rc<Self>>) {
///         out.push(self.left.take());
///         out.push(self.right.take());
///     }
/// }
/// ```
pub trait RcObject: Sized {
    /// Takes all `Rc`s in the object and appends them to `out`.
    ///
    /// This method is called by the CIRC algorithm just before an object is destructed.
    ///
    /// It may be convinient to use [`AtomicRc::take`] because it provides
    /// a mutable reference to the node. Additionally, it remains safe even if this
    /// method is not implemented correctly (e.g., returning fewer pointers than it actually has).
    fn pop_edges(&mut self, out: &mut Vec<Rc<Self>>);
}

impl<T> Tagged<RcInner<T>> {
    fn with_timestamp(self) -> Self {
        if self.is_null() {
            self
        } else {
            self.with_high_tag(global_epoch())
        }
    }
}

/// A result of unsuccessful [`AtomicRc::compare_exchange`].
///
/// It returns the ownership of the pointer which was given as a parameter `desired`.
pub struct CompareExchangeErrorRc<'g, T, P> {
    /// The `desired` which was given as a parameter of [`AtomicRc::compare_exchange`].
    pub desired: P,
    /// The current pointer value inside the atomic pointer.
    pub current: Snapshot<'g, T>,
}

/// A atomically mutable field that contains an [`Rc<T>`].
///
/// The pointer must be properly aligned. Since it is aligned, a tag can be stored into the unused
/// least significant bits of the address. For example, the tag for a pointer to a sized type `T`
/// should be less than `(1 << align_of::<T>().trailing_zeros())`.
pub struct AtomicRc<T: RcObject> {
    link: Atomic<TaggedCnt<T>>,
    _marker: PhantomData<T>,
}

unsafe impl<T: RcObject + Send + Sync> Send for AtomicRc<T> {}
unsafe impl<T: RcObject + Send + Sync> Sync for AtomicRc<T> {}

// Ensure that TaggedPtr<T> is 8-byte long,
// so that lock-free atomic operations are possible.
const_assert!(Atomic::<TaggedCnt<u8>>::is_lock_free());
const_assert!(size_of::<TaggedCnt<u8>>() == size_of::<usize>());
const_assert!(size_of::<Atomic<TaggedCnt<u8>>>() == size_of::<AtomicUsize>());

impl<T: RcObject> AtomicRc<T> {
    /// Constructs a new `AtomicRc` by allocating a new reference-couned object.
    #[inline(always)]
    pub fn new(obj: T) -> Self {
        Self {
            link: Atomic::new(Rc::<T>::new(obj).into_raw()),
            _marker: PhantomData,
        }
    }

    /// Constructs a new `AtomicRc` containing a null pointer.
    #[inline(always)]
    pub fn null() -> Self {
        Self {
            link: Atomic::new(Tagged::null()),
            _marker: PhantomData,
        }
    }

    /// Loads a raw tagged pointer from this `AtomicRc`.
    ///
    /// This method takes an [`Ordering`] argument which describes the memory ordering of this
    /// operation. Possible values are [`SeqCst`], [`Acquire`] and [`Relaxed`].
    ///
    /// Note that the returned pointer cannot be dereferenced safely, becuase it is protected by
    /// neither a SMR nor a reference count. To dereference, use [`AtomicRc::load`] method instead.
    ///
    /// # Panics
    ///
    /// Panics if `order` is [`Release`] or [`AcqRel`].
    #[inline]
    pub fn load_raw(&self, order: Ordering) -> TaggedCnt<T> {
        self.link.load(order)
    }

    /// Loads a [`Snapshot`] pointer from this `AtomicRc`.
    ///
    /// This method takes an [`Ordering`] argument which describes the memory ordering of this
    /// operation. Possible values are [`SeqCst`], [`Acquire`] and [`Relaxed`].
    ///
    /// # Panics
    ///
    /// Panics if `order` is [`Release`] or [`AcqRel`].
    #[inline]
    pub fn load<'g>(&self, order: Ordering, cs: &'g Cs) -> Snapshot<'g, T> {
        Snapshot::from_raw(self.load_raw(order), cs)
    }

    /// Stores an [`Rc`] pointer into this `AtomicRc`.
    ///
    /// This method takes an [`Ordering`] argument which describes the memory ordering of
    /// this operation.
    #[inline]
    pub fn store(&self, ptr: Rc<T>, order: Ordering, cs: &Cs) {
        let new_ptr = ptr.as_ptr();
        let old_ptr = self.link.swap(new_ptr.with_timestamp(), order);
        // Skip decrementing a strong count of the inserted pointer.
        forget(ptr);
        unsafe {
            // Did not use `Rc::drop`, to reuse the given `cs`.
            if let Some(cnt) = old_ptr.as_raw().as_mut() {
                RcInner::decrement_strong(cnt, 1, Some(cs));
            }
        }
    }

    /// Stores a [`Snapshot`] or [`Rc`] pointer into this `AtomicRc`,
    /// returning the previous [`Rc`].
    ///
    /// This method takes an [`Ordering`] argument which describes the memory ordering of
    /// this operation.
    #[inline(always)]
    pub fn swap(&self, new: Rc<T>, order: Ordering) -> Rc<T> {
        let new_ptr = new.into_raw();
        let old_ptr = self.link.swap(new_ptr.with_timestamp(), order);
        Rc::from_raw(old_ptr)
    }

    /// Stores the [`Rc`] pointer `desired` into the atomic pointer if the current value is the
    /// same as `expected` [`Snapshot`] pointer. The tag is also taken into account,
    /// so two pointers to the same object, but with different tags, will not be considered equal.
    ///
    /// The return value is a result indicating whether the desired pointer was written.
    /// On success the pointer that was in this `AtomicRc` is returned.
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
    pub fn compare_exchange<'g>(
        &self,
        expected: Snapshot<'g, T>,
        desired: Rc<T>,
        success: Ordering,
        failure: Ordering,
        cs: &'g Cs,
    ) -> Result<Rc<T>, CompareExchangeErrorRc<'g, T, Rc<T>>> {
        let mut expected_ptr = expected.as_ptr();
        let desired_ptr = desired.as_ptr().with_timestamp();
        loop {
            match self
                .link
                .compare_exchange(expected_ptr, desired_ptr, success, failure)
            {
                Ok(_) => {
                    // Skip decrementing a strong count of the inserted pointer.
                    forget(desired);
                    let rc = Rc::from_raw(expected_ptr);
                    return Ok(rc);
                }
                Err(current) => {
                    if current.with_high_tag(0) == expected_ptr.with_high_tag(0) {
                        expected_ptr = current;
                    } else {
                        let current = Snapshot::from_raw(current, cs);
                        return Err(CompareExchangeErrorRc { desired, current });
                    }
                }
            }
        }
    }

    /// Stores the [`Rc`] pointer `desired` into the atomic pointer if the current value is the
    /// same as `expected` [`Snapshot`] pointer. The tag is also taken into account,
    /// so two pointers to the same object, but with different tags, will not be considered equal.
    ///
    /// Unlike [`AtomicRc::compare_exchange`], this method is allowed to spuriously fail
    /// even when comparison succeeds, which can result in more efficient code on some platforms.
    /// The return value is a result indicating whether the desired pointer was written.
    /// On success the pointer that was in this `AtomicRc` is returned.
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
    pub fn compare_exchange_weak<'g>(
        &self,
        expected: Snapshot<'g, T>,
        desired: Rc<T>,
        success: Ordering,
        failure: Ordering,
        cs: &'g Cs,
    ) -> Result<Rc<T>, CompareExchangeErrorRc<'g, T, Rc<T>>> {
        let mut expected_ptr = expected.as_ptr();
        let desired_ptr = desired.as_ptr().with_timestamp();
        loop {
            match self
                .link
                .compare_exchange_weak(expected_ptr, desired_ptr, success, failure)
            {
                Ok(_) => {
                    // Skip decrementing a strong count of the inserted pointer.
                    forget(desired);
                    let rc = Rc::from_raw(expected_ptr);
                    return Ok(rc);
                }
                Err(current) => {
                    if current.with_high_tag(0) == expected_ptr.with_high_tag(0) {
                        expected_ptr = current;
                    } else {
                        let current = Snapshot::from_raw(current, cs);
                        return Err(CompareExchangeErrorRc { desired, current });
                    }
                }
            }
        }
    }

    /// Overwrites the tag value `desired_tag` to the atomic pointer if the current value is the
    /// same as `expected` [`Snapshot`] pointer. The tag is also taken into account,
    /// so two pointers to the same object, but with different tags, will not be considered equal.
    ///
    /// If the `desired_tag` uses more bits than the unused least significant bits of the pointer
    /// to `T`, it will be truncated to be fit.
    ///
    /// The return value is a result indicating whether the desired pointer was written.
    /// On success the pointer that was in this `AtomicRc` is returned.
    /// On failure the actual current value and a desired pointer to write are returned.
    /// For both cases, the ownership of `expected` is returned by a dedicated field.
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
    pub fn compare_exchange_tag<'g>(
        &self,
        expected: Snapshot<'g, T>,
        desired_tag: usize,
        success: Ordering,
        failure: Ordering,
        cs: &'g Cs,
    ) -> Result<Snapshot<'g, T>, CompareExchangeErrorRc<'g, T, Snapshot<'g, T>>> {
        let mut expected_raw = expected.as_ptr();
        let desired_raw = expected_raw.with_tag(desired_tag).with_timestamp();
        loop {
            match self
                .link
                .compare_exchange(expected_raw, desired_raw, success, failure)
            {
                Ok(current) => return Ok(Snapshot::from_raw(current, cs)),
                Err(current) => {
                    if current.with_high_tag(0) == expected_raw.with_high_tag(0) {
                        expected_raw = current;
                    } else {
                        return Err(CompareExchangeErrorRc {
                            desired: Snapshot::from_raw(desired_raw, cs),
                            current: Snapshot::from_raw(current, cs),
                        });
                    }
                }
            }
        }
    }

    /// Takes an underlying [`Rc`] from this [`AtomicRc`], leaving a null pointer.
    #[inline]
    pub fn take(&mut self) -> Rc<T> {
        Rc::from_raw(core::mem::take(self.link.get_mut()))
    }
}

impl<T: RcObject> Drop for AtomicRc<T> {
    #[inline(always)]
    fn drop(&mut self) {
        unsafe {
            let ptr = self.link.load(Relaxed);
            if let Some(cnt) = ptr.as_raw().as_mut() {
                RcInner::decrement_strong(cnt, 1, None);
            }
        }
    }
}

impl<T: RcObject> Default for AtomicRc<T> {
    #[inline(always)]
    fn default() -> Self {
        Self::null()
    }
}

impl<T: RcObject> From<Rc<T>> for AtomicRc<T> {
    #[inline]
    fn from(value: Rc<T>) -> Self {
        let ptr = value.into_raw();
        Self {
            link: Atomic::new(ptr),
            _marker: PhantomData,
        }
    }
}

/// A smart pointer for reference-counted pointer to an object of type `T`.
///
/// Unlike [`Snapshot`] pointer, This pointer owns a strong reference count by itself, preventing
/// reclamation by the backend EBR. When `T` implements [`Send`] and [`Sync`], [`Rc<T>`] also
/// implements these traits.
///
/// The pointer must be properly aligned. Since it is aligned, a tag can be stored into the unused
/// least significant bits of the address. For example, the tag for a pointer to a sized type `T`
/// should be less than `(1 << align_of::<T>().trailing_zeros())`.
pub struct Rc<T: RcObject> {
    ptr: TaggedCnt<T>,
    _marker: PhantomData<T>,
}

unsafe impl<T: RcObject + Send + Sync> Send for Rc<T> {}
unsafe impl<T: RcObject + Send + Sync> Sync for Rc<T> {}

impl<T: RcObject> Clone for Rc<T> {
    fn clone(&self) -> Self {
        let rc = Self {
            ptr: self.ptr,
            _marker: PhantomData,
        };
        unsafe {
            if let Some(cnt) = rc.ptr.as_raw().as_ref() {
                cnt.increment_strong();
            }
        }
        rc
    }
}

impl<T: RcObject> Rc<T> {
    /// Constructs a new `Rc` representing a null pointer.
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

    /// Constructs a new `Rc` by allocating a new reference-couned object.
    #[inline(always)]
    pub fn new(obj: T) -> Self {
        let ptr = RcInner::alloc(obj, 1);
        Self {
            ptr: TaggedCnt::from(ptr),
            _marker: PhantomData,
        }
    }

    /// Constructs multiple [`Rc`]s that point to the same object,
    /// which is allocated as a new reference-counted object.
    ///
    /// This method is more efficient than calling [`Rc::new`] once and cloning multiple times
    /// because it is sufficient to set the reference counter only once, avoiding expensive
    /// read-modify-write operations.
    #[inline(always)]
    pub fn new_many<const N: usize>(obj: T) -> [Self; N] {
        let ptr = RcInner::alloc(obj, N as _);
        [(); N].map(|_| Self {
            ptr: TaggedCnt::from(ptr),
            _marker: PhantomData,
        })
    }

    /// Constructs an iterator that produces the [`Rc`]s that point to the same object,
    /// which is allocated as a new reference-counted object.
    ///
    /// This method is more efficient than calling [`Rc::new`] once and cloning multiple times
    /// because it is sufficient to set the reference counter only once, avoiding expensive
    /// read-modify-write operations.
    #[inline(always)]
    pub fn new_many_iter(obj: T, count: usize) -> NewRcIter<T> {
        let ptr = RcInner::alloc(obj, count as _);
        NewRcIter {
            remain: count,
            ptr: TaggedCnt::from(ptr),
        }
    }

    /// Constructs multiple [`Weak`]s that point to the current object.
    ///
    /// This method is more efficient than calling [`Rc::downgrade`] multiple times
    /// because it is sufficient to set the reference counter only once, avoiding expensive
    /// read-modify-write operations.
    #[inline]
    pub fn weak_many<const N: usize>(&self) -> [Weak<T>; N] {
        if let Some(cnt) = unsafe { self.as_ptr().as_raw().as_ref() } {
            cnt.increment_weak(N as u32);
        }
        array::from_fn(|_| Weak::null())
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
    pub(crate) fn into_raw(self) -> TaggedCnt<T> {
        let new_ptr = self.as_ptr();
        // Skip decrementing the ref count.
        forget(self);
        new_ptr
    }

    /// Consumes this pointer and release a strong reference count it was owning.
    ///
    /// This method is more efficient than just `Drop`ing the pointer. The `Drop` method
    /// checks whether the current thread is pinned and pin the thread if it is not.
    /// However, this method skips that procedure as it already requires `Cs` as an argument.
    #[inline]
    pub fn finalize(self, cs: &Cs) {
        unsafe {
            if let Some(cnt) = self.ptr.as_raw().as_mut() {
                RcInner::decrement_strong(cnt, 1, Some(cs));
            }
        }
        forget(self);
    }

    /// Creates a [`Weak`] pointer by incrementing the weak reference counter.
    #[inline]
    pub fn downgrade(&self) -> Weak<T> {
        unsafe {
            if let Some(cnt) = self.as_ptr().as_raw().as_ref() {
                cnt.increment_weak(1);
                return Weak::from_raw(self.ptr);
            }
        }
        Weak::null()
    }

    /// Creates a [`Snapshot`] pointer to the same object.
    #[inline]
    pub fn as_snapshot<'g>(&self, cs: &'g Cs) -> Snapshot<'g, T> {
        Snapshot::from_raw(self.ptr, cs)
    }

    /// Dereferences the pointer and returns an immutable reference.
    ///
    /// It does not check whether the pointer is null.
    ///
    /// # Safety
    ///
    /// The pointer must be a valid memory location to dereference.
    #[inline]
    pub unsafe fn deref(&self) -> &T {
        self.as_ptr().deref().data()
    }

    /// Dereferences the pointer and returns a mutable reference.
    ///
    /// It does not check whether the pointer is null.
    ///
    /// # Safety
    ///
    /// The pointer must be a valid memory location to dereference and
    /// other threads must not have references to the object.
    #[inline]
    pub unsafe fn deref_mut(&mut self) -> &mut T {
        self.as_ptr().deref_mut().data_mut()
    }

    /// Dereferences the pointer and returns an immutable reference if it is not null.
    #[inline]
    pub fn as_ref(&self) -> Option<&T> {
        if self.as_ptr().is_null() {
            None
        } else {
            Some(unsafe { self.deref() })
        }
    }

    /// Dereferences the pointer and returns a mutable reference if it is not null.
    ///
    /// # Safety
    ///
    /// Other threads must not have references to the object.
    #[inline]
    pub unsafe fn as_mut(&mut self) -> Option<&mut T> {
        if self.as_ptr().is_null() {
            None
        } else {
            Some(unsafe { self.deref_mut() })
        }
    }
}

impl<T: RcObject> Default for Rc<T> {
    #[inline]
    fn default() -> Self {
        Self::null()
    }
}

impl<T: RcObject> Drop for Rc<T> {
    #[inline(always)]
    fn drop(&mut self) {
        unsafe {
            if let Some(cnt) = self.ptr.as_raw().as_mut() {
                RcInner::decrement_strong(cnt, 1, None);
            }
        }
    }
}

impl<T: RcObject> PartialEq for Rc<T> {
    #[inline(always)]
    fn eq(&self, other: &Self) -> bool {
        self.ptr == other.ptr
    }
}

/// An iterator generating [`Rc`] pointers to the same and newly allocated object.
///
/// See [`Rc::new_many_iter`] for the purpose of this iterator.
pub struct NewRcIter<T: RcObject> {
    remain: usize,
    ptr: TaggedCnt<T>,
}

impl<T: RcObject> Iterator for NewRcIter<T> {
    type Item = Rc<T>;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.remain == 0 {
            None
        } else {
            self.remain -= 1;
            Some(Rc {
                ptr: self.ptr,
                _marker: PhantomData,
            })
        }
    }
}

impl<T: RcObject> NewRcIter<T> {
    /// Aborts generating [`Rc`]s.
    ///
    /// It decreases the strong reference counter as the remaining number of [`Rc`]s that are not
    /// generated yet.
    #[inline]
    pub fn abort(self, cs: &Cs) {
        if self.remain > 0 {
            unsafe {
                RcInner::decrement_strong(self.ptr.as_raw(), self.remain as _, Some(cs));
            };
        }
        forget(self);
    }
}

impl<T: RcObject> Drop for NewRcIter<T> {
    #[inline]
    fn drop(&mut self) {
        if self.remain > 0 {
            unsafe {
                RcInner::decrement_strong(self.ptr.as_raw(), self.remain as _, None);
            };
        }
    }
}

/// A local pointer protected by the backend EBR.
///
/// Unlike [`Rc`] pointer, This pointer does not own a strong reference count by itself.
/// Instead, it prevents the destruction of the pointer by the coarse-grained protection that EBR
/// provides. This pointer is valid for use only during the lifetime of EBR guard `'g`.
pub struct Snapshot<'g, T> {
    acquired: TaggedCnt<T>,
    _marker: PhantomData<&'g T>,
}

impl<'g, T> Clone for Snapshot<'g, T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<'g, T> Copy for Snapshot<'g, T> {}

impl<'g, T: RcObject> Snapshot<'g, T> {
    /// Creates an [`Rc`] pointer by incrementing the strong reference counter.
    #[inline]
    pub fn upgrade(self) -> Rc<T> {
        let rc = Rc {
            ptr: self.as_ptr(),
            _marker: PhantomData,
        };
        unsafe {
            if let Some(cnt) = rc.ptr.as_raw().as_ref() {
                cnt.increment_strong();
            }
        }
        rc
    }

    /// Creates a `Weak` pointer by incrementing the weak reference counter.
    #[inline]
    pub fn downgrade(self) -> Weak<T> {
        let weak = Weak::from_raw(self.as_ptr());
        weak.increment_weak();
        weak
    }

    /// Returns the tag stored within the pointer.
    #[inline(always)]
    pub fn tag(self) -> usize {
        self.as_ptr().tag()
    }

    /// Returns the same pointer, but tagged with `tag`. `tag` is truncated to be fit into the
    /// unused bits of the pointer to `T`.
    #[inline]
    pub fn with_tag(self, tag: usize) -> Self {
        let mut result = self;
        result.acquired = result.acquired.with_tag(tag);
        result
    }

    /// Dereferences the pointer and returns an immutable reference.
    ///
    /// It does not check whether the pointer is null.
    ///
    /// # Safety
    ///
    /// The pointer must be a valid memory location to dereference.
    #[inline]
    pub unsafe fn deref(self) -> &'g T {
        self.as_ptr().deref().data()
    }

    /// Dereferences the pointer and returns a mutable reference.
    ///
    /// It does not check whether the pointer is null.
    ///
    /// # Safety
    ///
    /// The pointer must be a valid memory location to dereference and
    /// other threads must not have references to the object.
    #[inline]
    pub unsafe fn deref_mut(self) -> &'g mut T {
        self.as_ptr().deref_mut().data_mut()
    }

    /// Dereferences the pointer and returns an immutable reference if it is not null.
    #[inline]
    pub fn as_ref(self) -> Option<&'g T> {
        if self.as_ptr().is_null() {
            None
        } else {
            Some(unsafe { self.deref() })
        }
    }

    /// Dereferences the pointer and returns a mutable reference if it is not null.
    ///
    /// # Safety
    ///
    /// Other threads must not have references to the object.
    #[inline]
    pub unsafe fn as_mut(self) -> Option<&'g mut T> {
        if self.as_ptr().is_null() {
            None
        } else {
            Some(unsafe { self.deref_mut() })
        }
    }
}

impl<'g, T> Snapshot<'g, T> {
    /// Constructs a new `Snapshot` representing a null pointer.
    #[inline(always)]
    pub fn null() -> Self {
        Self {
            acquired: Tagged::null(),
            _marker: PhantomData,
        }
    }

    #[inline]
    pub(crate) fn from_raw(acquired: TaggedCnt<T>, _: &'g Cs) -> Self {
        Self {
            acquired,
            _marker: PhantomData,
        }
    }
}

impl<'g, T: RcObject> Default for Snapshot<'g, T> {
    #[inline]
    fn default() -> Self {
        Self::null()
    }
}

impl<'g, T> PartialEq for Snapshot<'g, T> {
    #[inline(always)]
    fn eq(&self, other: &Self) -> bool {
        self.acquired.eq(&other.acquired)
    }
}

impl<T: RcObject> Pointer<T> for Rc<T> {
    #[inline]
    fn as_ptr(&self) -> TaggedCnt<T> {
        self.ptr
    }
}

impl<'g, T> Pointer<T> for Snapshot<'g, T> {
    #[inline]
    fn as_ptr(&self) -> TaggedCnt<T> {
        self.acquired
    }
}
