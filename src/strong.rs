use std::{
    array,
    marker::PhantomData,
    mem::{self, forget},
    sync::atomic::{AtomicUsize, Ordering},
};

use atomic::Atomic;
use static_assertions::const_assert;

use crate::ebr_impl::{global_epoch, Cs, Tagged};
use crate::{Pointer, RcInner, TaggedCnt, Weak};

pub trait GraphNode: Sized {
    /// Returns `Rc`s in this node.
    /// It is safe to return less than the actual amount of `Rc`s.
    fn pop_outgoings(&mut self) -> Vec<Rc<Self>>;
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

/// A result of unsuccessful `compare_exchange`.
///
/// It returns the ownership of [`Rc`] pointer which was given as a parameter.
pub struct CompareExchangeErrorRc<'g, T, P> {
    /// The `desired` which was given as a parameter of `compare_exchange`.
    pub desired: P,
    /// The current pointer value inside the atomic pointer.
    pub current: Snapshot<'g, T>,
}

pub struct AtomicRc<T: GraphNode> {
    link: Atomic<TaggedCnt<T>>,
    _marker: PhantomData<T>,
}

unsafe impl<T: GraphNode + Send + Sync> Send for AtomicRc<T> {}
unsafe impl<T: GraphNode + Send + Sync> Sync for AtomicRc<T> {}

// Ensure that TaggedPtr<T> is 8-byte long,
// so that lock-free atomic operations are possible.
const_assert!(Atomic::<TaggedCnt<u8>>::is_lock_free());
const_assert!(mem::size_of::<TaggedCnt<u8>>() == mem::size_of::<usize>());
const_assert!(mem::size_of::<Atomic<TaggedCnt<u8>>>() == mem::size_of::<AtomicUsize>());

impl<T: GraphNode> AtomicRc<T> {
    #[inline(always)]
    pub fn new(obj: T) -> Self {
        Self {
            link: Atomic::new(Rc::<T>::new(obj).into_raw()),
            _marker: PhantomData,
        }
    }

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
    /// neither a SMR nor a reference count. To dereference, use `load` method of [`Snapshot`]
    /// instead.
    #[inline]
    pub fn load_raw(&self, order: Ordering) -> TaggedCnt<T> {
        self.link.load(order)
    }

    #[inline]
    pub fn load<'g>(&self, order: Ordering, cs: &'g Cs) -> Snapshot<'g, T> {
        Snapshot::from_raw(self.load_raw(order), cs)
    }

    #[inline]
    pub fn store(&self, ptr: impl StrongPtr<T>, order: Ordering, cs: &Cs) {
        let ptr = ptr.into_rc();
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

    /// Swaps the currently stored shared pointer with the given shared pointer.
    #[inline(always)]
    pub fn swap(&self, new: Rc<T>, order: Ordering) -> Rc<T> {
        let new_ptr = new.into_raw();
        let old_ptr = self.link.swap(new_ptr.with_timestamp(), order);
        Rc::from_raw(old_ptr)
    }

    /// Atomically compares the underlying pointer with expected, and if they refer to
    /// the same managed object, replaces the current pointer with a copy of desired
    /// (incrementing its reference count) and returns true. Otherwise, returns false.
    /// TODO: rename desired/expected to more Rust-like names.
    #[inline(always)]
    pub fn compare_exchange<'g>(
        &self,
        expected: impl StrongPtr<T>,
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

    /// Atomically compares the underlying pointer with expected, and if they refer to
    /// the same managed object, replaces the current pointer with a copy of desired
    /// (incrementing its reference count) and returns true. Otherwise, returns false.
    ///
    /// This function is allowed to spuriously fail even when the comparison succeeds.
    #[inline(always)]
    pub fn compare_exchange_weak<'g>(
        &self,
        expected: impl StrongPtr<T>,
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

    #[inline]
    pub fn compare_exchange_tag<'g>(
        &self,
        expected: impl StrongPtr<T>,
        desired_tag: usize,
        success: Ordering,
        failure: Ordering,
        cs: &'g Cs,
    ) -> Result<TaggedCnt<T>, CompareExchangeErrorRc<'g, T, TaggedCnt<T>>> {
        let mut expected = expected.as_ptr();
        let desired = expected.with_tag(desired_tag).with_timestamp();
        loop {
            match self
                .link
                .compare_exchange(expected, desired, success, failure)
            {
                Ok(current) => return Ok(current),
                Err(current) => {
                    if current.with_high_tag(0) == expected.with_high_tag(0) {
                        expected = current;
                    } else {
                        let current = Snapshot::from_raw(current, cs);
                        return Err(CompareExchangeErrorRc { desired, current });
                    }
                }
            }
        }
    }

    #[inline]
    pub fn take(&mut self) -> Rc<T> {
        let ptr = self.link.load(Ordering::Relaxed);
        self.link.store(Tagged::null(), Ordering::Relaxed);
        Rc::from_raw(ptr)
    }
}

impl<T: GraphNode> Drop for AtomicRc<T> {
    #[inline(always)]
    fn drop(&mut self) {
        unsafe {
            let ptr = self.link.load(Ordering::Relaxed);
            if let Some(cnt) = ptr.as_raw().as_mut() {
                RcInner::decrement_strong(cnt, 1, None);
            }
        }
    }
}

impl<T: GraphNode> Default for AtomicRc<T> {
    #[inline(always)]
    fn default() -> Self {
        Self::null()
    }
}

impl<T: GraphNode> From<Rc<T>> for AtomicRc<T> {
    #[inline]
    fn from(value: Rc<T>) -> Self {
        let ptr = value.into_raw();
        Self {
            link: Atomic::new(ptr),
            _marker: PhantomData,
        }
    }
}

pub struct Rc<T: GraphNode> {
    ptr: TaggedCnt<T>,
    _marker: PhantomData<T>,
}

unsafe impl<T: GraphNode + Send + Sync> Send for Rc<T> {}
unsafe impl<T: GraphNode + Send + Sync> Sync for Rc<T> {}

impl<T: GraphNode> Clone for Rc<T> {
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

impl<T: GraphNode> Rc<T> {
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
    pub fn new(obj: T) -> Self {
        let ptr = RcInner::alloc(obj, 1);
        Self {
            ptr: TaggedCnt::from(ptr),
            _marker: PhantomData,
        }
    }

    #[inline(always)]
    pub fn new_many<const N: usize>(obj: T) -> [Self; N] {
        let ptr = RcInner::alloc(obj, N as _);
        [(); N].map(|_| Self {
            ptr: TaggedCnt::from(ptr),
            _marker: PhantomData,
        })
    }

    #[inline(always)]
    pub fn new_many_iter(obj: T, count: usize) -> NewRcIter<T> {
        let ptr = RcInner::alloc(obj, count as _);
        NewRcIter {
            remain: count,
            ptr: TaggedCnt::from(ptr),
        }
    }

    #[inline]
    pub fn weak_many<const N: usize>(&self) -> [Weak<T>; N] {
        if let Some(cnt) = unsafe { self.as_ptr().as_raw().as_ref() } {
            cnt.increment_weak(N as u32);
        }
        array::from_fn(|_| Weak::null())
    }

    #[inline(always)]
    pub fn tag(&self) -> usize {
        self.ptr.tag()
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
    pub fn finalize(self, cs: &Cs) {
        unsafe {
            if let Some(cnt) = self.ptr.as_raw().as_mut() {
                RcInner::decrement_strong(cnt, 1, Some(cs));
            }
        }
        forget(self);
    }

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

    #[inline]
    pub fn as_snapshot<'g>(&self, cs: &'g Cs) -> Snapshot<'g, T> {
        Snapshot::from_raw(self.ptr, cs)
    }

    /// # Safety
    ///
    /// The pointer must be a valid memory location to dereference.
    #[inline]
    pub unsafe fn deref(&self) -> &T {
        self.as_ptr().deref().data()
    }

    /// # Safety
    ///
    /// The pointer must be a valid memory location to dereference and
    /// other threads must not have references to the object.
    #[inline]
    pub unsafe fn deref_mut(&mut self) -> &mut T {
        self.as_ptr().deref_mut().data_mut()
    }

    #[inline]
    pub fn as_ref(&self) -> Option<&T> {
        if self.as_ptr().is_null() {
            None
        } else {
            Some(unsafe { self.deref() })
        }
    }

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

impl<T: GraphNode> Default for Rc<T> {
    #[inline]
    fn default() -> Self {
        Self::null()
    }
}

impl<T: GraphNode> Drop for Rc<T> {
    #[inline(always)]
    fn drop(&mut self) {
        unsafe {
            if let Some(cnt) = self.ptr.as_raw().as_mut() {
                RcInner::decrement_strong(cnt, 1, None);
            }
        }
    }
}

impl<T: GraphNode> PartialEq for Rc<T> {
    #[inline(always)]
    fn eq(&self, other: &Self) -> bool {
        self.ptr == other.ptr
    }
}

pub struct NewRcIter<T: GraphNode> {
    remain: usize,
    ptr: TaggedCnt<T>,
}

impl<T: GraphNode> Iterator for NewRcIter<T> {
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

impl<T: GraphNode> NewRcIter<T> {
    #[inline]
    pub fn halt(self, cs: &Cs) {
        if self.remain > 0 {
            unsafe {
                RcInner::decrement_strong(self.ptr.as_raw(), self.remain as _, Some(cs));
            };
        }
        forget(self);
    }
}

impl<T: GraphNode> Drop for NewRcIter<T> {
    #[inline]
    fn drop(&mut self) {
        if self.remain > 0 {
            unsafe {
                RcInner::decrement_strong(self.ptr.as_raw(), self.remain as _, None);
            };
        }
    }
}

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

impl<'g, T: GraphNode> Snapshot<'g, T> {
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

    #[inline]
    pub fn downgrade(self) -> Weak<T> {
        let weak = Weak::from_raw(self.as_ptr());
        weak.increment_weak();
        weak
    }

    #[inline(always)]
    pub fn tag(self) -> usize {
        self.as_ptr().tag()
    }

    #[inline]
    pub fn with_tag(self, tag: usize) -> Self {
        let mut result = self;
        result.acquired = result.acquired.with_tag(tag);
        result
    }

    /// # Safety
    ///
    /// The pointer must be a valid memory location to dereference.
    #[inline]
    pub unsafe fn deref(self) -> &'g T {
        self.as_ptr().deref().data()
    }

    /// # Safety
    ///
    /// The pointer must be a valid memory location to dereference and
    /// other threads must not have references to the object.
    #[inline]
    pub unsafe fn deref_mut(self) -> &'g mut T {
        self.as_ptr().deref_mut().data_mut()
    }

    #[inline]
    pub fn as_ref(self) -> Option<&'g T> {
        if self.as_ptr().is_null() {
            None
        } else {
            Some(unsafe { self.deref() })
        }
    }

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

impl<'g, T: GraphNode> Default for Snapshot<'g, T> {
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

impl<T: GraphNode> Pointer<T> for Rc<T> {
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

pub trait StrongPtr<T>: Pointer<T> {
    const OWNS_REF_COUNT: bool;

    /// Consumes `self` and constructs a [`Rc`] pointing to the same object.
    ///
    /// If `self` is already [`Rc`], it will not touch the reference count.
    #[inline]
    fn into_rc(self) -> Rc<T>
    where
        T: GraphNode,
        Self: Sized,
    {
        let rc = Rc::from_raw(self.as_ptr());
        if Self::OWNS_REF_COUNT {
            // As we have a reference count already, we don't have to do anything, but
            // prevent calling a destructor which decrements it.
            forget(self);
        } else if let Some(cnt) = unsafe { self.as_ptr().as_raw().as_ref() } {
            cnt.increment_strong();
        }
        rc
    }
}

impl<T: GraphNode> StrongPtr<T> for Rc<T> {
    const OWNS_REF_COUNT: bool = true;
}

impl<'g, T> StrongPtr<T> for Snapshot<'g, T> {
    const OWNS_REF_COUNT: bool = false;
}
