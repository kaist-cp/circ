use std::{
    array,
    marker::PhantomData,
    mem::{self, forget, replace},
    sync::atomic::{AtomicUsize, Ordering},
};

use atomic::Atomic;
use static_assertions::const_assert;

use crate::{global_epoch, AtomicWeak, Cs, Pointer, RcInner, Tagged, TaggedCnt, Weak};

pub trait GraphNode {
    /// Returns `Rc`s in this node.
    /// It is safe to return less than the actual amount of `Rc`s.
    fn pop_outgoings(&mut self, result: &mut Vec<Rc<Self>>)
    where
        Self: Sized;
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
pub struct CompareExchangeErrorRc<T, P> {
    /// The `desired` which was given as a parameter of `compare_exchange`.
    pub desired: P,
    /// The current pointer value inside the atomic pointer.
    pub current: TaggedCnt<T>,
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
    pub fn load(&self, order: Ordering) -> TaggedCnt<T> {
        self.link.load(order)
    }

    #[inline]
    pub fn load_ss(&self, cs: &Cs) -> Snapshot<T> {
        let mut result = Snapshot::new();
        result.load(self, cs);
        result
    }

    #[inline]
    pub fn store<P: StrongPtr<T>>(&self, ptr: P, order: Ordering, cs: &Cs) {
        let ptr = ptr.into_rc();
        let new_ptr = ptr.as_ptr();
        let old_ptr = self.link.swap(new_ptr.with_timestamp(), order);
        // Skip decrementing a strong count of the inserted pointer.
        forget(ptr);
        unsafe {
            // Did not use `Rc::drop`, to reuse the given `cs`.
            if let Some(cnt) = old_ptr.as_raw().as_mut() {
                cnt.decrement_strong(1, Some(cs));
            }
        }
    }

    /// Swaps the currently stored shared pointer with the given shared pointer.
    /// This operation is thread-safe.
    /// (It is equivalent to `exchange` from the original implementation.)
    #[inline(always)]
    pub fn swap(&self, new: Rc<T>, order: Ordering) -> Rc<T> {
        let new_ptr = new.into_raw();
        let old_ptr = self.link.swap(new_ptr.with_timestamp(), order);
        Rc::from_raw(old_ptr)
    }

    /// Atomically compares the underlying pointer with expected, and if they refer to
    /// the same managed object, replaces the current pointer with a copy of desired
    /// (incrementing its reference count) and returns true. Otherwise, returns false.
    #[inline(always)]
    pub fn compare_exchange(
        &self,
        mut expected: TaggedCnt<T>,
        desired: Rc<T>,
        success: Ordering,
        failure: Ordering,
        _: &Cs,
    ) -> Result<Rc<T>, CompareExchangeErrorRc<T, Rc<T>>> {
        let desired_ptr = desired.as_ptr().with_timestamp();
        loop {
            match self
                .link
                .compare_exchange(expected, desired_ptr, success, failure)
            {
                Ok(_) => {
                    // Skip decrementing a strong count of the inserted pointer.
                    forget(desired);
                    let rc = Rc::from_raw(expected);
                    return Ok(rc);
                }
                Err(current) => {
                    if current.with_high_tag(0) == expected.with_high_tag(0) {
                        expected = current;
                    } else {
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
    pub fn compare_exchange_weak(
        &self,
        expected: TaggedCnt<T>,
        desired: Rc<T>,
        success: Ordering,
        failure: Ordering,
        _: &Cs,
    ) -> Result<Rc<T>, CompareExchangeErrorRc<T, Rc<T>>> {
        match self.link.compare_exchange_weak(
            expected,
            desired.as_ptr().with_timestamp(),
            success,
            failure,
        ) {
            Ok(_) => {
                // Skip decrementing a strong count of the inserted pointer.
                forget(desired);
                let rc = Rc::from_raw(expected);
                Ok(rc)
            }
            Err(current) => Err(CompareExchangeErrorRc { desired, current }),
        }
    }

    #[inline]
    pub fn compare_exchange_tag<P>(
        &self,
        expected: P,
        desired_tag: usize,
        success: Ordering,
        failure: Ordering,
        _: &Cs,
    ) -> Result<TaggedCnt<T>, CompareExchangeErrorRc<T, TaggedCnt<T>>>
    where
        P: StrongPtr<T>,
    {
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
    /// It is guaranteed that the current pointer on a failure is protected by `current_snap`.
    /// It is lock-free but not wait-free. Use `compare_exchange` for an wait-free implementation.
    #[inline(always)]
    pub fn compare_exchange_protecting_current(
        &self,
        expected: TaggedCnt<T>,
        mut desired: Rc<T>,
        current_snap: &mut Snapshot<T>,
        success: Ordering,
        failure: Ordering,
        cs: &Cs,
    ) -> Result<Rc<T>, CompareExchangeErrorRc<T, Rc<T>>> {
        loop {
            current_snap.load(self, cs);
            if current_snap.as_ptr() != expected {
                return Err(CompareExchangeErrorRc {
                    desired,
                    current: current_snap.as_ptr(),
                });
            }
            match self.compare_exchange(expected, desired, success, failure, cs) {
                Ok(rc) => return Ok(rc),
                Err(e) => {
                    if e.current == current_snap.as_ptr() {
                        return Err(e);
                    } else {
                        desired = e.desired
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
                cnt.decrement_strong(1, None);
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
    pub fn clone(&self) -> Self {
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
                cnt.decrement_strong(1, Some(cs));
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
                cnt.decrement_strong(1, None);
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
    pub fn halt(mut self, cs: &Cs) {
        if self.remain > 0 {
            unsafe {
                self.ptr
                    .deref_mut()
                    .decrement_strong(self.remain as _, Some(cs))
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
                self.ptr
                    .deref_mut()
                    .decrement_strong(self.remain as _, None)
            };
        }
    }
}

pub struct Snapshot<T> {
    acquired: TaggedCnt<T>,
}

impl<T> Clone for Snapshot<T> {
    fn clone(&self) -> Self {
        Self {
            acquired: self.acquired.clone(),
        }
    }
}

impl<T> Copy for Snapshot<T> {}

impl<T: GraphNode> Snapshot<T> {
    /// TODO: add ordering
    #[inline]
    pub fn load(&mut self, from: &AtomicRc<T>, _: &Cs) {
        self.acquired = from.load(Ordering::Acquire);
    }

    #[inline]
    pub fn protect(&mut self, ptr: &Rc<T>, _: &Cs) {
        self.acquired = ptr.as_ptr();
    }

    #[inline]
    pub fn protect_weak(&mut self, ptr: &Weak<T>, _: &Cs) -> bool {
        self.acquired = ptr.as_ptr();
        if !self.acquired.is_null() {
            if !unsafe { self.acquired.deref() }.non_zero() {
                self.acquired = Tagged::null();
                return false;
            }
        }
        true
    }

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
    pub fn with_tag(self, tag: usize) -> Snapshot<T> {
        Self {
            acquired: self.acquired.with_tag(tag),
        }
    }
}

impl<T> Snapshot<T> {
    #[inline(always)]
    pub fn new() -> Self {
        Self {
            acquired: Tagged::null(),
        }
    }

    #[inline]
    pub fn load_from_weak(&mut self, from: &AtomicWeak<T>, _: &Cs) -> bool {
        loop {
            self.acquired = from.load(Ordering::Acquire);

            if self.acquired.is_null() || unsafe { self.acquired.deref().non_zero() } {
                return true;
            } else {
                let ptr = replace(&mut self.acquired, Tagged::null());
                if ptr == from.link.load(Ordering::Acquire) {
                    return false;
                }
            }
        }
    }
}

impl<T: GraphNode> Default for Snapshot<T> {
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

impl<T> PartialEq for Snapshot<T> {
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

impl<T> Pointer<T> for Snapshot<T> {
    #[inline]
    fn as_ptr(&self) -> TaggedCnt<T> {
        self.acquired
    }
}

impl<T> Pointer<T> for &Snapshot<T> {
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

    #[inline]
    unsafe fn deref<'g>(&self) -> &'g T {
        self.as_ptr().deref().data()
    }

    #[inline]
    unsafe fn deref_mut<'g>(&mut self) -> &'g mut T {
        self.as_ptr().deref_mut().data_mut()
    }

    #[inline]
    fn as_ref(&self) -> Option<&T> {
        if self.as_ptr().is_null() {
            None
        } else {
            Some(unsafe { self.deref() })
        }
    }

    #[inline]
    fn as_mut(&mut self) -> Option<&mut T> {
        if self.as_ptr().is_null() {
            None
        } else {
            Some(unsafe { self.deref_mut() })
        }
    }
}

impl<T: GraphNode> StrongPtr<T> for Rc<T> {
    const OWNS_REF_COUNT: bool = true;
}

impl<T> StrongPtr<T> for Snapshot<T> {
    const OWNS_REF_COUNT: bool = false;
}

impl<T> StrongPtr<T> for &Snapshot<T> {
    const OWNS_REF_COUNT: bool = false;
}
