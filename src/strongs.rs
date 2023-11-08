use std::{
    marker::PhantomData,
    mem::{self, forget},
    sync::atomic::{AtomicUsize, Ordering},
};

use atomic::Atomic;
use static_assertions::const_assert;

use crate::{Acquired, AtomicWeak, Cs, Pointer, RcInner, Tagged, TaggedCnt, Weak};

pub trait GraphNode<C: Cs + ?Sized> {
    const UNIQUE_OUTDEGREE: bool;

    /// Returns `Rc`s in this node.
    /// It is safe to return less than the actual amount of `Rc`s.
    fn pop_outgoings(&self) -> Vec<Rc<Self, C>>
    where
        Self: Sized;

    fn pop_unique(&self) -> Rc<Self, C>
    where
        Self: Sized;
}

impl<T> Tagged<RcInner<T>> {
    fn with_timestamp<C: Cs>(self) -> Self {
        if self.is_null() {
            self
        } else {
            self.with_high_tag(C::timestamp().unwrap_or(0))
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

pub struct AtomicRc<T: GraphNode<C>, C: Cs> {
    link: Atomic<TaggedCnt<T>>,
    _marker: PhantomData<(T, *const C)>,
}

unsafe impl<T: GraphNode<C> + Send + Sync, C: Cs> Send for AtomicRc<T, C> {}
unsafe impl<T: GraphNode<C> + Send + Sync, C: Cs> Sync for AtomicRc<T, C> {}

// Ensure that TaggedPtr<T> is 8-byte long,
// so that lock-free atomic operations are possible.
const_assert!(Atomic::<TaggedCnt<u8>>::is_lock_free());
const_assert!(mem::size_of::<TaggedCnt<u8>>() == mem::size_of::<usize>());
const_assert!(mem::size_of::<Atomic<TaggedCnt<u8>>>() == mem::size_of::<AtomicUsize>());

impl<T: GraphNode<C>, C: Cs> AtomicRc<T, C> {
    #[inline(always)]
    pub fn new(obj: T) -> Self {
        Self {
            link: Atomic::new(Rc::<T, C>::new(obj).into_raw()),
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
    pub fn load_ss(&self, cs: &C) -> Snapshot<T, C> {
        let mut result = Snapshot::new();
        result.load(self, cs);
        result
    }

    #[inline]
    pub fn store<P: StrongPtr<T, C>>(&self, ptr: P, order: Ordering, cs: &C) {
        let ptr = ptr.into_rc();
        let new_ptr = ptr.as_ptr();
        let old_ptr = self.link.swap(new_ptr.with_timestamp::<C>(), order);
        // Skip decrementing a strong count of the inserted pointer.
        forget(ptr);
        unsafe {
            // Did not use `Rc::drop`, to reuse the given `cs`.
            if let Some(cnt) = old_ptr.as_raw().as_mut() {
                C::decrement_strong(cnt, 1, Some(cs));
            }
        }
    }

    /// Swaps the currently stored shared pointer with the given shared pointer.
    /// This operation is thread-safe.
    /// (It is equivalent to `exchange` from the original implementation.)
    #[inline(always)]
    pub fn swap(&self, new: Rc<T, C>, order: Ordering) -> Rc<T, C> {
        let new_ptr = new.into_raw();
        let old_ptr = self.link.swap(new_ptr.with_timestamp::<C>(), order);
        Rc::from_raw(old_ptr)
    }

    /// Atomically compares the underlying pointer with expected, and if they refer to
    /// the same managed object, replaces the current pointer with a copy of desired
    /// (incrementing its reference count) and returns true. Otherwise, returns false.
    #[inline(always)]
    pub fn compare_exchange(
        &self,
        mut expected: TaggedCnt<T>,
        desired: Rc<T, C>,
        success: Ordering,
        failure: Ordering,
        _: &C,
    ) -> Result<Rc<T, C>, CompareExchangeErrorRc<T, Rc<T, C>>> {
        let desired_ptr = desired.as_ptr().with_timestamp::<C>();
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
        desired: Rc<T, C>,
        success: Ordering,
        failure: Ordering,
        _: &C,
    ) -> Result<Rc<T, C>, CompareExchangeErrorRc<T, Rc<T, C>>> {
        match self.link.compare_exchange_weak(
            expected,
            desired.as_ptr().with_timestamp::<C>(),
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
        _: &C,
    ) -> Result<TaggedCnt<T>, CompareExchangeErrorRc<T, TaggedCnt<T>>>
    where
        P: StrongPtr<T, C>,
    {
        let mut expected = expected.as_ptr();
        let desired = expected.with_tag(desired_tag).with_timestamp::<C>();
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
        mut desired: Rc<T, C>,
        current_snap: &mut Snapshot<T, C>,
        success: Ordering,
        failure: Ordering,
        cs: &C,
    ) -> Result<Rc<T, C>, CompareExchangeErrorRc<T, Rc<T, C>>> {
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
    pub unsafe fn into_inner(self) -> Option<T> {
        let ptr = self.link.load(Ordering::Relaxed).as_raw();
        forget(self);

        if let Some(cnt) = ptr.as_mut() {
            if cnt.strong.load(Ordering::Relaxed) == 1 {
                return Some(C::own_object(ptr).into_inner());
            }
            C::decrement_strong(cnt, 1, Some(&C::unprotected()));
        }
        return None;
    }
}

impl<T: GraphNode<C>, C: Cs> Drop for AtomicRc<T, C> {
    #[inline(always)]
    fn drop(&mut self) {
        unsafe {
            let ptr = self.link.load(Ordering::Relaxed);
            if let Some(cnt) = ptr.as_raw().as_mut() {
                C::decrement_strong(cnt, 1, None);
            }
        }
    }
}

impl<T: GraphNode<C>, C: Cs> Default for AtomicRc<T, C> {
    #[inline(always)]
    fn default() -> Self {
        Self::null()
    }
}

impl<T: GraphNode<C>, C: Cs> From<Rc<T, C>> for AtomicRc<T, C> {
    #[inline]
    fn from(value: Rc<T, C>) -> Self {
        let ptr = value.into_raw();
        Self {
            link: Atomic::new(ptr),
            _marker: PhantomData,
        }
    }
}

pub struct Rc<T: GraphNode<C>, C: Cs + ?Sized> {
    ptr: TaggedCnt<T>,
    _marker: PhantomData<(T, *const C)>,
}

unsafe impl<T: GraphNode<C> + Send + Sync, C: Cs> Send for Rc<T, C> {}
unsafe impl<T: GraphNode<C> + Send + Sync, C: Cs> Sync for Rc<T, C> {}

impl<T: GraphNode<C>, C: Cs> Rc<T, C> {
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
        let ptr = C::create_object(obj, 1);
        Self {
            ptr: TaggedCnt::new(ptr),
            _marker: PhantomData,
        }
    }

    #[inline(always)]
    pub fn new_many<const N: usize>(obj: T) -> [Self; N] {
        let ptr = C::create_object(obj, N as _);
        [(); N].map(|_| Self {
            ptr: TaggedCnt::new(ptr),
            _marker: PhantomData,
        })
    }

    #[inline(always)]
    pub fn new_many_iter(obj: T, count: usize) -> NewRcIter<T, C> {
        let ptr = C::create_object(obj, count as _);
        NewRcIter {
            remain: count,
            ptr: TaggedCnt::new(ptr),
            _marker: PhantomData,
        }
    }

    #[inline(always)]
    pub fn clone(&self) -> Self {
        let rc = Self {
            ptr: self.ptr,
            _marker: PhantomData,
        };
        unsafe {
            if let Some(cnt) = rc.ptr.as_raw().as_ref() {
                C::increment_strong(cnt);
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
    pub unsafe fn into_inner(self) -> Option<T> {
        let ptr = self.ptr.as_raw();
        forget(self);

        if let Some(cnt) = ptr.as_mut() {
            if cnt.strong.load(Ordering::Relaxed) == 1 {
                return Some(C::own_object(ptr).into_inner());
            }
            C::decrement_strong(cnt, 1, Some(&C::unprotected()));
        }
        return None;
    }

    #[inline]
    pub unsafe fn into_inner_unchecked(self) -> T {
        let ptr = self.ptr.as_raw();
        forget(self);
        C::own_object(ptr).into_inner()
    }

    #[inline]
    pub fn finalize(self, cs: &C) {
        unsafe {
            if let Some(cnt) = self.ptr.as_raw().as_mut() {
                C::decrement_strong(cnt, 1, Some(cs));
            }
        }
        forget(self);
    }
}

impl<T: GraphNode<C>, C: Cs> Default for Rc<T, C> {
    #[inline]
    fn default() -> Self {
        Self::null()
    }
}

impl<T: GraphNode<C>, C: Cs + ?Sized> Drop for Rc<T, C> {
    #[inline(always)]
    fn drop(&mut self) {
        unsafe {
            if let Some(cnt) = self.ptr.as_raw().as_mut() {
                C::decrement_strong(cnt, 1, None);
            }
        }
    }
}

impl<T: GraphNode<C>, C: Cs> PartialEq for Rc<T, C> {
    #[inline(always)]
    fn eq(&self, other: &Self) -> bool {
        self.ptr == other.ptr
    }
}

pub struct NewRcIter<T: GraphNode<C>, C: Cs> {
    remain: usize,
    ptr: TaggedCnt<T>,
    _marker: PhantomData<(T, *const C)>,
}

impl<T: GraphNode<C>, C: Cs> Iterator for NewRcIter<T, C> {
    type Item = Rc<T, C>;

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

impl<T: GraphNode<C>, C: Cs> NewRcIter<T, C> {
    #[inline]
    pub fn halt(mut self, cs: &C) {
        if self.remain > 0 {
            unsafe { C::decrement_strong(self.ptr.deref_mut(), self.remain as _, Some(cs)) };
        }
        forget(self);
    }
}

impl<T: GraphNode<C>, C: Cs> Drop for NewRcIter<T, C> {
    #[inline]
    fn drop(&mut self) {
        if self.remain > 0 {
            unsafe { C::decrement_strong(self.ptr.deref_mut(), self.remain as _, None) };
        }
    }
}

pub struct Snapshot<T, C: Cs> {
    // Hint: `C::Acquired` is usually a wrapper struct containing `TaggedCnt`.
    acquired: C::RawShield<T>,
}

impl<T, C: Cs> Clone for Snapshot<T, C>
where
    C::RawShield<T>: Clone,
{
    fn clone(&self) -> Self {
        Self {
            acquired: self.acquired.clone(),
        }
    }
}

impl<T, C: Cs> Copy for Snapshot<T, C> where C::RawShield<T>: Copy {}

impl<T: GraphNode<C>, C: Cs> Snapshot<T, C> {
    #[inline(always)]
    pub fn new() -> Self {
        Self {
            acquired: <C as Cs>::RawShield::null(),
        }
    }

    #[inline]
    pub fn load(&mut self, from: &AtomicRc<T, C>, cs: &C) {
        cs.acquire(|order| from.load(order), &mut self.acquired);
    }

    #[inline]
    pub fn load_from_weak(&mut self, from: &AtomicWeak<T, C>, cs: &C) {
        loop {
            let ptr = cs.acquire(|order| from.load(order), &mut self.acquired);

            if !ptr.is_null() && unsafe { C::non_zero(ptr.deref()) } {
                return;
            } else {
                self.acquired.clear();
                if ptr.is_null() || ptr == from.link.load(Ordering::Acquire) {
                    return;
                }
            }
        }
    }

    #[inline]
    pub fn protect(&mut self, ptr: &Rc<T, C>, cs: &C) {
        cs.reserve(ptr.as_ptr(), &mut self.acquired);
    }

    #[inline]
    pub fn protect_weak(&mut self, ptr: &Weak<T, C>, cs: &C) -> bool {
        cs.reserve(ptr.as_ptr(), &mut self.acquired);
        if !self.acquired.is_null() {
            if !C::non_zero(unsafe { self.acquired.as_ptr().deref() }) {
                self.acquired.clear();
                return false;
            }
        }
        true
    }

    #[inline]
    pub fn upgrade(&self) -> Rc<T, C> {
        let rc = Rc {
            ptr: self.as_ptr(),
            _marker: PhantomData,
        };
        unsafe {
            if let Some(cnt) = rc.ptr.as_raw().as_ref() {
                C::increment_strong(cnt);
            }
        }
        rc
    }

    #[inline(always)]
    pub fn tag(&self) -> usize {
        self.as_ptr().tag()
    }

    #[inline]
    pub fn set_tag(&mut self, tag: usize) {
        self.acquired.set_tag(tag);
    }

    #[inline]
    pub fn with_tag<'s>(&'s self, tag: usize) -> TaggedSnapshot<'s, T, C> {
        TaggedSnapshot { inner: self, tag }
    }

    #[inline]
    pub fn clear(&mut self) {
        self.acquired.clear();
    }

    #[inline(always)]
    pub fn swap(p1: &mut Self, p2: &mut Self) {
        <C::RawShield<T> as Acquired<T>>::swap(&mut p1.acquired, &mut p2.acquired)
    }

    #[inline]
    pub unsafe fn copy_to(&self, other: &mut Self) {
        self.acquired.copy_to(&mut other.acquired);
    }

    #[inline]
    pub fn loan(&self) -> (Rc<T, C>, Debt<T, C>) {
        let ptr = self.acquired.as_ptr();
        (
            Rc::from_raw(ptr),
            Debt {
                ptr,
                _marker: PhantomData,
            },
        )
    }
}

impl<T: GraphNode<C>, C: Cs> Default for Snapshot<T, C> {
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

impl<T, C: Cs> PartialEq for Snapshot<T, C> {
    #[inline(always)]
    fn eq(&self, other: &Self) -> bool {
        self.acquired.eq(&other.acquired)
    }
}

/// A reference of a [`Snapshot`] with a overwriting tag value.
pub struct TaggedSnapshot<'s, T, C: Cs> {
    pub(crate) inner: &'s Snapshot<T, C>,
    pub(crate) tag: usize,
}

impl<T: GraphNode<C>, C: Cs> Pointer<T> for Rc<T, C> {
    #[inline]
    fn as_ptr(&self) -> TaggedCnt<T> {
        self.ptr
    }
}

impl<T, C: Cs> Pointer<T> for Snapshot<T, C> {
    #[inline]
    fn as_ptr(&self) -> TaggedCnt<T> {
        self.acquired.as_ptr()
    }
}

impl<T, C: Cs> Pointer<T> for &Snapshot<T, C> {
    #[inline]
    fn as_ptr(&self) -> TaggedCnt<T> {
        self.acquired.as_ptr()
    }
}

impl<'s, T, C: Cs> Pointer<T> for TaggedSnapshot<'s, T, C> {
    #[inline]
    fn as_ptr(&self) -> TaggedCnt<T> {
        self.inner.acquired.as_ptr().with_tag(self.tag)
    }
}

pub struct Debt<T: GraphNode<C>, C: Cs> {
    ptr: TaggedCnt<T>,
    _marker: PhantomData<*mut C>,
}

impl<T: GraphNode<C>, C: Cs> Drop for Debt<T, C> {
    #[inline]
    fn drop(&mut self) {
        panic!("Debt is not repaied!");
    }
}

impl<T: GraphNode<C>, C: Cs> Debt<T, C> {
    #[inline]
    pub fn repay(self, rc: Rc<T, C>) {
        assert!(self.ptr == rc.ptr);
        forget(self);
        forget(rc);
    }
}

pub trait StrongPtr<T, C: Cs>: Pointer<T> {
    const OWNS_REF_COUNT: bool;

    /// Consumes `self` and constructs a [`Rc`] pointing to the same object.
    ///
    /// If `self` is already [`Rc`], it will not touch the reference count.
    #[inline]
    fn into_rc(self) -> Rc<T, C>
    where
        T: GraphNode<C>,
        Self: Sized,
    {
        let rc = Rc::from_raw(self.as_ptr());
        if Self::OWNS_REF_COUNT {
            // As we have a reference count already, we don't have to do anything, but
            // prevent calling a destructor which decrements it.
            forget(self);
        } else if let Some(cnt) = unsafe { self.as_ptr().as_raw().as_ref() } {
            C::increment_strong(cnt);
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

impl<T: GraphNode<C>, C: Cs> StrongPtr<T, C> for Rc<T, C> {
    const OWNS_REF_COUNT: bool = true;
}

impl<T, C: Cs> StrongPtr<T, C> for Snapshot<T, C> {
    const OWNS_REF_COUNT: bool = false;
}

impl<T, C: Cs> StrongPtr<T, C> for &Snapshot<T, C> {
    const OWNS_REF_COUNT: bool = false;
}

impl<'s, T, C: Cs> StrongPtr<T, C> for TaggedSnapshot<'s, T, C> {
    const OWNS_REF_COUNT: bool = false;
}
