use std::{
    marker::PhantomData,
    mem::{self, forget},
    sync::atomic::AtomicUsize,
};

use atomic::{Atomic, Ordering};
use static_assertions::const_assert;

use crate::{Acquired, AtomicWeak, Cs, Pointer, Tagged, TaggedCnt, Weak};

/// A result of unsuccessful `compare_exchange`.
///
/// It returns the ownership of [`Rc`] pointer which was given as a parameter.
pub struct CompareExchangeErrorRc<T, P> {
    /// The `desired` which was given as a parameter of `compare_exchange`.
    pub desired: P,
    /// The current pointer value inside the atomic pointer.
    pub current: TaggedCnt<T>,
}

pub struct AtomicRc<T, C: Cs> {
    link: Atomic<TaggedCnt<T>>,
    _marker: PhantomData<(T, *const C)>,
}

unsafe impl<T: Send + Sync, C: Cs> Send for AtomicRc<T, C> {}
unsafe impl<T: Send + Sync, C: Cs> Sync for AtomicRc<T, C> {}

// Ensure that TaggedPtr<T> is 8-byte long,
// so that lock-free atomic operations are possible.
const_assert!(Atomic::<TaggedCnt<u8>>::is_lock_free());
const_assert!(mem::size_of::<TaggedCnt<u8>>() == mem::size_of::<usize>());
const_assert!(mem::size_of::<Atomic<TaggedCnt<u8>>>() == mem::size_of::<AtomicUsize>());

impl<T, C: Cs> AtomicRc<T, C> {
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
    pub fn store<P: StrongPtr<T, C>>(&self, ptr: P, order: Ordering, cs: &C) {
        let new_ptr = ptr.as_ptr();
        ptr.into_ref_count();
        let old_ptr = self.link.swap(new_ptr, order);
        unsafe {
            if let Some(cnt) = old_ptr.as_raw().as_mut() {
                cnt.decrement_strong(Some(cs));
            }
        }
    }

    /// Swaps the currently stored shared pointer with the given shared pointer.
    /// This operation is thread-safe.
    /// (It is equivalent to `exchange` from the original implementation.)
    #[inline(always)]
    pub fn swap(&self, new: Rc<T, C>, order: Ordering, _: &C) -> Rc<T, C> {
        let new_ptr = new.into_raw();
        Rc::from_raw(self.link.swap(new_ptr, order))
    }

    /// Atomically compares the underlying pointer with expected, and if they refer to
    /// the same managed object, replaces the current pointer with a copy of desired
    /// (incrementing its reference count) and returns true. Otherwise, returns false.
    #[inline(always)]
    pub fn compare_exchange<'g, P>(
        &self,
        expected: TaggedCnt<T>,
        desired: P,
        success: Ordering,
        failure: Ordering,
        _: &'g C,
    ) -> Result<Rc<T, C>, CompareExchangeErrorRc<T, P>>
    where
        P: StrongPtr<T, C>,
    {
        match self
            .link
            .compare_exchange(expected, desired.as_ptr(), success, failure)
        {
            Ok(_) => {
                let rc = Rc::from_raw(expected);
                // Here, `into_ref_count` increment the reference count of `desired` only if `desired`
                // doesn't own a reference counter.
                //
                // If `desired` is `Rc`, semantically the ownership of the reference count from
                // `desired` is moved to `self`. Because of this reason, we must skip decrementing
                // the reference count of `desired`.
                desired.into_ref_count();
                Ok(rc)
            }
            Err(current) => Err(CompareExchangeErrorRc { desired, current }),
        }
    }

    #[inline]
    pub fn compare_exchange_tag<'g, P>(
        &self,
        expected: P,
        desired_tag: usize,
        success: Ordering,
        failure: Ordering,
        _: &'g C,
    ) -> Result<TaggedCnt<T>, CompareExchangeErrorRc<T, TaggedCnt<T>>>
    where
        P: StrongPtr<T, C>,
    {
        let desired = expected.as_ptr().with_tag(desired_tag);
        match self
            .link
            .compare_exchange(expected.as_ptr(), desired, success, failure)
        {
            Ok(current) => Ok(current),
            Err(current) => Err(CompareExchangeErrorRc { desired, current }),
        }
    }

    /// Atomically compares the underlying pointer with expected, and if they refer to
    /// the same managed object, replaces the current pointer with a copy of desired
    /// (incrementing its reference count) and returns true. Otherwise, returns false.
    ///
    /// It is guaranteed that the current pointer on a failure is protected by `current_snap`.
    /// It is lock-free but not wait-free. Use `compare_exchange` for an wait-free implementation.
    #[inline(always)]
    pub fn compare_exchange_protecting_current<'g, P>(
        &self,
        expected: TaggedCnt<T>,
        mut desired: P,
        current_snap: &mut Snapshot<T, C>,
        success: Ordering,
        failure: Ordering,
        cs: &'g C,
    ) -> Result<Rc<T, C>, CompareExchangeErrorRc<T, P>>
    where
        P: StrongPtr<T, C>,
    {
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
                        desired = e.desired;
                    }
                }
            }
        }
    }

    #[inline(always)]
    pub fn fetch_or<'g>(&self, tag: usize, order: Ordering, _: &'g C) -> TaggedCnt<T> {
        // HACK: The size and alignment of `Atomic<TaggedCnt<T>>` will be same with `AtomicUsize`.
        // The equality of the sizes is checked by `const_assert!`.
        let link = unsafe { &*(&self.link as *const _ as *const AtomicUsize) };
        let prev = link.fetch_or(tag, order);
        TaggedCnt::new(prev as *mut _)
    }

    #[inline]
    pub unsafe fn into_inner(self) -> Option<T> {
        let ptr = self.link.load(Ordering::Relaxed).as_raw();
        forget(self);

        if let Some(cnt) = ptr.as_mut() {
            if cnt.strong.load(Ordering::Relaxed) == 1 {
                return Some(C::own_object(ptr).into_inner());
            }
            cnt.decrement_strong(Some(&C::unprotected()));
        }
        return None;
    }
}

impl<T, C: Cs> Drop for AtomicRc<T, C> {
    #[inline(always)]
    fn drop(&mut self) {
        let ptr = self.link.load(Ordering::Relaxed);
        unsafe {
            if let Some(cnt) = ptr.as_raw().as_mut() {
                let cs = &C::new();
                cnt.decrement_strong(Some(cs));
            }
        }
    }
}

impl<T, C: Cs> Default for AtomicRc<T, C> {
    #[inline(always)]
    fn default() -> Self {
        Self::null()
    }
}

impl<T, C: Cs> From<Rc<T, C>> for AtomicRc<T, C> {
    #[inline]
    fn from(value: Rc<T, C>) -> Self {
        let ptr = value.into_raw();
        Self {
            link: Atomic::new(ptr),
            _marker: PhantomData,
        }
    }
}

pub struct Rc<T, C: Cs> {
    ptr: TaggedCnt<T>,
    _marker: PhantomData<(T, *const C)>,
}

unsafe impl<T: Send + Sync, C: Cs> Send for Rc<T, C> {}
unsafe impl<T: Send + Sync, C: Cs> Sync for Rc<T, C> {}

impl<T, C: Cs> Rc<T, C> {
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
    pub fn from_snapshot<'g>(ptr: &Snapshot<T, C>) -> Self {
        let rc = Self {
            ptr: ptr.as_ptr(),
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
    pub fn new(obj: T) -> Self {
        let ptr = C::create_object(obj);
        Self {
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
    pub unsafe fn into_inner(self) -> Option<T> {
        let ptr = self.ptr.as_raw();
        forget(self);

        if let Some(cnt) = ptr.as_mut() {
            if cnt.strong.load(Ordering::Relaxed) == 1 {
                return Some(C::own_object(ptr).into_inner());
            }
            cnt.decrement_strong(Some(&C::unprotected()));
        }
        return None;
    }
}

impl<T, C: Cs> Default for Rc<T, C> {
    #[inline]
    fn default() -> Self {
        Self::null()
    }
}

impl<T, C: Cs> Drop for Rc<T, C> {
    #[inline(always)]
    fn drop(&mut self) {
        unsafe {
            if let Some(cnt) = self.ptr.as_raw().as_mut() {
                cnt.decrement_strong(Some(&C::new()));
            }
        }
    }
}

impl<T, C: Cs> PartialEq for Rc<T, C> {
    #[inline(always)]
    fn eq(&self, other: &Self) -> bool {
        self.ptr == other.ptr
    }
}

pub struct Snapshot<T, C: Cs> {
    // Hint: `C::Acquired` is usually a wrapper struct containing `TaggedCnt`.
    acquired: C::RawShield<T>,
}

impl<T, C: Cs> Snapshot<T, C> {
    #[inline(always)]
    pub fn new() -> Self {
        Self {
            acquired: <C as Cs>::RawShield::null(),
        }
    }

    #[inline]
    pub fn load(&mut self, from: &AtomicRc<T, C>, cs: &C) {
        cs.acquire(&from.link, &mut self.acquired);
    }

    #[inline]
    pub fn load_from_weak(&mut self, from: &AtomicWeak<T, C>, cs: &C) {
        loop {
            let ptr = cs.acquire(&from.link, &mut self.acquired);

            if !ptr.is_null() && unsafe { ptr.deref().non_zero() } {
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
            if !unsafe { self.acquired.as_ptr().deref() }.non_zero() {
                self.acquired.clear();
                return false;
            }
        }
        true
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

    #[inline]
    pub fn swap(p1: &mut Self, p2: &mut Self) {
        <C::RawShield<T> as Acquired<T>>::swap(&mut p1.acquired, &mut p2.acquired)
    }
}

impl<T, C: Cs> Default for Snapshot<T, C> {
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

impl<T, C: Cs> Drop for Snapshot<T, C> {
    #[inline(always)]
    fn drop(&mut self) {
        self.acquired.clear();
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

impl<T, C: Cs> Pointer<T> for Rc<T, C> {
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

pub trait StrongPtr<T, C: Cs>: Pointer<T> {
    const OWNS_REF_COUNT: bool;

    /// Consumes the aquired pointer, incrementing the reference count if we didn't increment
    /// it before.
    ///
    /// Semantically, it is equivalent to giving ownership of a reference count outside the
    /// environment.
    ///
    /// For example, we do nothing but forget its ownership if the pointer is [`Rc`],
    /// but increment the reference count if the pointer is [`Snapshot`].
    #[inline]
    fn into_ref_count(self)
    where
        Self: Sized,
    {
        if Self::OWNS_REF_COUNT {
            // As we have a reference count already, we don't have to do anything, but
            // prevent calling a destructor which decrements it.
            forget(self);
        } else if let Some(cnt) = unsafe { self.as_ptr().as_raw().as_ref() } {
            cnt.increment_strong();
        }
    }

    /// Consumes `self` and constructs a [`Rc`] pointing to the same object.
    ///
    /// If `self` is already [`Rc`], it will not touch the reference count.
    #[inline]
    fn into_rc(self) -> Rc<T, C>
    where
        Self: Sized,
    {
        let rc = Rc::from_raw(self.as_ptr());
        if Self::OWNS_REF_COUNT {
            self.into_ref_count();
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

impl<T, C: Cs> StrongPtr<T, C> for Rc<T, C> {
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
