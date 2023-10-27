use std::{mem::swap, ptr::null};

use atomic::Ordering;

use crate::{Acquired, Cs, RcInner, TaggedCnt, Validatable};

use super::hp_impl::{HazardPointer, Thread, DEFAULT_THREAD};

pub struct AcquiredHP<T> {
    hazptr: HazardPointer,
    ptr: TaggedCnt<T>,
}

impl<T> Acquired<T> for AcquiredHP<T> {
    #[inline]
    fn clear(&mut self) {
        self.hazptr.reset_protection();
        self.ptr = TaggedCnt::null();
    }

    #[inline]
    fn as_ptr(&self) -> TaggedCnt<T> {
        self.ptr
    }

    #[inline]
    fn set_tag(&mut self, tag: usize) {
        self.ptr = self.ptr.with_tag(tag);
    }

    #[inline]
    fn null() -> Self {
        Self {
            hazptr: HazardPointer::default(),
            ptr: TaggedCnt::null(),
        }
    }

    #[inline]
    fn is_null(&self) -> bool {
        self.ptr.is_null()
    }

    #[inline]
    fn swap(p1: &mut Self, p2: &mut Self) {
        HazardPointer::swap(&mut p1.hazptr, &mut p2.hazptr);
        swap(&mut p1.ptr, &mut p2.ptr);
    }

    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.ptr == other.ptr
    }

    #[inline]
    unsafe fn copy_to(&self, other: &mut Self) {
        other.ptr = self.ptr;
        other.hazptr.protect_raw(other.ptr.as_raw());
        membarrier::light_membarrier();
    }
}

pub struct WeakGuardHP<T>(AcquiredHP<T>);

impl<T> Validatable<T> for WeakGuardHP<T> {
    fn validate(&self) -> bool {
        true
    }

    fn ptr(&self) -> TaggedCnt<T> {
        self.0.ptr
    }
}

pub struct CsHP {
    thread: *const Thread,
}

impl Cs for CsHP {
    type RawShield<T> = AcquiredHP<T>;
    type WeakGuard<T> = WeakGuardHP<T>;

    #[inline]
    fn new() -> Self {
        let thread = DEFAULT_THREAD.with(|t| (&**t) as *const Thread);
        Self { thread }
    }

    #[inline]
    unsafe fn unprotected() -> Self {
        Self { thread: null() }
    }

    #[inline]
    fn create_object<T>(obj: T, init_strong: u32) -> *mut crate::RcInner<T> {
        let obj = RcInner::new(obj, init_strong);
        Box::into_raw(Box::new(obj))
    }

    #[inline]
    unsafe fn own_object<T>(ptr: *mut RcInner<T>) -> RcInner<T> {
        *Box::from_raw(ptr)
    }

    #[inline]
    fn reserve<T>(&self, ptr: TaggedCnt<T>, shield: &mut Self::RawShield<T>) {
        shield.ptr = ptr;
        shield.hazptr.protect_raw(ptr.as_raw());
        membarrier::light_membarrier();
    }

    #[inline]
    fn acquire<T, F>(&self, load: F, shield: &mut Self::RawShield<T>) -> TaggedCnt<T>
    where
        F: Fn(Ordering) -> TaggedCnt<T>,
    {
        let mut ptr = load(Ordering::Relaxed);
        loop {
            shield.ptr = ptr;
            shield.hazptr.protect_raw(ptr.as_raw());
            membarrier::light_membarrier();

            let new_ptr = load(Ordering::Acquire);
            if new_ptr == ptr {
                break ptr;
            }
            ptr = new_ptr;
        }
    }

    #[inline]
    fn weak_acquire<T>(&self, ptr: TaggedCnt<T>) -> *mut Self::WeakGuard<T> {
        let thread = unsafe { self.thread.as_ref() }.unwrap();
        let mut hazptr = HazardPointer::new(thread);
        hazptr.protect_raw(ptr.as_raw());
        membarrier::light_membarrier();
        Box::into_raw(Box::new(WeakGuardHP(AcquiredHP { hazptr, ptr })))
    }

    #[inline]
    unsafe fn dispose_weak_guard<T>(ptr: *mut Self::WeakGuard<T>) {
        let guard = *Box::from_raw(ptr);
        let hazptr = guard.0.hazptr;
        let thread = &*DEFAULT_THREAD.with(|t| (&**t) as *const Thread);
        if thread.record == hazptr.owner_record() {
            drop(hazptr);
        } else {
            hazptr.deliver_to_owner();
        }
    }

    #[inline]
    unsafe fn defer<T, F>(&self, ptr: *mut RcInner<T>, f: F)
    where
        F: FnOnce(&mut RcInner<T>),
    {
        debug_assert!(!ptr.is_null());
        let cnt = &mut *ptr;
        if let Some(thread) = self.thread.as_ref() {
            thread.defer(ptr, move || f(cnt));
        } else {
            f(cnt);
        }
    }

    #[inline]
    fn clear(&mut self) {
        // No-op for HP.
    }
}
