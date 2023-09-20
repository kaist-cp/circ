use std::{mem::swap, ptr::null};

use atomic::Ordering;

use crate::{Acquired, Counted, Cs, TaggedCnt};

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
}

pub struct CsHP {
    thread: *const Thread,
}

impl Cs for CsHP {
    type RawShield<T> = AcquiredHP<T>;

    #[inline]
    fn new() -> Self {
        let thread = DEFAULT_THREAD.with(|t| (&**t) as *const Thread);
        Self { thread }
    }

    #[inline]
    unsafe fn without_epoch() -> Self {
        Self::new()
    }

    #[inline]
    unsafe fn unprotected() -> Self {
        Self { thread: null() }
    }

    #[inline]
    fn create_object<T>(&self, obj: T) -> *mut crate::Counted<T> {
        let obj = Counted::new(obj);
        Box::into_raw(Box::new(obj))
    }

    #[inline]
    fn reserve<T>(&self, ptr: TaggedCnt<T>, shield: &mut Self::RawShield<T>) {
        shield.ptr = ptr;
        shield.hazptr.protect_raw(ptr.as_raw());
        membarrier::light();
    }

    #[inline]
    fn protect_snapshot<T>(
        &self,
        link: &atomic::Atomic<TaggedCnt<T>>,
        shield: &mut Self::RawShield<T>,
    ) -> bool {
        let mut ptr = link.load(Ordering::Relaxed);
        loop {
            shield.ptr = ptr;
            shield.hazptr.protect_raw(ptr.as_raw());
            membarrier::light();

            let new_ptr = link.load(Ordering::Acquire);
            if new_ptr == ptr {
                break;
            }
            ptr = new_ptr;
        }

        if !ptr.is_null() && unsafe { ptr.deref() }.ref_count() == 0 {
            shield.clear();
            false
        } else {
            true
        }
    }

    #[inline]
    unsafe fn delete_object<T>(&self, ptr: *mut Counted<T>) {
        drop(Box::from_raw(ptr));
    }

    #[inline]
    unsafe fn retire<T>(&self, ptr: *mut Counted<T>, ret_type: crate::RetireType) {
        debug_assert!(!ptr.is_null());
        let cnt = &mut *ptr;
        if let Some(thread) = self.thread.as_ref() {
            thread.defer(ptr, move || {
                let inner_guard = Self::new();
                inner_guard.eject(cnt, ret_type);
            });
        } else {
            self.eject(cnt, ret_type);
        }
    }

    #[inline]
    fn clear(&mut self) {
        // No-op for HP.
    }
}
