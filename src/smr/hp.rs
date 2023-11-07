use std::mem::{swap, ManuallyDrop};
use std::ptr::null;

use atomic::Ordering;

use crate::{Acquired, Cs, GraphNode, RcInner, TaggedCnt, Validatable};

use super::hp_impl::{HazardPointer, Thread, DEFAULT_THREAD};

const DESTRUCTED: u32 = 1 << (u32::BITS - 1);

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

    #[inline(always)]
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

    #[inline]
    unsafe fn dispose<T>(inner: &mut RcInner<T>) {
        ManuallyDrop::drop(&mut inner.storage);
        Self::decrement_weak(inner);
    }

    #[inline]
    fn increment_strong<T>(inner: &RcInner<T>) -> bool {
        let val = inner.strong.fetch_add(1, Ordering::SeqCst);
        if (val & DESTRUCTED) != 0 {
            return false;
        }
        if val == 0 {
            // The previous fetch_add created a permission to run decrement again.
            // Now create an actual reference.
            inner.strong.fetch_add(1, Ordering::SeqCst);
        }
        return true;
    }

    #[inline]
    unsafe fn decrement_strong<T: GraphNode<Self>>(
        inner: &mut RcInner<T>,
        count: u32,
        cs: Option<&Self>,
    ) {
        if inner.strong.fetch_sub(count, Ordering::SeqCst) == count {
            Self::schedule_try_destruct(inner, cs);
        }
    }

    #[inline]
    unsafe fn schedule_try_destruct<T: GraphNode<Self>>(inner: &mut RcInner<T>, cs: Option<&Self>) {
        if let Some(cs) = cs {
            cs.defer(
                inner,
                #[inline(always)]
                |inner| unsafe { Self::try_destruct(inner) },
            )
        } else {
            Self::new().defer(
                inner,
                #[inline(always)]
                |inner| unsafe { Self::try_destruct(inner) },
            )
        }
    }

    #[inline]
    unsafe fn try_destruct<T: GraphNode<Self>>(inner: &mut RcInner<T>) {
        if inner
            .strong
            .compare_exchange(0, DESTRUCTED, Ordering::SeqCst, Ordering::SeqCst)
            .is_ok()
        {
            Self::dispose(inner);
        } else {
            Self::decrement_strong(inner, 1, None);
        }
    }

    #[inline]
    fn increment_weak<T>(inner: &RcInner<T>) {
        inner.weak.fetch_add(1, Ordering::SeqCst);
    }

    #[inline]
    unsafe fn decrement_weak<T>(inner: &mut RcInner<T>) {
        if inner.weak.fetch_sub(1, Ordering::SeqCst) == 1 {
            drop(Self::own_object(inner));
        }
    }

    #[inline]
    fn non_zero<T>(inner: &RcInner<T>) -> bool {
        let mut curr = inner.strong.load(Ordering::SeqCst);
        if curr == 0 {
            curr = inner
                .strong
                .compare_exchange(0, 1, Ordering::SeqCst, Ordering::SeqCst)
                .err()
                .unwrap_or(1);
        }
        (curr & DESTRUCTED) == 0
    }

    #[inline]
    fn timestamp() -> Option<usize> {
        None
    }
}
