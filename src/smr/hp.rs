use std::mem::{swap, ManuallyDrop};
use std::ptr::null;

use atomic::Ordering;

use crate::{Acquired, Cs, GraphNode, RcInner, TaggedCnt, Validatable};

use super::hp_impl::{HazardPointer, Thread, DEFAULT_THREAD};

const DESTRUCTED: u64 = 1 << (u64::BITS - 1);
const WEAKED: u64 = 1 << (u64::BITS - 2);
const STRONG: u64 = (1 << 31) - 1;
const WEAK: u64 = ((1 << 31) - 1) << 31;
const COUNT: u64 = 1;
const WEAK_COUNT: u64 = 1 << 31;

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
        let obj = RcInner::new(obj, (init_strong as u64) * COUNT + WEAK_COUNT);
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
    fn clear(&mut self) {
        // No-op for HP.
    }

    #[inline]
    fn increment_strong<T>(inner: &RcInner<T>) -> bool {
        let val = inner.state.fetch_add(COUNT, Ordering::SeqCst);
        if (val & DESTRUCTED) != 0 {
            return false;
        }
        if val & STRONG == 0 {
            // The previous fetch_add created a permission to run decrement again.
            // Now create an actual reference.
            inner.state.fetch_add(COUNT, Ordering::SeqCst);
        }
        return true;
    }

    #[inline]
    unsafe fn decrement_strong<T: GraphNode<Self>>(
        inner: &mut RcInner<T>,
        count: u32,
        cs: Option<&Self>,
    ) {
        let count = count as u64 * COUNT;
        if inner.state.fetch_sub(count, Ordering::SeqCst) & STRONG == count {
            cs.defer(inner, |inner| Self::try_destruct(inner));
        }
    }

    #[inline]
    unsafe fn try_destruct<T: GraphNode<Self>>(inner: &mut RcInner<T>) {
        let mut old = inner.state.load(Ordering::SeqCst);
        loop {
            if old & STRONG > 0 {
                Self::decrement_strong(inner, 1, None);
                return;
            }
            match inner.state.compare_exchange(
                old,
                old | DESTRUCTED,
                Ordering::SeqCst,
                Ordering::SeqCst,
            ) {
                Ok(_) => {
                    ManuallyDrop::drop(&mut inner.storage);
                    if old & WEAKED == 0 {
                        drop(Self::own_object(inner));
                    } else {
                        Self::decrement_weak(inner, None);
                    }
                    return;
                }
                Err(curr) => old = curr,
            }
        }
    }

    #[inline]
    unsafe fn try_dealloc<T>(inner: &mut RcInner<T>) {
        if inner.state.load(Ordering::SeqCst) & WEAK > 0 {
            Self::decrement_weak(inner, None);
        } else {
            drop(Self::own_object(inner));
        }
    }

    #[inline]
    fn increment_weak<T>(inner: &RcInner<T>) {
        let mut old = inner.state.load(Ordering::SeqCst);
        while old & WEAKED == 0 {
            // In this case, `increment_weak` must have been called from `Rc::downgrade`,
            // guaranteeing weak > 0, so it can’t be incremented from 0.
            debug_assert!(old & WEAK != 0);
            match inner.state.compare_exchange(
                old,
                (old | WEAKED) + WEAK_COUNT,
                Ordering::SeqCst,
                Ordering::SeqCst,
            ) {
                Ok(_) => return,
                Err(curr) => old = curr,
            }
        }
        if inner.state.fetch_add(WEAK_COUNT, Ordering::SeqCst) & WEAK == 0 {
            inner.state.fetch_add(WEAK_COUNT, Ordering::SeqCst);
        }
    }

    #[inline]
    unsafe fn decrement_weak<T>(inner: &mut RcInner<T>, cs: Option<&Self>) {
        if inner.state.fetch_sub(WEAK_COUNT, Ordering::SeqCst) & WEAK == WEAK_COUNT {
            cs.defer(inner, |inner| Self::try_dealloc(inner));
        }
    }

    #[inline]
    fn non_zero<T>(inner: &RcInner<T>) -> bool {
        let mut old = inner.state.load(Ordering::SeqCst);
        while old & (DESTRUCTED | STRONG) == 0 {
            match inner
                .state
                .compare_exchange(old, old + COUNT, Ordering::SeqCst, Ordering::SeqCst)
            {
                Ok(_) => return true,
                Err(curr) => old = curr,
            }
        }
        old & DESTRUCTED == 0
    }

    #[inline]
    fn timestamp() -> Option<usize> {
        None
    }

    fn strong_count<T>(inner: &RcInner<T>) -> u32 {
        ((inner.state.load(Ordering::Relaxed) & STRONG) / COUNT) as u32
    }
}

trait Deferable {
    unsafe fn defer<T, F>(&self, ptr: *mut RcInner<T>, f: F)
    where
        F: FnOnce(&mut RcInner<T>);
}

impl Deferable for CsHP {
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
}

impl Deferable for Option<&CsHP> {
    unsafe fn defer<T, F>(&self, ptr: *mut RcInner<T>, f: F)
    where
        F: FnOnce(&mut RcInner<T>),
    {
        if let Some(cs) = self {
            cs.defer(ptr, f)
        } else {
            CsHP::new().defer(ptr, f)
        }
    }
}
