use std::mem::{swap, ManuallyDrop};

use atomic::Ordering;

use super::ebr_impl::{default_collector, pin, Guard};
use crate::utils::RcInner;
use crate::{Acquired, Cs, GraphNode, TaggedCnt, HIGH_TAG_WIDTH};
use crate::{Pointer, Validatable};

const EPOCH_WIDTH: u32 = HIGH_TAG_WIDTH;
const EPOCH_MASK_HEIGHT: u32 = u32::BITS - EPOCH_WIDTH;
const EPOCH_MASK: u32 = ((1 << EPOCH_WIDTH) - 1) << EPOCH_MASK_HEIGHT;
const DESTRUCTED_MASK: u32 = 1 << (EPOCH_MASK_HEIGHT - 1);

/// Effectively wraps the presence of epoch and destruction bits.
#[derive(Clone, Copy)]
struct StrongCount {
    inner: u32,
}

impl StrongCount {
    fn from_raw(inner: u32) -> Self {
        Self { inner }
    }

    fn from_parts(epoch: usize, dest: bool, count: u32) -> Self {
        let epoch = ((epoch & ((1 << EPOCH_WIDTH) - 1)) as u32) << EPOCH_MASK_HEIGHT;
        let dest = if dest { DESTRUCTED_MASK } else { 0 };
        Self::from_raw(epoch | dest | count)
    }

    fn epoch(self) -> u32 {
        (self.inner & EPOCH_MASK) >> EPOCH_MASK_HEIGHT
    }

    fn count(self) -> u32 {
        self.inner & !EPOCH_MASK & !DESTRUCTED_MASK
    }

    fn destructed(self) -> bool {
        (self.inner & DESTRUCTED_MASK) != 0
    }

    fn with_epoch(self, epoch: usize) -> Self {
        Self::from_parts(epoch, self.destructed(), self.count())
    }

    fn add_count(self, val: u32) -> Self {
        Self::from_parts(self.epoch() as usize, self.destructed(), self.count() + val)
    }

    fn sub_count(self, val: u32) -> Self {
        debug_assert!(self.count() >= val);
        Self::from_parts(self.epoch() as usize, self.destructed(), self.count() - val)
    }

    fn with_destructed(self, dest: bool) -> Self {
        Self::from_parts(self.epoch() as usize, dest, self.count())
    }
}

struct Modular<const WIDTH: u32> {
    max: isize,
}

impl<const WIDTH: u32> Modular<WIDTH> {
    /// Creates a modular space where `max` ia the maximum.
    pub fn new(max: isize) -> Self {
        Self { max }
    }

    // Sends a number to a modular space.
    fn trans(&self, val: isize) -> isize {
        debug_assert!(val <= self.max);
        (val - (self.max + 1)) % (1 << WIDTH)
    }

    // Receives a number from a modular space.
    fn inver(&self, val: isize) -> isize {
        (val as isize + (self.max + 1)) % (1 << WIDTH)
    }

    pub fn max(&self, nums: &[isize]) -> isize {
        self.inver(nums.iter().fold(isize::MIN, |acc, val| {
            acc.max(self.trans(val % (1 << WIDTH)))
        }))
    }

    // Checks if `a` is less than or equal to `b` in the modular space.
    pub fn le(&self, a: isize, b: isize) -> bool {
        self.trans(a) <= self.trans(b)
    }
}

/// A tagged pointer which is pointing a `CountedObjPtr<T>`.
///
/// We may want to use `crossbeam_ebr::Shared` as a `Acquired`,
/// but trait interfaces can be complicated because `crossbeam_ebr::Shared`
/// requires to specify a lifetime specifier.
pub struct AcquiredEBR<T>(TaggedCnt<T>);

impl<T> Acquired<T> for AcquiredEBR<T> {
    #[inline(always)]
    fn as_ptr(&self) -> TaggedCnt<T> {
        self.0
    }

    #[inline(always)]
    fn null() -> Self {
        Self(TaggedCnt::null())
    }

    #[inline(always)]
    fn is_null(&self) -> bool {
        self.0.is_null()
    }

    #[inline(always)]
    fn swap(p1: &mut Self, p2: &mut Self) {
        swap(p1, p2);
    }

    #[inline(always)]
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }

    #[inline]
    fn clear(&mut self) {
        self.0 = TaggedCnt::null();
    }

    #[inline]
    fn set_tag(&mut self, tag: usize) {
        self.0 = self.0.with_tag(tag);
    }

    #[inline]
    unsafe fn copy_to(&self, other: &mut Self) {
        other.0 = self.0;
    }
}

impl<T> Clone for AcquiredEBR<T> {
    fn clone(&self) -> Self {
        Self(self.0)
    }
}

impl<T> Copy for AcquiredEBR<T> {}

pub struct WeakGuardEBR<T>(TaggedCnt<T>);

impl<T> Validatable<T> for WeakGuardEBR<T> {
    fn validate(&self) -> bool {
        true
    }

    fn ptr(&self) -> TaggedCnt<T> {
        self.0
    }
}

pub struct CsEBR {
    guard: Option<Guard>,
}

impl CsEBR {
    pub fn guard(&self) -> Option<&Guard> {
        self.guard.as_ref()
    }
}

impl From<Guard> for CsEBR {
    #[inline(always)]
    fn from(guard: Guard) -> Self {
        Self { guard: Some(guard) }
    }
}

impl Cs for CsEBR {
    type RawShield<T> = AcquiredEBR<T>;
    type WeakGuard<T> = WeakGuardEBR<T>;

    #[inline(always)]
    fn new() -> Self {
        Self::from(pin())
    }

    #[inline]
    unsafe fn unprotected() -> Self {
        Self { guard: None }
    }

    #[inline(always)]
    fn create_object<T>(obj: T, init_strong: u32) -> *mut RcInner<T> {
        let obj = RcInner::new(obj, init_strong);
        Box::into_raw(Box::new(obj))
    }

    #[inline]
    unsafe fn own_object<T>(ptr: *mut RcInner<T>) -> RcInner<T> {
        *Box::from_raw(ptr)
    }

    #[inline(always)]
    fn reserve<T>(&self, ptr: TaggedCnt<T>, shield: &mut Self::RawShield<T>) {
        *shield = AcquiredEBR(ptr);
    }

    #[inline(always)]
    fn acquire<T, F>(&self, load: F, shield: &mut Self::RawShield<T>) -> TaggedCnt<T>
    where
        F: Fn(Ordering) -> TaggedCnt<T>,
    {
        let ptr = load(Ordering::Acquire);
        *shield = AcquiredEBR(ptr);
        ptr
    }

    #[inline(always)]
    unsafe fn defer<T, F>(&self, ptr: *mut RcInner<T>, f: F)
    where
        F: FnOnce(&mut RcInner<T>),
    {
        debug_assert!(!ptr.is_null());
        let cnt = &mut *ptr;
        if let Some(guard) = &self.guard {
            guard.defer_unchecked(move || f(cnt));
        } else {
            f(cnt);
        }
    }

    #[inline]
    fn clear(&mut self) {
        if let Some(guard) = &mut self.guard {
            guard.repin();
        }
    }

    #[inline]
    unsafe fn dispose<T>(inner: &mut RcInner<T>)
    where
        T: GraphNode<Self>,
        Self: Sized,
    {
        let curr_epoch = Self::timestamp().unwrap();
        let modu: Modular<EPOCH_WIDTH> = Modular::new(curr_epoch as isize + 1);
        if T::UNIQUE_OUTDEGREE {
            dispose_list(inner, curr_epoch, &modu);
        } else {
            dispose_general_node(inner, curr_epoch, &modu, 0);
        }
    }

    #[inline]
    fn increment_strong<T>(inner: &RcInner<T>) -> bool {
        let val = StrongCount::from_raw(inner.strong.fetch_add(1, Ordering::SeqCst));
        if val.destructed() {
            return false;
        }
        if val.count() == 0 {
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
        let epoch = Self::timestamp().unwrap();
        // Should mark the current epoch on the strong count with CAS.
        let hit_zero = loop {
            let curr = StrongCount::from_raw(inner.strong.load(Ordering::SeqCst));
            debug_assert!(curr.count() >= count);
            if inner
                .strong
                .compare_exchange(
                    curr.inner,
                    curr.with_epoch(epoch).sub_count(count).inner,
                    Ordering::SeqCst,
                    Ordering::SeqCst,
                )
                .is_ok()
            {
                break curr.count() == count;
            }
        };

        // Trigger a collection periodically.
        if let Some(cs) = cs {
            if hit_zero {
                Self::schedule_try_destruct(inner, Some(cs));
            }
            if let Some(guard) = cs.guard.as_ref() {
                guard.incr_manual_collection();
            }
        } else {
            let cs = Self::new();
            if hit_zero {
                Self::schedule_try_destruct(inner, Some(&cs));
            }
            cs.guard.as_ref().unwrap().incr_manual_collection();
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
        let curr = StrongCount::from_raw(inner.strong.load(Ordering::SeqCst));
        debug_assert!(!curr.destructed());
        if curr.count() == 0
            && inner
                .strong
                .compare_exchange(
                    curr.inner,
                    curr.with_destructed(true).inner,
                    Ordering::SeqCst,
                    Ordering::SeqCst,
                )
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
        let mut curr = StrongCount::from_raw(inner.strong.load(Ordering::SeqCst));
        if curr.count() == 0 {
            curr = match inner.strong.compare_exchange(
                curr.inner,
                curr.add_count(1).inner,
                Ordering::SeqCst,
                Ordering::SeqCst,
            ) {
                Ok(_) => curr.add_count(1),
                Err(prev) => StrongCount::from_raw(prev),
            }
        }
        !curr.destructed()
    }

    #[inline]
    fn timestamp() -> Option<usize> {
        Some(default_collector().global_epoch().value())
    }
}

unsafe fn dispose_general_node<T: GraphNode<CsEBR>, const M: u32>(
    ptr: *mut RcInner<T>,
    curr_epoch: usize,
    modu: &Modular<M>,
    depth: usize,
) {
    let rc = match ptr.as_mut() {
        Some(rc) => rc,
        None => return,
    };

    if depth >= 1024 {
        // Prevent a potential stack overflow.
        CsEBR::schedule_try_destruct(rc, None);
        return;
    }

    let strong = StrongCount::from_raw(rc.strong.load(Ordering::SeqCst));
    let node_epoch = strong.epoch();
    debug_assert_eq!(strong.count(), 0);

    // Note that checking whether it is a root is necessary, because if `node_epoch` is
    // old enough, `modu.le` may return false.
    if depth == 0 || modu.le(node_epoch as _, curr_epoch as isize - 3) {
        // The current node is immediately reclaimable.
        for next in rc.data().pop_outgoings() {
            if next.is_null() {
                continue;
            }

            let next_ptr = next.into_raw();
            let next_ref = next_ptr.deref();
            let link_epoch = next_ptr.high_tag() as u32;

            // Decrement next node's strong count and update its epoch.
            let next_cnt = loop {
                let cnt_curr = StrongCount::from_raw(next_ref.strong.load(Ordering::SeqCst));
                let next_epoch =
                    modu.max(&[node_epoch as _, link_epoch as _, cnt_curr.epoch() as _]);
                let cnt_next = cnt_curr.sub_count(1).with_epoch(next_epoch as _);

                if next_ref
                    .strong
                    .compare_exchange(
                        cnt_curr.inner,
                        cnt_next.inner,
                        Ordering::SeqCst,
                        Ordering::SeqCst,
                    )
                    .is_ok()
                {
                    break cnt_next;
                }
            };

            // If the reference count hit zero, try dispose it recursively.
            if next_cnt.count() == 0 {
                dispose_general_node(next_ptr.as_raw(), curr_epoch, modu, depth + 1);
            }
        }
        unsafe {
            ManuallyDrop::drop(&mut rc.storage);
            CsEBR::decrement_weak(rc);
        }
    } else {
        // It is likely to be unsafe to reclaim right now.
        CsEBR::schedule_try_destruct(rc, None);
    }
}

unsafe fn dispose_list<T: GraphNode<CsEBR>, const M: u32>(
    root: *mut RcInner<T>,
    curr_epoch: usize,
    modu: &Modular<M>,
) {
    let mut ptr = Some(root);
    while let Some(rc) = ptr.take().and_then(|ptr| ptr.as_mut()) {
        let strong = StrongCount::from_raw(rc.strong.load(Ordering::SeqCst));
        let node_epoch = strong.epoch();
        debug_assert_eq!(strong.count(), 0);

        // Note that checking whether it is a root is necessary, because if `node_epoch` is
        // old enough, `modu.le` may return false.
        if root == rc || modu.le(node_epoch as _, curr_epoch as isize - 3) {
            // The current node is immediately reclaimable.
            let next = rc.data().pop_unique();
            if !next.is_null() {
                let next_ptr = next.into_raw();
                let next_ref = next_ptr.deref();
                let link_epoch = next_ptr.high_tag() as u32;

                // Decrement next node's strong count and update its epoch.
                let next_cnt = loop {
                    let cnt_curr = StrongCount::from_raw(next_ref.strong.load(Ordering::SeqCst));
                    let next_epoch =
                        modu.max(&[node_epoch as _, link_epoch as _, cnt_curr.epoch() as _]);
                    let cnt_next = cnt_curr.sub_count(1).with_epoch(next_epoch as _);

                    if next_ref
                        .strong
                        .compare_exchange(
                            cnt_curr.inner,
                            cnt_next.inner,
                            Ordering::SeqCst,
                            Ordering::SeqCst,
                        )
                        .is_ok()
                    {
                        break cnt_next;
                    }
                };

                // If the reference count hit zero, try dispose it.
                if next_cnt.count() == 0 {
                    ptr = Some(next_ptr.as_raw());
                }
            }
            unsafe {
                ManuallyDrop::drop(&mut rc.storage);
                CsEBR::decrement_weak(rc);
            }
        } else {
            // It is likely to be unsafe to reclaim right now.
            CsEBR::schedule_try_destruct(rc, None);
        }
    }
}
