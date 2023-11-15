use std::cell::Cell;
use std::mem::{swap, ManuallyDrop, MaybeUninit};
use std::sync::atomic::AtomicUsize;

use atomic::Ordering;

use super::ebr_impl::{default_collector, pin, Guard};
use crate::utils::RcInner;
use crate::{Acquired, Cs, GraphNode, TaggedCnt, HIGH_TAG_WIDTH};
use crate::{Pointer, Validatable};

const EPOCH_WIDTH: u32 = HIGH_TAG_WIDTH;
const EPOCH_MASK_HEIGHT: u32 = u64::BITS - EPOCH_WIDTH;
const EPOCH: u64 = ((1 << EPOCH_WIDTH) - 1) << EPOCH_MASK_HEIGHT;
const DESTRUCTED: u64 = 1 << (EPOCH_MASK_HEIGHT - 1);
const WEAKED: u64 = 1 << (EPOCH_MASK_HEIGHT - 2);
const TOTAL_COUNT_WIDTH: u32 = u64::BITS - EPOCH_WIDTH - 2;
const WEAK_WIDTH: u32 = TOTAL_COUNT_WIDTH / 2;
const STRONG_WIDTH: u32 = TOTAL_COUNT_WIDTH - WEAK_WIDTH;
const STRONG: u64 = (1 << STRONG_WIDTH) - 1;
const WEAK: u64 = ((1 << WEAK_WIDTH) - 1) << STRONG_WIDTH;
const COUNT: u64 = 1;
const WEAK_COUNT: u64 = 1 << STRONG_WIDTH;

thread_local! {
    static DISPOSE_COUNTER: Cell<usize> = Cell::new(0);
}

pub static TOTAL_DISPOSED: AtomicUsize = AtomicUsize::new(0);
pub static DISPOSE_CALL: AtomicUsize = AtomicUsize::new(0);
pub static DISPOSED: [AtomicUsize; 1024] = unsafe { MaybeUninit::zeroed().assume_init() };
pub static DISPOSED_EX: AtomicUsize = AtomicUsize::new(0);
pub static APPROX_MAX: AtomicUsize = AtomicUsize::new(0);

/// Effectively wraps the presence of epoch and destruction bits.
#[derive(Clone, Copy)]
struct State {
    inner: u64,
}

impl State {
    fn from_raw(inner: u64) -> Self {
        Self { inner }
    }

    fn epoch(self) -> u32 {
        ((self.inner & EPOCH) >> EPOCH_MASK_HEIGHT) as u32
    }

    fn strong(self) -> u32 {
        ((self.inner & STRONG) / COUNT) as u32
    }

    fn weak(self) -> u32 {
        ((self.inner & WEAK) / WEAK_COUNT) as u32
    }

    fn destructed(self) -> bool {
        (self.inner & DESTRUCTED) != 0
    }

    fn weaked(&self) -> bool {
        (self.inner & WEAKED) != 0
    }

    fn with_epoch(self, epoch: usize) -> Self {
        Self::from_raw((self.inner & !EPOCH) | (((epoch as u64) << EPOCH_MASK_HEIGHT) & EPOCH))
    }

    fn add_strong(self, val: u32) -> Self {
        Self::from_raw(self.inner + (val as u64) * COUNT)
    }

    fn sub_strong(self, val: u32) -> Self {
        debug_assert!(self.strong() >= val);
        Self::from_raw(self.inner - (val as u64) * COUNT)
    }

    fn add_weak(self, val: u32) -> Self {
        Self::from_raw(self.inner + (val as u64) * WEAK_COUNT)
    }

    fn with_destructed(self, dest: bool) -> Self {
        Self::from_raw((self.inner & !DESTRUCTED) | if dest { DESTRUCTED } else { 0 })
    }

    fn with_weaked(self, weaked: bool) -> Self {
        Self::from_raw((self.inner & !WEAKED) | if weaked { WEAKED } else { 0 })
    }

    fn as_raw(self) -> u64 {
        self.inner
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
        let obj = RcInner::new(obj, (init_strong as u64) * COUNT + WEAK_COUNT);
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

    #[inline]
    fn clear(&mut self) {
        if let Some(guard) = &mut self.guard {
            guard.repin();
        }
    }

    #[inline]
    fn increment_strong<T>(inner: &RcInner<T>) -> bool {
        let val = State::from_raw(inner.state.fetch_add(COUNT, Ordering::SeqCst));
        if val.destructed() {
            return false;
        }
        if val.strong() == 0 {
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
        let epoch = cs
            .and_then(|cs| cs.guard.as_ref())
            .map(|guard| guard.local_epoch().value())
            .unwrap_or_else(|| default_collector().global_epoch().value());
        // Should mark the current epoch on the strong count with CAS.
        let hit_zero = loop {
            let curr = State::from_raw(inner.state.load(Ordering::SeqCst));
            debug_assert!(curr.strong() >= count);
            if inner
                .state
                .compare_exchange(
                    curr.as_raw(),
                    curr.with_epoch(epoch).sub_strong(count).as_raw(),
                    Ordering::SeqCst,
                    Ordering::SeqCst,
                )
                .is_ok()
            {
                break curr.strong() == count;
            }
        };

        // `incr_manual_collection` periodically triggers a collection.
        if let Some(cs) = cs {
            if hit_zero {
                cs.defer(inner, |inner| Self::try_destruct(inner));
            }
            if let Some(guard) = cs.guard.as_ref() {
                guard.incr_manual_collection();
            }
        } else {
            let cs = Self::new();
            if hit_zero {
                cs.defer(inner, |inner| Self::try_destruct(inner));
            }
            cs.guard.as_ref().unwrap().incr_manual_collection();
        }
    }

    #[inline]
    unsafe fn try_destruct<T: GraphNode<Self>>(inner: &mut RcInner<T>) {
        let mut old = State::from_raw(inner.state.load(Ordering::SeqCst));
        debug_assert!(!old.destructed());
        loop {
            if old.strong() > 0 {
                Self::decrement_strong(inner, 1, None);
                return;
            }
            match inner.state.compare_exchange(
                old.as_raw(),
                old.with_destructed(true).as_raw(),
                Ordering::SeqCst,
                Ordering::SeqCst,
            ) {
                // Note that `decrement_weak` will be called in `dispose`.
                Ok(_) => return dispose(inner),
                Err(curr) => old = State::from_raw(curr),
            }
        }
    }

    #[inline]
    unsafe fn try_dealloc<T>(inner: &mut RcInner<T>) {
        if State::from_raw(inner.state.load(Ordering::SeqCst)).weak() > 0 {
            Self::decrement_weak(inner, None);
        } else {
            drop(Self::own_object(inner));
        }
    }

    #[inline]
    fn increment_weak<T>(inner: &RcInner<T>) {
        let mut old = State::from_raw(inner.state.load(Ordering::SeqCst));
        while !old.weaked() {
            // In this case, `increment_weak` must have been called from `Rc::downgrade`,
            // guaranteeing weak > 0, so it can’t be incremented from 0.
            debug_assert!(old.weak() != 0);
            match inner.state.compare_exchange(
                old.as_raw(),
                old.with_weaked(true).add_weak(1).as_raw(),
                Ordering::SeqCst,
                Ordering::SeqCst,
            ) {
                Ok(_) => return,
                Err(curr) => old = State::from_raw(curr),
            }
        }
        if State::from_raw(inner.state.fetch_add(WEAK_COUNT, Ordering::SeqCst)).weak() == 0 {
            inner.state.fetch_add(WEAK_COUNT, Ordering::SeqCst);
        }
    }

    #[inline]
    unsafe fn decrement_weak<T>(inner: &mut RcInner<T>, cs: Option<&Self>) {
        debug_assert!(State::from_raw(inner.state.load(Ordering::SeqCst)).weak() >= 1);
        if State::from_raw(inner.state.fetch_sub(WEAK_COUNT, Ordering::SeqCst)).weak() == 1 {
            cs.defer(inner, |inner| Self::try_dealloc(inner));
        }
    }

    #[inline]
    fn non_zero<T>(inner: &RcInner<T>) -> bool {
        let mut old = State::from_raw(inner.state.load(Ordering::SeqCst));
        while !old.destructed() && old.strong() == 0 {
            match inner.state.compare_exchange(
                old.as_raw(),
                old.add_strong(1).as_raw(),
                Ordering::SeqCst,
                Ordering::SeqCst,
            ) {
                Ok(_) => return true,
                Err(curr) => old = State::from_raw(curr),
            }
        }
        !old.destructed()
    }

    #[inline]
    fn timestamp(&self) -> Option<usize> {
        Some(
            self.guard
                .as_ref()
                .map(|guard| guard.local_epoch().value())
                .unwrap_or_else(|| default_collector().global_epoch().value()),
        )
    }

    fn strong_count<T>(inner: &RcInner<T>) -> u32 {
        State::from_raw(inner.state.load(Ordering::Relaxed)).strong()
    }
}

#[inline]
unsafe fn dispose<T: GraphNode<CsEBR>>(inner: *mut RcInner<T>) {
    DISPOSE_COUNTER.with(|counter| {
        // let prev = counter.get();
        let cs = &CsEBR::new();
        if T::UNIQUE_OUTDEGREE {
            dispose_list(inner, counter, cs);
        } else {
            dispose_general_node(inner, 0, counter, cs);
        }
        // let next = counter.get();

        // let disposed = next - prev;
        // TOTAL_DISPOSED.fetch_add(disposed, Ordering::Relaxed);
        // DISPOSE_CALL.fetch_add(1, Ordering::Relaxed);
        // if let Some(slot) = DISPOSED.get(disposed) {
        //     slot.fetch_add(1, Ordering::Relaxed);
        // } else {
        //     DISPOSED_EX.fetch_add(1, Ordering::Relaxed);
        //     let prev_max = APPROX_MAX.load(Ordering::Acquire);
        //     if prev_max < disposed {
        //         APPROX_MAX.store(disposed, Ordering::Release);
        //     }
        // }
    });
}

#[inline]
unsafe fn dispose_general_node<T: GraphNode<CsEBR>>(
    ptr: *mut RcInner<T>,
    depth: usize,
    counter: &Cell<usize>,
    cs: &CsEBR,
) {
    let rc = match ptr.as_mut() {
        Some(rc) => rc,
        None => return,
    };

    let count = counter.get();
    counter.set(count + 1);
    if count % 128 == 0 {
        if let Some(local) = cs.guard.as_ref().unwrap().local.as_ref() {
            local.repin_without_collect();
        }
    }

    if depth >= 1024 {
        // Prevent a potential stack overflow.
        cs.defer(rc, |rc| CsEBR::try_destruct(rc));
        return;
    }

    let state = State::from_raw(rc.state.load(Ordering::SeqCst));
    let node_epoch = state.epoch();
    debug_assert_eq!(state.strong(), 0);

    let curr_epoch = default_collector().global_epoch().value();
    let modu: Modular<EPOCH_WIDTH> = Modular::new(curr_epoch as isize + 1);
    let mut outgoings = Vec::new();

    // Note that checking whether it is a root is necessary, because if `node_epoch` is
    // old enough, `modu.le` may return false.
    if depth == 0 || modu.le(node_epoch as _, curr_epoch as isize - 3) {
        // The current node is immediately reclaimable.
        rc.data().pop_outgoings(&mut outgoings, cs);
        unsafe {
            ManuallyDrop::drop(&mut rc.storage);
            if State::from_raw(rc.state.load(Ordering::SeqCst)).weaked() {
                CsEBR::decrement_weak(rc, Some(cs));
            } else {
                drop(CsEBR::own_object(rc));
            }
        }
        for next in outgoings.drain(..) {
            if next.is_null() {
                continue;
            }

            let next_ptr = next.into_raw();
            let next_ref = next_ptr.deref();
            let link_epoch = next_ptr.high_tag() as u32;

            // Decrement next node's strong count and update its epoch.
            let next_cnt = loop {
                let cnt_curr = State::from_raw(next_ref.state.load(Ordering::SeqCst));
                let next_epoch =
                    modu.max(&[node_epoch as _, link_epoch as _, cnt_curr.epoch() as _]);
                let cnt_next = cnt_curr.sub_strong(1).with_epoch(next_epoch as _);

                if next_ref
                    .state
                    .compare_exchange(
                        cnt_curr.as_raw(),
                        cnt_next.as_raw(),
                        Ordering::SeqCst,
                        Ordering::SeqCst,
                    )
                    .is_ok()
                {
                    break cnt_next;
                }
            };

            // If the reference count hit zero, try dispose it recursively.
            if next_cnt.strong() == 0 {
                dispose_general_node(next_ptr.as_raw(), depth + 1, counter, cs);
            }
        }
    } else {
        // It is likely to be unsafe to reclaim right now.
        cs.defer(rc, |rc| CsEBR::try_destruct(rc));
    }
}

#[inline]
unsafe fn dispose_list<T: GraphNode<CsEBR>>(
    root: *mut RcInner<T>,
    counter: &Cell<usize>,
    cs: &CsEBR,
) {
    let mut ptr = Some(root);
    let mut curr_epoch = default_collector().global_epoch().value();
    let mut modu: Modular<EPOCH_WIDTH> = Modular::new(curr_epoch as isize + 1);

    while let Some(rc) = ptr.take().and_then(|ptr| ptr.as_mut()) {
        let count = counter.get();
        counter.set(count + 1);
        if count % 512 == 0 {
            if let Some(local) = cs.guard.as_ref().unwrap().local.as_ref() {
                local.repin_without_collect();
            }
            curr_epoch = default_collector().global_epoch().value();
            modu = Modular::new(curr_epoch as isize + 1);
        }
        let state = State::from_raw(rc.state.load(Ordering::SeqCst));
        let node_epoch = state.epoch();
        debug_assert_eq!(state.strong(), 0);

        // Note that checking whether it is a root is necessary, because if `node_epoch` is
        // old enough, `modu.le` may return false.
        if root == rc || modu.le(node_epoch as _, curr_epoch as isize - 3) {
            // The current node is immediately reclaimable.
            let next = rc.data().pop_unique(cs);
            unsafe {
                ManuallyDrop::drop(&mut rc.storage);
                if State::from_raw(rc.state.load(Ordering::SeqCst)).weaked() {
                    CsEBR::decrement_weak(rc, Some(cs));
                } else {
                    drop(CsEBR::own_object(rc));
                }
            }
            if !next.is_null() {
                let next_ptr = next.into_raw();
                let next_ref = next_ptr.deref();
                let link_epoch = next_ptr.high_tag() as u32;

                // Decrement next node's strong count and update its epoch.
                let next_cnt = loop {
                    let cnt_curr = State::from_raw(next_ref.state.load(Ordering::SeqCst));
                    let next_epoch =
                        modu.max(&[node_epoch as _, link_epoch as _, cnt_curr.epoch() as _]);
                    let cnt_next = cnt_curr.sub_strong(1).with_epoch(next_epoch as _);

                    if next_ref
                        .state
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
                if next_cnt.strong() == 0 {
                    ptr = Some(next_ptr.as_raw());
                }
            }
        } else {
            // It is likely to be unsafe to reclaim right now.
            cs.defer(rc, |rc| CsEBR::try_destruct(rc));
        }
    }
}

trait Deferable {
    unsafe fn defer<T, F>(&self, ptr: *mut RcInner<T>, f: F)
    where
        F: FnOnce(&mut RcInner<T>);
}

impl Deferable for CsEBR {
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
}

impl Deferable for Option<&CsEBR> {
    unsafe fn defer<T, F>(&self, ptr: *mut RcInner<T>, f: F)
    where
        F: FnOnce(&mut RcInner<T>),
    {
        if let Some(cs) = self {
            cs.defer(ptr, f)
        } else {
            CsEBR::new().defer(ptr, f)
        }
    }
}
