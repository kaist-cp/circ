use std::cell::Cell;
use std::sync::atomic::Ordering;
use std::{mem::ManuallyDrop, sync::atomic::AtomicU64};

use crate::ebr_impl::{cs, global_epoch, Guard, Tagged, HIGH_TAG_WIDTH};
use crate::RcObject;

pub type TaggedCnt<T> = Tagged<RcInner<T>>;

/// A trait for all smart pointer types.
pub trait Pointer<T> {
    /// Returns an underlying raw tagged pointer.
    fn as_ptr(&self) -> TaggedCnt<T>;

    /// Returns `true` if the pointer is null.
    fn is_null(&self) -> bool {
        self.as_ptr().is_null()
    }
}

trait Deferable {
    unsafe fn defer_with_inner<T, F>(&self, ptr: *mut RcInner<T>, f: F)
    where
        F: FnOnce(*mut RcInner<T>);
}

impl Deferable for Guard {
    unsafe fn defer_with_inner<T, F>(&self, ptr: *mut RcInner<T>, f: F)
    where
        F: FnOnce(*mut RcInner<T>),
    {
        debug_assert!(!ptr.is_null());
        self.defer_unchecked(move || f(ptr));
    }
}

impl Deferable for Option<&Guard> {
    unsafe fn defer_with_inner<T, F>(&self, ptr: *mut RcInner<T>, f: F)
    where
        F: FnOnce(*mut RcInner<T>),
    {
        if let Some(guard) = self {
            guard.defer_with_inner(ptr, f)
        } else {
            cs().defer_with_inner(ptr, f)
        }
    }
}

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
    static DISPOSE_COUNTER: Cell<usize> = const { Cell::new(0) };
}

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
        (val + (self.max + 1)) % (1 << WIDTH)
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

/// A reference-counted object of type `T` with an atomic reference counts.
pub struct RcInner<T> {
    storage: ManuallyDrop<T>,
    state: AtomicU64,
}

impl<T> RcInner<T> {
    #[inline(always)]
    pub(crate) fn alloc(obj: T, init_strong: u32) -> *mut Self {
        let obj = Self {
            storage: ManuallyDrop::new(obj),
            state: AtomicU64::new((init_strong as u64) * COUNT + WEAK_COUNT),
        };
        Box::into_raw(Box::new(obj))
    }

    /// # Safety
    ///
    /// The given `ptr` must not be shared across more than one thread.
    pub(crate) unsafe fn dealloc(ptr: *mut Self) {
        drop(Box::from_raw(ptr));
    }

    /// Returns an immutable reference to the object.
    pub fn data(&self) -> &T {
        &self.storage
    }

    /// Returns a mutable reference to the object.
    pub fn data_mut(&mut self) -> &mut T {
        &mut self.storage
    }

    #[inline]
    pub(crate) fn increment_strong(&self) -> bool {
        let val = State::from_raw(self.state.fetch_add(COUNT, Ordering::SeqCst));
        if val.destructed() {
            return false;
        }
        if val.strong() == 0 {
            // The previous fetch_add created a permission to run decrement again.
            // Now create an actual reference.
            self.state.fetch_add(COUNT, Ordering::SeqCst);
        }
        true
    }

    #[inline]
    unsafe fn try_dealloc(ptr: *mut Self) {
        if State::from_raw((*ptr).state.load(Ordering::SeqCst)).weak() > 0 {
            Self::decrement_weak(ptr, None);
        } else {
            Self::dealloc(ptr);
        }
    }

    #[inline]
    pub(crate) fn increment_weak(&self, count: u32) {
        let mut old = State::from_raw(self.state.load(Ordering::SeqCst));
        while !old.weaked() {
            // In this case, `increment_weak` must have been called from `Rc::downgrade`,
            // guaranteeing weak > 0, so it can’t be incremented from 0.
            debug_assert!(old.weak() != 0);
            match self.state.compare_exchange(
                old.as_raw(),
                old.with_weaked(true).add_weak(count).as_raw(),
                Ordering::SeqCst,
                Ordering::SeqCst,
            ) {
                Ok(_) => return,
                Err(curr) => old = State::from_raw(curr),
            }
        }
        if State::from_raw(
            self.state
                .fetch_add(count as u64 * WEAK_COUNT, Ordering::SeqCst),
        )
        .weak()
            == 0
        {
            self.state.fetch_add(WEAK_COUNT, Ordering::SeqCst);
        }
    }

    #[inline]
    pub(crate) unsafe fn decrement_weak(ptr: *mut Self, guard: Option<&Guard>) {
        debug_assert!(State::from_raw((*ptr).state.load(Ordering::SeqCst)).weak() >= 1);
        if State::from_raw((*ptr).state.fetch_sub(WEAK_COUNT, Ordering::SeqCst)).weak() == 1 {
            guard.defer_with_inner(ptr, |inner| Self::try_dealloc(inner));
        }
    }

    #[inline]
    pub(crate) fn non_zero(&self) -> bool {
        let mut old = State::from_raw(self.state.load(Ordering::SeqCst));
        while !old.destructed() && old.strong() == 0 {
            match self.state.compare_exchange(
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
}

impl<T: RcObject> RcInner<T> {
    #[inline]
    pub(crate) unsafe fn decrement_strong(ptr: *mut Self, count: u32, guard: Option<&Guard>) {
        let epoch = global_epoch();
        // Should mark the current epoch on the strong count with CAS.
        let hit_zero = loop {
            let curr = State::from_raw((*ptr).state.load(Ordering::SeqCst));
            debug_assert!(curr.strong() >= count);
            if (*ptr)
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

        let trigger_recl = |guard: &Guard| {
            if hit_zero {
                guard.defer_with_inner(ptr, |inner| Self::try_destruct(inner));
            }
            // Periodically triggers a collection.
            guard.incr_manual_collection();
        };

        if let Some(guard) = guard {
            trigger_recl(guard)
        } else {
            trigger_recl(&cs())
        }
    }

    #[inline]
    unsafe fn try_destruct(ptr: *mut Self) {
        let mut old = State::from_raw((*ptr).state.load(Ordering::SeqCst));
        debug_assert!(!old.destructed());
        loop {
            if old.strong() > 0 {
                Self::decrement_strong(ptr, 1, None);
                return;
            }
            match (*ptr).state.compare_exchange(
                old.as_raw(),
                old.with_destructed(true).as_raw(),
                Ordering::SeqCst,
                Ordering::SeqCst,
            ) {
                // Note that `decrement_weak` will be called in `dispose`.
                Ok(_) => return dispose(ptr),
                Err(curr) => old = State::from_raw(curr),
            }
        }
    }
}

#[inline]
unsafe fn dispose<T: RcObject>(inner: *mut RcInner<T>) {
    DISPOSE_COUNTER.with(|counter| {
        let guard = &cs();
        dispose_general_node(inner, 0, counter, guard);
    });
}

#[inline]
unsafe fn dispose_general_node<T: RcObject>(
    ptr: *mut RcInner<T>,
    depth: usize,
    counter: &Cell<usize>,
    guard: &Guard,
) {
    let rc = match ptr.as_mut() {
        Some(rc) => rc,
        None => return,
    };

    let count = counter.get();
    counter.set(count + 1);
    if count % 128 == 0 {
        if let Some(local) = guard.local.as_ref() {
            local.repin_without_collect();
        }
    }

    if depth >= 1024 {
        // Prevent a potential stack overflow.
        guard.defer_with_inner(rc, |rc| RcInner::try_destruct(rc));
        return;
    }

    let state = State::from_raw(rc.state.load(Ordering::SeqCst));
    let node_epoch = state.epoch();
    debug_assert_eq!(state.strong(), 0);

    let curr_epoch = global_epoch();
    let modu: Modular<EPOCH_WIDTH> = Modular::new(curr_epoch as isize + 1);
    let mut outgoings = Vec::new();

    // Note that checking whether it is a root is necessary, because if `node_epoch` is
    // old enough, `modu.le` may return false.
    if depth == 0 || modu.le(node_epoch as _, curr_epoch as isize - 3) {
        // The current node is immediately reclaimable.
        rc.data_mut().pop_edges(&mut outgoings);
        unsafe {
            ManuallyDrop::drop(&mut rc.storage);
            if State::from_raw(rc.state.load(Ordering::SeqCst)).weaked() {
                RcInner::decrement_weak(rc, Some(guard));
            } else {
                RcInner::dealloc(rc);
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
                dispose_general_node(next_ptr.as_raw(), depth + 1, counter, guard);
            }
        }
    } else {
        // It is likely to be unsafe to reclaim right now.
        guard.defer_with_inner(rc, |rc| RcInner::try_destruct(rc));
    }
}
