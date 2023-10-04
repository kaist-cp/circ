use core::marker::PhantomData;
use core::sync::atomic::{AtomicBool, AtomicPtr, Ordering};
use core::{mem, ptr};

use super::thread::Thread;
use super::DEFAULT_THREAD;

#[derive(Debug)]
pub struct HazardPointer {
    thread: *const Thread,
    idx: usize,
}

impl Default for HazardPointer {
    fn default() -> Self {
        DEFAULT_THREAD.with(|t| HazardPointer::new(t))
    }
}

impl HazardPointer {
    /// Create a hazard pointer in the given thread
    #[inline(always)]
    pub fn new(thread: &Thread) -> Self {
        let idx = thread.acquire();
        Self { thread, idx }
    }

    #[inline]
    unsafe fn hazard_array(&self) -> &HazardArray {
        &*(*(*self.thread).hazards).hazptrs.load(Ordering::Acquire)
    }

    #[inline]
    fn slot(&self) -> &AtomicPtr<u8> {
        unsafe {
            let array = self.hazard_array();
            array.get_unchecked(self.idx)
        }
    }

    /// Protect the given address.
    pub fn protect_raw<T>(&mut self, ptr: *mut T) {
        self.slot().store(ptr as *mut u8, Ordering::Release);
    }

    /// Release the protection awarded by this hazard pointer, if any.
    pub fn reset_protection(&mut self) {
        self.slot().store(ptr::null_mut(), Ordering::Release);
    }

    /// Check if `src` still points to `pointer`. If not, returns the current value.
    ///
    /// For a pointer `p`, if "`src` still pointing to `pointer`" implies that `p` is not retired,
    /// then `Ok(())` means that shields set to `p` are validated.
    pub fn validate<T>(pointer: *mut T, src: &AtomicPtr<T>) -> Result<(), *mut T> {
        membarrier::light_membarrier();
        let new = src.load(Ordering::Acquire);
        if pointer == new {
            Ok(())
        } else {
            Err(new)
        }
    }

    /// Try protecting `pointer` obtained from `src`. If not, returns the current value.
    ///
    /// If "`src` still pointing to `pointer`" implies that `pointer` is not retired, then `Ok(())`
    /// means that this shield is validated.
    pub fn try_protect<T>(&mut self, pointer: *mut T, src: &AtomicPtr<T>) -> Result<(), *mut T> {
        self.protect_raw(pointer);
        Self::validate(pointer, src)
    }

    /// Get a protected pointer from `src`.
    ///
    /// See `try_protect()`.
    pub fn protect<T>(&mut self, src: &AtomicPtr<T>) -> *mut T {
        let mut pointer = src.load(Ordering::Relaxed);
        while let Err(new) = self.try_protect(pointer, src) {
            pointer = new;
        }
        pointer
    }

    #[inline]
    pub fn swap(x: &mut HazardPointer, y: &mut HazardPointer) {
        mem::swap(&mut x.idx, &mut y.idx);
    }
}

impl Drop for HazardPointer {
    fn drop(&mut self) {
        self.reset_protection();
        unsafe { (*(self.thread as *mut Thread)).release(self.idx) };
    }
}

/// Push-only list of recyclable thread records
#[derive(Debug)]
pub(crate) struct ThreadRecords {
    head: AtomicPtr<ThreadRecord>,
}

/// Single-writer growable hazard pointer array.
/// Does not shrink. (Use single-writer doubly linked list? see HP04)
#[derive(Debug)]
pub struct ThreadRecord {
    pub(crate) next: *mut ThreadRecord,
    pub(crate) available: AtomicBool,
    pub(crate) hazptrs: AtomicPtr<HazardArray>,
}

pub(crate) type HazardArray = Vec<AtomicPtr<u8>>;

impl ThreadRecords {
    pub(crate) const fn new() -> Self {
        Self {
            head: AtomicPtr::new(ptr::null_mut()),
        }
    }

    pub(crate) fn acquire(&self) -> (&ThreadRecord, Vec<usize>) {
        if let Some(avail) = self.try_acquire_available() {
            return avail;
        }
        self.acquire_new()
    }

    fn try_acquire_available(&self) -> Option<(&ThreadRecord, Vec<usize>)> {
        let mut cur = self.head.load(Ordering::Acquire);
        while let Some(cur_ref) = unsafe { cur.as_ref() } {
            if cur_ref.available.load(Ordering::Relaxed)
                && cur_ref
                    .available
                    .compare_exchange(true, false, Ordering::Relaxed, Ordering::Relaxed)
                    .is_ok()
            {
                let len = unsafe { &*cur_ref.hazptrs.load(Ordering::Relaxed) }.len();
                return Some((cur_ref, (0..len).collect()));
            }
            cur = cur_ref.next;
        }
        None
    }

    fn acquire_new(&self) -> (&ThreadRecord, Vec<usize>) {
        const HAZARD_ARRAY_INIT_SIZE: usize = 64;
        let array = Vec::from(unsafe { mem::zeroed::<[AtomicPtr<u8>; HAZARD_ARRAY_INIT_SIZE]>() });
        let new = Box::leak(Box::new(ThreadRecord {
            hazptrs: AtomicPtr::new(Box::into_raw(Box::new(array))),
            next: ptr::null_mut(),
            available: AtomicBool::new(false),
        }));

        let mut head = self.head.load(Ordering::Relaxed);
        loop {
            new.next = head;
            match self
                .head
                .compare_exchange(head, new, Ordering::Release, Ordering::Relaxed)
            {
                Ok(_) => return (new, (0..HAZARD_ARRAY_INIT_SIZE).collect()),
                Err(head_new) => head = head_new,
            }
        }
    }

    pub(crate) fn release(&self, rec: &ThreadRecord) {
        rec.available.store(true, Ordering::Release);
    }

    pub(crate) fn iter(&self) -> ThreadRecordsIter<'_> {
        ThreadRecordsIter {
            cur: self.head.load(Ordering::Acquire).cast_const(),
            _marker: PhantomData,
        }
    }
}

pub(crate) struct ThreadRecordsIter<'domain> {
    cur: *const ThreadRecord,
    _marker: PhantomData<&'domain ThreadRecord>,
}

impl<'domain> Iterator for ThreadRecordsIter<'domain> {
    type Item = &'domain ThreadRecord;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let cur_ref = unsafe { self.cur.as_ref()? };
            self.cur = cur_ref.next;
            if !cur_ref.available.load(Ordering::Acquire) {
                return Some(cur_ref);
            }
        }
    }
}

impl ThreadRecord {
    pub(crate) fn iter<'domain>(&self, reader: &Thread) -> ThreadHazardArrayIter<'domain> {
        let mut hp = HazardPointer::new(reader);
        let array = hp.protect(&self.hazptrs);
        ThreadHazardArrayIter {
            array: unsafe { &*array }.as_slice(),
            idx: 0,
            _hp: hp,
            _marker: PhantomData,
        }
    }
}

pub(crate) struct ThreadHazardArrayIter<'domain> {
    array: *const [AtomicPtr<u8>],
    idx: usize,
    _hp: HazardPointer,
    _marker: PhantomData<&'domain ()>,
}

impl<'domain> Iterator for ThreadHazardArrayIter<'domain> {
    type Item = *mut u8;

    fn next(&mut self) -> Option<Self::Item> {
        let array = unsafe { &*self.array };
        for i in self.idx..array.len() {
            self.idx += 1;
            let slot = unsafe { array.get_unchecked(i) };
            let value = slot.load(Ordering::Acquire);
            if !value.is_null() {
                return Some(value);
            }
        }
        None
    }
}
