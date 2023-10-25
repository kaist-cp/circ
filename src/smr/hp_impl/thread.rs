use core::ptr::null_mut;
use core::sync::atomic::{AtomicPtr, Ordering};
use std::cell::{Cell, RefCell};

use super::domain::Domain;
use super::hazard::ThreadRecord;
use super::retire::{Pile, Retired};

pub struct Thread {
    pub(crate) domain: *const Domain,
    pub(crate) record: *const ThreadRecord,
    pub(crate) retired: RefCell<Vec<Retired>>,
    pub(crate) count: Cell<usize>,
    pub(crate) in_recl: Cell<bool>,
    pub(crate) must_retry: Cell<bool>,
}

impl Thread {
    pub fn new(domain: &Domain) -> Self {
        let record = domain.threads.acquire();
        Self {
            domain,
            record,
            retired: RefCell::new(Vec::new()),
            count: Cell::new(0),
            in_recl: Cell::new(false),
            must_retry: Cell::new(false),
        }
    }
}

// stuff related to reclamation
impl Thread {
    const COUNTS_BETWEEN_FLUSH: usize = 64;
    const COUNTS_BETWEEN_COLLECT: usize = 128;

    fn domain(&self) -> &Domain {
        unsafe { &*self.domain }
    }

    fn flush_retireds(&self) {
        self.domain()
            .num_garbages
            .fetch_add(self.retired.borrow().len(), Ordering::AcqRel);
        self.domain().retireds.push(self.retired.take())
    }

    // NOTE: T: Send not required because we reclaim only locally.
    #[inline]
    pub unsafe fn retire<T>(&self, ptr: *mut T) {
        self.defer(ptr as *mut _, move || unsafe { drop(Box::from_raw(ptr)) });
    }

    #[inline]
    pub unsafe fn defer<T, F>(&self, ptr: *mut T, f: F)
    where
        F: FnOnce(),
    {
        self.retired
            .borrow_mut()
            .push(Retired::new(ptr as *mut _, f));
        let count = self.count.get().wrapping_add(1);
        self.count.set(count);
        if count % Self::COUNTS_BETWEEN_FLUSH == 0 {
            self.flush_retireds();
        }
        // TODO: collecting right after pushing is kinda weird
        if count % Self::COUNTS_BETWEEN_COLLECT == 0 {
            self.do_reclamation();
        }
    }

    #[inline]
    pub(crate) fn do_reclamation(&self) {
        if self.in_recl.get() {
            // Prevent nested collections, but trigger a retrial.
            self.must_retry.set(true);
            return;
        }

        self.in_recl.set(true);
        loop {
            self.do_reclamation_inner();

            if self.must_retry.get() {
                self.must_retry.set(false);
            } else {
                break;
            }
        }
        self.in_recl.set(false);
    }

    #[inline]
    pub(crate) fn do_reclamation_inner(&self) {
        let retireds = self.domain().retireds.pop_all_flatten();
        let retireds_len = retireds.len();
        if retireds.is_empty() {
            return;
        }

        membarrier::heavy();

        let guarded_ptrs = self.domain().collect_guarded_ptrs(self);
        let not_freed: Vec<Retired> = retireds
            .into_iter()
            .filter_map(|element| {
                if guarded_ptrs.contains(&element.ptr) {
                    Some(element)
                } else {
                    unsafe { element.call() };
                    None
                }
            })
            .collect();
        self.domain()
            .num_garbages
            .fetch_sub(retireds_len - not_freed.len(), Ordering::AcqRel);
        self.domain().retireds.push(not_freed);
    }
}

// stuff related to hazards
impl Thread {
    fn available_indices(&self) -> &RefCell<Vec<usize>> {
        &unsafe { &*self.record }.available_indices
    }

    fn returned_hazptrs(&self) -> &Pile<usize> {
        &unsafe { &*self.record }.returned_hazptrs
    }

    /// acquire hazard slot
    #[inline(always)]
    pub(crate) fn acquire(&self) -> usize {
        let idx = self.available_indices().borrow_mut().pop();
        if let Some(idx) = idx {
            return idx;
        }

        let mut delivered = self.returned_hazptrs().pop_all();
        if !delivered.is_empty() {
            unsafe {
                let slots = &*(*self.record).hazptrs.load(Ordering::Acquire);
                for i in &delivered {
                    slots.get_unchecked(*i).store(null_mut(), Ordering::Release);
                }
            }
            let mut available_indices = self.available_indices().borrow_mut();
            available_indices.append(&mut delivered);
            return available_indices.pop().unwrap();
        }

        self.grow_array();
        self.acquire()
    }

    fn grow_array(&self) {
        let array_ptr = unsafe { &*self.record }.hazptrs.load(Ordering::Relaxed);
        let array = unsafe { &*array_ptr };
        let size = array.len();
        let new_size = size * 2;
        let mut new_array = Box::new(Vec::with_capacity(new_size));
        for i in 0..size {
            new_array.push(AtomicPtr::new(array[i].load(Ordering::Relaxed)));
        }
        for _ in size..new_size {
            new_array.push(AtomicPtr::new(null_mut()));
        }
        unsafe { &*self.record }
            .hazptrs
            .store(Box::into_raw(new_array), Ordering::Release);
        unsafe { self.retire(array_ptr) };
        self.available_indices().borrow_mut().extend(size..new_size)
    }
}

impl Drop for Thread {
    fn drop(&mut self) {
        self.flush_retireds();
        membarrier::heavy();
        assert!(self.retired.borrow().is_empty());
        self.domain().threads.release(unsafe { &*self.record });
    }
}
