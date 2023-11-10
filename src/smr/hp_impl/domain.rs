use core::sync::atomic::{AtomicUsize, Ordering};

use crossbeam_utils::CachePadded;
use rustc_hash::FxHashSet;

use super::hazard::ThreadRecords;
use super::retire::{Pile, Retired};
use super::thread::Thread;

#[derive(Debug)]
pub struct Domain {
    pub(crate) threads: CachePadded<ThreadRecords>,
    pub(crate) retireds: CachePadded<Pile<Vec<Retired>>>,
    pub(crate) num_garbages: CachePadded<AtomicUsize>,
}

impl Domain {
    pub const fn new() -> Self {
        Self {
            threads: CachePadded::new(ThreadRecords::new()),
            retireds: CachePadded::new(Pile::new()),
            num_garbages: CachePadded::new(AtomicUsize::new(0)),
        }
    }

    pub fn collect_guarded_ptrs(&self, reclaimer: &Thread) -> FxHashSet<*mut u8> {
        self.threads
            .iter()
            .flat_map(|thread| thread.iter(reclaimer))
            .collect()
    }

    pub fn num_garbages(&self) -> usize {
        self.num_garbages.load(Ordering::Acquire)
    }
}

impl Drop for Domain {
    fn drop(&mut self) {
        for t in self.threads.iter() {
            assert!(t.available.load(Ordering::Relaxed))
        }
        while !self.retireds.is_empty() {
            let mut retireds = self.retireds.pop_all_flatten();
            for r in retireds.drain(..) {
                unsafe { r.call() };
            }
        }
    }
}
