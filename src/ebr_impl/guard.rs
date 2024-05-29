use core::fmt;
use core::mem;

use scopeguard::defer;

// use super::collector::Collector;
use super::deferred::Deferred;
use super::internal::Local;
use super::RawShared;

/// A RAII-style guard that keeps the current thread in an EBR critical section.
pub struct Guard {
    pub(crate) local: *const Local,
}

impl Guard {
    /// Stores a function so that it can be executed at some point after all currently pinned
    /// threads get unpinned.
    ///
    /// This method first stores `f` into the thread-local (or handle-local) cache. If this cache
    /// becomes full, some functions are moved into the global cache. At the same time, some
    /// functions from both local and global caches may get executed in order to incrementally
    /// clean up the caches as they fill up.
    ///
    /// There is no guarantee when exactly `f` will be executed. The only guarantee is that it
    /// won't be executed until all currently pinned threads get unpinned. In theory, `f` might
    /// never run, but the epoch-based garbage collection will make an effort to execute it
    /// reasonably soon.
    ///
    /// If this method is called from an [`unprotected`] guard, the function will simply be
    /// executed immediately.
    ///
    /// # Safety
    ///
    /// The given function must not hold reference onto the stack. It is highly recommended that
    /// the passed function is **always** marked with `move` in order to prevent accidental
    /// borrows.
    ///
    /// Apart from that, keep in mind that another thread may execute `f`, so anything accessed by
    /// the closure must be `Send`.
    pub(crate) unsafe fn defer_unchecked<F, R>(&self, f: F)
    where
        F: FnOnce() -> R,
    {
        if let Some(local) = self.local.as_ref() {
            local.defer(Deferred::new(move || drop(f())), self);
        } else {
            drop(f());
        }
    }

    /// Stores a destructor for an object so that it can be deallocated and dropped at some point
    /// after all currently pinned threads get unpinned.
    ///
    /// This method first stores the destructor into the thread-local (or handle-local) cache. If
    /// this cache becomes full, some destructors are moved into the global cache. At the same
    /// time, some destructors from both local and global caches may get executed in order to
    /// incrementally clean up the caches as they fill up.
    ///
    /// There is no guarantee when exactly the destructor will be executed. The only guarantee is
    /// that it won't be executed until all currently pinned threads get unpinned. In theory, the
    /// destructor might never run, but the epoch-based garbage collection will make an effort to
    /// execute it reasonably soon.
    ///
    /// If this method is called from an [`unprotected`] guard, the destructor will simply be
    /// executed immediately.
    ///
    /// # Safety
    ///
    /// The object must not be reachable by other threads anymore, otherwise it might be still in
    /// use when the destructor runs.
    ///
    /// Apart from that, keep in mind that another thread may execute the destructor, so the object
    /// must be sendable to other threads.
    pub(crate) unsafe fn defer_destroy<T>(&self, ptr: RawShared<T>) {
        self.defer_unchecked(move || unsafe { ptr.drop() });
    }

    /// Clears up the thread-local cache of deferred functions by executing them or moving into the
    /// global cache.
    ///
    /// Call this method after deferring execution of a function if you want to get it executed as
    /// soon as possible. Flushing will make sure it is residing in in the global cache, so that
    /// any thread has a chance of taking the function and executing it.
    ///
    // If this method is called from an [`unprotected`] guard, it is a no-op (nothing happens).
    pub fn flush(&self) {
        if let Some(local) = unsafe { self.local.as_ref() } {
            local.flush(self);
        }
    }

    /// Restarts (deactivate and reactivate) the critical section.
    ///
    /// This method is useful when you don't want delay the advancement of the global epoch by
    /// holding an old epoch. For safety, you should not maintain any guard-based reference across
    /// the call (the latter is enforced by `&mut self`). The thread will only be repinned if this
    /// is the only active guard for the current thread.
    ///
    // If this method is called from an [`unprotected`] guard, then the call will be just no-op.
    pub fn repin(&mut self) {
        if let Some(local) = unsafe { self.local.as_ref() } {
            local.repin();
        }
    }

    /// Temporarily deactivate the critical section, executes the given function and then
    /// reactivates the critical section.
    ///
    /// This method is useful when you need to perform a long-running operation (e.g. sleeping)
    /// and don't need to maintain any guard-based reference across the call (the latter is enforced
    /// by `&mut self`). The thread will only be unpinned if this is the only active guard for the
    /// current thread.
    ///
    // If this method is called from an [`unprotected`] guard, then the passed function is called
    // directly without unpinning the thread.
    pub fn repin_after<F, R>(&mut self, f: F) -> R
    where
        F: FnOnce() -> R,
    {
        if let Some(local) = unsafe { self.local.as_ref() } {
            // We need to acquire a handle here to ensure the Local doesn't
            // disappear from under us.
            local.acquire_handle();
            local.unpin();
        }

        // Ensure the Guard is re-pinned even if the function panics
        defer! {
            if let Some(local) = unsafe { self.local.as_ref() } {
                mem::forget(local.pin());
                local.release_handle();
            }
        }

        f()
    }

    /*
    /// Returns the `Collector` associated with this guard.
    ///
    /// This method is useful when you need to ensure that all guards used with
    /// a data structure come from the same collector.
    ///
    /// If this method is called from an [`unprotected`] guard, then `None` is returned.
    pub fn collector(&self) -> Option<&Collector> {
        unsafe { self.local.as_ref().map(|local| local.collector()) }
    }
    */

    /// Increases the manual collection counter, and perform collection if the counter reaches
    /// the threshold which is set by `set_manual_collection_interval`.
    pub(crate) fn incr_manual_collection(&self) {
        if let Some(local) = unsafe { self.local.as_ref() } {
            local.incr_manual_collection(self);
        }
    }
}

impl Drop for Guard {
    #[inline]
    fn drop(&mut self) {
        if let Some(local) = unsafe { self.local.as_ref() } {
            local.unpin();
        }
    }
}

impl fmt::Debug for Guard {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.pad("Guard { .. }")
    }
}

/// Returns a reference to a dummy guard that allows unprotected access to atomic pointers.
///
/// This guard should be used in special occasions only. Note that it doesn't actually keep any
/// thread pinned - it's just a fake guard that allows loading from [`crate::AtomicRc`]s unsafely.
///
/// # Safety
///
/// Loading and dereferencing data from atomic shared pointers using this guard is safe only if
/// the pointers are not being concurrently modified by other threads.
#[inline]
pub unsafe fn unprotected() -> Guard {
    Guard {
        local: core::ptr::null(),
    }
}
