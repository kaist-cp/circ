use core::fmt;
use core::mem;

use scopeguard::defer;

use super::collector::Collector;
use super::deferred::Deferred;
use super::epoch::Epoch;
use super::internal::Local;
use super::RawShared;

/// A guard that keeps the current thread pinned.
pub struct Cs {
    pub(crate) local: *const Local,
}

impl Cs {
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
    pub fn defer<F, R>(&self, f: F)
    where
        F: FnOnce() -> R,
        F: Send + 'static,
    {
        unsafe {
            self.defer_unchecked(f);
        }
    }

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
    ///
    /// We intentionally didn't require `F: Send`, because Rust's type systems usually cannot prove
    /// `F: Send` for typical use cases. For example, consider the following code snippet, which
    /// exemplifies the typical use case of deferring the deallocation of a shared reference:
    ///
    /// ```ignore
    /// let shared = Owned::new(7i32).into_shared(guard);
    /// guard.defer_unchecked(move || shared.into_owned()); // `Shared` is not `Send`!
    /// ```
    ///
    /// While `Shared` is not `Send`, it's safe for another thread to call the deferred function,
    /// because it's called only after the grace period and `shared` is no longer shared with other
    /// threads. But we don't expect type systems to prove this.
    pub unsafe fn defer_unchecked<F, R>(&self, f: F)
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
    ///
    /// We intentionally didn't require `T: Send`, because Rust's type systems usually cannot prove
    /// `T: Send` for typical use cases. For example, consider the following code snippet, which
    /// exemplifies the typical use case of deferring the deallocation of a shared reference:
    ///
    /// ```ignore
    /// let shared = Owned::new(7i32).into_shared(guard);
    /// guard.defer_destroy(shared); // `Shared` is not `Send`!
    /// ```
    ///
    /// While `Shared` is not `Send`, it's safe for another thread to call the destructor, because
    /// it's called only after the grace period and `shared` is no longer shared with other
    /// threads. But we don't expect type systems to prove this.
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
    /// If this method is called from an [`unprotected`] guard, it is a no-op (nothing happens).
    pub fn flush(&self) {
        if let Some(local) = unsafe { self.local.as_ref() } {
            local.flush(self);
        }
    }

    /// Unpins and then immediately re-pins the thread.
    ///
    /// This method is useful when you don't want delay the advancement of the global epoch by
    /// holding an old epoch. For safety, you should not maintain any guard-based reference across
    /// the call (the latter is enforced by `&mut self`). The thread will only be repinned if this
    /// is the only active guard for the current thread.
    ///
    /// If this method is called from an [`unprotected`] guard, then the call will be just no-op.
    pub fn repin(&mut self) {
        if let Some(local) = unsafe { self.local.as_ref() } {
            local.repin();
        }
    }

    /// Temporarily unpins the thread, executes the given function and then re-pins the thread.
    ///
    /// This method is useful when you need to perform a long-running operation (e.g. sleeping)
    /// and don't need to maintain any guard-based reference across the call (the latter is enforced
    /// by `&mut self`). The thread will only be unpinned if this is the only active guard for the
    /// current thread.
    ///
    /// If this method is called from an [`unprotected`] guard, then the passed function is called
    /// directly without unpinning the thread.
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

    /// Returns the `Collector` associated with this guard.
    ///
    /// This method is useful when you need to ensure that all guards used with
    /// a data structure come from the same collector.
    ///
    /// If this method is called from an [`unprotected`] guard, then `None` is returned.
    pub fn collector(&self) -> Option<&Collector> {
        unsafe { self.local.as_ref().map(|local| local.collector()) }
    }

    /// Returns the current local epoch. If the guard is unprotected, returns the starting epoch.
    pub fn local_epoch(&self) -> Epoch {
        unsafe { self.local.as_ref() }
            .map(|local| local.epoch())
            .unwrap_or(Epoch::starting())
    }

    /// Increases the manual collection counter, and perform collection if the counter reaches
    /// the threshold which is set by `set_manual_collection_interval`.
    pub fn incr_manual_collection(&self) {
        if let Some(local) = unsafe { self.local.as_ref() } {
            local.incr_manual_collection(self);
        }
    }

    /// Returns the current length of the local garbage bag.
    pub fn local_bag_len(&self) -> usize {
        unsafe { self.local.as_ref() }
            .map(|local| local.bag_len())
            .unwrap_or(0)
    }

    /// Pushes the local garbages to the global queue without collecting.
    ///
    /// It may be useful when a thread cannot put effort into collecting its own garbages,
    /// but wants not to block the reclamation.
    pub fn push_to_global(&self) {
        if let Some(local) = unsafe { self.local.as_ref() } {
            local.push_to_global(self);
        }
    }
}

impl Drop for Cs {
    #[inline]
    fn drop(&mut self) {
        if let Some(local) = unsafe { self.local.as_ref() } {
            local.unpin();
        }
    }
}

impl fmt::Debug for Cs {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.pad("Cs { .. }")
    }
}

/// Returns a reference to a dummy guard that allows unprotected access to [`Atomic`]s.
///
/// This guard should be used in special occasions only. Note that it doesn't actually keep any
/// thread pinned - it's just a fake guard that allows loading from [`Atomic`]s unsafely.
///
/// Note that calling [`defer`] with a dummy guard will not defer the function - it will just
/// execute the function immediately.
///
/// # Safety
///
/// Loading and dereferencing data from an [`Atomic`] using this guard is safe only if the
/// [`Atomic`] is not being concurrently modified by other threads.
#[inline]
pub unsafe fn unprotected() -> Cs {
    Cs {
        local: core::ptr::null(),
    }
}
