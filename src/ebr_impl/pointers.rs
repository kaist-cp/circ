use core::hash::Hash;
use core::marker::PhantomData;
use core::mem::align_of;
use core::ptr::null_mut;
use core::sync::atomic::AtomicUsize;

use atomic::{Atomic, Ordering};

use super::Guard;

pub struct Tagged<T: ?Sized> {
    ptr: *mut T,
}

impl<T> Default for Tagged<T> {
    fn default() -> Self {
        Self { ptr: null_mut() }
    }
}

impl<T> Clone for Tagged<T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T> Copy for Tagged<T> {}

impl<T> PartialEq for Tagged<T> {
    fn eq(&self, other: &Self) -> bool {
        self.with_high_tag(0).ptr == other.with_high_tag(0).ptr
    }
}

impl<T> Eq for Tagged<T> {}

impl<T> Hash for Tagged<T> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.ptr.hash(state)
    }
}

impl<T> From<*const T> for Tagged<T> {
    fn from(value: *const T) -> Self {
        Self {
            ptr: value.cast_mut(),
        }
    }
}

impl<T> From<*mut T> for Tagged<T> {
    fn from(value: *mut T) -> Self {
        Self { ptr: value }
    }
}

pub(crate) const HIGH_TAG_WIDTH: u32 = 4;

impl<T> Tagged<T> {
    const fn high_bits_pos() -> u32 {
        usize::BITS - HIGH_TAG_WIDTH
    }

    const fn high_bits() -> usize {
        ((1 << HIGH_TAG_WIDTH) - 1) << Self::high_bits_pos()
    }

    pub fn null() -> Self {
        Self { ptr: null_mut() }
    }

    pub fn is_null(&self) -> bool {
        self.as_raw().is_null()
    }

    pub fn tag(&self) -> usize {
        let ptr = self.ptr as usize;
        ptr & low_bits::<T>()
    }

    pub fn high_tag(&self) -> usize {
        let ptr = self.ptr as usize;
        (ptr & Self::high_bits()) >> Self::high_bits_pos()
    }

    /// Converts the pointer to a raw pointer (without the tag).
    pub fn as_raw(&self) -> *mut T {
        let ptr = self.ptr as usize;
        (ptr & !low_bits::<T>() & !Self::high_bits()) as *mut T
    }

    pub fn with_tag(&self, tag: usize) -> Self {
        Self::from(with_tag(self.ptr, tag))
    }

    pub fn with_high_tag(&self, tag: usize) -> Self {
        Self::from(
            (self.ptr as usize & !Self::high_bits()
                | ((tag & ((1 << HIGH_TAG_WIDTH) - 1)) << Self::high_bits_pos()))
                as *mut T,
        )
    }

    /// # Safety
    ///
    /// The pointer (without high and low tag bits) must be a valid location to dereference.
    pub unsafe fn deref<'g>(&self) -> &'g T {
        &*self.as_raw()
    }

    /// # Safety
    ///
    /// The pointer (without high and low tag bits) must be a valid location to dereference.
    pub unsafe fn deref_mut<'g>(&mut self) -> &'g mut T {
        &mut *self.as_raw()
    }

    /// # Safety
    ///
    /// The pointer (without high and low tag bits) must be a valid location to dereference.
    pub unsafe fn as_ref<'g>(&self) -> Option<&'g T> {
        if self.is_null() {
            None
        } else {
            Some(self.deref())
        }
    }
}

/// Returns a bitmask containing the unused least significant bits of an aligned pointer to `T`.
const fn low_bits<T>() -> usize {
    (1 << align_of::<T>().trailing_zeros()) - 1
}

/// Returns the pointer with the given tag
fn with_tag<T>(ptr: *mut T, tag: usize) -> *mut T {
    ((ptr as usize & !low_bits::<T>()) | (tag & low_bits::<T>())) as *mut T
}

pub(crate) struct RawAtomic<T> {
    inner: Atomic<Tagged<T>>,
}

unsafe impl<T: Send + Sync> Send for RawAtomic<T> {}
unsafe impl<T: Send + Sync> Sync for RawAtomic<T> {}

impl<T> RawAtomic<T> {
    pub fn null() -> Self {
        Self {
            inner: Atomic::new(Tagged::null()),
        }
    }

    pub fn load<'g>(&self, order: Ordering, _: &'g Guard) -> RawShared<'g, T> {
        RawShared::from(self.inner.load(order))
    }

    pub fn store(&self, val: RawShared<'_, T>, order: Ordering) {
        self.inner.store(val.inner, order);
    }

    pub fn compare_exchange<'g>(
        &self,
        current: RawShared<'g, T>,
        new: RawShared<'g, T>,
        success: Ordering,
        failure: Ordering,
        _: &'g Guard,
    ) -> Result<RawShared<'g, T>, RawShared<'g, T>> {
        self.inner
            .compare_exchange(current.inner, new.inner, success, failure)
            .map(RawShared::from)
            .map_err(RawShared::from)
    }

    pub fn compare_exchange_weak<'g>(
        &self,
        current: RawShared<'g, T>,
        new: RawShared<'g, T>,
        success: Ordering,
        failure: Ordering,
        _: &'g Guard,
    ) -> Result<RawShared<'g, T>, RawShared<'g, T>> {
        self.inner
            .compare_exchange_weak(current.inner, new.inner, success, failure)
            .map(RawShared::from)
            .map_err(RawShared::from)
    }

    pub fn fetch_or<'g>(&self, tag: usize, order: Ordering, _: &'g Guard) -> RawShared<'g, T> {
        // HACK: The size and alignment of `Atomic<TaggedCnt<T>>` will be same with `AtomicUsize`.
        // The equality of the sizes is checked by `const_assert!`.
        let inner = unsafe { &*(&self.inner as *const _ as *const AtomicUsize) };
        let prev = inner.fetch_or(low_bits::<T>() & tag, order);
        RawShared::from(prev as *const _)
    }
}

pub(crate) struct RawShared<'g, T> {
    inner: Tagged<T>,
    _marker: PhantomData<&'g T>,
}

impl<'g, T> Clone for RawShared<'g, T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<'g, T> Copy for RawShared<'g, T> {}

impl<'g, T> From<*const T> for RawShared<'g, T> {
    fn from(value: *const T) -> Self {
        Self {
            inner: Tagged::from(value),
            _marker: PhantomData,
        }
    }
}

impl<'g, T> From<*mut T> for RawShared<'g, T> {
    fn from(value: *mut T) -> Self {
        Self {
            inner: Tagged::from(value),
            _marker: PhantomData,
        }
    }
}

impl<'g, T> From<Tagged<T>> for RawShared<'g, T> {
    fn from(inner: Tagged<T>) -> Self {
        Self {
            inner,
            _marker: PhantomData,
        }
    }
}

impl<'g, T> PartialEq for RawShared<'g, T> {
    fn eq(&self, other: &Self) -> bool {
        self.inner == other.inner
    }
}

impl<'g, T> RawShared<'g, T> {
    pub fn null() -> Self {
        Self {
            inner: Tagged::null(),
            _marker: PhantomData,
        }
    }

    pub fn from_owned(init: T) -> Self {
        Self {
            inner: Tagged::from(Box::into_raw(Box::new(init))),
            _marker: PhantomData,
        }
    }

    pub unsafe fn drop(self) {
        drop(Box::from_raw(self.inner.as_raw()))
    }

    pub unsafe fn deref(self) -> &'g T {
        self.inner.deref()
    }

    pub unsafe fn as_ref(self) -> Option<&'g T> {
        self.inner.as_ref()
    }

    pub fn tag(self) -> usize {
        self.inner.tag()
    }

    pub fn with_tag(self, tag: usize) -> Self {
        Self {
            inner: self.inner.with_tag(tag),
            _marker: PhantomData,
        }
    }

    pub fn as_raw(self) -> *mut T {
        self.inner.as_raw()
    }

    #[cfg(test)]
    pub fn is_null(self) -> bool {
        self.inner.is_null()
    }
}
