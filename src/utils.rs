use core::mem;
use std::{
    hash::Hash,
    mem::ManuallyDrop,
    ptr::null_mut,
    sync::atomic::{AtomicU64, Ordering},
};

/// An instance of an object of type T with an atomic reference count.
pub struct RcInner<T> {
    pub storage: ManuallyDrop<T>,
    pub state: AtomicU64,
}

impl<T> RcInner<T> {
    pub fn new(val: T, init_strong: u32) -> Self {
        Self {
            storage: ManuallyDrop::new(val),
            state: AtomicU64::new(init_strong as _),
        }
    }

    pub fn data(&self) -> &T {
        &self.storage
    }

    pub fn data_mut(&mut self) -> &mut T {
        &mut self.storage
    }

    pub fn into_inner(self) -> T {
        ManuallyDrop::into_inner(self.storage)
    }

    pub fn has_one_strong(&self) -> bool {
        self.state.load(Ordering::Acquire) == 0
    }
}

pub struct Tagged<T> {
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

pub const HIGH_TAG_WIDTH: u32 = 4;

impl<T> Tagged<T> {
    const fn high_bits_pos() -> u32 {
        usize::BITS - HIGH_TAG_WIDTH
    }

    const fn high_bits() -> usize {
        ((1 << HIGH_TAG_WIDTH) - 1) << Self::high_bits_pos()
    }

    pub fn new(ptr: *mut T) -> Self {
        Self { ptr }
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

    pub fn as_usize(&self) -> usize {
        self.ptr as usize
    }

    pub fn with_tag(&self, tag: usize) -> Self {
        Self::new(with_tag(self.ptr, tag))
    }

    pub fn with_high_tag(&self, tag: usize) -> Self {
        Self::new(
            (self.ptr as usize & !Self::high_bits()
                | ((tag & ((1 << HIGH_TAG_WIDTH) - 1)) << Self::high_bits_pos()))
                as *mut T,
        )
    }

    pub unsafe fn deref<'g>(&self) -> &'g T {
        &*self.as_raw()
    }

    pub unsafe fn deref_mut<'g>(&mut self) -> &'g mut T {
        &mut *self.as_raw()
    }

    pub unsafe fn as_ref<'g>(&self) -> Option<&'g T> {
        if self.is_null() {
            None
        } else {
            Some(self.deref())
        }
    }

    pub unsafe fn as_mut<'g>(&mut self) -> Option<&'g mut T> {
        if self.is_null() {
            None
        } else {
            Some(self.deref_mut())
        }
    }
}

/// Returns a bitmask containing the unused least significant bits of an aligned pointer to `T`.
const fn low_bits<T>() -> usize {
    (1 << mem::align_of::<T>().trailing_zeros()) - 1
}

/// Returns the pointer with the given tag
fn with_tag<T>(ptr: *mut T, tag: usize) -> *mut T {
    ((ptr as usize & !low_bits::<T>()) | (tag & low_bits::<T>())) as *mut T
}

pub type TaggedCnt<T> = Tagged<RcInner<T>>;

pub trait Pointer<T> {
    fn as_ptr(&self) -> TaggedCnt<T>;
    fn is_null(&self) -> bool {
        self.as_ptr().is_null()
    }
}
