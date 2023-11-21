use std::{mem::ManuallyDrop, sync::atomic::AtomicU64};

use crate::Tagged;

/// An instance of an object of type T with an atomic reference count.
pub struct RcInner<T> {
    pub storage: ManuallyDrop<T>,
    pub state: AtomicU64,
}

impl<T> RcInner<T> {
    pub fn new(val: T, init: u64) -> Self {
        Self {
            storage: ManuallyDrop::new(val),
            state: AtomicU64::new(init),
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
}

pub type TaggedCnt<T> = Tagged<RcInner<T>>;

pub trait Pointer<T> {
    fn as_ptr(&self) -> TaggedCnt<T>;
    fn is_null(&self) -> bool {
        self.as_ptr().is_null()
    }
}
