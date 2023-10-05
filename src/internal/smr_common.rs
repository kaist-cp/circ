use atomic::Ordering;

use crate::internal::utils::{RcInner, TaggedCnt};

/// A SMR-specific acquired pointer trait.
///
/// In most cases such as EBR, IBR and Hyaline, Acquired is equivalent to a simple tagged
/// pointer pointing a Counted<T>.
///
/// However, for some pointer-based SMR, `Acquired` should contain other information like an
/// index of a hazard slot. For this reason, a type for acquired pointer must be SMR-dependent,
/// and every SMR must provide some reasonable interfaces to access and manage this pointer.
pub trait Acquired<T> {
    fn clear(&mut self);
    fn as_ptr(&self) -> TaggedCnt<T>;
    fn set_tag(&mut self, tag: usize);
    fn null() -> Self;
    fn is_null(&self) -> bool;
    fn swap(p1: &mut Self, p2: &mut Self);
    fn eq(&self, other: &Self) -> bool;
    unsafe fn copy_to(&self, other: &mut Self);
}

pub trait Validatable<T> {
    fn validate(&self) -> bool;
    fn ptr(&self) -> TaggedCnt<T>;
}

/// A SMR-specific critical section manager trait.
///
/// We construct this `Cs` right before starting an operation,
/// and drop(or `clear`) it after the operation.
pub trait Cs {
    /// A SMR-specific acquired pointer trait
    ///
    /// For more information, read a comment on `Acquired<T>`.
    type RawShield<T>: Acquired<T>;
    type WeakGuard<T>: Validatable<T>;

    fn new() -> Self;
    unsafe fn unprotected() -> Self;
    fn create_object<T>(obj: T) -> *mut RcInner<T>;
    unsafe fn own_object<T>(ptr: *mut RcInner<T>) -> RcInner<T>;
    /// Creates a shield for the given pointer, assuming that `ptr` is already protected by a
    /// reference count.
    fn reserve<T>(&self, ptr: TaggedCnt<T>, shield: &mut Self::RawShield<T>);
    fn acquire<T, F>(&self, load: F, shield: &mut Self::RawShield<T>) -> TaggedCnt<T>
    where
        F: Fn(Ordering) -> TaggedCnt<T>;
    fn weak_acquire<T>(&self, ptr: TaggedCnt<T>) -> *mut Self::WeakGuard<T>;
    unsafe fn own_weak_guard<T>(ptr: *mut Self::WeakGuard<T>) -> Self::WeakGuard<T>;
    unsafe fn defer<T, F>(&self, ptr: *mut RcInner<T>, f: F)
    where
        F: FnOnce(&mut RcInner<T>);
    fn clear(&mut self);
}
