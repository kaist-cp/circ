use atomic::Ordering;

use crate::{GraphNode, RcInner, TaggedCnt};

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
    fn create_object<T>(obj: T, init_strong: u32) -> *mut RcInner<T>;
    unsafe fn own_object<T>(ptr: *mut RcInner<T>) -> RcInner<T>;
    /// Creates a shield for the given pointer, assuming that `ptr` is already protected by a
    /// reference count.
    fn reserve<T>(&self, ptr: TaggedCnt<T>, shield: &mut Self::RawShield<T>);
    fn acquire<T, F>(&self, load: F, shield: &mut Self::RawShield<T>) -> TaggedCnt<T>
    where
        F: Fn(Ordering) -> TaggedCnt<T>;
    fn clear(&mut self);

    fn timestamp() -> Option<usize>;
    fn increment_strong<T>(inner: &RcInner<T>) -> bool;
    unsafe fn decrement_strong<T: GraphNode<Self>>(
        inner: &mut RcInner<T>,
        count: u32,
        cs: Option<&Self>,
    );
    unsafe fn try_destruct<T: GraphNode<Self>>(inner: &mut RcInner<T>);
    unsafe fn try_dealloc<T>(inner: &mut RcInner<T>);
    fn increment_weak<T>(inner: &RcInner<T>);
    unsafe fn decrement_weak<T>(inner: &mut RcInner<T>, cs: Option<&Self>);
    fn non_zero<T>(inner: &RcInner<T>) -> bool;
}
