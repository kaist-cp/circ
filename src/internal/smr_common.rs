use atomic::Atomic;

use crate::internal::utils::Counted;
use crate::internal::utils::EjectAction;
use crate::internal::utils::TaggedCnt;

pub enum RetireType {
    DecrementStrongCount,
    DecrementWeakCount,
    Dispose,
}

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

    fn new() -> Self;
    unsafe fn without_epoch() -> Self;
    unsafe fn unprotected() -> Self;
    fn create_object<T>(&self, obj: T) -> *mut Counted<T>;
    /// Creates a shield for the given pointer, assuming that `ptr` is already protected by a
    /// reference count.
    fn reserve<T>(&self, ptr: TaggedCnt<T>, shield: &mut Self::RawShield<T>);
    fn protect_snapshot<T>(
        &self,
        link: &Atomic<TaggedCnt<T>>,
        shield: &mut Self::RawShield<T>,
    ) -> bool;
    unsafe fn delete_object<T>(&self, ptr: *mut Counted<T>);
    unsafe fn retire<T>(&self, ptr: *mut Counted<T>, ret_type: RetireType);
    fn clear(&mut self);

    #[inline]
    unsafe fn dispose<T>(&self, cnt: &mut Counted<T>) {
        debug_assert!(cnt.ref_count() == 0);
        cnt.dispose();
        if cnt.release_weak() {
            self.destroy(cnt);
        }
    }

    #[inline]
    unsafe fn destroy<T>(&self, cnt: &mut Counted<T>) {
        debug_assert!(cnt.ref_count() == 0);
        self.delete_object(cnt);
    }

    /// Perform an eject action. This can correspond to any action that
    /// should be delayed until the ptr is no longer protected
    #[inline]
    unsafe fn eject<T>(&self, cnt: &mut Counted<T>, ret_type: RetireType) {
        match ret_type {
            RetireType::DecrementStrongCount => self.decrement_ref_cnt(cnt),
            RetireType::DecrementWeakCount => self.decrement_weak_cnt(cnt),
            RetireType::Dispose => self.dispose(cnt),
        }
    }

    #[inline]
    unsafe fn increment_ref_cnt<T>(&self, cnt: &Counted<T>) -> bool {
        cnt.add_ref()
    }

    #[inline]
    unsafe fn increment_weak_cnt<T>(&self, cnt: &Counted<T>) -> bool {
        cnt.add_weak()
    }

    #[inline]
    unsafe fn decrement_ref_cnt<T>(&self, cnt: &mut Counted<T>) {
        debug_assert!(cnt.ref_count() >= 1);
        let result = cnt.release_ref();

        match result {
            EjectAction::Nothing => {}
            EjectAction::Delay => self.retire(cnt, RetireType::Dispose),
            EjectAction::Destroy => self.destroy(cnt),
        }
    }

    #[inline]
    unsafe fn decrement_weak_cnt<T>(&self, cnt: &mut Counted<T>) {
        debug_assert!(cnt.weak_count() >= 1);
        if cnt.release_weak() {
            self.destroy(cnt);
        }
    }

    #[inline]
    unsafe fn delayed_decrement_ref_cnt<T>(&self, cnt: &mut Counted<T>) {
        debug_assert!(cnt.ref_count() >= 1);
        self.retire(cnt, RetireType::DecrementStrongCount);
    }

    #[inline]
    unsafe fn delayed_decrement_weak_cnt<T>(&self, cnt: &mut Counted<T>) {
        debug_assert!(cnt.weak_count() >= 1);
        self.retire(cnt, RetireType::DecrementWeakCount);
    }
}
