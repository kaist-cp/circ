#![feature(associated_type_bounds)]
#![feature(cfg_sanitize)]
#![feature(core_intrinsics)]
#![feature(const_maybe_uninit_zeroed)]
mod smr;
mod smr_common;
mod strongs;
mod utils;
mod weak;

pub use smr::*;
pub use smr_common::*;
pub use strongs::*;
pub use utils::*;
pub use weak::*;

#[inline]
pub fn set_counts_between_flush_ebr(counts: usize) {
    smr::ebr_impl::set_bag_capacity(counts);
}

#[inline]
pub fn set_counts_between_flush_hp(counts: usize) {
    smr::hp_impl::set_counts_between_flush(counts);
}

#[inline]
pub fn cleanup_ebr() {
    let mut guard = smr::ebr_impl::pin();
    while guard.local_bag_len() > 0 || !smr::ebr_impl::default_collector().is_global_queue_empty() {
        guard.flush();
        guard.repin();
    }
}
