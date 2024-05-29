#![doc = include_str!("../README.md")]

pub(crate) mod ebr_impl;
mod strong;
mod utils;
mod weak;

pub use ebr_impl::{cs, Guard};
pub use strong::*;
pub use utils::*;
pub use weak::*;
