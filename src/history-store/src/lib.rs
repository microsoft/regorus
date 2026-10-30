#![no_std]
#![cfg_attr(not(verus_keep_ghost), forbid(unsafe_code))]
#![cfg_attr(verus_keep_ghost, feature(proc_macro_hygiene, allocator_api))]
#![cfg_attr(docsrs, feature(doc_cfg))]
extern crate alloc;
#[cfg(any(feature = "std", test))]
extern crate std;
#[cfg(feature = "runtime")]
#[cfg_attr(docsrs, doc(cfg(feature = "runtime")))]
#[doc(hidden)]
pub mod cache;
#[cfg(feature = "runtime")]
#[cfg_attr(docsrs, doc(cfg(feature = "runtime")))]
#[doc(hidden)]
pub mod graph;
#[cfg(feature = "runtime")]
#[cfg_attr(docsrs, doc(cfg(feature = "runtime")))]
pub mod history;
#[cfg(feature = "runtime")]
#[cfg_attr(docsrs, doc(cfg(feature = "runtime")))]
pub mod store;
#[cfg(feature = "runtime")]
#[cfg_attr(docsrs, doc(cfg(feature = "runtime")))]
pub mod typed;
#[cfg(verus_keep_ghost)]
pub mod verify;
#[cfg(feature = "runtime")]
pub use history::{Checkpoint, History};
#[cfg(feature = "runtime")]
pub use typed::Store;
