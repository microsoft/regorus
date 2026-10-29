#![no_std]
// Verus generates erased unsafe scaffolding for native specifications.
#![cfg_attr(not(verus_keep_ghost), forbid(unsafe_code))]
#![cfg_attr(verus_keep_ghost, feature(proc_macro_hygiene, allocator_api))]
#![cfg_attr(docsrs, feature(doc_cfg))]

extern crate alloc;
#[cfg(any(feature = "std", test, feature = "test-util"))]
extern crate std;

pub mod compile;
pub mod error;
pub mod event;
pub mod flat;
pub mod flatten;
pub mod limits;
pub mod observation;
pub mod scope;

#[cfg(feature = "runtime")]
#[cfg_attr(docsrs, doc(cfg(feature = "runtime")))]
pub mod kernel;

#[cfg(verus_keep_ghost)]
pub mod verify;

pub use compile::{FlatEncoder, lower_flat};
pub use error::{CompileError, HistoryError};
pub use event::{Grant, Request};
pub use flatten::{ComponentValue, flatten_rule};
