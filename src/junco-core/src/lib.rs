#![no_std]
#![forbid(unsafe_code)]
#![cfg_attr(docsrs, feature(doc_cfg))]

extern crate alloc;
#[cfg(any(feature = "std", test, feature = "test-util"))]
extern crate std;

pub mod compile;
pub mod errors;
pub mod event;
pub mod flat;
pub mod flatten;
pub mod limits;
pub mod observation;
#[cfg(feature = "runtime")]
#[cfg_attr(docsrs, doc(cfg(feature = "runtime")))]
pub mod reference;
pub mod scope;

pub use compile::{FlatEncoder, lower_flat};
pub use errors::{CompileError, HistoryError};
pub use event::{Grant, Request};
pub use flatten::flatten_rule;
