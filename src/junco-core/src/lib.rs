#![no_std]
#![forbid(unsafe_code)]
#![cfg_attr(docsrs, feature(doc_cfg))]

extern crate alloc;
#[cfg(any(feature = "std", test))]
extern crate std;

pub mod errors;
pub mod event;
pub mod flat;
pub mod flatten;
pub mod limits;
pub mod observation;
pub mod scope;

pub use errors::{CompileError, HistoryError};
pub use event::{Grant, Request};
pub use flatten::flatten_rule;
