#![no_std]
#![cfg_attr(not(verus_keep_ghost), forbid(unsafe_code))]
#![cfg_attr(verus_keep_ghost, feature(proc_macro_hygiene, allocator_api))]
#![cfg_attr(docsrs, feature(doc_cfg))]

extern crate alloc;
#[cfg(any(feature = "std", test))]
extern crate std;

#[cfg(feature = "runtime")]
#[cfg_attr(docsrs, doc(cfg(feature = "runtime")))]
pub mod compile;
#[cfg(feature = "runtime")]
#[cfg_attr(docsrs, doc(cfg(feature = "runtime")))]
pub mod compiled_rule;
#[cfg(feature = "runtime")]
#[cfg_attr(docsrs, doc(cfg(feature = "runtime")))]
pub mod error;
#[cfg(feature = "runtime")]
pub(crate) mod normalize;
#[cfg(feature = "runtime")]
#[cfg_attr(docsrs, doc(cfg(feature = "runtime")))]
pub mod policy;
#[cfg(feature = "runtime")]
pub(crate) mod progress;
#[cfg(feature = "runtime")]
#[cfg_attr(docsrs, doc(cfg(feature = "runtime")))]
pub mod runtime;
#[cfg(feature = "runtime")]
pub(crate) mod symbolic;
#[cfg(feature = "runtime")]
#[cfg_attr(docsrs, doc(cfg(feature = "runtime")))]
pub mod validator;
#[cfg(all(verus_keep_ghost, feature = "runtime"))]
pub mod verify;

#[cfg(feature = "runtime")]
pub(crate) type WorkVec<T> = smallvec::SmallVec<[T; 4]>;

#[cfg(feature = "runtime")]
pub use compiled_rule::CompiledRule;
#[cfg(feature = "runtime")]
pub use error::PolicyError;
#[cfg(feature = "runtime")]
pub use policy::{PolicyDecision, TraceDiagnostic, TracePolicy, TraceRule};
#[cfg(feature = "runtime")]
pub use runtime::{BatchCursor, RuleRuntime};
#[cfg(feature = "runtime")]
pub use validator::{Decision, Denial, Validator, ValidatorBuilder};

#[cfg(all(test, feature = "runtime"))]
mod graph_tests;
