#![no_std]
#![cfg_attr(not(verus_keep_ghost), forbid(unsafe_code))]
#![cfg_attr(verus_keep_ghost, feature(proc_macro_hygiene, allocator_api))]
#![cfg_attr(docsrs, feature(doc_cfg))]

extern crate alloc;
#[cfg(any(feature = "std", test))]
extern crate std;

#[cfg(feature = "runtime")]
pub(crate) mod compile;
#[cfg(feature = "runtime")]
#[cfg_attr(docsrs, doc(cfg(feature = "runtime")))]
pub mod compiled_rule;
#[cfg(feature = "runtime")]
#[cfg_attr(docsrs, doc(cfg(feature = "runtime")))]
mod error;
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
#[cfg(all(verus_keep_ghost, feature = "runtime"))]
pub mod spec;
#[cfg(feature = "runtime")]
pub(crate) mod symbolic;
#[cfg(feature = "runtime")]
#[cfg_attr(docsrs, doc(cfg(feature = "runtime")))]
mod symbolic_language;
#[cfg(feature = "runtime")]
#[cfg_attr(docsrs, doc(cfg(feature = "runtime")))]
pub mod validator;
#[cfg(all(verus_keep_ghost, feature = "runtime"))]
pub mod verify;
#[cfg(all(verus_keep_ghost, feature = "runtime"))]
pub use compile::verify as compile_verify;
#[cfg(all(verus_keep_ghost, feature = "runtime"))]
pub use normalize::verify as normalize_verify;
#[cfg(all(verus_keep_ghost, feature = "runtime"))]
pub use symbolic::verify as symbolic_verify;

#[cfg(feature = "runtime")]
pub(crate) type WorkVec<T> = smallvec::SmallVec<[T; 4]>;

#[cfg(feature = "runtime")]
pub use compiled_rule::CompiledRule;
#[cfg(feature = "runtime")]
pub use error::PolicyError;
#[cfg(feature = "runtime")]
pub use policy::{PolicyDecision, TracePolicy, TraceRule};
#[cfg(feature = "runtime")]
pub use runtime::RuleRuntime;
#[cfg(feature = "runtime")]
pub use symbolic_language::SymbolicLanguage;
#[cfg(all(verus_keep_ghost, feature = "runtime"))]
pub use symbolic_language::verify as symbolic_language_verify;
#[cfg(feature = "runtime")]
pub use validator::{Decision, Denial, Validator};

#[cfg(all(test, feature = "runtime"))]
mod graph_tests;
