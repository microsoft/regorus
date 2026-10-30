#![no_std]
// Verus generates erased unsafe scaffolding for native specifications.
#![cfg_attr(not(verus_keep_ghost), forbid(unsafe_code))]
#![cfg_attr(verus_keep_ghost, feature(proc_macro_hygiene, allocator_api))]
#![cfg_attr(docsrs, feature(doc_cfg))]

extern crate alloc;
#[cfg(any(feature = "std", test))]
extern crate std;

pub mod event;
pub mod syntax;
#[cfg(verus_keep_ghost)]
pub mod verify;

pub use event::Event;
pub use frunk_core::Coprod;
pub use frunk_core::coproduct::{CNil, Coproduct};
pub use syntax::{
    AtomPattern, Comparison, Component, ComponentPattern, Head, RegexExpr, Rule, RuleMode, TestExpr,
};
