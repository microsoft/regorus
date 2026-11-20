#![no_std]
#![forbid(unsafe_code)]
#![cfg_attr(docsrs, feature(doc_cfg))]

extern crate alloc;
#[cfg(any(feature = "std", test))]
extern crate std;

pub mod event;
pub mod key_hash;
pub mod syntax;

pub use event::{
    Arity, Component2, Component3, Component4, Event, MAX_ARITY, N1, N2, N3, N4, N5, N6, N7, N8,
};
pub use key_hash::KeyHash;
pub use syntax::{
    AtomPattern, Comparison, Component, ComponentPattern, Head, RegexExpr, Rule, RuleMode, TestExpr,
};
