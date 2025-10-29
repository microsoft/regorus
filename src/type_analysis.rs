//! Static type analysis and constant propagation for Regorus queries.
//!
//! The type analysis module walks Rego queries following the execution
//! order computed by the scheduler. For every expression it records a
//! lightweight type descriptor together with constant information when the
//! value can be statically determined. The results are stored in
//! [`Lookup`](crate::lookup::Lookup) tables so that other subsystems (the
//! VS Code plugin, validation passes, or even the interpreter itself in the
//! future) can reuse the inferred information without mutating the AST.
//!
//! The implementation purposefully reuses existing building blocks:
//!
//! * [`schema`](crate::schema) provides the authoritative types for
//!   `input` and `data` roots.
//! * [`lookup`](crate::lookup::Lookup) stores per-expression facts so that
//!   we never need to modify nodes inside `ast`.
//! * [`scheduler`](crate::scheduler::Schedule) dictates the order in which
//!   statements are analysed, matching the interpreter's execution model.
//!
//! The module is split across a couple of dedicated files so the concerns
//! remain focused:
//!
//! * `model.rs` contains the type representations shared across the
//!   analysis.
//! * `context.rs` keeps the lookup tables and scoped environments used
//!   while walking queries.
//! * `constants.rs` exposes a tiny helper for tracking constant values.
//! * `propagation/` contains the analyser pipeline split across smaller
//!   units so orchestration, expression handling, and helpers stay focused.

pub mod builtins;
pub mod constants;
pub mod context;
pub mod model;
pub mod propagation;
pub mod result;
pub(crate) mod value_utils;

pub use constants::{ConstantFact, ConstantStore};
pub use context::{LookupContext, ScopedBindings};
pub use model::{
    ConstantValue, HybridType, HybridTypeKind, PathSegment, RuleAnalysis, RuleConstantState,
    SourceOrigin, SourceRoot, StructuralObjectShape, StructuralType, TypeDescriptor,
    TypeDiagnostic, TypeDiagnosticKind, TypeFact, TypeProvenance,
};
pub use propagation::{AnalysisState, TypeAnalysisOptions, TypeAnalyzer};
pub use result::TypeAnalysisResult;
