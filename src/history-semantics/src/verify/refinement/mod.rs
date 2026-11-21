//! Specification hierarchy for the correctness of policy-refinement analysis.
//!
//! Each layer holds definitions, the theorem statements (`stmt_*` spec functions returning the
//! proposition), and their proofs (`theorem_*`, each with `ensures stmt_*(...)`). Every `stmt_*`
//! is proved. The mapping to the paper's results is the index `crate::verify::paper`.
//!
//! Layers, top-down:
//! - [`semantics`]: proofs of the policy questions (refinement iff coverage, redundancy iff
//!   coverage, genericity) and the constants of a rule. What each analyzer verdict means is stated by
//!   the analyzer specification (`history_analysis::spec::analyzer`), over the semantics and the
//!   analysis questions (`junco_core::spec::{semantics, questions}`).
//! - [`encoding`]: typed rules as numeric rules, through the existing verified front end
//!   (`flatten_rule`, `lower_flat`, `compile`), plus renaming invariance for fresh values.
//! - [`inclusion`]: constraints, `Split`, constrained inclusion, and the policy reduction.
//! - [`search`]: items, witnesses, successor cases, and the breadth-first search.
//! - [`pruning`]: state decomposition, dead items, domination, syntactic simulation.
//! - [`finiteness`]: finitely many reachable states, via the abstract model of `finite_states`.
//! - [`implementation`]: graph ids, interned constraints and letters as abstract objects.
pub mod encoding;
pub mod finiteness;
pub mod implementation;
pub mod inclusion;
pub mod pruning;
pub mod search;
pub mod semantics;
