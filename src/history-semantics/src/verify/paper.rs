//! Paper index: one `stmt_<label>` per result of the paper, in paper order, each a
//! proposition over the definitions of its layer and each proved by `theorem_<label>` from the
//! layer that mechanizes it. [`theorem_paper_index`] proves every row at once, so a renamed or
//! deleted statement breaks the index.
//!
//! Paths are relative to `crates/history-semantics/src/verify/`. Definitions (`def:*`) are
//! reviewer-interface files (`docs/verification/INTERFACES.md`) and carry no `stmt_`.
//!
//! | Paper label | `stmt_` (this module) | Mechanized statement | Proof | File |
//! |---|---|---|---|---|
//! | `sec:events` (product events) | — (definition) | `event_view`, `event_laws` | event-law lemmas | `crates/history-syntax/src/spec/events.rs` |
//! | `lem:similarity-language` | `stmt_lem_similarity_language` | `stmt_similarity_preserves_language` | `theorem_similarity_preserves_language` | `history_algebra.rs` |
//! | `lem:sderiv` | `stmt_lem_sderiv` | `stmt_symbolic_derivative_correct` | `theorem_symbolic_derivative_correct` | `history_algebra.rs` |
//! | `thm:sderiv` | `stmt_thm_sderiv` | `stmt_symbolic_run_correct` | `theorem_symbolic_run_correct` | `history_algebra.rs` |
//! | `thm:matcher` | `stmt_thm_matcher` | `stmt_rule_decision` (steps 2–3; step 1 holds by the definition of `pair_lang`), `stmt_similar_tails_same_decision` (normalization) | `theorem_rule_decision`, `theorem_similar_tails_same_decision` | `history_algebra.rs` |
//! | `thm:matcher` (monitor level) | `stmt_matcher` | `check_step` and `trace_safe` for `Validator::check`/`rollback`: a grant means no rule is violated, a denial carries the index and mode of the first violated rule, every reachable history is trace safe | `theorem_matcher`; `theorem_monitor_check`, `theorem_trace_safe`, `theorem_analyzer_to_monitor` and the exec client `monitor_client` in `crates/history-semantics/tests/reviewer.rs` | `crates/history-semantics/src/spec/monitor.rs` |
//! | `def:violates`, `def:policy-violates` | — (definition) | `rule_violated`, `policy_denies`, `least_violation` | — | `crates/junco-core/src/spec/semantics.rs` |
//! | `def:policy-refinement` | — (definition) | `refines`, `covers` | — | `crates/junco-core/src/spec/questions.rs` |
//! | `app:policy-reduction` | `stmt_app_policy_reduction` | `stmt_refines_iff_covers`, `stmt_redundant_iff_covered` (over events); `stmt_vacuity_reductions` (numeric, constrained form); `stmt_vacuity_via_refinement` (typed vacuity through `at_least_as_strict`) | `theorem_refines_iff_covers`, `theorem_redundant_iff_covered`, `theorem_vacuity_reductions`, `theorem_vacuity_via_refinement` | `refinement/semantics.rs`, `refinement/inclusion.rs` |
//! | `prop:policy` | `stmt_prop_policy` | not mechanized as stated; the rule-by-rule reduction `stmt_policy_reduction` and its composition with search outcomes `stmt_policy_search_composition` replace it | `theorem_policy_reduction`, `theorem_policy_search_composition` | `refinement/inclusion.rs` |
//! | `def:constraints`, `def:split` | — (definition) | `Constraint`, `paper_split`; `stmt_paper_split_ok` shows `Split` is a valid split family | `theorem_paper_split_ok` | `refinement/inclusion.rs` |
//! | `def:atoms`, `def:realize`, `def:successors` | — (definition) | `Assignment`, `realizes`, `steps_ok` | — | `refinement/search.rs` |
//! | `lem:succ`, `lem:uniform` | `stmt_lem_succ`, `stmt_lem_uniform` | `stmt_successor_cases` (one statement over successor cases; declared finite domains included) | `theorem_successor_cases` | `refinement/search.rs` |
//! | `thm:search` | `stmt_thm_search` | `stmt_search_correct` (soundness, completeness, minimality, assuming correct successor cases for the expanded items), `stmt_search_terminates` (termination, conditional on finitely many items), `stmt_items_from_states` | `theorem_search_correct`, `theorem_search_terminates`, `theorem_items_from_states`; for the executable, `Search::run` ensuring `search_exec::search_result` (correctness), and `theorem_impl_items_bound` with `search_exec::lemma_running_items_bound` (termination) | `refinement/search.rs`, `refinement/finiteness.rs`, `refinement/implementation.rs` |
//! | `eq:decomposition`, `def:decomposition` | `stmt_eq_decomposition` | `stmt_decomposition` | `theorem_decomposition` | `refinement/pruning.rs` |
//! | `lem:prune`, `def:pruning` | `stmt_lem_prune` | `stmt_prune_sound`, `stmt_checks_discard` | `theorem_prune_sound`, `theorem_checks_discard` | `refinement/pruning.rs` |
//! | `lem:simulation`, `fig:simulation` | `stmt_lem_simulation` | `stmt_sim_rules_sound`, `stmt_test_rules_sound` (the code's relation is smaller than the figure's) | `theorem_sim_rules_sound`, `theorem_test_rules_sound` | `refinement/pruning.rs` |
//! | `lem:finite-states`, `app:finiteness` | `stmt_lem_finite_states` | `stmt_reachable_states_finite`, `stmt_lift_injective`; for the implementation `m_impl().contract()` and the parametric `theorem_impl_finitely_many_items` | `theorem_reachable_states_finite`, `theorem_lift_injective`, `theorem_impl_contract` | `refinement/finiteness.rs`, `finite_impl.rs` |
//! | Executable analyzer (Section 6) | `stmt_analyzer_coverage`, `stmt_analyzer_real_counterexamples`, `stmt_analyzer_refinement`, `stmt_analyzer_redundancy`, `stmt_analyzer_tail_inclusion`, `stmt_analyzer_escapes`, `stmt_analyzer_minimality` (in `crates/history-analysis/tests/reviewer.rs`; the analyzer specification is downstream of this crate) | `covered_spec` decides coverage; counterexamples are real pairs in the domains; `at_least_as_strict_spec`/`redundant_spec`; `tail_included_spec`; escapes (`no_invariant_failure`, `Exhausted` claims nothing); `minimal_in_case` | `theorem_covered_decision`, `theorem_real_counterexamples`, `theorem_refinement`, `theorem_redundancy`, `theorem_tail_inclusion`, `theorem_escapes`, `theorem_minimality`, `theorem_vacuity_corollaries`, `analyzer_client` | `crates/history-analysis/src/spec/analyzer.rs`, `crates/history-analysis/tests/reviewer.rs` |
//!
//! Auxiliary statements, not paper results but cited by `app:mech-diff`: `stmt_genericity`
//! (`refinement/semantics.rs`), `stmt_numeric_genericity`, `stmt_source_regex_local`,
//! `stmt_front_end_denies` (`refinement/encoding.rs`), `stmt_paper_split_ok`
//! (`refinement/inclusion.rs`).
//!
//! Sections and algorithms, with the module whose definitions follow them: `sec:rules`,
//! `sec:policy` (`refinement/semantics.rs`); `sec:search-state`, `sec:search`, `alg:succ`,
//! `alg:search`, `app:cases`, `app:search-proof` (`refinement/search.rs`); `app:pruning`,
//! `app:simulation` (`refinement/pruning.rs`); `app:mech-diff` (the differences, listed in
//! `VERIFY.md`).
use crate::spec::monitor::{ValidatorView, check_frame, check_step, rollback_step, trace_safe};
use crate::validator::{Decision, verify as validator};
use crate::verify::finite_impl;
use crate::verify::history_algebra as algebra;
use crate::verify::refinement::{encoding, finiteness, inclusion, pruning, search, semantics};
use history_syntax::Event;
use junco_core::HistoryError;
use junco_core::event::Request;
use junco_core::kernel::verify as model;
use junco_core::spec::semantics as sem;
use junco_core::verify::history_specs::SrcTest;
use vstd::prelude::*;

verus! {

/// Proposition Similarity preserves language (`lem:similarity-language`).
pub open spec fn stmt_lem_similarity_language() -> bool {
    algebra::stmt_similarity_preserves_language()
}

pub proof fn theorem_lem_similarity_language()
    ensures stmt_lem_similarity_language(),
{
    algebra::theorem_similarity_preserves_language();
}

/// Lemma One-step correctness (`lem:sderiv`), for any letter type `L`.
pub open spec fn stmt_lem_sderiv<L>() -> bool {
    algebra::stmt_symbolic_derivative_correct::<L>()
}

pub proof fn theorem_lem_sderiv<L>()
    ensures stmt_lem_sderiv::<L>(),
{
    algebra::theorem_symbolic_derivative_correct::<L>();
}

/// Theorem Symbolic derivative correctness (`thm:sderiv`), for any letter type `L`.
pub open spec fn stmt_thm_sderiv<L>() -> bool {
    algebra::stmt_symbolic_run_correct::<L>()
}

pub proof fn theorem_thm_sderiv<L>()
    ensures stmt_thm_sderiv::<L>(),
{
    algebra::theorem_symbolic_run_correct::<L>();
}

/// Theorem Matcher correctness (`thm:matcher`) over the paper-shaped numeric rules: a fired rule
/// decides by the symbolic run under its head substitution, and similar tails decide alike. That
/// an unmatched head does not fire holds by the definition of `pair_lang`. At the level of
/// `Validator::check` the theorem is `check_step`.
pub open spec fn stmt_thm_matcher() -> bool {
    &&& algebra::stmt_rule_decision()
    &&& algebra::stmt_similar_tails_same_decision()
}

pub proof fn theorem_thm_matcher()
    ensures stmt_thm_matcher(),
{
    algebra::theorem_rule_decision();
    algebra::theorem_similar_tails_same_decision();
}

/// Theorem Matcher correctness at the level of `Validator` (`thm:matcher`): a `check` whose
/// result satisfies `check_step` grants only when no rule is violated, denies with the index and
/// mode of the first violated rule in source order, and never fails with an invariant error; a `check` or
/// `rollback` preserves `trace_safe`.
pub open spec fn stmt_matcher<E: Event, M>() -> bool {
    &&& forall|before: ValidatorView<E>, request: Request<E, M>, result: Result<Decision<E, M>, HistoryError>|
        #[trigger] check_step(before, request, result) ==> match result {
            Ok(Decision::Grant(_)) => forall|i: int| 0 <= i < before.rules.len()
                ==> !sem::rule_violated(#[trigger] before.rules[i], request.event, before.history),
            Ok(Decision::Denied(denial)) => exists|i: int| 0 <= i < before.rules.len()
                && sem::rule_violated(#[trigger] before.rules[i], request.event, before.history)
                && denial.mode == before.rules[i].mode
                && i == denial.index as int
                && forall|j: int| 0 <= j < i ==> !sem::rule_violated(#[trigger] before.rules[j], request.event, before.history),
            Err(error) => !(error is Invariant),
        }
    &&& forall|before: ValidatorView<E>, after: ValidatorView<E>, request: Request<E, M>, result: Result<Decision<E, M>, HistoryError>|
        trace_safe(before) && #[trigger] check_frame(before, after, request, result) && check_step(before, request, result)
        ==> trace_safe(after)
    &&& forall|before: ValidatorView<E>, after: ValidatorView<E>, result: Result<(), HistoryError>|
        trace_safe(before) && #[trigger] rollback_step(before, after, result) ==> trace_safe(after)
}

pub proof fn theorem_matcher<E: Event, M>()
    ensures stmt_matcher::<E, M>(),
{
    assert forall|before: ValidatorView<E>, request: Request<E, M>, result: Result<Decision<E, M>, HistoryError>|
        #[trigger] check_step(before, request, result) implies match result {
            Ok(Decision::Grant(_)) => forall|i: int| 0 <= i < before.rules.len()
                ==> !sem::rule_violated(#[trigger] before.rules[i], request.event, before.history),
            Ok(Decision::Denied(denial)) => exists|i: int| 0 <= i < before.rules.len()
                && sem::rule_violated(#[trigger] before.rules[i], request.event, before.history)
                && denial.mode == before.rules[i].mode
                && i == denial.index as int
                && forall|j: int| 0 <= j < i ==> !sem::rule_violated(#[trigger] before.rules[j], request.event, before.history),
            Err(error) => !(error is Invariant),
        } by {
        match result {
            Ok(Decision::Grant(_)) => {
                assert forall|i: int| 0 <= i < before.rules.len()
                    implies !sem::rule_violated(#[trigger] before.rules[i], request.event, before.history) by {
                    if sem::rule_violated(before.rules[i], request.event, before.history) {
                        assert(sem::policy_denies(before.rules, request.event, before.history));
                    }
                }
            },
            Ok(Decision::Denied(denial)) => {
                let i = denial.index as int;
                assert(sem::rule_violated(before.rules[i], request.event, before.history));
            },
            Err(_) => {},
        }
    }
    assert forall|before: ValidatorView<E>, after: ValidatorView<E>, request: Request<E, M>, result: Result<Decision<E, M>, HistoryError>|
        trace_safe(before) && #[trigger] check_frame(before, after, request, result) && check_step(before, request, result)
        implies trace_safe(after) by {
        validator::lemma_check_preserves_trace_safe(before, after, request, result);
    }
    assert forall|before: ValidatorView<E>, after: ValidatorView<E>, result: Result<(), HistoryError>|
        trace_safe(before) && #[trigger] rollback_step(before, after, result) implies trace_safe(after) by {
        validator::lemma_rollback_preserves_trace_safe(before, after, result);
    }
}

/// Reductions of refinement, redundancy and vacuity (appendix `app:policy-reduction`): refinement
/// is rule-by-rule coverage, redundancy is coverage by the rest, and the vacuity questions are
/// constrained inclusions of denial expressions.
pub open spec fn stmt_app_policy_reduction<E: Event>() -> bool {
    &&& semantics::stmt_refines_iff_covers::<E>()
    &&& semantics::stmt_redundant_iff_covered::<E>()
    &&& inclusion::stmt_vacuity_reductions()
    &&& inclusion::stmt_vacuity_via_refinement::<E>()
}

pub proof fn theorem_app_policy_reduction<E: Event>()
    ensures stmt_app_policy_reduction::<E>(),
{
    semantics::theorem_refines_iff_covers::<E>();
    semantics::theorem_redundant_iff_covered::<E>();
    inclusion::theorem_vacuity_reductions();
    inclusion::theorem_vacuity_via_refinement::<E>();
}

/// Proposition Refinement as inclusion (`prop:policy`) is not mechanized as stated; what the
/// analyzer uses and what is proved is the rule-by-rule reduction over split cases and its
/// composition with the search outcomes.
pub open spec fn stmt_prop_policy() -> bool {
    &&& inclusion::stmt_policy_reduction()
    &&& inclusion::stmt_policy_search_composition()
}

pub proof fn theorem_prop_policy()
    ensures stmt_prop_policy(),
{
    inclusion::theorem_policy_reduction();
    inclusion::theorem_policy_search_composition();
}

/// Lemma Computing successors (`lem:succ`): the successor cases of an item are finite, entail the
/// item's constraint, and compute the derivative for every realizing valuation and event.
pub open spec fn stmt_lem_succ() -> bool {
    search::stmt_successor_cases()
}

pub proof fn theorem_lem_succ()
    ensures stmt_lem_succ(),
{
    search::theorem_successor_cases();
}

/// Lemma Uniform reachability (`lem:uniform`): every valuation of a case's constraint realizes
/// the case with some event in the domains, and every pair belongs to exactly one case. Stated
/// together with `lem:succ` as `stmt_successor_cases`.
pub open spec fn stmt_lem_uniform() -> bool {
    search::stmt_successor_cases()
}

pub proof fn theorem_lem_uniform()
    ensures stmt_lem_uniform(),
{
    search::theorem_successor_cases();
}

/// Inclusion search correctness and minimum counterexample length under complete successor
/// cases for expanded trace nodes; termination given finitely many reachable items, which
/// finitely many reachable states provide.
pub open spec fn stmt_thm_search() -> bool {
    &&& search::stmt_search_correct()
    &&& search::stmt_search_terminates()
    &&& finiteness::stmt_items_from_states()
}

pub proof fn theorem_thm_search()
    ensures stmt_thm_search(),
{
    search::theorem_search_correct();
    search::theorem_search_terminates();
    finiteness::theorem_items_from_states();
}

/// Equation `eq:decomposition`: a state's language is the intersection of its required parts
/// minus the union of its excluded parts.
pub open spec fn stmt_eq_decomposition() -> bool {
    pruning::stmt_decomposition()
}

pub proof fn theorem_eq_decomposition()
    ensures stmt_eq_decomposition(),
{
    pruning::theorem_decomposition();
}

/// Lemma Pruning soundness (`lem:prune`): the implemented checks only discard items the search
/// may discard.
pub open spec fn stmt_lem_prune() -> bool {
    &&& pruning::stmt_prune_sound()
    &&& pruning::stmt_checks_discard()
}

pub proof fn theorem_lem_prune()
    ensures stmt_lem_prune(),
{
    pruning::theorem_prune_sound();
    pruning::theorem_checks_discard();
}

/// Lemma Simulation soundness (`lem:simulation`): the syntactic simulation rules on states and on
/// tests imply language inclusion.
pub open spec fn stmt_lem_simulation() -> bool {
    &&& pruning::stmt_sim_rules_sound()
    &&& pruning::stmt_test_rules_sound()
}

pub proof fn theorem_lem_simulation()
    ensures stmt_lem_simulation(),
{
    pruning::theorem_sim_rules_sound();
    pruning::theorem_test_rules_sound();
}

/// Lemma Finitely many residuals (`lem:finite-states`): under the normalizer contract every state
/// reachable from a state lies in a finite set; the implementation's model satisfies the contract
/// and its graph abstraction is injective.
pub open spec fn stmt_lem_finite_states() -> bool {
    &&& finiteness::stmt_reachable_states_finite()
    &&& finiteness::stmt_lift_injective()
    &&& finite_impl::m_impl().contract()
}

pub proof fn theorem_lem_finite_states()
    ensures stmt_lem_finite_states(),
{
    finiteness::theorem_reachable_states_finite();
    finiteness::theorem_lift_injective();
    finite_impl::theorem_impl_contract();
}

/// Every row of the table above, plus the auxiliary statements, in one proof.
pub proof fn theorem_paper_index<E: Event>()
    ensures
        stmt_lem_similarity_language(),
        stmt_lem_sderiv::<SrcTest>(),
        stmt_lem_sderiv::<model::Test>(),
        stmt_thm_sderiv::<SrcTest>(),
        stmt_thm_sderiv::<model::Test>(),
        stmt_thm_matcher(),
        stmt_matcher::<E, ()>(),
        stmt_app_policy_reduction::<E>(),
        stmt_prop_policy(),
        inclusion::stmt_paper_split_ok(),
        stmt_lem_succ(),
        stmt_lem_uniform(),
        stmt_thm_search(),
        stmt_eq_decomposition(),
        stmt_lem_prune(),
        stmt_lem_simulation(),
        stmt_lem_finite_states(),
        semantics::stmt_genericity::<E>(),
        encoding::stmt_numeric_genericity(),
        encoding::stmt_source_regex_local(),
        encoding::stmt_front_end_denies::<E>(),
{
    theorem_lem_similarity_language();
    theorem_lem_sderiv::<SrcTest>();
    theorem_lem_sderiv::<model::Test>();
    theorem_thm_sderiv::<SrcTest>();
    theorem_thm_sderiv::<model::Test>();
    theorem_thm_matcher();
    theorem_matcher::<E, ()>();
    theorem_app_policy_reduction::<E>();
    theorem_prop_policy();
    inclusion::theorem_paper_split_ok();
    theorem_lem_succ();
    theorem_lem_uniform();
    theorem_thm_search();
    theorem_eq_decomposition();
    theorem_lem_prune();
    theorem_lem_simulation();
    theorem_lem_finite_states();
    semantics::theorem_genericity::<E>();
    encoding::theorem_numeric_genericity();
    encoding::theorem_source_regex_local();
    encoding::theorem_front_end_denies::<E>();
}

} // verus!
