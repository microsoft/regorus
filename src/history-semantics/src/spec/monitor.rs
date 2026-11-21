//! The monitor's guarantees (Theorem `thm:matcher` at the level of `Validator`).
//!
//! A `Validator` is read through `ValidatorView`: the rules passed to `add_rule`, in order, and
//! the committed history (oldest first). `check_step` is the meaning of one `check` against the
//! state before it, `check_frame` what it does to the state; `trace_safe` is the invariant they
//! preserve. All three are stated with the semantics' (`junco_core::spec::semantics`) `policy_permits` and `least_violation` over events.
//! The guarantee is conditional on the hypotheses' (`junco_core::spec::hypotheses`) `event_obligations::<E>()` where the contracts say so:
//! the compiled rules' hash containers are trusted only for faithful keys.

use crate::validator::Decision;
use history_syntax::Event;
use history_syntax::spec::events::RuleView;
use junco_core::HistoryError;
use junco_core::event::Request;
use junco_core::spec::semantics::{least_violation, policy_permits, resource_error};
use vstd::prelude::*;

verus! {

/// What a reviewer needs of a `Validator`: the rules passed to `add_rule`, in order, and the
/// committed history (oldest first).
pub struct ValidatorView<E: Event> {
    pub rules: Seq<RuleView<E::Component>>,
    pub history: Seq<E>,
}

/// Frame of one `check`: rules unchanged; a grant appends exactly the candidate; a denial or an
/// error leaves the history as it was.
pub open spec fn check_frame<E: Event, M>(
    before: ValidatorView<E>, after: ValidatorView<E>, request: Request<E, M>,
    result: Result<Decision<E, M>, HistoryError>,
) -> bool {
    after.rules == before.rules && match result {
        Ok(Decision::Grant(grant)) => grant.event == request.event && grant.metadata == request.metadata
            && after.history == before.history.push(request.event),
        Ok(Decision::Denied(denial)) => denial.event == request.event && after.history == before.history,
        Err(_) => after.history == before.history,
    }
}

/// Meaning of one `check` against the state before it (`thm:matcher`): Grant iff no rule is
/// violated; Denied identifies the least violated rule and its mode; errors are operational resource failures.
pub open spec fn check_step<E: Event, M>(
    before: ValidatorView<E>, request: Request<E, M>, result: Result<Decision<E, M>, HistoryError>,
) -> bool {
    match result {
        Ok(Decision::Grant(_)) => policy_permits(before.rules, request.event, before.history),
        Ok(Decision::Denied(denial)) =>
            least_violation(before.rules, request.event, before.history, denial.index as int)
                && denial.mode == before.rules[denial.index as int].mode,
        Err(error) => resource_error(error),
    }
}

/// Meaning of `permits`: the answer is whether the policy permits the candidate after the
/// committed history, without committing anything.
pub open spec fn permits_result<E: Event>(
    v: ValidatorView<E>, candidate: E, result: Result<bool, HistoryError>,
) -> bool {
    match result {
        Ok(permitted) => permitted == policy_permits(v.rules, candidate, v.history),
        Err(error) => resource_error(error),
    }
}

/// `rollback` only truncates to a prefix; on error nothing changes.
pub open spec fn rollback_step<E: Event>(
    before: ValidatorView<E>, after: ValidatorView<E>, result: Result<(), HistoryError>,
) -> bool {
    after.rules == before.rules && match result {
        Ok(()) => after.history.is_prefix_of(before.history),
        Err(_) => after.history == before.history,
    }
}

/// Trace safety: every committed event was permitted by every rule against its prefix.
pub open spec fn trace_safe<E: Event>(v: ValidatorView<E>) -> bool {
    forall|j: int| 0 <= j < v.history.len()
        ==> policy_permits(v.rules, #[trigger] v.history[j], v.history.take(j))
}

} // verus!
