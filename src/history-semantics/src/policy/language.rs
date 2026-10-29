//! The tail shape a state-machine policy classifies a resource's history with.

use history_syntax::{Event, RegexExpr, TestExpr};

/// The last state-changing event on the head resource is `setter`.
///
/// `Concat[All, T(setter), Star(T(stable))]` pins `setter` to the LAST state change: `accepts`
/// explores every split point, and the trailing `Star` forbids any later change.
pub fn last_state_change<E: Event>(setter: TestExpr<E>, stable: TestExpr<E>) -> RegexExpr<E> {
    RegexExpr::concat([
        RegexExpr::all(),
        RegexExpr::test(setter),
        RegexExpr::star(RegexExpr::test(stable)),
    ])
}
