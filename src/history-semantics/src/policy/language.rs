//! The tail shape a state-machine policy classifies a resource's history with.

#[cfg(verus_keep_ghost)]
use alloc::boxed::Box;
use alloc::vec;
#[cfg(verus_keep_ghost)]
use history_syntax::spec::events::RegexView;
use history_syntax::{Event, RegexExpr, TestExpr};
use vstd::prelude::*;

/// A setter event followed only by stable events, with any preceding history.
///
/// Setter and stable tests may overlap; this does not assert a unique last setter.
#[verus_verify]
#[verus_spec(result => ensures result@ == RegexView::Concat(seq![
    RegexView::All, RegexView::Test(setter@),
    RegexView::Star(Box::new(RegexView::Test(stable@))),
]))]
pub fn last_state_change<E: Event>(setter: TestExpr<E>, stable: TestExpr<E>) -> RegexExpr<E> {
    proof_decl! { let ghost expected = seq![RegexView::All, RegexView::Test(setter@),
    RegexView::Star(Box::new(RegexView::Test(stable@)))]; }
    let result = RegexExpr::Concat(vec![
        RegexExpr::all(),
        RegexExpr::test(setter),
        RegexExpr::star(RegexExpr::test(stable)),
    ]);
    proof! {
        reveal_with_fuel(history_syntax::spec::events::regex_view, 3);
        broadcast use {vstd::std_specs::vec::group_vec_axioms, vstd::seq::group_seq_lemmas};
        assert(match result@ { RegexView::Concat(parts) => parts =~= expected, _ => false });
    }
    result
}
