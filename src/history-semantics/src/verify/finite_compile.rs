//! Compiled tails are hereditary normal forms: every test and regex `CompiledPair::compile`
//! (`compile.rs`) builds from a flat rule lifts to a normal form (`finite_impl::test_nf`,
//! `finite_impl::regex_nf`), so the lifted root of a compiled pair is a state of
//! `finite_impl::m_impl` (the `instantiation_ok` obligation of `refinement::finiteness`).
//! One lemma per constructor used by `compile`: constants and atoms, `TestId::connective`
//! ([`lemma_connective_nf`]), `RegexId::from_test`, `concat`, `set`, `not` (via the
//! `finite_link` lemmas), and `star` (its own ensures, [`lemma_star_future`]).
use crate::normalize::verify as norm;
use crate::verify::finite_impl::*;
use crate::verify::finite_link::*;
use crate::verify::finite_trans::lemma_cat_nf;
use alloc::boxed::Box;
use junco_core::kernel::verify as model;
use junco_core::kernel::{RegexId, TestId};
use junco_core::verify::history_specs::Regex;
use vstd::prelude::*;

verus! {

broadcast use junco_core::kernel::verify::group_kernel_views;

pub open spec fn tests_nf(g: model::Graph, ts: Seq<TestId>) -> bool {
    forall|k: int| #![trigger ts[k]] 0 <= k < ts.len() ==> ts[k]@ < g.tests.len() && test_nf(model::lift_test(g, ts[k]@))
}

/// The tests and regexes built so far by `compile` are normal forms.
#[verifier::opaque]
pub open spec fn compiled_nf(g: model::Graph, ts: Seq<TestId>, rs: Seq<RegexId>) -> bool {
    tests_nf(g, ts) && norm::regex_ids_valid(g, rs) && ids_nf(g, rs)
}

pub proof fn lemma_compiled_empty(g: model::Graph)
    ensures compiled_nf(g, Seq::empty(), Seq::empty()),
{
    reveal(compiled_nf);
}

pub proof fn lemma_compiled_stable(a: model::Graph, b: model::Graph, ts: Seq<TestId>, rs: Seq<RegexId>)
    requires model::graph_wf(a), model::graph_extends(a, b), compiled_nf(a, ts, rs),
    ensures compiled_nf(b, ts, rs),
{
    reveal(compiled_nf);
    model::lemma_graph_wf_elim(a);
    assert forall|k: int| #![trigger ts[k]] 0 <= k < ts.len() implies ts[k]@ < b.tests.len() && test_nf(model::lift_test(b, ts[k]@)) by {
        model::lemma_lift_test_stable(a, b, ts[k]@);
    }
    assert forall|k: int| 0 <= k < rs.len() implies rs[k]@ < b.regexes.len() by {}
    assert forall|k: int| 0 <= k < rs.len() implies regex_nf(#[trigger] model::lift_regex(b, rs[k]@)) by {
        assert(rs[k]@ < a.regexes.len());
        model::lemma_lift_regex_stable(a, b, rs[k]@);
    }
}

/// The `k`-th compiled regex.
pub proof fn lemma_compiled_regex(g: model::Graph, ts: Seq<TestId>, rs: Seq<RegexId>, k: int)
    requires compiled_nf(g, ts, rs), 0 <= k < rs.len(),
    ensures rs[k]@ < g.regexes.len(), regex_nf(model::lift_regex(g, rs[k]@)),
{
    reveal(compiled_nf);
}

pub proof fn lemma_compiled_test(g: model::Graph, ts: Seq<TestId>, rs: Seq<RegexId>, k: int)
    requires compiled_nf(g, ts, rs), 0 <= k < ts.len(),
    ensures ts[k]@ < g.tests.len(), test_nf(model::lift_test(g, ts[k]@)),
{
    reveal(compiled_nf);
}

pub proof fn lemma_push_test(before: model::Graph, after: model::Graph, ts: Seq<TestId>, rs: Seq<RegexId>, id: TestId)
    requires model::graph_wf(before), model::graph_extends(before, after), compiled_nf(before, ts, rs),
        id@ < after.tests.len(), test_nf(model::lift_test(after, id@)),
    ensures compiled_nf(after, ts.push(id), rs),
{
    lemma_compiled_stable(before, after, ts, rs);
    reveal(compiled_nf);
    assert forall|k: int| #![trigger ts.push(id)[k]] 0 <= k < ts.push(id).len()
        implies ts.push(id)[k]@ < after.tests.len() && test_nf(model::lift_test(after, ts.push(id)[k]@)) by {
        if k < ts.len() { assert(ts.push(id)[k] == ts[k]); }
    }
}

pub proof fn lemma_push_regex(before: model::Graph, after: model::Graph, ts: Seq<TestId>, rs: Seq<RegexId>, id: RegexId)
    requires model::graph_wf(before), model::graph_extends(before, after), compiled_nf(before, ts, rs),
        id@ < after.regexes.len(), regex_nf(model::lift_regex(after, id@)),
    ensures compiled_nf(after, ts, rs.push(id)),
{
    lemma_compiled_stable(before, after, ts, rs);
    reveal(compiled_nf);
    assert forall|k: int| 0 <= k < rs.push(id).len() implies rs.push(id)[k]@ < after.regexes.len() by {
        if k < rs.len() { assert(rs.push(id)[k] == rs[k]); }
    }
    assert forall|k: int| 0 <= k < rs.push(id).len() implies regex_nf(#[trigger] model::lift_regex(after, rs.push(id)[k]@)) by {
        if k < rs.len() { assert(rs.push(id)[k] == rs[k]); }
    }
}

// ===== tests =====

/// Constants and atoms are normal forms.
pub proof fn lemma_test_simple_nf(g: model::Graph, id: nat)
    requires model::graph_wf(g),
        id == g.constants.test_true || id == g.constants.test_false || (id < g.tests.len() && g.tests[id as int] is Atom),
    ensures id < g.tests.len(), test_nf(model::lift_test(g, id)),
{
    norm::regex_constants(g);
    if id < g.tests.len() { lemma_test_lift(g, id); }
}

/// `TestId::connective` on normal-form operands (`test_connective_result`) is a normal form.
pub proof fn lemma_connective_nf(before: model::Graph, after: model::Graph, ts: Seq<TestId>, rs: Seq<RegexId>,
    children: Seq<u32>, selected: Seq<TestId>, and: bool, r: nat)
    requires model::graph_wf(before), model::graph_wf(after), model::graph_extends(before, after), compiled_nf(before, ts, rs),
        selected.len() == children.len(),
        forall|i: int| 0 <= i < children.len() ==> #[trigger] children[i] < ts.len() && selected[i] == ts[children[i] as int],
        r < after.tests.len(), norm::test_connective_result(before, after, selected, and, r),
    ensures test_nf(model::lift_test(after, r)),
{
    reveal(compiled_nf);
    norm::regex_constants(before);
    model::lemma_graph_wf_elim(before);
    assert forall|k: int| 0 <= k < selected.len() implies #[trigger] selected[k]@ < before.tests.len()
        && test_nf(model::lift_test(before, selected[k]@)) by {
        assert(children[k] < ts.len());
        assert(selected[k] == ts[children[k] as int]);
    }
    if r == before.constants.test_true || r == before.constants.test_false {
        model::lemma_lift_test_stable(before, after, r);
    } else if norm::test_member(before, selected, and, r) {
        lemma_test_member_link(before, selected, and, r);
        model::lemma_lift_test_stable(before, after, r);
    } else {
        lemma_test_lift(after, r);
        match after.tests[r as int] {
            model::TestNode::And(ks) => { lemma_connective_kids(before, after, selected, and, r, ks); },
            model::TestNode::Or(ks) => { lemma_connective_kids(before, after, selected, and, r, ks); },
            _ => {},
        }
    }
}

// ===== regexes =====

pub proof fn lemma_regex_const_nf(g: model::Graph, id: nat)
    requires model::graph_wf(g), id == g.constants.empty || id == g.constants.all || id == g.constants.epsilon,
    ensures id < g.regexes.len(), regex_nf(model::lift_regex(g, id)),
{
    norm::regex_constants(g);
}

/// `RegexId::from_test` on a compiled test.
pub proof fn lemma_from_test_nf(before: model::Graph, after: model::Graph, ts: Seq<TestId>, rs: Seq<RegexId>, k: int, id: nat)
    requires model::graph_wf(before), model::graph_wf(after), model::graph_extends(before, after), compiled_nf(before, ts, rs),
        0 <= k < ts.len(), id < after.regexes.len(),
        if ts[k]@ == after.constants.test_false { id == after.constants.empty }
            else { after.regexes[id as int].kind == model::RegexKindNode::Test(ts[k]@) },
    ensures regex_nf(model::lift_regex(after, id)),
{
    lemma_compiled_test(before, ts, rs, k);
    norm::regex_constants(after);
    model::lemma_graph_wf_elim(before);
    if ts[k]@ != after.constants.test_false {
        lemma_regex_lift(after, id);
        model::lemma_lift_test_stable(before, after, ts[k]@);
    }
}

pub proof fn lemma_selected_nf(g: model::Graph, ts: Seq<TestId>, rs: Seq<RegexId>, children: Seq<u32>, selected: Seq<RegexId>)
    requires compiled_nf(g, ts, rs), selected.len() == children.len(),
        forall|i: int| 0 <= i < children.len() ==> #[trigger] children[i] < rs.len() && selected[i] == rs[children[i] as int],
    ensures norm::regex_ids_valid(g, selected), ids_nf(g, selected),
{
    reveal(compiled_nf);
    assert forall|i: int| 0 <= i < selected.len() implies selected[i]@ < g.regexes.len() by {
        assert(children[i] < rs.len());
        assert(selected[i] == rs[children[i] as int]);
    }
    assert forall|i: int| 0 <= i < selected.len() implies regex_nf(#[trigger] model::lift_regex(g, selected[i]@)) by {
        assert(children[i] < rs.len());
        assert(selected[i] == rs[children[i] as int]);
    }
}

/// `RegexId::concat` on compiled regexes.
pub proof fn lemma_concat_nf(before: model::Graph, after: model::Graph, ts: Seq<TestId>, rs: Seq<RegexId>,
    children: Seq<u32>, selected: Seq<RegexId>, id: nat)
    requires model::graph_wf(before), model::graph_wf(after), model::graph_extends(before, after), compiled_nf(before, ts, rs),
        selected.len() == children.len(),
        forall|i: int| 0 <= i < children.len() ==> #[trigger] children[i] < rs.len() && selected[i] == rs[children[i] as int],
        id < after.regexes.len(), norm::regex_concat_result(before, after, selected, id),
    ensures regex_nf(model::lift_regex(after, id)),
{
    lemma_selected_nf(before, ts, rs, children, selected);
    lemma_concat_link(before, after, selected, id);
    let xs = lifts(before, selected);
    assert forall|i: int| 0 <= i < xs.len() implies regex_nf(#[trigger] xs[i]) by {
        assert(xs[i] == model::lift_regex(before, selected[i]@));
    }
    lemma_cat_nf(xs);
}

/// `RegexId::set` on compiled regexes.
pub proof fn lemma_set_nf(before: model::Graph, after: model::Graph, ts: Seq<TestId>, rs: Seq<RegexId>,
    children: Seq<u32>, selected: Seq<RegexId>, inter: bool, id: nat)
    requires model::graph_wf(before), model::graph_wf(after), model::graph_extends(before, after), compiled_nf(before, ts, rs),
        selected.len() == children.len(),
        forall|i: int| 0 <= i < children.len() ==> #[trigger] children[i] < rs.len() && selected[i] == rs[children[i] as int],
        id < after.regexes.len(),
        norm::regex_set_flat_inputs(before, selected, inter) ==> norm::regex_set_shape(before, after, selected, inter, id),
    ensures regex_nf(model::lift_regex(after, id)),
{
    lemma_selected_nf(before, ts, rs, children, selected);
    lemma_flat_inputs(before, selected, inter);
    lemma_set_link(before, after, selected, inter, id);
}

/// `RegexId::not` on a compiled regex.
pub proof fn lemma_not_nf(before: model::Graph, after: model::Graph, ts: Seq<TestId>, rs: Seq<RegexId>, k: int, id: nat)
    requires model::graph_wf(before), model::graph_wf(after), model::graph_extends(before, after), compiled_nf(before, ts, rs),
        0 <= k < rs.len(), id < after.regexes.len(), norm::regex_not_result(after, rs[k]@, id),
    ensures regex_nf(model::lift_regex(after, id)),
{
    lemma_compiled_regex(before, ts, rs, k);
    model::lemma_graph_wf_elim(before);
    model::lemma_lift_regex_stable(before, after, rs[k]@);
    lemma_not_link(after, rs[k]@, id);
}

/// Before `RegexId::star`'s head match: each of its outputs is a normal form when its operand is.
pub proof fn lemma_star_future(g0: model::Graph, this: nat)
    requires model::graph_wf(g0), this < g0.regexes.len(),
    ensures forall|g1: model::Graph, id: nat| model::graph_extends(g0, g1) && model::graph_wf(g1)
        && (id == g0.constants.epsilon || id == g0.constants.all || id == this
            || (id < g1.regexes.len() && g1.regexes[id as int].kind == model::RegexKindNode::Star(this)))
        && regex_nf(model::lift_regex(g0, this))
        ==> regex_nf(#[trigger] model::lift_regex(g1, id)),
{
    assert forall|g1: model::Graph, id: nat| model::graph_extends(g0, g1) && model::graph_wf(g1)
        && (id == g0.constants.epsilon || id == g0.constants.all || id == this
            || (id < g1.regexes.len() && g1.regexes[id as int].kind == model::RegexKindNode::Star(this)))
        && regex_nf(model::lift_regex(g0, this))
        implies regex_nf(#[trigger] model::lift_regex(g1, id)) by {
        model::lemma_graph_wf_elim(g0);
        norm::regex_constants(g1);
        model::lemma_lift_regex_stable(g0, g1, this);
        if id == g0.constants.epsilon || id == g0.constants.all || id == this {
        } else {
            lemma_regex_lift(g1, id);
            assert(model::lift_regex(g1, id) == Regex::<model::Test>::Star(Box::new(model::lift_regex(g1, this))));
        }
    }
}

} // verus!
