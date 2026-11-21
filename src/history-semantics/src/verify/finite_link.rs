//! Link between the implemented regex constructors and the model `verify::finite_impl::m_impl`.
//!
//! The constructors' postconditions in `normalize::verify` (`regex_not_result`,
//! `regex_concat_result`, `regex_set_shape`, `test_connective_result`) are stated on graph ids.
//! Lifted to trees, they say that the implementation's outputs are outputs of the model's
//! constructors applied to the lifted inputs ((N1)–(N4) and the combined tests of (N5)), and that
//! hereditary normal forms are preserved ((N0)): [`lemma_not_link`], [`lemma_concat_link`],
//! [`lemma_set_link`].
use crate::normalize::verify as norm;
use crate::verify::finite_impl::*;
use crate::verify::finite_states::*;
use crate::verify::refinement::finiteness::{
    lemma_lift_regex_injective, lemma_lift_test_injective,
};
use junco_core::kernel::verify as model;
use junco_core::kernel::{RegexId, TestId};
use junco_core::verify::history_specs::Regex;
use vstd::prelude::*;

verus! {

broadcast use junco_core::kernel::verify::group_kernel_views;

/// The lifted trees of `ids`.
pub open spec fn lifts(g: model::Graph, ids: Seq<RegexId>) -> Seq<R> {
    Seq::new(ids.len(), |i: int| model::lift_regex(g, ids[i]@))
}

pub open spec fn lift_set(g: model::Graph, ids: Seq<RegexId>) -> Set<R> {
    lifts(g, ids).to_set()
}

pub open spec fn ids_nf(g: model::Graph, ids: Seq<RegexId>) -> bool {
    forall|i: int| 0 <= i < ids.len() ==> regex_nf(#[trigger] model::lift_regex(g, ids[i]@))
}

pub open spec fn nats_nf(g: model::Graph, ids: Seq<nat>) -> bool {
    forall|i: int| 0 <= i < ids.len() ==> regex_nf(#[trigger] model::lift_regex(g, ids[i]))
}

// ===== lifting single nodes =====

/// The lift of a regex node, read off its kind.
pub proof fn lemma_regex_lift(g: model::Graph, id: nat)
    requires model::graph_wf(g), id < g.regexes.len(),
    ensures
        model::lift_regex(g, id) == norm::regex_unbounded_kind(g, g.regexes[id as int].kind),
        model::regex_kind_wf_at(g, g.regexes[id as int].kind, id),
        r_kind(model::lift_regex(g, id)) == node_kind(g.regexes[id as int].kind),
{
    norm::regex_unfold(g, id);
}

pub open spec fn node_kind(k: model::RegexKindNode) -> Kind {
    match k {
        model::RegexKindNode::Empty => Kind::Empty, model::RegexKindNode::Epsilon => Kind::Epsilon,
        model::RegexKindNode::All => Kind::Universal, model::RegexKindNode::Test(_) => Kind::Test,
        model::RegexKindNode::Union(_) => Kind::Union, model::RegexKindNode::Intersect(_) => Kind::Intersect,
        model::RegexKindNode::Not(_) => Kind::Not, model::RegexKindNode::Star(_) => Kind::Star,
        model::RegexKindNode::Concat(_) => Kind::List,
    }
}

/// The lift of a test node, read off the node.
pub proof fn lemma_test_lift(g: model::Graph, id: nat)
    requires model::graph_wf(g), id < g.tests.len(),
    ensures
        match g.tests[id as int] {
            model::TestNode::And(cs) => model::bounded(cs, id) && model::strictly_increasing(cs)
                && model::lift_test(g, id) == model::Test::And(Seq::new(cs.len(), |j: int| model::lift_test(g, cs[j]))),
            model::TestNode::Or(cs) => model::bounded(cs, id) && model::strictly_increasing(cs)
                && model::lift_test(g, id) == model::Test::Or(Seq::new(cs.len(), |j: int| model::lift_test(g, cs[j]))),
            model::TestNode::True => model::lift_test(g, id) == model::Test::True,
            model::TestNode::False => model::lift_test(g, id) == model::Test::False,
            model::TestNode::Atom(p, b) => model::lift_test(g, id) == model::Test::Atom(p, b),
        },
{
    model::lemma_graph_test_wf(g, id);
    match g.tests[id as int] {
        model::TestNode::And(cs) => {
            assert(model::lift_tests(g, cs, id) =~= Seq::new(cs.len(), |j: int| model::lift_test(g, cs[j])));
        },
        model::TestNode::Or(cs) => {
            assert(model::lift_tests(g, cs, id) =~= Seq::new(cs.len(), |j: int| model::lift_test(g, cs[j])));
        },
        _ => {},
    }
}

/// Distinct ids lift to distinct trees, so strictly increasing children lift without duplicates.
pub proof fn lemma_regex_lifts_nodup(g: model::Graph, cs: Seq<nat>)
    requires model::graph_wf(g), model::bounded(cs, g.regexes.len()), model::strictly_increasing(cs),
    ensures model::lift_regexes(g, cs).no_duplicates(),
{
    let ls = model::lift_regexes(g, cs);
    assert forall|i: int, j: int| 0 <= i < ls.len() && 0 <= j < ls.len() && i != j implies ls[i] != ls[j] by {
        if ls[i] == ls[j] {
            lemma_lift_regex_injective(g, cs[i], cs[j]);
            if i < j { assert(cs[i] < cs[j]); } else { assert(cs[j] < cs[i]); }
        }
    }
}

pub proof fn lemma_test_lifts_nodup(g: model::Graph, cs: Seq<nat>)
    requires model::graph_wf(g), model::bounded(cs, g.tests.len()), model::strictly_increasing(cs),
    ensures Seq::new(cs.len(), |j: int| model::lift_test(g, cs[j])).no_duplicates(),
{
    let ls = Seq::new(cs.len(), |j: int| model::lift_test(g, cs[j]));
    assert forall|i: int, j: int| 0 <= i < ls.len() && 0 <= j < ls.len() && i != j implies ls[i] != ls[j] by {
        if ls[i] == ls[j] {
            lemma_lift_test_injective(g, cs[i], cs[j]);
            if i < j { assert(cs[i] < cs[j]); } else { assert(cs[j] < cs[i]); }
        }
    }
}

// ===== (N3) =====

/// `N(¬x)` of the implementation lifts to `r_not` of the lifted operand.
pub proof fn lemma_not_link(g: model::Graph, x: nat, r: nat)
    requires model::graph_wf(g), x < g.regexes.len(), r < g.regexes.len(), regex_nf(model::lift_regex(g, x)),
        norm::regex_not_result(g, x, r),
    ensures model::lift_regex(g, r) == r_not(model::lift_regex(g, x)), regex_nf(model::lift_regex(g, r)),
{
    norm::regex_constants(g);
    lemma_regex_lift(g, x);
    lemma_regex_lift(g, r);
    match g.regexes[x as int].kind {
        model::RegexKindNode::Empty => {},
        model::RegexKindNode::All => {},
        model::RegexKindNode::Not(inner) => {},
        _ => {
            assert(g.regexes[r as int].kind == model::RegexKindNode::Not(x));
        },
    }
}

// ===== (N4) =====

/// The implementation's flattening lifts to the model's.
pub proof fn lemma_flat_link(g: model::Graph, ids: Seq<RegexId>)
    requires model::graph_wf(g), norm::regex_ids_valid(g, ids),
    ensures
        model::lift_regexes(g, norm::regex_concat_flat(g, ids)) == pre().flat(lifts(g, ids)),
        model::bounded(norm::regex_concat_flat(g, ids), g.regexes.len()),
        (exists|i: int| 0 <= i < ids.len() && g.regexes[ids[i]@ as int].kind == model::RegexKindNode::Empty)
            == pre().has_empty(lifts(g, ids)),
    decreases ids.len(),
{
    norm::regex_constants(g);
    if ids.len() > 0 {
        let init = ids.drop_last();
        let x = ids.last()@;
        lemma_flat_link(g, init);
        lemma_regex_lift(g, x);
        let ls = lifts(g, ids);
        assert(ls.drop_last() =~= lifts(g, init));
        assert(ls.last() == model::lift_regex(g, x));
        let fi = norm::regex_concat_flat(g, init);
        let px = norm::regex_concat_piece(g, x);
        assert(norm::regex_concat_flat(g, ids) == fi + px);
        assert(model::lift_regexes(g, fi + px) =~= model::lift_regexes(g, fi) + model::lift_regexes(g, px));
        assert(model::lift_regexes(g, px) =~= pre().piece(model::lift_regex(g, x))) by {
            match g.regexes[x as int].kind {
                model::RegexKindNode::Concat(cs) => {},
                model::RegexKindNode::Epsilon => {},
                _ => {},
            }
        }
        assert(model::bounded(px, g.regexes.len())) by {
            match g.regexes[x as int].kind {
                model::RegexKindNode::Concat(cs) => {
                    assert forall|j: int| 0 <= j < cs.len() implies #[trigger] cs[j] < g.regexes.len() by { assert(cs[j] < x); }
                },
                _ => {},
            }
        }
        assert(model::bounded(fi + px, g.regexes.len())) by {
            assert forall|j: int| 0 <= j < (fi + px).len() implies #[trigger] (fi + px)[j] < g.regexes.len() by {
                if j < fi.len() { assert((fi + px)[j] == fi[j]); } else { assert((fi + px)[j] == px[j - fi.len()]); }
            }
        }
        let e_ids = exists|i: int| 0 <= i < ids.len() && g.regexes[ids[i]@ as int].kind == model::RegexKindNode::Empty;
        let e_init = exists|i: int| 0 <= i < init.len() && g.regexes[init[i]@ as int].kind == model::RegexKindNode::Empty;
        assert(e_ids == (e_init || g.regexes[x as int].kind == model::RegexKindNode::Empty)) by {
            if e_ids {
                let i = choose|i: int| 0 <= i < ids.len() && g.regexes[ids[i]@ as int].kind == model::RegexKindNode::Empty;
                if i < init.len() { assert(init[i] == ids[i]); }
            }
            if e_init {
                let i = choose|i: int| 0 <= i < init.len() && g.regexes[init[i]@ as int].kind == model::RegexKindNode::Empty;
                assert(init[i] == ids[i]);
            }
        }
        assert(pre().has_empty(ls) == (pre().has_empty(lifts(g, init)) || ls.last() == Regex::<model::Test>::Empty)) by {
            if pre().has_empty(ls) {
                let i = choose|i: int| 0 <= i < ls.len() && ls[i] == pre().empty;
                if i < init.len() { assert(lifts(g, init)[i] == ls[i]); }
            }
            if pre().has_empty(lifts(g, init)) {
                let i = choose|i: int| 0 <= i < lifts(g, init).len() && lifts(g, init)[i] == pre().empty;
                assert(lifts(g, init)[i] == ls[i]);
            }
        }
    } else {
        assert(lifts(g, ids) =~= Seq::<R>::empty());
        assert(model::lift_regexes(g, Seq::<nat>::empty()) =~= Seq::<R>::empty());
    }
}

/// `N(x₁⋯xₖ)` of the implementation lifts to `r_cat` of the lifted factors.
pub proof fn lemma_concat_link(before: model::Graph, after: model::Graph, children: Seq<RegexId>, r: nat)
    requires model::graph_wf(before), model::graph_wf(after), model::graph_extends(before, after),
        norm::regex_ids_valid(before, children), r < after.regexes.len(),
        norm::regex_concat_result(before, after, children, r),
    ensures model::lift_regex(after, r) == r_cat(lifts(before, children)),
{
    norm::regex_constants(before);
    norm::regex_constants(after);
    lemma_flat_link(before, children);
    let f = norm::regex_concat_flat(before, children);
    model::lemma_graph_wf_elim(before);
    if exists|i: int| 0 <= i < children.len() && before.regexes[children[i]@ as int].kind == model::RegexKindNode::Empty {
    } else if f.len() == 0 {
    } else if f.len() == 1 {
        model::lemma_lift_regex_stable(before, after, f[0]);
    } else {
        lemma_regex_lift(after, r);
        assert forall|j: int| 0 <= j < f.len() implies #[trigger] model::lift_regex(after, f[j]) == model::lift_regex(before, f[j]) by {
            model::lemma_lift_regex_stable(before, after, f[j]);
        }
        assert(model::lift_regexes(after, f) =~= model::lift_regexes(before, f));
    }
}

// ===== (N1), (N2), (N5) =====

/// Pieces lift to pieces: `regex_piece_contains` is `sops` on lifted trees.
pub proof fn lemma_piece_link(g: model::Graph, c: nat, inter: bool, o: nat)
    requires model::graph_wf(g), c < g.regexes.len(), norm::regex_piece_contains(g, c, inter, o),
    ensures o < g.regexes.len(), pre().sops(inter, model::lift_regex(g, c)).contains(model::lift_regex(g, o)),
        regex_nf(model::lift_regex(g, c)) ==> regex_nf(model::lift_regex(g, o)) && !pre().is_set(inter, model::lift_regex(g, o)),
{
    broadcast use vstd::prelude::Seq::to_set_ensures;
    lemma_regex_lift(g, c);
    match g.regexes[c as int].kind {
        model::RegexKindNode::Union(cs) => {
            if !inter {
                let j = choose|j: int| 0 <= j < cs.len() && cs[j] == o;
                assert(cs[j] < c);
                assert(model::lift_regexes(g, cs)[j] == model::lift_regex(g, o));
                if regex_nf(model::lift_regex(g, c)) {
                    assert(regex_nf(model::lift_regexes(g, cs)[j]));
                }
            }
        },
        model::RegexKindNode::Intersect(cs) => {
            if inter {
                let j = choose|j: int| 0 <= j < cs.len() && cs[j] == o;
                assert(cs[j] < c);
                assert(model::lift_regexes(g, cs)[j] == model::lift_regex(g, o));
                if regex_nf(model::lift_regex(g, c)) {
                    assert(regex_nf(model::lift_regexes(g, cs)[j]));
                }
            }
        },
        _ => {},
    }
}

/// Test pieces lift to `test_piece`.
pub proof fn lemma_test_piece_link(g: model::Graph, c: nat, and: bool, t: nat)
    requires model::graph_wf(g), c < g.tests.len(), norm::test_piece_contains(g, c, and, t),
    ensures t < g.tests.len(), test_piece(and, model::lift_test(g, c), model::lift_test(g, t)),
        test_nf(model::lift_test(g, c)) ==> test_nf(model::lift_test(g, t)) && !is_conn(and, model::lift_test(g, t)),
{
    lemma_test_lift(g, c);
    match g.tests[c as int] {
        model::TestNode::And(cs) => {
            if and {
                let j = choose|j: int| 0 <= j < cs.len() && cs[j] == t;
                assert(cs[j] < c);
                let ks = Seq::new(cs.len(), |j: int| model::lift_test(g, cs[j]));
                assert(ks[j] == model::lift_test(g, t));
                assert(ks.contains(model::lift_test(g, t)));
            }
        },
        model::TestNode::Or(cs) => {
            if !and {
                let j = choose|j: int| 0 <= j < cs.len() && cs[j] == t;
                assert(cs[j] < c);
                let ks = Seq::new(cs.len(), |j: int| model::lift_test(g, cs[j]));
                assert(ks[j] == model::lift_test(g, t));
                assert(ks.contains(model::lift_test(g, t)));
            }
        },
        _ => {},
    }
}

/// Members of `ops₊(X)` lift into `in_sops_of`, and are normal forms that are not sets.
pub proof fn lemma_member_link(g: model::Graph, children: Seq<RegexId>, inter: bool, o: nat)
    requires model::graph_wf(g), norm::regex_ids_valid(g, children), ids_nf(g, children),
        norm::regex_member(g, children, inter, o),
    ensures o < g.regexes.len(), pre().in_sops_of(inter, lift_set(g, children), model::lift_regex(g, o)),
        regex_nf(model::lift_regex(g, o)), !pre().is_set(inter, model::lift_regex(g, o)),
{
    broadcast use vstd::prelude::Seq::to_set_ensures;
    let i = choose|i: int| 0 <= i < children.len() && #[trigger] norm::regex_piece_contains(g, children[i]@, inter, o);
    lemma_piece_link(g, children[i]@, inter, o);
    assert(regex_nf(model::lift_regex(g, children[i]@)));
    assert(lifts(g, children)[i] == model::lift_regex(g, children[i]@));
    assert(lift_set(g, children).contains(model::lift_regex(g, children[i]@)));
}

/// Normal-form inputs are flat for the set constructor (its precondition `regex_set_flat_inputs`).
pub proof fn lemma_flat_inputs(g: model::Graph, children: Seq<RegexId>, inter: bool)
    requires model::graph_wf(g), norm::regex_ids_valid(g, children), ids_nf(g, children),
    ensures norm::regex_set_flat_inputs(g, children, inter),
{
    assert forall|o: nat| norm::regex_member(g, children, inter, o) implies !norm::regex_is_set(g, o, inter) by {
        lemma_member_link(g, children, inter, o);
        lemma_regex_lift(g, o);
    }
}

/// The member tests of `ts`, as regex states.
pub open spec fn test_states(g: model::Graph, ts: Seq<TestId>) -> Set<R> {
    Seq::new(ts.len(), |k: int| Regex::Test(model::lift_test(g, ts[k]@))).to_set()
}

/// Every test of `ts` is the test of a member: its regex is a test state among the operands.
pub proof fn lemma_member_tests(g: model::Graph, children: Seq<RegexId>, inter: bool, ts: Seq<TestId>)
    requires model::graph_wf(g), norm::regex_ids_valid(g, children), ids_nf(g, children),
        forall|k: int| 0 <= k < ts.len() ==> norm::regex_member_test(g, children, inter, #[trigger] ts[k]@),
    ensures
        forall|u: R| #[trigger] test_states(g, ts).contains(u) ==> pre().is_test(u) && pre().in_sops_of(inter, lift_set(g, children), u),
        forall|k: int| 0 <= k < ts.len() ==> #[trigger] ts[k]@ < g.tests.len() && test_nf(model::lift_test(g, ts[k]@)),
{
    broadcast use vstd::prelude::Seq::to_set_ensures;
    let s = Seq::new(ts.len(), |k: int| Regex::Test(model::lift_test(g, ts[k]@)));
    assert forall|k: int| 0 <= k < ts.len() implies #[trigger] ts[k]@ < g.tests.len() && test_nf(model::lift_test(g, ts[k]@))
        && pre().is_test(s[k]) && pre().in_sops_of(inter, lift_set(g, children), s[k]) by {
        let o = choose|o: nat| #[trigger] norm::regex_member(g, children, inter, o)
            && o < g.regexes.len() && g.regexes[o as int].kind == model::RegexKindNode::Test(ts[k]@);
        lemma_member_link(g, children, inter, o);
        lemma_regex_lift(g, o);
        assert(model::lift_regex(g, o) == s[k]);
    }
    assert forall|u: R| #[trigger] test_states(g, ts).contains(u) implies pre().is_test(u) && pre().in_sops_of(inter, lift_set(g, children), u) by {
        let k = choose|k: int| 0 <= k < s.len() && s[k] == u;
        assert(ts[k]@ < g.tests.len());
    }
}

/// A piece of a member test of `ts` lifts to a piece of a test state.
pub proof fn lemma_test_member_link(g: model::Graph, ts: Seq<TestId>, and: bool, t: nat)
    requires model::graph_wf(g), forall|k: int| 0 <= k < ts.len() ==> #[trigger] ts[k]@ < g.tests.len() && test_nf(model::lift_test(g, ts[k]@)),
        norm::test_member(g, ts, and, t),
    ensures t < g.tests.len(), piece_of(and, test_states(g, ts), model::lift_test(g, t)),
        test_nf(model::lift_test(g, t)), !is_conn(and, model::lift_test(g, t)),
{
    broadcast use vstd::prelude::Seq::to_set_ensures;
    let k = choose|k: int| 0 <= k < ts.len() && #[trigger] norm::test_piece_contains(g, ts[k]@, and, t);
    lemma_test_piece_link(g, ts[k]@, and, t);
    let s = Seq::new(ts.len(), |k: int| Regex::Test(model::lift_test(g, ts[k]@)));
    assert(s[k] == Regex::Test(model::lift_test(g, ts[k]@)));
    assert(test_states(g, ts).contains(Regex::Test(model::lift_test(g, ts[k]@))));
}

/// A combined test (`regex_combined_test`) lifts to a test combination of the model.
pub proof fn lemma_combined_link(before: model::Graph, after: model::Graph, children: Seq<RegexId>, inter: bool, o: nat)
    requires model::graph_wf(before), model::graph_wf(after), model::graph_extends(before, after),
        norm::regex_ids_valid(before, children), ids_nf(before, children),
        norm::regex_combined_test(before, after, children, inter, o),
    ensures pre().is_test(model::lift_regex(after, o)),
        exists|us: Set<R>| #[trigger] pre().combo_from(inter, lift_set(before, children), us, model::lift_regex(after, o)),
{
    let (t, ts) = choose|t: nat, ts: Seq<TestId>|
        after.regexes[o as int].kind == model::RegexKindNode::Test(t)
        && (forall|k: int| 0 <= k < ts.len() ==> norm::regex_member_test(before, children, inter, #[trigger] ts[k]@))
        && #[trigger] norm::test_connective_result(before, after, ts, inter, t);
    lemma_member_tests(before, children, inter, ts);
    let us = test_states(before, ts);
    lemma_regex_lift(after, o);
    assert(t < after.tests.len());
    let phi = model::lift_test(after, t);
    assert(model::lift_regex(after, o) == Regex::Test(phi));
    norm::regex_constants(before);
    norm::regex_constants(after);
    model::lemma_graph_wf_elim(before);
    assert(test_nf(phi) && test_combo(inter, us, phi)) by {
        if t == before.constants.test_true || t == before.constants.test_false {
        } else if norm::test_member(before, ts, inter, t) {
            lemma_test_member_link(before, ts, inter, t);
            model::lemma_lift_test_stable(before, after, t);
        } else {
            lemma_test_lift(after, t);
            match after.tests[t as int] {
                model::TestNode::And(ks) => {
                    lemma_connective_kids(before, after, ts, inter, t, ks);
                },
                model::TestNode::Or(ks) => {
                    lemma_connective_kids(before, after, ts, inter, t, ks);
                },
                _ => {},
            }
        }
    }
    assert(r_combo(inter, us, model::lift_regex(after, o)));
    assert(pre().combo_from(inter, lift_set(before, children), us, model::lift_regex(after, o)));
}

/// The children of a combined connective lift to duplicate-free pieces of the member tests.
pub proof fn lemma_connective_kids(before: model::Graph, after: model::Graph, ts: Seq<TestId>, inter: bool, t: nat, ks: Seq<nat>)
    requires model::graph_wf(before), model::graph_wf(after), model::graph_extends(before, after),
        forall|k: int| 0 <= k < ts.len() ==> #[trigger] ts[k]@ < before.tests.len() && test_nf(model::lift_test(before, ts[k]@)),
        t < after.tests.len(),
        after.tests[t as int] == (if inter { model::TestNode::And(ks) } else { model::TestNode::Or(ks) }),
        forall|k: int| 0 <= k < ks.len() ==> norm::test_member(before, ts, inter, #[trigger] ks[k]),
    ensures ({
        let phi = model::lift_test(after, t);
        test_nf(phi) && is_conn(inter, phi)
            && forall|k: int| 0 <= k < test_kids(phi).len() ==> piece_of(inter, test_states(before, ts), #[trigger] test_kids(phi)[k])
    }),
{
    lemma_test_lift(after, t);
    model::lemma_graph_wf_elim(before);
    let kids = Seq::new(ks.len(), |j: int| model::lift_test(after, ks[j]));
    assert forall|j: int| 0 <= j < ks.len() implies #[trigger] kids[j] == model::lift_test(before, ks[j])
        && piece_of(inter, test_states(before, ts), kids[j]) && test_nf(kids[j]) && !is_conn(inter, kids[j]) by {
        lemma_test_member_link(before, ts, inter, ks[j]);
        model::lemma_lift_test_stable(before, after, ks[j]);
    }
    lemma_test_lifts_nodup(after, ks);
    let phi = model::lift_test(after, t);
    assert(test_kids(phi) == kids);
    if inter {
        assert(phi == model::Test::And(kids));
        assert forall|j: int| 0 <= j < kids.len() implies test_nf(#[trigger] kids[j]) && !(kids[j] is And) by {}
    } else {
        assert(phi == model::Test::Or(kids));
        assert forall|j: int| 0 <= j < kids.len() implies test_nf(#[trigger] kids[j]) && !(kids[j] is Or) by {}
    }
}

/// A legal operand of `N(ΣX)` (`N(&X)`) lifts to an operand allowed by (N1)/(N2), is a normal
/// form, and is not a set of the same kind.
pub proof fn lemma_operand_link(before: model::Graph, after: model::Graph, children: Seq<RegexId>, inter: bool, o: nat)
    requires model::graph_wf(before), model::graph_wf(after), model::graph_extends(before, after),
        norm::regex_ids_valid(before, children), ids_nf(before, children),
        norm::regex_set_operand_ok(before, after, children, inter, o), o < after.regexes.len(),
    ensures ({
        let x = model::lift_regex(after, o);
        &&& regex_nf(x) && !pre().is_set(inter, x)
        &&& pre().in_sops_of(inter, lift_set(before, children), x)
            || (pre().is_test(x) && exists|us: Set<R>| #[trigger] pre().combo_from(inter, lift_set(before, children), us, x))
    }),
{
    model::lemma_graph_wf_elim(before);
    if norm::regex_member(before, children, inter, o) {
        lemma_member_link(before, children, inter, o);
        model::lemma_lift_regex_stable(before, after, o);
    } else {
        lemma_combined_link(before, after, children, inter, o);
    }
}

/// (N1)/(N2), (N5) for the implementation: the output of `RegexId::set` on normal-form inputs is
/// an output of the model's set constructor on the lifted inputs (in particular a normal form).
pub proof fn lemma_set_link(before: model::Graph, after: model::Graph, children: Seq<RegexId>, inter: bool, r: nat)
    requires model::graph_wf(before), model::graph_wf(after), model::graph_extends(before, after),
        norm::regex_ids_valid(before, children), ids_nf(before, children), r < after.regexes.len(),
        norm::regex_set_shape(before, after, children, inter, r),
    ensures (core().nset)(inter, lift_set(before, children), model::lift_regex(after, r)),
        regex_nf(model::lift_regex(after, r)),
{
    norm::regex_constants(before);
    norm::regex_constants(after);
    model::lemma_graph_wf_elim(before);
    let u = model::lift_regex(after, r);
    let xs = lift_set(before, children);
    if r == before.constants.empty || r == before.constants.all || r == before.constants.epsilon {
        assert(pre().nset_shape(inter, xs, u));
    } else {
        lemma_regex_lift(after, r);
        match after.regexes[r as int].kind {
            model::RegexKindNode::Union(cs) => {
                if !inter { lemma_set_node_link(before, after, children, inter, r, cs); }
                else { lemma_single_link(before, after, children, inter, r); }
            },
            model::RegexKindNode::Intersect(cs) => {
                if inter { lemma_set_node_link(before, after, children, inter, r, cs); }
                else { lemma_single_link(before, after, children, inter, r); }
            },
            _ => { lemma_single_link(before, after, children, inter, r); },
        }
    }
}

/// The output is not a set of the connective's kind: it is itself a legal operand.
pub proof fn lemma_single_link(before: model::Graph, after: model::Graph, children: Seq<RegexId>, inter: bool, r: nat)
    requires model::graph_wf(before), model::graph_wf(after), model::graph_extends(before, after),
        norm::regex_ids_valid(before, children), ids_nf(before, children), r < after.regexes.len(),
        norm::regex_set_shape(before, after, children, inter, r),
        !(r == before.constants.empty || r == before.constants.all || r == before.constants.epsilon),
        !norm::regex_is_set(after, r, inter),
    ensures (core().nset)(inter, lift_set(before, children), model::lift_regex(after, r)),
        regex_nf(model::lift_regex(after, r)),
{
    let u = model::lift_regex(after, r);
    let xs = lift_set(before, children);
    assert(norm::regex_piece_contains(after, r, inter, r));
    lemma_operand_link(before, after, children, inter, r);
    assert(pre().sops(inter, u) == set![u]);
    assert(pre().nset_shape(inter, xs, u));
}

/// The output is a set node of the connective's kind: its operands are legal operands.
pub proof fn lemma_set_node_link(before: model::Graph, after: model::Graph, children: Seq<RegexId>, inter: bool, r: nat, cs: Seq<nat>)
    requires model::graph_wf(before), model::graph_wf(after), model::graph_extends(before, after),
        norm::regex_ids_valid(before, children), ids_nf(before, children), r < after.regexes.len(),
        norm::regex_set_shape(before, after, children, inter, r),
        !(r == before.constants.empty || r == before.constants.all || r == before.constants.epsilon),
        after.regexes[r as int].kind == set_kind_node(inter, cs),
    ensures (core().nset)(inter, lift_set(before, children), model::lift_regex(after, r)),
        regex_nf(model::lift_regex(after, r)),
{
    let u = model::lift_regex(after, r);
    let xs = lift_set(before, children);
    lemma_regex_lift(after, r);
    let ls = model::lift_regexes(after, cs);
    assert(model::bounded(cs, r) && model::strictly_increasing(cs));
    assert(model::bounded(cs, after.regexes.len())) by {
        assert forall|j: int| 0 <= j < cs.len() implies #[trigger] cs[j] < after.regexes.len() by { assert(cs[j] < r); }
    }
    lemma_regex_lifts_nodup(after, cs);
    assert(u == set_node(inter, ls));
    assert forall|j: int| 0 <= j < cs.len() implies ({
        let x = #[trigger] ls[j];
        &&& regex_nf(x) && !pre().is_set(inter, x)
        &&& pre().in_sops_of(inter, xs, x)
            || (pre().is_test(x) && exists|us: Set<R>| #[trigger] pre().combo_from(inter, xs, us, x))
    }) by {
        assert(cs[j] < r);
        assert(norm::regex_piece_contains(after, r, inter, cs[j])) by {
            assert(cs.contains(cs[j]));
        }
        lemma_operand_link(before, after, children, inter, cs[j]);
    }
    assert(regex_nf(u)) by {
        if inter {
            assert forall|j: int| 0 <= j < ls.len() implies regex_nf(#[trigger] ls[j]) && !(ls[j] is Intersect) by {}
        } else {
            assert forall|j: int| 0 <= j < ls.len() implies regex_nf(#[trigger] ls[j]) && !(ls[j] is Union) by {}
        }
    }
    assert forall|o: R| #[trigger] pre().sops(inter, u).contains(o) implies
        pre().in_sops_of(inter, xs, o)
        || (pre().is_test(o) && exists|us: Set<R>| #[trigger] pre().combo_from(inter, xs, us, o)) by {
        broadcast use vstd::prelude::Seq::to_set_ensures;
        assert(ls.contains(o));
        let j = choose|j: int| 0 <= j < ls.len() && ls[j] == o;
    }
    assert(pre().nset_shape(inter, xs, u));
}

pub open spec fn set_kind_node(inter: bool, cs: Seq<nat>) -> model::RegexKindNode {
    if inter { model::RegexKindNode::Intersect(cs) } else { model::RegexKindNode::Union(cs) }
}

} // verus!
