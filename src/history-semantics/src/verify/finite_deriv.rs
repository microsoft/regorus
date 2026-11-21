//! Class bounds of the implemented derivative (`symbolic.rs` `RegexId::derivative`): the
//! transition built for a normal-form state `p` is a normal form whose class consists of literals
//! and products of `p` in `verify::finite_impl::m_impl` ([`dbound`], i.e. `finite_trans::dclass`).
//! The derivative cache carries [`dbound`] for every entry (`symbolic::verify::derivative_cache_wf`).
//! Per regex kind: constants and tests ([`lemma_dbound_const`], [`lemma_dbound_test`]), stars
//! ([`lemma_dbound_star`], via `star_lit`), complements ([`lemma_dbound_not`], via `not_lit`), and
//! sets and lists from the bounds of their factors ([`fbound`], [`lemma_factor_set`],
//! [`lemma_factor_concat`], [`lemma_derive_future`]).
use crate::normalize::verify::{self as norm, ActionShape};
use crate::symbolic::verify::{derivative_cache_wf, derivative_constants, derivative_correct};
use crate::verify::finite_branch::*;
use crate::verify::finite_collect::*;
use crate::verify::finite_impl::*;
use crate::verify::finite_link::*;
use crate::verify::finite_machine::*;
use crate::verify::finite_states::*;
use crate::verify::finite_steps::*;
use crate::verify::finite_trans::*;
use alloc::boxed::Box;
use junco_core::kernel::verify as model;
use junco_core::kernel::{RegexId, TransitionId};
use junco_core::verify::history_specs::Regex;
use vstd::prelude::*;

verus! {

broadcast use junco_core::kernel::verify::group_kernel_views;

/// The derivative `t` of the regex id `root` has the class bound of its lifted state, when that
/// state is a normal form.
#[verifier::opaque]
pub open spec fn dbound(g: model::Graph, root: nat, t: nat) -> bool {
    regex_nf(model::lift_regex(g, root)) ==> dclass(g, t, model::lift_regex(g, root))
}

/// `v` is a literal and a product of `p`.
pub open spec fn lp(p: R, v: R) -> bool {
    (m_impl().lit)(p, v) && (m_impl().prod)(p, v)
}

/// A factor result of the derivative of `root`: a normal form whose class consists of literals
/// and products of `root`'s state.
pub open spec fn fbound(g: model::Graph, root: nat, t: nat) -> bool {
    nf_sum(g, t) && forall|v: R| #[trigger] tcls(g, t, v) ==> lp(model::lift_regex(g, root), v)
}

#[verifier::opaque]
pub open spec fn results_bound(g: model::Graph, root: nat, results: Seq<TransitionId>) -> bool {
    regex_nf(model::lift_regex(g, root)) ==> forall|k: int| 0 <= k < results.len() ==> #[trigger] fbound(g, root, results[k]@)
}

// ===== literals and products =====

/// Constants are literals and products of every state.
pub proof fn lemma_const_lp(p: R, v: R)
    requires regex_nf(p), rconst(v),
    ensures lp(p, v),
{
    let m = m_impl();
    lemma_models_agree();
    assert(regex_nf(v));
    assert(m.lit_shape(p, v)) by {
        if !m.base_kind(p) {
            if m.k(p) == Kind::Union { lemma_cl_const(false, |w: R| m.ops_lit(p, w), v); }
            else if m.k(p) == Kind::Intersect { lemma_cl_const(true, |w: R| m.ops_lit(p, w), v); }
            else if m.k(p) == Kind::Not { lemma_cl_const(true, |w: R| m.not_lit(p, w), v); }
            else if m.k(p) == Kind::Star { lemma_cl_const(false, |w: R| m.star_lit(p, w), v); }
            else { lemma_cl_const(false, |w: R| m.list_lit(p, w), v); }
        }
    }
    lemma_lit_fold(p, v);
    assert(m.prod_shape(p, v)) by {
        if m.k(p) == Kind::Intersect || m.k(p) == Kind::Not { lemma_cl_const(true, |w: R| (m.lit)(p, w), v); }
    }
    lemma_prod_fold(p, v);
}

/// A literal `v` of `p` built by the literal shape is a literal and a product.
pub proof fn lemma_lit_to_lp(p: R, v: R)
    requires regex_nf(p), regex_nf(v), m_impl().lit_shape(p, v), !m_impl().base_kind(p), m_impl().k(p) != Kind::Union,
    ensures lp(p, v),
{
    let m = m_impl();
    lemma_lit_fold(p, v);
    assert(m.prod_shape(p, v)) by {
        if m.k(p) == Kind::Intersect || m.k(p) == Kind::Not { lemma_cl_base(true, |w: R| (m.lit)(p, w), v); }
    }
    lemma_prod_fold(p, v);
}

pub proof fn lemma_dclass_from(g: model::Graph, t: nat, p: R)
    requires nf_sum(g, t), forall|v: R| #[trigger] tcls(g, t, v) ==> lp(p, v), !m_impl().base_kind(p),
    ensures dclass(g, t, p),
{}

// ===== stability =====

pub proof fn lemma_dbound_stable(a: model::Graph, b: model::Graph, root: nat, t: nat)
    requires model::graph_wf(a), model::graph_extends(a, b), root < a.regexes.len(), t < a.transitions.len(), dbound(a, root, t),
    ensures dbound(b, root, t),
{
    reveal(dbound);
    lemma_regex_nf_stable(a, b, root);
    lemma_trans_stable(a, b, t);
    let p = model::lift_regex(a, root);
    if regex_nf(p) {
        assert forall|w: R| #[trigger] tcls(b, t, w) implies (m_impl().lit)(p, w) && (m_impl().prod)(p, w) by { assert(tcls(a, t, w)); }
        assert forall|w: R| #[trigger] ycls(b, t, w) && m_impl().base_kind(p) implies rconst(w) by { assert(ycls(a, t, w)); }
    }
}

pub proof fn lemma_fbound_stable(a: model::Graph, b: model::Graph, root: nat, t: nat)
    requires model::graph_wf(a), model::graph_extends(a, b), root < a.regexes.len(), fbound(a, root, t),
    ensures fbound(b, root, t),
{
    lemma_regex_nf_stable(a, b, root);
    lemma_trans_stable(a, b, t);
    assert forall|v: R| #[trigger] tcls(b, t, v) implies lp(model::lift_regex(b, root), v) by { assert(tcls(a, t, v)); }
}

pub proof fn lemma_results_stable(a: model::Graph, b: model::Graph, root: nat, results: Seq<TransitionId>)
    requires model::graph_wf(a), model::graph_extends(a, b), root < a.regexes.len(), results_bound(a, root, results),
    ensures results_bound(b, root, results),
{
    reveal(results_bound);
    lemma_regex_nf_stable(a, b, root);
    if regex_nf(model::lift_regex(b, root)) {
        assert forall|k: int| 0 <= k < results.len() implies #[trigger] fbound(b, root, results[k]@) by {
            assert(fbound(a, root, results[k]@));
            lemma_fbound_stable(a, b, root, results[k]@);
        }
    }
}

pub proof fn lemma_results_push(g: model::Graph, root: nat, results: Seq<TransitionId>, t: TransitionId)
    requires results_bound(g, root, results), regex_nf(model::lift_regex(g, root)) ==> fbound(g, root, t@),
    ensures results_bound(g, root, results.push(t)),
{
    reveal(results_bound);
    if regex_nf(model::lift_regex(g, root)) {
        assert forall|k: int| 0 <= k < results.push(t).len() implies #[trigger] fbound(g, root, results.push(t)[k]@) by {
            if k < results.len() { assert(results.push(t)[k] == results[k]); }
        }
    }
}

pub proof fn lemma_results_empty(g: model::Graph, root: nat)
    ensures results_bound(g, root, Seq::empty()),
{ reveal(results_bound); }

// ===== constants and tests =====

pub proof fn lemma_dbound_const(g: model::Graph, root: nat, out: nat)
    requires model::graph_wf(g), root < g.regexes.len(),
        match g.regexes[root as int].kind {
            model::RegexKindNode::Empty => out == g.constants.transition_empty,
            model::RegexKindNode::Epsilon => out == g.constants.transition_empty,
            model::RegexKindNode::All => out == g.constants.transition_all,
            _ => false,
        },
    ensures dbound(g, root, out),
{
    reveal(dbound);
    lemma_regex_lift(g, root);
    lemma_const_transitions(g);
    model::lemma_graph_wf_elim(g);
    norm::regex_constants(g);
    let p = model::lift_regex(g, root);
    if regex_nf(p) {
        let c = g.constants;
        lemma_const_cls(g, c.transition_all, c.all);
        assert forall|w: R| #[trigger] tcls(g, out, w) implies (m_impl().lit)(p, w) && (m_impl().prod)(p, w) by {
            lemma_const_lp(p, w);
        }
        assert forall|w: R| #[trigger] ycls(g, out, w) && m_impl().base_kind(p) implies rconst(w) by {}
    }
}

pub proof fn lemma_dbound_test(g0: model::Graph, g: model::Graph, root: nat, t: nat, out: nat)
    requires model::graph_wf(g0), model::graph_wf(g), model::graph_extends(g0, g), root < g0.regexes.len(),
        g0.regexes[root as int].kind == model::RegexKindNode::Test(t),
        (nf_sum(g0, g0.constants.transition_epsilon) && nf_sum(g0, g0.constants.transition_empty))
            ==> ite_bound(g, out, g0.constants.transition_epsilon, g0.constants.transition_empty),
    ensures dbound(g, root, out),
{
    reveal(dbound);
    lemma_const_transitions(g0);
    lemma_regex_lift(g0, root);
    lemma_regex_nf_stable(g0, g, root);
    lemma_const_transitions(g);
    let c = g.constants;
    let p = model::lift_regex(g, root);
    lemma_av_le_cls(g, out, out);
    if regex_nf(p) {
        assert forall|w: R| #[trigger] tcls(g, out, w) implies (m_impl().lit)(p, w) && (m_impl().prod)(p, w) by {
            assert((av_of(g, out).x)(w));
            assert(tcls(g, c.transition_epsilon, w) || tcls(g, c.transition_empty, w));
            lemma_const_lp(p, w);
        }
        assert forall|w: R| #[trigger] ycls(g, out, w) implies rconst(w) by {
            assert((av_of(g, out).y)(w));
            assert(ycls(g, c.transition_epsilon, w) || ycls(g, c.transition_empty, w));
        }
    }
}

// ===== stars and complements =====

pub proof fn lemma_ids_nf1(g: model::Graph, s: Seq<RegexId>, r: RegexId)
    requires s.len() == 1, s[0] == r, regex_nf(model::lift_regex(g, r@)),
    ensures ids_nf(g, s),
{
    assert forall|i: int| 0 <= i < s.len() implies regex_nf(#[trigger] model::lift_regex(g, s[i]@)) by { assert(i == 0); }
}

pub proof fn lemma_dbound_star(g0: model::Graph, g: model::Graph, root: RegexId, inner: nat, d: nat, out: nat)
    requires model::graph_wf(g0), model::graph_wf(g), model::graph_extends(g0, g), root@ < g0.regexes.len(),
        g0.regexes[root@ as int].kind == model::RegexKindNode::Star(inner), d < g0.transitions.len(),
        dbound(g0, inner, d), (nf_sum(g0, d) && ids_nf(g0, seq![root])) ==> app_bound(g, out, d, lifts(g, seq![root])),
    ensures dbound(g, root@, out),
{
    reveal(dbound);
    lemma_regex_lift(g0, root@);
    lemma_regex_nf_stable(g0, g, root@);
    let p = model::lift_regex(g, root@);
    if regex_nf(p) {
        let m = m_impl();
        lemma_models_agree();
        let b = model::lift_regex(g0, inner);
        assert(p == Regex::<model::Test>::Star(Box::new(b)));
        assert(regex_nf(b));
        assert(dclass(g0, d, b));
        lemma_ids_nf1(g0, seq![root], root);
        lemma_trans_stable(g0, g, d);
        assert(lifts(g, seq![root]) =~= seq![p]);
        assert forall|v: R| #[trigger] tcls(g, out, v) implies lp(p, v) by {
            lemma_cls_nf(g, out, v);
            if rconst(v) { lemma_const_lp(p, v); } else {
                let w = choose|w: R| tcls(g, d, w) && v == #[trigger] cat_front(w, lifts(g, seq![root]));
                assert(tcls(g0, d, w));
                assert((m.prod)(b, w));
                assert(seq![w] + seq![p] =~= seq![w, p]);
                assert(v == m.cat2(w, p));
                assert((m.body)(p) == b);
                assert(m.star_lit(p, v));
                lemma_cl_base(false, |x: R| m.star_lit(p, x), v);
                assert(m.lit_shape(p, v));
                lemma_lit_to_lp(p, v);
            }
        }
        lemma_dclass_from(g, out, p);
    }
}

pub proof fn lemma_dbound_not(g0: model::Graph, g: model::Graph, root: nat, inner: nat, d: nat, out: nat)
    requires model::graph_wf(g0), model::graph_wf(g), model::graph_extends(g0, g), root < g0.regexes.len(),
        g0.regexes[root as int].kind == model::RegexKindNode::Not(inner), d < g0.transitions.len(),
        dbound(g0, inner, d), nf_sum(g0, d) ==> run_bound(g, ActionShape::Not(d), out),
    ensures dbound(g, root, out),
{
    reveal(dbound);
    lemma_regex_lift(g0, root);
    lemma_regex_nf_stable(g0, g, root);
    let p = model::lift_regex(g, root);
    if regex_nf(p) {
        let m = m_impl();
        lemma_models_agree();
        let b = model::lift_regex(g0, inner);
        assert(p == Regex::<model::Test>::Not(Box::new(b)));
        assert(regex_nf(b));
        assert(dclass(g0, d, b));
        lemma_trans_stable(g0, g, d);
        lemma_av_stable(g0, g, d);
        let nb = |w: R| neg_of(av_of(g, d), w);
        let lb = |w: R| m.not_lit(p, w);
        assert forall|w: R| #[trigger] nb(w) implies lb(w) by {
            let x = choose|x: R| (av_of(g, d).x)(x) && w == #[trigger] r_not(x);
            assert(tcls(g0, d, x));
            assert((m.lit)(b, x));
            assert((m.body)(p) == b);
            assert(w == (m.nnot)(x));
        }
        assert forall|v: R| #[trigger] tcls(g, out, v) implies lp(p, v) by {
            lemma_cls_nf(g, out, v);
            assert((av_of(g, out).x)(v));
            lemma_cl_mono(true, nb, lb, v);
            assert(m.lit_shape(p, v));
            lemma_lit_to_lp(p, v);
        }
        lemma_dclass_from(g, out, p);
    }
}

// ===== sets and lists =====

/// The derivative of a member of a set state is a factor of the set's derivative.
pub proof fn lemma_factor_set(g: model::Graph, root: nat, i: int, d: nat)
    requires model::graph_wf(g), root < g.regexes.len(), d < g.transitions.len(),
        match g.regexes[root as int].kind {
            model::RegexKindNode::Union(cs) => 0 <= i < cs.len() && dbound(g, cs[i], d),
            model::RegexKindNode::Intersect(cs) => 0 <= i < cs.len() && dbound(g, cs[i], d),
            _ => false,
        },
    ensures regex_nf(model::lift_regex(g, root)) ==> fbound(g, root, d),
{
    reveal(dbound);
    lemma_regex_lift(g, root);
    let p = model::lift_regex(g, root);
    if regex_nf(p) {
        let m = m_impl();
        lemma_models_agree();
        let cs = match g.regexes[root as int].kind {
            model::RegexKindNode::Union(cs) => cs, model::RegexKindNode::Intersect(cs) => cs, _ => Seq::empty(),
        };
        let ls = model::lift_regexes(g, cs);
        let o = ls[i];
        assert(o == model::lift_regex(g, cs[i]));
        assert(regex_nf(o));
        assert(dclass(g, d, o));
        assert((m.ops)(p).contains(o)) by {
            broadcast use vstd::prelude::Seq::to_set_ensures;
            assert(ls.contains(o));
        }
        let inter = g.regexes[root as int].kind is Intersect;
        assert forall|v: R| #[trigger] tcls(g, d, v) implies lp(p, v) by {
            lemma_cls_nf(g, d, v);
            assert((m.lit)(o, v) && (m.prod)(o, v));
            assert(m.ops_lit(p, v));
            lemma_cl_base(inter, |w: R| m.ops_lit(p, w), v);
            assert(m.lit_shape(p, v));
            lemma_lit_fold(p, v);
            assert(m.prod_shape(p, v)) by {
                if inter { lemma_cl_base(true, |w: R| (m.lit)(p, w), v); }
            }
            lemma_prod_fold(p, v);
        }
    }
}

/// The append of the derivative of a list element to the following elements is a factor of the
/// list's derivative.
pub proof fn lemma_factor_concat(g: model::Graph, root: nat, i: int, d: nat, suffix: Seq<RegexId>, out: nat)
    requires model::graph_wf(g), root < g.regexes.len(), d < g.transitions.len(),
        match g.regexes[root as int].kind {
            model::RegexKindNode::Concat(cs) => 0 <= i < cs.len() && dbound(g, cs[i], d)
                && model::regex_ids(suffix) == cs.subrange(i + 1, cs.len() as int),
            _ => false,
        },
        norm::regex_ids_valid(g, suffix),
        (nf_sum(g, d) && ids_nf(g, suffix)) ==> app_bound(g, out, d, lifts(g, suffix)),
    ensures regex_nf(model::lift_regex(g, root)) ==> fbound(g, root, out),
{
    reveal(dbound);
    lemma_regex_lift(g, root);
    let p = model::lift_regex(g, root);
    if regex_nf(p) {
        let m = m_impl();
        lemma_models_agree();
        theorem_impl_contract();
        let cs = g.regexes[root as int].kind->Concat_0;
        let es = model::lift_regexes(g, cs);
        assert((m.elems)(p) == es);
        let o = es[i];
        assert(o == model::lift_regex(g, cs[i]));
        assert(regex_nf(o));
        assert(dclass(g, d, o));
        let ys = lifts(g, suffix);
        let sub = cs.subrange(i + 1, cs.len() as int);
        assert(model::regex_ids(suffix).len() == suffix.len());
        assert(ys.len() == es.skip(i + 1).len());
        assert forall|j: int| 0 <= j < ys.len() implies ys[j] == es.skip(i + 1)[j] && regex_nf(#[trigger] model::lift_regex(g, suffix[j]@)) by {
            assert(model::regex_ids(suffix)[j] == suffix[j]@);
            assert(model::regex_ids(suffix)[j] == sub[j]);
            assert(sub[j] == cs[i + 1 + j]);
            assert(es.skip(i + 1)[j] == es[i + 1 + j]);
            assert(es[i + 1 + j] == model::lift_regex(g, cs[i + 1 + j]));
            assert(ys[j] == model::lift_regex(g, suffix[j]@));
        }
        assert(ys =~= es.skip(i + 1));
        assert(ids_nf(g, suffix));
        assert forall|v: R| #[trigger] tcls(g, out, v) implies lp(p, v) by {
            lemma_cls_nf(g, out, v);
            if rconst(v) { lemma_const_lp(p, v); } else {
                let w = choose|w: R| tcls(g, d, w) && v == #[trigger] cat_front(w, ys);
                assert((m.prod)(o, w) && (m.lit)(o, w));
                lemma_cls_nf(g, d, w);
                if i < es.len() - 1 {
                    assert(v == (m.ncat)(seq![w] + es.skip(i + 1)));
                    assert(m.list_lit(p, v));
                } else {
                    assert(es.skip(i + 1) =~= Seq::<R>::empty());
                    assert(seq![w] + es.skip(i + 1) =~= seq![w]);
                    lemma_cat_single(m, w);
                    assert(v == w);
                    assert(es.last() == o);
                    assert(m.list_lit(p, v));
                }
                lemma_cl_base(false, |x: R| m.list_lit(p, x), v);
                assert(m.lit_shape(p, v));
                lemma_lit_to_lp(p, v);
            }
        }
    }
}

/// `lemma_factor_concat` with the cache and suffix read in the graph `g0` before the append.
pub proof fn lemma_factor_concat2(g0: model::Graph, g: model::Graph, root: nat, i: int, d: nat, suffix: Seq<RegexId>, out: nat)
    requires model::graph_wf(g0), model::graph_wf(g), model::graph_extends(g0, g), root < g0.regexes.len(), d < g0.transitions.len(),
        match g0.regexes[root as int].kind {
            model::RegexKindNode::Concat(cs) => 0 <= i < cs.len() && dbound(g0, cs[i], d)
                && model::regex_ids(suffix) == cs.subrange(i + 1, cs.len() as int),
            _ => false,
        },
        norm::regex_ids_valid(g0, suffix),
        (nf_sum(g0, d) && ids_nf(g0, suffix)) ==> app_bound(g, out, d, lifts(g, suffix)),
    ensures regex_nf(model::lift_regex(g, root)) ==> fbound(g, root, out),
{
    lemma_regex_nf_stable(g0, g, root);
    assert(g.regexes[root as int] == g0.regexes[root as int]) by {
        assert(g0.regexes == g.regexes.subrange(0, g0.regexes.len() as int));
    }
    model::lemma_graph_regex_wf(g0, root);
    assert(g0.regexes[root as int].kind is Concat);
    let cs = g0.regexes[root as int].kind->Concat_0;
    assert(0 <= i < cs.len());
    assert(cs[i] < g0.regexes.len());
    lemma_dbound_stable(g0, g, cs[i], d);
    lemma_nf_sum_stable(g0, g, d);
    lemma_lifts_ids(g0, g, suffix);
    if ids_nf(g, suffix) {
        assert forall|j: int| 0 <= j < suffix.len() implies regex_nf(#[trigger] model::lift_regex(g0, suffix[j]@)) by {
            assert(lifts(g0, suffix)[j] == lifts(g, suffix)[j]);
            assert(regex_nf(model::lift_regex(g, suffix[j]@)));
        }
        assert(ids_nf(g0, suffix));
    }
    assert(norm::regex_ids_valid(g, suffix)) by {
        assert forall|j: int| 0 <= j < suffix.len() implies suffix[j]@ < g.regexes.len() by {}
    }
    lemma_factor_concat(g, root, i, d, suffix, out);
}

/// A closure of literals and products of an intersection state consists of literals and
/// products.
pub proof fn lemma_inter_closed(p: R, v: R)
    requires regex_nf(p), p is Intersect, cl(true, |w: R| lp(p, w), v), regex_nf(v),
    ensures lp(p, v),
{
    let m = m_impl();
    theorem_impl_contract();
    lemma_models_agree();
    let ob = |w: R| m.ops_lit(p, w);
    assert forall|w: R| #[trigger] lp(p, w) implies cl(true, ob, w) by {
        assert(m.lit_shape(p, w));
    }
    lemma_cl_mono(true, |w: R| lp(p, w), |w: R| cl(true, ob, w), v);
    lemma_cl_idem(true, ob, v);
    assert(m.lit_shape(p, v));
    lemma_lit_to_lp(p, v);
}

/// Before the final set constructor of `derive`: whatever the constructor returns in a later graph
/// has the class bound of the root.
pub proof fn lemma_derive_future(g0: model::Graph, root: nat, results: Seq<TransitionId>, inter: bool)
    requires model::graph_wf(g0), root < g0.regexes.len(), norm::transition_ids_valid(g0, results),
        results_bound(g0, root, results),
        match g0.regexes[root as int].kind {
            model::RegexKindNode::Union(_) => !inter,
            model::RegexKindNode::Concat(_) => !inter,
            model::RegexKindNode::Intersect(_) => inter,
            _ => false,
        },
    ensures
        forall|h: model::Graph, out: nat| model::graph_extends(g0, h) && (all_nf(g0, model::transition_ids(results)) ==> if inter {
            run_bound(h, ActionShape::Fold(model::transition_ids(results), 0), out)
        } else { collect_out(h, model::transition_ids(results), false, out) }) ==> #[trigger] dbound(h, root, out),
{
    reveal(dbound);
    reveal(results_bound);
    let ts = model::transition_ids(results);
    assert forall|h: model::Graph, out: nat| model::graph_extends(g0, h) && (all_nf(g0, ts) ==> if inter {
        run_bound(h, ActionShape::Fold(ts, 0), out)
    } else { collect_out(h, ts, false, out) }) implies #[trigger] dbound(h, root, out) by {
        lemma_regex_nf_stable(g0, h, root);
        let p = model::lift_regex(h, root);
        lemma_regex_lift(g0, root);
        if regex_nf(p) {
            assert(all_nf(g0, ts)) by {
                assert forall|k: int| 0 <= k < ts.len() implies nf_sum(g0, #[trigger] ts[k]) by {
                    assert(ts[k] == results[k]@);
                    assert(fbound(g0, root, results[k]@));
                }
            }
            lemma_all_nf_stable(g0, h, ts);
            // every result's class consists of literals and products of `p`
            let base = |w: R| lp(p, w);
            assert forall|k: int, w: R| 0 <= k < avs(h, ts).len() && #[trigger] (avs(h, ts)[k].x)(w) implies lp(p, w) && cl(true, base, w) by {
                assert(ts[k] == results[k]@);
                assert(fbound(g0, root, results[k]@));
                lemma_fbound_stable(g0, h, root, results[k]@);
                assert(tcls(h, ts[k], w));
                lemma_cl_base(true, base, w);
            }
            if inter {
                assert forall|k: int, w: R| 0 <= k < avs(h, ts).len() && #[trigger] (avs(h, ts)[k].x)(w) implies cl(true, base, w) by {}
                lemma_meet_le_cl(avs(h, ts), base);
                assert forall|v: R| #[trigger] tcls(h, out, v) implies lp(p, v) by {
                    assert((av_of(h, out).x)(v));
                    lemma_cls_nf(h, out, v);
                    lemma_inter_closed(p, v);
                }
            } else {
                assert forall|v: R| #[trigger] tcls(h, out, v) implies lp(p, v) by {
                    assert(cbound(h, ts, false, v));
                    if rconst(v) { lemma_const_lp(p, v); } else {
                        let k = choose|k: int| #![trigger avs(h, ts)[k]] 0 <= k < avs(h, ts).len() && (avs(h, ts)[k].x)(v);
                    }
                }
            }
            lemma_dclass_from(h, out, p);
        }
    }
}

/// What `RegexId::derivative_step` establishes for the transition `out` it builds for `root`
/// (`g0` is the graph before the constructors, `cache` the derivative cache): constants, the
/// conditional of a test, the class bounds of `append`/`not` on the cached derivative of the
/// body, and [`dbound`] itself for sets and lists (from `DerivativeFactors::derive`).
pub open spec fn native_bound(g0: model::Graph, g: model::Graph, root: RegexId, cache: Seq<Option<TransitionId>>, out: nat) -> bool {
    match g0.regexes[root@ as int].kind {
        model::RegexKindNode::Empty => out == g0.constants.transition_empty,
        model::RegexKindNode::Epsilon => out == g0.constants.transition_empty,
        model::RegexKindNode::All => out == g0.constants.transition_all,
        model::RegexKindNode::Test(_) => (nf_sum(g0, g0.constants.transition_epsilon) && nf_sum(g0, g0.constants.transition_empty))
            ==> ite_bound(g, out, g0.constants.transition_epsilon, g0.constants.transition_empty),
        model::RegexKindNode::Star(inner) => inner < cache.len() && cache[inner as int] is Some
            && ((nf_sum(g0, cache[inner as int]->Some_0@) && ids_nf(g0, seq![root]))
                ==> app_bound(g, out, cache[inner as int]->Some_0@, lifts(g, seq![root]))),
        model::RegexKindNode::Not(inner) => inner < cache.len() && cache[inner as int] is Some
            && (nf_sum(g0, cache[inner as int]->Some_0@) ==> run_bound(g, ActionShape::Not(cache[inner as int]->Some_0@), out)),
        _ => dbound(g, root@, out),
    }
}

/// Before the head match of `derivative_step`: whatever the match builds in a later graph has
/// the class bound of `root`.
pub proof fn lemma_native_future(g0: model::Graph, root: RegexId, cache: Seq<Option<TransitionId>>)
    requires model::graph_wf(g0), root@ < g0.regexes.len(), derivative_cache_wf(g0, cache),
    ensures forall|g: model::Graph, out: nat| model::graph_extends(g0, g) && model::graph_wf(g)
        && #[trigger] native_bound(g0, g, root, cache, out) ==> dbound(g, root@, out),
{
    assert forall|g: model::Graph, out: nat| model::graph_extends(g0, g) && model::graph_wf(g)
        && #[trigger] native_bound(g0, g, root, cache, out) implies dbound(g, root@, out) by {
        derivative_constants(g0);
        match g0.regexes[root@ as int].kind {
            model::RegexKindNode::Empty => { lemma_dbound_const(g0, root@, out); lemma_dbound_stable(g0, g, root@, out); },
            model::RegexKindNode::Epsilon => { lemma_dbound_const(g0, root@, out); lemma_dbound_stable(g0, g, root@, out); },
            model::RegexKindNode::All => { lemma_dbound_const(g0, root@, out); lemma_dbound_stable(g0, g, root@, out); },
            model::RegexKindNode::Test(t) => { lemma_dbound_test(g0, g, root@, t, out); },
            model::RegexKindNode::Star(inner) => {
                let d = cache[inner as int]->Some_0;
                assert(derivative_correct(g0, inner, d) && dbound(g0, inner, d@));
                lemma_dbound_star(g0, g, root, inner, d@, out);
            },
            model::RegexKindNode::Not(inner) => {
                let d = cache[inner as int]->Some_0;
                assert(derivative_correct(g0, inner, d) && dbound(g0, inner, d@));
                lemma_dbound_not(g0, g, root@, inner, d@, out);
            },
            _ => {},
        }
    }
}

} // verus!
