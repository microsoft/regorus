//! The steps of the transition normalizer's action machine (`normalize.rs` `Action::*_step`)
//! satisfy the machine typing invariant `verify::finite_steps::xeffect`, one lemma per branch.
use crate::normalize::verify::{self as norm, ActionShape, ChildShape};
use crate::verify::finite_collect::*;
use crate::verify::finite_impl::*;
use crate::verify::finite_link::*;
use crate::verify::finite_machine::*;
use crate::verify::finite_steps::*;
use crate::verify::finite_trans::*;
use junco_core::kernel::verify as model;
use junco_core::kernel::{RegexId, TestId, TransitionId};
use junco_core::verify::history_specs::Regex;
use vstd::prelude::*;

verus! {

broadcast use junco_core::kernel::verify::group_kernel_views;

// ===== abstract operations =====

pub proof fn lemma_if_le(a: AV, b: AV, c: AV)
    requires av_le(a, c), av_le(b, c),
    ensures av_le(av_if(a, b), c),
{}
/// `av_le` between node values, stated on classes.
pub proof fn lemma_av_le_cls(g: model::Graph, s: nat, t: nat)
    requires av_le(av_of(g, s), av_of(g, t)),
    ensures forall|v: R| #[trigger] tcls(g, s, v) ==> tcls(g, t, v), forall|v: R| #[trigger] ycls(g, s, v) ==> ycls(g, t, v),
{
    assert forall|v: R| #[trigger] tcls(g, s, v) implies tcls(g, t, v) by { assert((av_of(g, s).x)(v)); }
    assert forall|v: R| #[trigger] ycls(g, s, v) implies ycls(g, t, v) by { assert((av_of(g, s).y)(v)); }
}


/// A union of values below `t` is below `t`, when `t` contains the constants.
pub proof fn lemma_union_le(xs: Seq<AV>, t: AV)
    requires forall|i: int| 0 <= i < xs.len() ==> #[trigger] av_le(xs[i], t),
        forall|v: R| rconst(v) ==> #[trigger] (t.x)(v), forall|v: R| #[trigger] (t.y)(v),
    ensures av_le(av_union(xs), t),
{
    assert forall|v: R| #[trigger] (av_union(xs).x)(v) implies (t.x)(v) by {
        if any_x(xs, v) {
            let i = choose|i: int| #![trigger xs[i]] 0 <= i < xs.len() && (xs[i].x)(v);
            assert(av_le(xs[i], t));
        }
    }
}

/// A meet of values whose classes lie in the closure of `base` lies in it.
pub proof fn lemma_meet_le_cl(xs: Seq<AV>, base: spec_fn(R) -> bool)
    requires forall|i: int, w: R| 0 <= i < xs.len() && #[trigger] (xs[i].x)(w) ==> cl(true, base, w),
    ensures forall|v: R| #[trigger] (av_meet(xs).x)(v) ==> cl(true, base, v),
{
    assert forall|v: R| #[trigger] (av_meet(xs).x)(v) implies cl(true, base, v) by {
        assert forall|w: R| #[trigger] any_x(xs, w) implies cl(true, base, w) by {
            let i = choose|i: int| #![trigger xs[i]] 0 <= i < xs.len() && (xs[i].x)(w);
        }
        lemma_cl_mono(true, |w: R| any_x(xs, w), |w: R| cl(true, base, w), v);
        lemma_cl_idem(true, base, v);
    }
}

/// `t`'s class is in the closure of the pair `(a, b)` when it is in `a`'s or `b`'s.
pub proof fn lemma_pair_base(g: model::Graph, a: nat, b: nat, t: nat)
    requires (forall|v: R| #[trigger] tcls(g, t, v) ==> tcls(g, a, v)) || (forall|v: R| #[trigger] tcls(g, t, v) ==> tcls(g, b, v)),
    ensures forall|v: R| #[trigger] tcls(g, t, v) ==> cl(true, |w: R| any_x(seq![av_of(g, a), av_of(g, b)], w), v),
{
    let s = seq![av_of(g, a), av_of(g, b)];
    assert forall|v: R| #[trigger] tcls(g, t, v) implies cl(true, |w: R| any_x(s, w), v) by {
        if tcls(g, a, v) { assert(s[0] == av_of(g, a)); assert(any_x(s, v)); }
        else { assert(s[1] == av_of(g, b)); assert(any_x(s, v)); }
        lemma_cl_base(true, |w: R| any_x(s, w), v);
    }
}

/// A meet over `(l, r)` is below the meet over `(a, b)` when `l ≤ a` and `r ≤ b`.
pub proof fn lemma_meet_pair_le(g: model::Graph, l: nat, r: nat, a: nat, b: nat)
    requires forall|v: R| #[trigger] tcls(g, l, v) ==> tcls(g, a, v), forall|v: R| #[trigger] tcls(g, r, v) ==> tcls(g, b, v),
    ensures av_le(av_meet(seq![av_of(g, l), av_of(g, r)]), av_meet(seq![av_of(g, a), av_of(g, b)])),
{
    let s = seq![av_of(g, l), av_of(g, r)];
    let base = |w: R| any_x(seq![av_of(g, a), av_of(g, b)], w);
    lemma_pair_base(g, a, b, l);
    lemma_pair_base(g, a, b, r);
    assert forall|i: int, w: R| 0 <= i < s.len() && #[trigger] (s[i].x)(w) implies cl(true, base, w) by {
        if i == 0 { assert(tcls(g, l, w)); } else { assert(tcls(g, r, w)); }
    }
    lemma_meet_le_cl(s, base);
}

pub proof fn lemma_meet_pair_const(g: model::Graph, a: nat, b: nat, v: R)
    requires rconst(v),
    ensures (av_meet(seq![av_of(g, a), av_of(g, b)]).x)(v),
{
    lemma_cl_const(true, |w: R| any_x(seq![av_of(g, a), av_of(g, b)], w), v);
}

// ===== children =====

pub open spec fn ctasks(cs: Seq<nat>, f: ChildShape) -> Seq<ActionShape> {
    cs.reverse().map(|i: int, c: nat| norm::transition_child_shape(f, c))
}

pub open spec fn child_avs(g: model::Graph, cs: Seq<nat>, f: ChildShape) -> Seq<AV> {
    cs.map(|i: int, c: nat| push_av(g, norm::transition_child_shape(f, c)))
}

pub proof fn lemma_child_actions(g: model::Graph, id: nat, f: ChildShape)
    ensures norm::transition_child_actions(g, id, f) == ctasks(norm::transition_children(g, id), f),
{
    assert(norm::transition_child_actions(g, id, f) =~= ctasks(norm::transition_children(g, id), f));
}

/// Child actions run in source order, each pushing its value.
pub proof fn lemma_arun_children(g: model::Graph, cs: Seq<nat>, f: ChildShape, s: Seq<AV>)
    ensures arun(g, ctasks(cs, f), s) == Some(s + child_avs(g, cs, f)),
    decreases cs.len(),
{
    let acts = ctasks(cs, f);
    if cs.len() == 0 {
        assert(acts =~= Seq::<ActionShape>::empty());
        assert(s + child_avs(g, cs, f) =~= s);
    } else {
        let rest = cs.drop_first();
        let t = norm::transition_child_shape(f, cs[0]);
        assert(acts.last() == t);
        assert(acts.drop_last() =~= ctasks(rest, f));
        lemma_aapply_push(g, t, s);
        lemma_arun_children(g, rest, f, s.push(push_av(g, t)));
        assert(s.push(push_av(g, t)) + child_avs(g, rest, f) =~= s + child_avs(g, cs, f));
    }
}

/// A set action over the children's actions pushes the union or meet of their values.
pub proof fn lemma_arun_set_children(g: model::Graph, cs: Seq<nat>, f: ChildShape, s: Seq<AV>, inter: bool)
    ensures arun(g, seq![if inter { ActionShape::Intersect(cs.len()) } else { ActionShape::Union(cs.len()) }] + ctasks(cs, f), s)
        == Some(s.push(if inter { av_meet(child_avs(g, cs, f)) } else { av_union(child_avs(g, cs, f)) })),
{
    let u = if inter { ActionShape::Intersect(cs.len()) } else { ActionShape::Union(cs.len()) };
    lemma_arun_prefix(g, seq![u], ctasks(cs, f), s);
    lemma_arun_children(g, cs, f, s);
    let n = s + child_avs(g, cs, f);
    lemma_arun_one(g, u, n);
    assert(n.take(s.len() as int) =~= s);
    assert(n.subrange(s.len() as int, n.len() as int) =~= child_avs(g, cs, f));
}

pub proof fn lemma_xnf_children(g: model::Graph, cs: Seq<nat>, f: ChildShape)
    requires all_nf(g, cs), match f {
        ChildShape::Clean(_) => true, ChildShape::Not => true,
        ChildShape::Append(r) => r < g.regexes.len() && regex_nf(model::lift_regex(g, r)),
        ChildShape::PairLeft(o) => nf_sum(g, o), ChildShape::PairRight(o) => nf_sum(g, o),
    },
    ensures xnf_tasks(g, ctasks(cs, f)),
{
    assert forall|i: int| 0 <= i < ctasks(cs, f).len() implies #[trigger] xnf_task(g, ctasks(cs, f)[i]) by {
        assert(cs.reverse()[i] == cs[cs.len() - 1 - i]);
        assert(nf_sum(g, cs[cs.len() - 1 - i]));
    }
}

/// The child tasks of a set node after `p0`.
pub proof fn lemma_child_effect(e: model::Graph, g: model::Graph, task: ActionShape, p0: Seq<ActionShape>, v0: Seq<TransitionId>,
    id: nat, f: ChildShape, inter: bool, y: AV)
    requires xctx(e, g, task, p0, v0), norm::transition_action_pushes(task), id < g.transitions.len(),
        all_nf(g, norm::transition_children(g, id)), match f {
            ChildShape::Clean(_) => true, ChildShape::Not => true,
            ChildShape::Append(r) => r < g.regexes.len() && regex_nf(model::lift_regex(g, r)),
            ChildShape::PairLeft(o) => nf_sum(g, o), ChildShape::PairRight(o) => nf_sum(g, o),
        },
        y == (if inter { av_meet(child_avs(g, norm::transition_children(g, id), f)) }
            else { av_union(child_avs(g, norm::transition_children(g, id), f)) }),
        av_le(y, push_av(g, task)),
    ensures xeffect(g, task, p0, v0, p0.push(if inter { ActionShape::Intersect(norm::transition_children(g, id).len()) }
            else { ActionShape::Union(norm::transition_children(g, id).len()) }) + norm::transition_child_actions(g, id, f), v0),
{
    reveal(xpre); reveal(xeffect); reveal(xrun); reveal(xcfg); reveal(xstep);
    let cs = norm::transition_children(g, id);
    let u = if inter { ActionShape::Intersect(cs.len()) } else { ActionShape::Union(cs.len()) };
    lemma_child_actions(g, id, f);
    let exp = seq![u] + ctasks(cs, f);
    lemma_arun_set_children(g, cs, f, vavs(g, v0), inter);
    lemma_xnf_children(g, cs, f);
    lemma_xnf1(g, u);
    lemma_xnf_tasks_append(g, seq![u], ctasks(cs, f));
    lemma_xpre_stable(e, g, task, p0, v0);
    lemma_effect(e, g, task, p0, v0, exp, v0, y);
    assert(p0 + exp =~= p0.push(u) + ctasks(cs, f));
}

/// `arun([c, t2, t1], s)` for a conditional `c` over two pushing tasks.
pub proof fn lemma_arun_cond(g: model::Graph, c: ActionShape, t2: ActionShape, t1: ActionShape, s: Seq<AV>)
    requires c is If || c is CleanIf, norm::transition_action_pushes(t1), norm::transition_action_pushes(t2),
    ensures arun(g, seq![c, t2, t1], s) == Some(s.push(av_if(push_av(g, t1), push_av(g, t2)))),
{
    let s1 = s.push(push_av(g, t1));
    let s2 = s1.push(push_av(g, t2));
    assert(seq![c, t2, t1] =~= seq![c, t2].push(t1));
    assert(seq![c, t2] =~= seq![c].push(t2));
    lemma_arun_push(g, seq![c, t2], t1, s);
    lemma_aapply_push(g, t1, s);
    lemma_arun_push(g, seq![c], t2, s1);
    lemma_aapply_push(g, t2, s1);
    lemma_arun_one(g, c, s2);
    assert(s2.take(s2.len() as int - 2) =~= s);
    assert(s2[s2.len() as int - 2] == push_av(g, t1));
}

/// A conditional expansion `p0 ++ [c, t2, t1]` whose join is below the action's effect.
pub proof fn lemma_cond_effect(e: model::Graph, g: model::Graph, task: ActionShape, p0: Seq<ActionShape>, v0: Seq<TransitionId>,
    c: ActionShape, t2: ActionShape, t1: ActionShape)
    requires xctx(e, g, task, p0, v0), norm::transition_action_pushes(task), c is If || c is CleanIf,
        norm::transition_action_pushes(t1), norm::transition_action_pushes(t2), xnf_task(g, t1), xnf_task(g, t2),
        av_le(push_av(g, t1), push_av(g, task)), av_le(push_av(g, t2), push_av(g, task)),
    ensures xeffect(g, task, p0, v0, p0.push(c).push(t2).push(t1), v0),
{
    reveal(xpre); reveal(xeffect); reveal(xrun); reveal(xcfg); reveal(xstep);
    let exp = seq![c, t2, t1];
    lemma_arun_cond(g, c, t2, t1, vavs(g, v0));
    lemma_xnf3(g, c, t2, t1);
    lemma_xpre_stable(e, g, task, p0, v0);
    lemma_if_le(push_av(g, t1), push_av(g, t2), push_av(g, task));
    lemma_effect(e, g, task, p0, v0, exp, v0, av_if(push_av(g, t1), push_av(g, t2)));
    assert(p0 + exp =~= p0.push(c).push(t2).push(t1));
}

/// A single pushing task replaces the action.
pub proof fn lemma_replace_effect(e: model::Graph, g: model::Graph, task: ActionShape, p0: Seq<ActionShape>, v0: Seq<TransitionId>,
    t: ActionShape)
    requires xctx(e, g, task, p0, v0), norm::transition_action_pushes(task), norm::transition_action_pushes(t), xnf_task(g, t),
        av_le(push_av(g, t), push_av(g, task)),
    ensures xeffect(g, task, p0, v0, p0.push(t), v0),
{
    reveal(xpre); reveal(xeffect); reveal(xrun); reveal(xcfg); reveal(xstep);
    lemma_arun_one(g, t, vavs(g, v0));
    lemma_aapply_push(g, t, vavs(g, v0));
    lemma_xnf1(g, t);
    lemma_xpre_stable(e, g, task, p0, v0);
    lemma_effect(e, g, task, p0, v0, seq![t], v0, push_av(g, t));
    assert(p0 + seq![t] =~= p0.push(t));
}

/// A local conditional is one of its branches or a conditional node over them.
pub proof fn lemma_local_if(g: model::Graph, test: nat, a: nat, b: nat, out: nat)
    requires model::graph_wf(g), a < g.transitions.len(), b < g.transitions.len(), nf_sum(g, a), nf_sum(g, b),
        out == a || out == b || (out < g.transitions.len() && g.transitions[out as int] == model::TransitionNode::If(test, a, b)),
    ensures out < g.transitions.len(), nf_sum(g, out), av_le(av_of(g, out), av_if(av_of(g, a), av_of(g, b))),
{
    if out != a && out != b {
        lemma_if_cls(g, out, test, a, b);
    }
}

// ===== clean_step =====

pub proof fn lemma_clean_self(e: model::Graph, g: model::Graph, p0: Seq<ActionShape>, v0: Seq<TransitionId>,
    id: TransitionId, path: TestId)
    requires xctx(e, g, ActionShape::Clean(id@, path@), p0, v0),
    ensures xeffect(g, ActionShape::Clean(id@, path@), p0, v0, p0, v0.push(id)),
{
    reveal(xpre); reveal(xeffect); reveal(xrun); reveal(xcfg); reveal(xstep);
    lemma_nf_sum_stable(e, g, id@);
    lemma_av_le_refl(av_of(g, id@));
    lemma_effect_value(e, g, ActionShape::Clean(id@, path@), p0, v0, id);
}

pub proof fn lemma_clean_if(e: model::Graph, g: model::Graph, p0: Seq<ActionShape>, v0: Seq<TransitionId>,
    id: TransitionId, path: TestId, test: TestId, a: TransitionId, b: TransitionId, yes: TestId, no: TestId)
    requires xctx(e, g, ActionShape::Clean(id@, path@), p0, v0),
        e.transitions[id@ as int] == model::TransitionNode::If(test@, a@, b@),
    ensures xeffect(g, ActionShape::Clean(id@, path@), p0, v0, norm::transition_clean_if_tasks(g, test, a, b, yes, no, p0), v0),
{
    reveal(xpre); reveal(xeffect); reveal(xrun); reveal(xcfg); reveal(xstep);
    let task = ActionShape::Clean(id@, path@);
    lemma_nf_sum_stable(e, g, id@);
    lemma_if_cls(g, id@, test@, a@, b@);
    lemma_nf_children(g, id@);
    let ta = ActionShape::Clean(a@, yes@);
    let tb = ActionShape::Clean(b@, no@);
    if yes@ == g.constants.test_false {
        lemma_replace_effect(e, g, task, p0, v0, tb);
    } else if no@ == g.constants.test_false {
        lemma_replace_effect(e, g, task, p0, v0, ta);
    } else {
        lemma_cond_effect(e, g, task, p0, v0, ActionShape::If(test@), tb, ta);
    }
}

pub proof fn lemma_clean_children(e: model::Graph, g: model::Graph, p0: Seq<ActionShape>, v0: Seq<TransitionId>,
    id: TransitionId, path: TestId, inter: bool)
    requires xctx(e, g, ActionShape::Clean(id@, path@), p0, v0), id@ < e.transitions.len(),
        match e.transitions[id@ as int] {
            model::TransitionNode::Union(_) => !inter,
            model::TransitionNode::Intersect(_) => inter,
            _ => false,
        },
    ensures xeffect(g, ActionShape::Clean(id@, path@), p0, v0, norm::transition_clean_child_tasks(g, id, path, inter, p0), v0),
{
    reveal(xpre); reveal(xeffect); reveal(xrun); reveal(xcfg); reveal(xstep);
    let task = ActionShape::Clean(id@, path@);
    lemma_nf_sum_stable(e, g, id@);
    lemma_nf_children(g, id@);
    norm::transition_lemma_children(g, id@);
    let cs = norm::transition_children(g, id@);
    let f = ChildShape::Clean(path@);
    assert(child_avs(g, cs, f) =~= avs(g, cs));
    if inter {
        lemma_inter_cls(g, id@, cs);
        lemma_child_effect(e, g, task, p0, v0, id@, f, inter, av_meet(avs(g, cs)));
    } else {
        lemma_union_cls(g, id@, cs);
        lemma_child_effect(e, g, task, p0, v0, id@, f, inter, av_union(avs(g, cs)));
    }
}

pub proof fn lemma_clean_not(e: model::Graph, g: model::Graph, p0: Seq<ActionShape>, v0: Seq<TransitionId>,
    id: TransitionId, path: TestId, inner: TransitionId)
    requires xctx(e, g, ActionShape::Clean(id@, path@), p0, v0),
        e.transitions[id@ as int] == model::TransitionNode::Not(inner@),
    ensures xeffect(g, ActionShape::Clean(id@, path@), p0, v0,
        p0.push(ActionShape::NotResult).push(ActionShape::Clean(inner@, path@)), v0),
{
    reveal(xpre); reveal(xeffect); reveal(xrun); reveal(xcfg); reveal(xstep);
    let task = ActionShape::Clean(id@, path@);
    lemma_nf_sum_stable(e, g, id@);
    lemma_nf_children(g, id@);
    lemma_not_cls(g, id@, inner@);
    let s = vavs(g, v0);
    let t1 = ActionShape::Clean(inner@, path@);
    let exp = seq![ActionShape::NotResult, t1];
    assert(exp =~= seq![ActionShape::NotResult].push(t1));
    lemma_arun_push(g, seq![ActionShape::NotResult], t1, s);
    lemma_arun_one(g, ActionShape::NotResult, s.push(av_of(g, inner@)));
    assert(s.push(av_of(g, inner@)).drop_last() =~= s);
    lemma_xnf2(g, ActionShape::NotResult, t1);
    lemma_xpre_stable(e, g, task, p0, v0);
    lemma_effect(e, g, task, p0, v0, exp, v0, av_neg(av_of(g, inner@)));
    assert(p0 + exp =~= p0.push(ActionShape::NotResult).push(t1));
}

/// `N(w N(ys))` is in the class of an append node over `ys`.
pub proof fn lemma_app_link(g: model::Graph, t: nat, k: nat, rs: Seq<nat>, w: R)
    requires model::graph_wf(g), t < g.transitions.len(), g.transitions[t as int] == model::TransitionNode::Append(k, rs),
        nf_sum(g, t), tcls(g, k, w),
    ensures tcls(g, t, cat_r(w, r_cat(model::lift_regexes(g, rs)))), regex_nf(w),
{
    lemma_append_cls(g, t, k, rs);
    lemma_nf_children(g, t);
    lemma_cls_nf(g, k, w);
    let ys = model::lift_regexes(g, rs);
    assert(all_rnf(ys)) by {
        assert forall|i: int| 0 <= i < ys.len() implies regex_nf(#[trigger] ys[i]) by {}
    }
    lemma_cat_nest(w, ys);
    assert(tcls(g, t, ccat(g, w, rs)));
}

pub proof fn lemma_lifts_ids(e: model::Graph, g: model::Graph, xs: Seq<RegexId>)
    requires model::graph_wf(e), model::graph_extends(e, g), norm::regex_ids_valid(e, xs),
    ensures lifts(e, xs) == model::lift_regexes(g, model::regex_ids(xs)), lifts(e, xs) == lifts(g, xs),
        model::bounded(model::regex_ids(xs), e.regexes.len()),
{
    assert forall|i: int| 0 <= i < xs.len() implies #[trigger] model::lift_regex(e, xs[i]@) == model::lift_regex(g, xs[i]@) by {
        lemma_regex_nf_stable(e, g, xs[i]@);
    }
    assert(lifts(e, xs) =~= model::lift_regexes(g, model::regex_ids(xs)));
    assert(lifts(e, xs) =~= lifts(g, xs));
    assert forall|i: int| 0 <= i < model::regex_ids(xs).len() implies #[trigger] model::regex_ids(xs)[i] < e.regexes.len() by {}
}

pub proof fn lemma_clean_append(e: model::Graph, g: model::Graph, p0: Seq<ActionShape>, v0: Seq<TransitionId>,
    id: TransitionId, path: TestId, inner: TransitionId, xs: Seq<RegexId>, r: RegexId)
    requires xctx(e, g, ActionShape::Clean(id@, path@), p0, v0),
        e.transitions[id@ as int] == model::TransitionNode::Append(inner@, model::regex_ids(xs)),
        norm::regex_ids_valid(e, xs), r@ < g.regexes.len(), norm::regex_concat_result(e, g, xs, r@),
    ensures xeffect(g, ActionShape::Clean(id@, path@), p0, v0,
        p0.push(ActionShape::AppendResult(r@)).push(ActionShape::Clean(inner@, path@)), v0),
{
    reveal(xpre); reveal(xeffect); reveal(xrun); reveal(xcfg); reveal(xstep);
    let task = ActionShape::Clean(id@, path@);
    let rs = model::regex_ids(xs);
    lemma_nf_sum_stable(e, g, id@);
    lemma_nf_children(g, id@);
    lemma_append_cls(g, id@, inner@, rs);
    lemma_lifts_ids(e, g, xs);
    lemma_concat_link(e, g, xs, r@);
    let ys = model::lift_regexes(g, rs);
    assert(all_rnf(ys)) by { assert forall|i: int| 0 <= i < ys.len() implies regex_nf(#[trigger] ys[i]) by {} }
    lemma_cat_nf(ys);
    let z = model::lift_regex(g, r@);
    let y = av_app(av_of(g, inner@), z);
    assert forall|v: R| #[trigger] (y.x)(v) implies tcls(g, id@, v) by {
        if app_of(av_of(g, inner@), z, v) {
            let w = choose|w: R| (av_of(g, inner@).x)(w) && v == #[trigger] cat_r(w, z);
            lemma_app_link(g, id@, inner@, rs, w);
        }
    }
    assert forall|v: R| #[trigger] (y.y)(v) implies ycls(g, id@, v) by {}
    let s = vavs(g, v0);
    let t1 = ActionShape::Clean(inner@, path@);
    let t2 = ActionShape::AppendResult(r@);
    let exp = seq![t2, t1];
    assert(exp =~= seq![t2].push(t1));
    lemma_arun_push(g, seq![t2], t1, s);
    lemma_arun_one(g, t2, s.push(av_of(g, inner@)));
    assert(s.push(av_of(g, inner@)).drop_last() =~= s);
    lemma_xnf2(g, t2, t1);
    lemma_xpre_stable(e, g, task, p0, v0);
    lemma_effect(e, g, task, p0, v0, exp, v0, y);
    assert(p0 + exp =~= p0.push(t2).push(t1));
}

// ===== not_step =====

pub proof fn lemma_not_const(e: model::Graph, g1: model::Graph, g: model::Graph, p0: Seq<ActionShape>, v0: Seq<TransitionId>,
    id: TransitionId, head: RegexId, r: RegexId, out: TransitionId)
    requires xctx(e, g, ActionShape::Not(id@), p0, v0), model::graph_wf(g1), model::graph_extends(e, g1), model::graph_extends(g1, g),
        e.transitions[id@ as int] == model::TransitionNode::Const(head@),
        r@ < g1.regexes.len(), norm::regex_not_result(g1, head@, r@),
        out@ < g.transitions.len(), g.transitions[out@ as int] == model::TransitionNode::Const(r@),
    ensures xeffect(g, ActionShape::Not(id@), p0, v0, p0, v0.push(out)),
{
    reveal(xpre); reveal(xeffect); reveal(xrun); reveal(xcfg); reveal(xstep);
    let task = ActionShape::Not(id@);
    lemma_nf_sum_stable(e, g, id@);
    lemma_nf_children(e, id@);
    lemma_regex_nf_stable(e, g1, head@);
    lemma_not_link(g1, head@, r@);
    lemma_regex_nf_stable(g1, g, r@);
    lemma_regex_nf_stable(e, g, head@);
    lemma_const_cls(g, id@, head@);
    lemma_const_cls(g, out@, r@);
    let x = model::lift_regex(g, head@);
    let base = |w: R| neg_of(av_of(g, id@), w);
    assert((av_of(g, id@).x)(x));
    assert(base(r_not(x)));
    assert forall|v: R| #[trigger] tcls(g, out@, v) implies (av_neg(av_of(g, id@)).x)(v) by {
        if rconst(v) { lemma_cl_const(true, base, v); } else { lemma_cl_base(true, base, v); }
    }
    lemma_nf_weaken(g, out@);
    lemma_effect_value(e, g, task, p0, v0, out);
}

pub proof fn lemma_not_double(e: model::Graph, g: model::Graph, p0: Seq<ActionShape>, v0: Seq<TransitionId>,
    id: TransitionId, inner: TransitionId)
    requires xctx(e, g, ActionShape::Not(id@), p0, v0), e.transitions[id@ as int] == model::TransitionNode::Not(inner@),
    ensures xeffect(g, ActionShape::Not(id@), p0, v0, p0, v0.push(inner)),
{
    reveal(xpre); reveal(xeffect); reveal(xrun); reveal(xcfg); reveal(xstep);
    let task = ActionShape::Not(id@);
    lemma_nf_sum_stable(e, g, id@);
    lemma_nf_children(g, id@);
    lemma_not_cls(g, id@, inner@);
    let base = |w: R| neg_of(av_of(g, id@), w);
    let nb = |w: R| neg_of(av_of(g, inner@), w);
    assert forall|v: R| #[trigger] tcls(g, inner@, v) implies cl(true, base, v) by {
        lemma_cls_nf(g, inner@, v);
        lemma_not_not(v);
        assert(nb(r_not(v)));
        lemma_cl_base(true, nb, r_not(v));
        assert((av_neg(av_of(g, inner@)).x)(r_not(v)));
        assert(tcls(g, id@, r_not(v)));
        assert(base(r_not(r_not(v))));
        lemma_cl_base(true, base, v);
    }
    lemma_effect_value(e, g, task, p0, v0, inner);
}

pub proof fn lemma_not_wrap(e: model::Graph, g: model::Graph, p0: Seq<ActionShape>, v0: Seq<TransitionId>,
    id: TransitionId, out: TransitionId)
    requires xctx(e, g, ActionShape::Not(id@), p0, v0), e.transitions[id@ as int] is Append,
        out@ < g.transitions.len(), g.transitions[out@ as int] == model::TransitionNode::Not(id@),
    ensures xeffect(g, ActionShape::Not(id@), p0, v0, p0, v0.push(out)),
{
    reveal(xpre); reveal(xeffect); reveal(xrun); reveal(xcfg); reveal(xstep);
    let task = ActionShape::Not(id@);
    lemma_nf_sum_stable(e, g, id@);
    lemma_not_cls(g, out@, id@);
    assert(nf_prod(g, id@));
    assert(nf_lit(g, id@));
    assert(nf_lit(g, out@));
    lemma_nf_weaken(g, out@);
    lemma_effect_value(e, g, task, p0, v0, out);
}

pub proof fn lemma_not_flip(e: model::Graph, g: model::Graph, p0: Seq<ActionShape>, v0: Seq<TransitionId>,
    id: TransitionId, test: TestId, a: TransitionId, b: TransitionId, guard: TestId, out: TransitionId)
    requires xctx(e, g, ActionShape::Not(id@), p0, v0), e.transitions[id@ as int] == model::TransitionNode::If(test@, a@, b@),
        a@ == e.constants.transition_all, b@ == e.constants.transition_empty,
        out@ == a@ || out@ == b@ || (out@ < g.transitions.len() && g.transitions[out@ as int] == model::TransitionNode::If(guard@, a@, b@)),
    ensures xeffect(g, ActionShape::Not(id@), p0, v0, p0.push(ActionShape::Clean(out@, g.constants.test_true)), v0),
{
    reveal(xpre); reveal(xeffect); reveal(xrun); reveal(xcfg); reveal(xstep);
    let task = ActionShape::Not(id@);
    lemma_const_transitions(g);
    lemma_local_if(g, guard@, a@, b@, out@);
    let t = ActionShape::Clean(out@, g.constants.test_true);
    assert forall|v: R| #[trigger] (av_of(g, out@).x)(v) implies (av_neg(av_of(g, id@)).x)(v) by {
        lemma_cl_const(true, |w: R| neg_of(av_of(g, id@), w), v);
    }
    lemma_replace_effect(e, g, task, p0, v0, t);
}

/// Not or Append over a conditional: the action on both branches under the test.
pub proof fn lemma_unary_if(e: model::Graph, g: model::Graph, p0: Seq<ActionShape>, v0: Seq<TransitionId>,
    id: TransitionId, test: TestId, a: TransitionId, b: TransitionId, suffix: Option<RegexId>)
    requires xctx(e, g, match suffix { Some(r) => ActionShape::Append(id@, r@), None => ActionShape::Not(id@) }, p0, v0),
        e.transitions[id@ as int] == model::TransitionNode::If(test@, a@, b@),
    ensures xeffect(g, match suffix { Some(r) => ActionShape::Append(id@, r@), None => ActionShape::Not(id@) }, p0, v0,
        norm::machine_unary_if_tasks(g, test, a, b, suffix, p0), v0),
{
    reveal(xpre); reveal(xeffect); reveal(xrun); reveal(xcfg); reveal(xstep);
    let task = match suffix { Some(r) => ActionShape::Append(id@, r@), None => ActionShape::Not(id@) };
    lemma_xpre_stable(e, g, task, p0, v0);
    lemma_nf_sum_stable(e, g, id@);
    lemma_if_cls(g, id@, test@, a@, b@);
    lemma_nf_children(g, id@);
    let ta = match suffix { Some(r) => ActionShape::Append(a@, r@), None => ActionShape::Not(a@) };
    let tb = match suffix { Some(r) => ActionShape::Append(b@, r@), None => ActionShape::Not(b@) };
    match suffix {
        Some(r) => {
            lemma_app_mono(av_of(g, a@), av_of(g, id@), model::lift_regex(g, r@));
            lemma_app_mono(av_of(g, b@), av_of(g, id@), model::lift_regex(g, r@));
        },
        None => {
            lemma_neg_mono(av_of(g, a@), av_of(g, id@));
            lemma_neg_mono(av_of(g, b@), av_of(g, id@));
        },
    }
    lemma_cond_effect(e, g, task, p0, v0, ActionShape::CleanIf(test@, g.constants.test_true), tb, ta);
}

/// Not or Append over a set node: the action on each child, combined by the dual or same set action.
pub proof fn lemma_unary_children(e: model::Graph, g: model::Graph, p0: Seq<ActionShape>, v0: Seq<TransitionId>,
    id: TransitionId, suffix: Option<RegexId>, inter: bool)
    requires xctx(e, g, match suffix { Some(r) => ActionShape::Append(id@, r@), None => ActionShape::Not(id@) }, p0, v0),
        id@ < e.transitions.len(),
        match suffix {
            Some(r) => !inter && e.transitions[id@ as int] is Union,
            None => match e.transitions[id@ as int] {
                model::TransitionNode::Union(_) => inter,
                model::TransitionNode::Intersect(_) => !inter,
                _ => false,
            },
        },
    ensures xeffect(g, match suffix { Some(r) => ActionShape::Append(id@, r@), None => ActionShape::Not(id@) }, p0, v0,
        norm::machine_unary_child_tasks(g, id, suffix, inter, p0), v0),
{
    reveal(xpre); reveal(xeffect); reveal(xrun); reveal(xcfg); reveal(xstep);
    let task = match suffix { Some(r) => ActionShape::Append(id@, r@), None => ActionShape::Not(id@) };
    let f = match suffix { Some(r) => ChildShape::Append(r@), None => ChildShape::Not };
    lemma_xpre_stable(e, g, task, p0, v0);
    lemma_nf_sum_stable(e, g, id@);
    lemma_nf_children(g, id@);
    norm::transition_lemma_children(g, id@);
    let cs = norm::transition_children(g, id@);
    let xs = child_avs(g, cs, f);
    let t = push_av(g, task);
    // every child is below the node
    assert forall|i: int| 0 <= i < cs.len() implies #[trigger] av_le(av_of(g, cs[i]), av_of(g, id@)) by {
        match g.transitions[id@ as int] {
            model::TransitionNode::Union(ds) => { lemma_union_cls(g, id@, ds); },
            model::TransitionNode::Intersect(ds) => {
                lemma_inter_cls(g, id@, ds);
                assert forall|v: R| #[trigger] tcls(g, cs[i], v) implies tcls(g, id@, v) by {}
            },
            _ => {},
        }
    }
    assert forall|i: int| 0 <= i < xs.len() implies #[trigger] av_le(xs[i], t) by {
        assert(xs[i] == push_av(g, norm::transition_child_shape(f, cs[i])));
        assert(av_le(av_of(g, cs[i]), av_of(g, id@)));
        match suffix {
            Some(r) => { lemma_app_mono(av_of(g, cs[i]), av_of(g, id@), model::lift_regex(g, r@)); },
            None => { lemma_neg_mono(av_of(g, cs[i]), av_of(g, id@)); },
        }
    }
    assert forall|v: R| rconst(v) implies #[trigger] (t.x)(v) by {
        match suffix {
            Some(r) => {},
            None => { lemma_cl_const(true, |w: R| neg_of(av_of(g, id@), w), v); },
        }
    }
    let y = if inter { av_meet(xs) } else { av_union(xs) };
    if inter {
        let base = |w: R| neg_of(av_of(g, id@), w);
        assert forall|i: int, w: R| 0 <= i < xs.len() && #[trigger] (xs[i].x)(w) implies cl(true, base, w) by {
            assert(av_le(xs[i], t));
        }
        lemma_meet_le_cl(xs, base);
    } else {
        lemma_union_le(xs, t);
    }
    lemma_child_effect(e, g, task, p0, v0, id@, f, inter, y);
}

// ===== append_step =====

/// Pushing a constant transition below an action whose class contains the constants.
pub proof fn lemma_push_const(e: model::Graph, g: model::Graph, task: ActionShape, p0: Seq<ActionShape>, v0: Seq<TransitionId>,
    out: TransitionId)
    requires xctx(e, g, task, p0, v0), norm::transition_action_pushes(task), out@ == g.constants.transition_empty,
        forall|v: R| rconst(v) ==> #[trigger] (push_av(g, task).x)(v), forall|v: R| #[trigger] (push_av(g, task).y)(v),
    ensures xeffect(g, task, p0, v0, p0, v0.push(out)),
{
    reveal(xpre); reveal(xeffect); reveal(xrun); reveal(xcfg); reveal(xstep);
    lemma_const_transitions(g);
    lemma_effect_value(e, g, task, p0, v0, out);
}

pub proof fn lemma_append_eps(e: model::Graph, g: model::Graph, p0: Seq<ActionShape>, v0: Seq<TransitionId>,
    id: TransitionId, r: RegexId)
    requires xctx(e, g, ActionShape::Append(id@, r@), p0, v0), r@ == e.constants.epsilon,
    ensures xeffect(g, ActionShape::Append(id@, r@), p0, v0, p0, v0.push(id)),
{
    reveal(xpre); reveal(xeffect); reveal(xrun); reveal(xcfg); reveal(xstep);
    let task = ActionShape::Append(id@, r@);
    lemma_nf_sum_stable(e, g, id@);
    norm::regex_constants(g);
    let s = model::lift_regex(g, r@);
    assert forall|v: R| #[trigger] tcls(g, id@, v) implies (av_app(av_of(g, id@), s).x)(v) by {
        lemma_cls_nf(g, id@, v);
        lemma_cat_eps(v);
        assert(v == cat_r(v, s));
    }
    lemma_effect_value(e, g, task, p0, v0, id);
}

pub proof fn lemma_append_empty(e: model::Graph, g: model::Graph, p0: Seq<ActionShape>, v0: Seq<TransitionId>,
    id: TransitionId, r: RegexId, out: TransitionId)
    requires xctx(e, g, ActionShape::Append(id@, r@), p0, v0), out@ == g.constants.transition_empty,
    ensures xeffect(g, ActionShape::Append(id@, r@), p0, v0, p0, v0.push(out)),
{
    reveal(xpre); reveal(xeffect); reveal(xrun); reveal(xcfg); reveal(xstep);
    lemma_push_const(e, g, ActionShape::Append(id@, r@), p0, v0, out);
}

pub proof fn lemma_append_const(e: model::Graph, g1: model::Graph, g: model::Graph, p0: Seq<ActionShape>, v0: Seq<TransitionId>,
    id: TransitionId, r: RegexId, head: RegexId, out_r: RegexId, out: TransitionId)
    requires xctx(e, g, ActionShape::Append(id@, r@), p0, v0), model::graph_wf(g1), model::graph_extends(e, g1), model::graph_extends(g1, g),
        e.transitions[id@ as int] == model::TransitionNode::Const(head@),
        out_r@ < g1.regexes.len(), norm::regex_concat_result(e, g1, seq![head, r], out_r@),
        out@ < g.transitions.len(), g.transitions[out@ as int] == model::TransitionNode::Const(out_r@),
    ensures xeffect(g, ActionShape::Append(id@, r@), p0, v0, p0, v0.push(out)),
{
    reveal(xpre); reveal(xeffect); reveal(xrun); reveal(xcfg); reveal(xstep);
    let task = ActionShape::Append(id@, r@);
    lemma_xpre_stable(e, g, task, p0, v0);
    lemma_nf_sum_stable(e, g, id@);
    lemma_nf_children(e, id@);
    let hs = seq![head, r];
    assert(norm::regex_ids_valid(e, hs)) by {
        assert forall|i: int| 0 <= i < hs.len() implies hs[i]@ < e.regexes.len() by {}
    }
    lemma_concat_link(e, g1, hs, out_r@);
    lemma_regex_nf_stable(e, g, head@);
    lemma_regex_nf_stable(e, g, r@);
    lemma_regex_nf_stable(g1, g, out_r@);
    let x = model::lift_regex(g, head@);
    let s = model::lift_regex(g, r@);
    assert(lifts(e, hs) =~= seq![x, s]);
    assert(seq![x, s] =~= seq![x] + seq![s]);
    lemma_rnf_seq2(seq![x, s]);
    lemma_cat_nf(seq![x, s]);
    lemma_const_cls(g, id@, head@);
    lemma_const_cls(g, out@, out_r@);
    assert((av_of(g, id@).x)(x));
    assert(app_of(av_of(g, id@), s, cat_r(x, s)));
    lemma_nf_weaken(g, out@);
    lemma_effect_value(e, g, task, p0, v0, out);
}

pub proof fn lemma_append_nested(e: model::Graph, g: model::Graph, p0: Seq<ActionShape>, v0: Seq<TransitionId>,
    id: TransitionId, r: RegexId, inner: TransitionId, children: Seq<RegexId>, combined: RegexId)
    requires xctx(e, g, ActionShape::Append(id@, r@), p0, v0),
        e.transitions[id@ as int] == model::TransitionNode::Append(inner@, model::regex_ids(children)),
        norm::regex_ids_valid(e, children), combined@ < g.regexes.len(),
        norm::regex_concat_result(e, g, children.push(r), combined@),
    ensures xeffect(g, ActionShape::Append(id@, r@), p0, v0, p0.push(ActionShape::Append(inner@, combined@)), v0),
{
    reveal(xpre); reveal(xeffect); reveal(xrun); reveal(xcfg); reveal(xstep);
    let task = ActionShape::Append(id@, r@);
    lemma_xpre_stable(e, g, task, p0, v0);
    lemma_nf_sum_stable(e, g, id@);
    lemma_nf_children(g, id@);
    let rs = model::regex_ids(children);
    lemma_append_cls(g, id@, inner@, rs);
    let cr = children.push(r);
    assert(norm::regex_ids_valid(e, cr)) by {
        assert forall|i: int| 0 <= i < cr.len() implies cr[i]@ < e.regexes.len() by {
            if i < children.len() { assert(cr[i] == children[i]); }
        }
    }
    lemma_concat_link(e, g, cr, combined@);
    lemma_lifts_ids(e, g, children);
    lemma_regex_nf_stable(e, g, r@);
    let ys = model::lift_regexes(g, rs);
    let z = model::lift_regex(g, r@);
    assert(lifts(e, cr) =~= ys.push(z));
    assert(all_rnf(ys)) by { assert forall|i: int| 0 <= i < ys.len() implies regex_nf(#[trigger] ys[i]) by {} }
    assert(all_rnf(ys.push(z))) by {
        assert forall|i: int| 0 <= i < ys.push(z).len() implies regex_nf(#[trigger] ys.push(z)[i]) by {
            if i < ys.len() { assert(ys.push(z)[i] == ys[i]); }
        }
    }
    lemma_cat_nf(ys.push(z));
    let lc = model::lift_regex(g, combined@);
    let t = ActionShape::Append(inner@, combined@);
    assert forall|v: R| #[trigger] (push_av(g, t).x)(v) implies (av_app(av_of(g, id@), z).x)(v) by {
        if app_of(av_of(g, inner@), lc, v) {
            let w = choose|w: R| (av_of(g, inner@).x)(w) && v == #[trigger] cat_r(w, lc);
            lemma_cls_nf(g, inner@, w);
            lemma_cat_shift(w, ys, z);
            let w2 = ccat(g, w, rs);
            assert(tcls(g, id@, w2));
            assert(v == cat_r(w2, z));
        }
    }
    lemma_replace_effect(e, g, task, p0, v0, t);
}

pub proof fn lemma_append_raw(e: model::Graph, g: model::Graph, p0: Seq<ActionShape>, v0: Seq<TransitionId>,
    id: TransitionId, r: RegexId, xs: Seq<RegexId>, out: TransitionId)
    requires xctx(e, g, ActionShape::Append(id@, r@), p0, v0),
        e.transitions[id@ as int] is Intersect || e.transitions[id@ as int] is Not,
        xs == seq![r] || e.regexes[r@ as int].kind == model::RegexKindNode::Concat(model::regex_ids(xs)),
        norm::regex_ids_valid(e, xs),
        out@ < g.transitions.len(), g.transitions[out@ as int] == model::TransitionNode::Append(id@, model::regex_ids(xs)),
    ensures xeffect(g, ActionShape::Append(id@, r@), p0, v0, p0, v0.push(out)),
{
    reveal(xpre); reveal(xeffect); reveal(xrun); reveal(xcfg); reveal(xstep);
    let task = ActionShape::Append(id@, r@);
    lemma_xpre_stable(e, g, task, p0, v0);
    lemma_nf_sum_stable(e, g, id@);
    let rs = model::regex_ids(xs);
    let ls = model::lift_regexes(g, rs);
    let z = model::lift_regex(g, r@);
    lemma_lifts_ids(e, g, xs);
    lemma_regex_nf_stable(e, g, r@);
    if xs == seq![r] {
        assert(ls =~= seq![z]);
        assert(all_rnf(ls)) by { assert forall|i: int| 0 <= i < 1 implies regex_nf(#[trigger] ls[i]) by {} }
        assert forall|w: R| #[trigger] ccat(g, w, rs) == cat_r(w, z) by { assert(seq![w] + ls =~= seq![w, z]); }
    } else {
        lemma_regex_lift(e, r@);
        assert(model::lift_regexes(e, rs) =~= ls) by {
            assert forall|i: int| 0 <= i < rs.len() implies #[trigger] model::lift_regex(e, rs[i]) == model::lift_regex(g, rs[i]) by {
                assert(lifts(e, xs)[i] == model::lift_regex(e, xs[i]@));
            }
        }
        assert(z == Regex::<model::Test>::Concat(ls));
        lemma_cat_list(ls);
        assert forall|w: R| regex_nf(w) implies #[trigger] ccat(g, w, rs) == cat_r(w, z) by { lemma_cat_nest(w, ls); }
    }
    lemma_append_cls(g, out@, id@, rs);
    assert forall|v: R| #[trigger] tcls(g, out@, v) implies (av_app(av_of(g, id@), z).x)(v) by {
        if !rconst(v) {
            let w = choose|w: R| tcls(g, id@, w) && v == #[trigger] ccat(g, w, rs);
            lemma_cls_nf(g, id@, w);
            assert(v == cat_r(w, z));
        }
    }
    assert(nf_prod(g, id@));
    assert(nats_nf(g, rs)) by {
        assert forall|i: int| 0 <= i < rs.len() implies regex_nf(#[trigger] model::lift_regex(g, rs[i])) by { assert(ls[i] == model::lift_regex(g, rs[i])); }
    }
    assert(model::bounded(rs, g.regexes.len())) by {
        assert forall|i: int| 0 <= i < rs.len() implies #[trigger] rs[i] < g.regexes.len() by {}
    }
    assert(nf_lit(g, out@));
    lemma_nf_weaken(g, out@);
    lemma_effect_value(e, g, task, p0, v0, out);
}

// ===== pair_step =====

pub proof fn lemma_pair_keep(e: model::Graph, g: model::Graph, p0: Seq<ActionShape>, v0: Seq<TransitionId>,
    a: TransitionId, b: TransitionId, out: TransitionId)
    requires xctx(e, g, ActionShape::Pair(a@, b@), p0, v0),
        out@ == a@ || out@ == b@ || out@ == g.constants.transition_empty,
    ensures xeffect(g, ActionShape::Pair(a@, b@), p0, v0, p0, v0.push(out)),
{
    reveal(xpre); reveal(xeffect); reveal(xrun); reveal(xcfg); reveal(xstep);
    let task = ActionShape::Pair(a@, b@);
    lemma_nf_sum_stable(e, g, a@);
    lemma_nf_sum_stable(e, g, b@);
    lemma_const_transitions(g);
    if out@ == a@ || out@ == b@ {
        lemma_pair_base(g, a@, b@, out@);
        lemma_effect_value(e, g, task, p0, v0, out);
    } else {
        assert forall|v: R| rconst(v) implies #[trigger] (push_av(g, task).x)(v) by { lemma_meet_pair_const(g, a@, b@, v); }
        lemma_push_const(e, g, task, p0, v0, out);
    }
}

pub proof fn lemma_pair_const(e: model::Graph, g1: model::Graph, g: model::Graph, p0: Seq<ActionShape>, v0: Seq<TransitionId>,
    a: TransitionId, b: TransitionId, x: RegexId, y: RegexId, r: RegexId, out: TransitionId)
    requires xctx(e, g, ActionShape::Pair(a@, b@), p0, v0), model::graph_wf(g1), model::graph_extends(e, g1), model::graph_extends(g1, g),
        e.transitions[a@ as int] == model::TransitionNode::Const(x@), e.transitions[b@ as int] == model::TransitionNode::Const(y@),
        r@ < g1.regexes.len(),
        norm::regex_set_flat_inputs(e, seq![x, y], true) ==> norm::regex_set_shape(e, g1, seq![x, y], true, r@),
        out@ < g.transitions.len(), g.transitions[out@ as int] == model::TransitionNode::Const(r@),
    ensures xeffect(g, ActionShape::Pair(a@, b@), p0, v0, p0, v0.push(out)),
{
    reveal(xpre); reveal(xeffect); reveal(xrun); reveal(xcfg); reveal(xstep);
    let task = ActionShape::Pair(a@, b@);
    lemma_nf_sum_stable(e, g, a@);
    lemma_nf_sum_stable(e, g, b@);
    lemma_nf_children(e, a@);
    lemma_nf_children(e, b@);
    let xy = seq![x, y];
    assert(norm::regex_ids_valid(e, xy)) by { assert forall|i: int| 0 <= i < xy.len() implies xy[i]@ < e.regexes.len() by {} }
    assert(ids_nf(e, xy)) by {
        assert forall|i: int| 0 <= i < xy.len() implies regex_nf(#[trigger] model::lift_regex(e, xy[i]@)) by {}
    }
    lemma_flat_inputs(e, xy, true);
    lemma_set_link(e, g1, xy, true, r@);
    lemma_regex_nf_stable(g1, g, r@);
    lemma_regex_nf_stable(e, g, x@);
    lemma_regex_nf_stable(e, g, y@);
    lemma_const_cls(g, a@, x@);
    lemma_const_cls(g, b@, y@);
    lemma_const_cls(g, out@, r@);
    let s = seq![av_of(g, a@), av_of(g, b@)];
    let base = |w: R| any_x(s, w);
    assert forall|z: R| lift_set(e, xy).contains(z) implies cl(true, base, z) by {
        broadcast use vstd::prelude::Seq::to_set_ensures;
        let k = choose|k: int| 0 <= k < lifts(e, xy).len() && lifts(e, xy)[k] == z;
        if k == 0 { assert(s[0].x == av_of(g, a@).x); assert((s[0].x)(z)); }
        else { assert(s[1].x == av_of(g, b@).x); assert((s[1].x)(z)); }
        lemma_cl_base(true, base, z);
    }
    lemma_cl_nset(true, base, lift_set(e, xy), model::lift_regex(g1, r@));
    assert forall|v: R| #[trigger] tcls(g, out@, v) implies cl(true, base, v) by {
        if rconst(v) { lemma_cl_const(true, base, v); }
    }
    lemma_nf_weaken(g, out@);
    lemma_effect_value(e, g, task, p0, v0, out);
}

pub proof fn lemma_pair_union(e: model::Graph, g: model::Graph, p0: Seq<ActionShape>, v0: Seq<TransitionId>,
    a: TransitionId, b: TransitionId, left: bool)
    requires xctx(e, g, ActionShape::Pair(a@, b@), p0, v0),
        left ==> e.transitions[a@ as int] is Union, !left ==> e.transitions[b@ as int] is Union,
    ensures xeffect(g, ActionShape::Pair(a@, b@), p0, v0,
        p0.push(ActionShape::Union(norm::transition_children(g, if left { a@ } else { b@ }).len()))
            + norm::transition_child_actions(g, if left { a@ } else { b@ }, if left { ChildShape::PairLeft(b@) } else { ChildShape::PairRight(a@) }),
        v0),
{
    reveal(xpre); reveal(xeffect); reveal(xrun); reveal(xcfg); reveal(xstep);
    let task = ActionShape::Pair(a@, b@);
    let id = if left { a@ } else { b@ };
    let f = if left { ChildShape::PairLeft(b@) } else { ChildShape::PairRight(a@) };
    lemma_xpre_stable(e, g, task, p0, v0);
    lemma_nf_sum_stable(e, g, a@);
    lemma_nf_sum_stable(e, g, b@);
    lemma_nf_children(g, id);
    norm::transition_lemma_children(g, id);
    let cs = norm::transition_children(g, id);
    match g.transitions[id as int] { model::TransitionNode::Union(ds) => { lemma_union_cls(g, id, ds); }, _ => {} }
    let xs = child_avs(g, cs, f);
    let t = push_av(g, task);
    assert forall|i: int| 0 <= i < xs.len() implies #[trigger] av_le(xs[i], t) by {
        assert(xs[i] == push_av(g, norm::transition_child_shape(f, cs[i])));
        assert(av_le(av_of(g, cs[i]), av_of(g, id)));
        lemma_av_le_cls(g, cs[i], id);
        if left { lemma_meet_pair_le(g, cs[i], b@, a@, b@); } else { lemma_meet_pair_le(g, a@, cs[i], a@, b@); }
    }
    assert forall|v: R| rconst(v) implies #[trigger] (t.x)(v) by { lemma_meet_pair_const(g, a@, b@, v); }
    lemma_union_le(xs, t);
    lemma_child_effect(e, g, task, p0, v0, id, f, false, av_union(xs));
}

/// A pair split on a test: pairs `(l1, r1)` and `(l2, r2)` of members below `a` and `b`.
pub proof fn lemma_pair_ifs(e: model::Graph, g: model::Graph, p0: Seq<ActionShape>, v0: Seq<TransitionId>,
    a: nat, b: nat, test: nat, l1: nat, r1: nat, l2: nat, r2: nat)
    requires xctx(e, g, ActionShape::Pair(a, b), p0, v0),
        nf_sum(g, l1), nf_sum(g, r1), nf_sum(g, l2), nf_sum(g, r2),
        forall|v: R| #[trigger] tcls(g, l1, v) ==> tcls(g, a, v), forall|v: R| #[trigger] tcls(g, l2, v) ==> tcls(g, a, v),
        forall|v: R| #[trigger] tcls(g, r1, v) ==> tcls(g, b, v), forall|v: R| #[trigger] tcls(g, r2, v) ==> tcls(g, b, v),
    ensures xeffect(g, ActionShape::Pair(a, b), p0, v0,
        p0.push(ActionShape::CleanIf(test, g.constants.test_true)).push(ActionShape::Pair(l2, r2)).push(ActionShape::Pair(l1, r1)), v0),
{
    reveal(xpre); reveal(xeffect); reveal(xrun); reveal(xcfg); reveal(xstep);
    let task = ActionShape::Pair(a, b);
    lemma_meet_pair_le(g, l1, r1, a, b);
    lemma_meet_pair_le(g, l2, r2, a, b);
    lemma_cond_effect(e, g, task, p0, v0, ActionShape::CleanIf(test, g.constants.test_true),
        ActionShape::Pair(l2, r2), ActionShape::Pair(l1, r1));
}

pub proof fn lemma_pair_split(e: model::Graph, g: model::Graph, p0: Seq<ActionShape>, v0: Seq<TransitionId>,
    a: TransitionId, b: TransitionId, test: TestId, t: TransitionId, el: TransitionId, left: bool)
    requires xctx(e, g, ActionShape::Pair(a@, b@), p0, v0),
        e.transitions[(if left { a@ } else { b@ }) as int] == model::TransitionNode::If(test@, t@, el@),
    ensures xeffect(g, ActionShape::Pair(a@, b@), p0, v0,
        p0.push(ActionShape::CleanIf(test@, g.constants.test_true))
            .push(if left { ActionShape::Pair(el@, b@) } else { ActionShape::Pair(a@, el@) })
            .push(if left { ActionShape::Pair(t@, b@) } else { ActionShape::Pair(a@, t@) }), v0),
{
    reveal(xpre); reveal(xeffect); reveal(xrun); reveal(xcfg); reveal(xstep);
    let id = if left { a@ } else { b@ };
    lemma_nf_sum_stable(e, g, a@);
    lemma_nf_sum_stable(e, g, b@);
    lemma_if_cls(g, id, test@, t@, el@);
    lemma_nf_children(g, id);
    lemma_av_le_cls(g, t@, id);
    lemma_av_le_cls(g, el@, id);
    if left {
        lemma_pair_ifs(e, g, p0, v0, a@, b@, test@, t@, b@, el@, b@);
    } else {
        lemma_pair_ifs(e, g, p0, v0, a@, b@, test@, a@, t@, a@, el@);
    }
}

pub proof fn lemma_pair_both(e: model::Graph, g: model::Graph, p0: Seq<ActionShape>, v0: Seq<TransitionId>,
    a: TransitionId, b: TransitionId, x: TestId, xt: TransitionId, xe: TransitionId, y: TestId, yt: TransitionId, ye: TransitionId)
    requires xctx(e, g, ActionShape::Pair(a@, b@), p0, v0),
        e.transitions[a@ as int] == model::TransitionNode::If(x@, xt@, xe@),
        e.transitions[b@ as int] == model::TransitionNode::If(y@, yt@, ye@),
    ensures xeffect(g, ActionShape::Pair(a@, b@), p0, v0,
        p0.push(ActionShape::CleanIf(x@, g.constants.test_true)).push(ActionShape::Pair(xe@, ye@)).push(ActionShape::Pair(xt@, yt@)), v0),
{
    reveal(xpre); reveal(xeffect); reveal(xrun); reveal(xcfg); reveal(xstep);
    lemma_nf_sum_stable(e, g, a@);
    lemma_nf_sum_stable(e, g, b@);
    lemma_if_cls(g, a@, x@, xt@, xe@);
    lemma_if_cls(g, b@, y@, yt@, ye@);
    lemma_nf_children(g, a@);
    lemma_nf_children(g, b@);
    lemma_av_le_cls(g, xt@, a@);
    lemma_av_le_cls(g, xe@, a@);
    lemma_av_le_cls(g, yt@, b@);
    lemma_av_le_cls(g, ye@, b@);
    lemma_pair_ifs(e, g, p0, v0, a@, b@, x@, xt@, yt@, xe@, ye@);
}

pub proof fn lemma_pair_empty_branches(e: model::Graph, g: model::Graph, p0: Seq<ActionShape>, v0: Seq<TransitionId>,
    a: TransitionId, b: TransitionId, x: TestId, xt: TransitionId, y: TestId, yt: TransitionId, guard: TestId, emp: TransitionId)
    requires xctx(e, g, ActionShape::Pair(a@, b@), p0, v0),
        e.transitions[a@ as int] == model::TransitionNode::If(x@, xt@, emp@),
        e.transitions[b@ as int] == model::TransitionNode::If(y@, yt@, emp@),
        emp@ == e.constants.transition_empty,
    ensures xeffect(g, ActionShape::Pair(a@, b@), p0, v0,
        p0.push(ActionShape::CleanIf(guard@, g.constants.test_true)).push(ActionShape::SwapThen).push(ActionShape::Pair(xt@, yt@)),
        v0.push(emp)),
{
    reveal(xpre); reveal(xeffect); reveal(xrun); reveal(xcfg); reveal(xstep);
    let task = ActionShape::Pair(a@, b@);
    lemma_xpre_stable(e, g, task, p0, v0);
    lemma_nf_sum_stable(e, g, a@);
    lemma_nf_sum_stable(e, g, b@);
    lemma_if_cls(g, a@, x@, xt@, emp@);
    lemma_if_cls(g, b@, y@, yt@, emp@);
    lemma_nf_children(g, a@);
    lemma_nf_children(g, b@);
    lemma_const_transitions(g);
    lemma_av_le_cls(g, xt@, a@);
    lemma_av_le_cls(g, yt@, b@);
    let m = av_meet(seq![av_of(g, xt@), av_of(g, yt@)]);
    let ev = av_of(g, emp@);
    let tp = push_av(g, task);
    lemma_meet_pair_le(g, xt@, yt@, a@, b@);
    assert forall|v: R| #[trigger] (ev.x)(v) implies (tp.x)(v) by { lemma_meet_pair_const(g, a@, b@, v); }
    let yv = av_if(m, ev);
    let s = vavs(g, v0);
    let s1 = s.push(ev);
    lemma_vavs_push(g, v0, emp);
    let tc0 = ActionShape::CleanIf(guard@, g.constants.test_true);
    let tpair = ActionShape::Pair(xt@, yt@);
    let exp = seq![tc0, ActionShape::SwapThen, tpair];
    assert(exp =~= seq![tc0, ActionShape::SwapThen].push(tpair));
    assert(seq![tc0, ActionShape::SwapThen] =~= seq![tc0].push(ActionShape::SwapThen));
    lemma_arun_push(g, seq![tc0, ActionShape::SwapThen], tpair, s1);
    let s2 = s1.push(m);
    lemma_arun_push(g, seq![tc0], ActionShape::SwapThen, s2);
    let s3 = s.push(m).push(ev);
    assert(s2.take(s2.len() as int - 2).push(s2.last()).push(s2[s2.len() as int - 2]) =~= s3);
    lemma_arun_one(g, tc0, s3);
    assert(s3.take(s3.len() as int - 2) =~= s);
    assert(s3[s3.len() as int - 2] == m);
    lemma_xnf3(g, tc0, ActionShape::SwapThen, tpair);
    lemma_xnf_values_push(g, v0, emp);
    lemma_effect(e, g, task, p0, v0, exp, v0.push(emp), yv);
    assert(p0 + exp =~= p0.push(tc0).push(ActionShape::SwapThen).push(tpair));
}

pub proof fn lemma_pair_collect(e: model::Graph, g: model::Graph, p0: Seq<ActionShape>, v0: Seq<TransitionId>,
    a: TransitionId, b: TransitionId, out: TransitionId)
    requires xctx(e, g, ActionShape::Pair(a@, b@), p0, v0),
        !(e.transitions[a@ as int] is If) && !(e.transitions[a@ as int] is Union),
        !(e.transitions[b@ as int] is If) && !(e.transitions[b@ as int] is Union),
        all_nf(e, model::transition_ids(seq![a, b])) ==> collect_out(g, model::transition_ids(seq![a, b]), true, out@),
    ensures xeffect(g, ActionShape::Pair(a@, b@), p0, v0, p0, v0.push(out)),
{
    reveal(xpre); reveal(xeffect); reveal(xrun); reveal(xcfg); reveal(xstep);
    let task = ActionShape::Pair(a@, b@);
    let ts = model::transition_ids(seq![a, b]);
    assert(ts =~= seq![a@, b@]);
    assert(all_nf(e, ts)) by { assert forall|k: int| 0 <= k < ts.len() implies nf_sum(e, #[trigger] ts[k]) by {} }
    lemma_nf_sum_stable(e, g, a@);
    lemma_nf_sum_stable(e, g, b@);
    let cs = seq![a@, b@];
    assert(avs(g, cs) =~= seq![av_of(g, a@), av_of(g, b@)]);
    assert(nf_prod(g, a@));
    assert(nf_prod(g, b@));
    assert(all_prod(g, cs)) by { assert forall|k: int| 0 <= k < cs.len() implies nf_prod(g, #[trigger] cs[k]) by {} }
    assert(nf_prod(g, out@));
    lemma_nf_weaken(g, out@);
    assert forall|v: R| #[trigger] tcls(g, out@, v) implies (push_av(g, task).x)(v) by { assert(cbound(g, cs, true, v)); }
    lemma_effect_value(e, g, task, p0, v0, out);
}

// ===== fold_step =====

pub proof fn lemma_effect_raw(e: model::Graph, g: model::Graph, task: ActionShape, p0: Seq<ActionShape>, v0: Seq<TransitionId>,
    exp: Seq<ActionShape>, v1: Seq<TransitionId>)
    requires xctx(e, g, task, p0, v0), xnf_tasks(g, exp), xnf_values(g, v1),
        aref(aapply(g, task, vavs(g, v0)), arun(g, exp, vavs(g, v1))),
    ensures xeffect(g, task, p0, v0, p0 + exp, v1),
{
    reveal(xpre); reveal(xeffect); reveal(xrun); reveal(xcfg); reveal(xstep);
    lemma_xpre_stable(e, g, task, p0, v0);
    lemma_xnf_tasks_append(g, p0, exp);
    assert((p0 + exp).subrange(p0.len() as int, (p0 + exp).len() as int) =~= exp);
    assert(p0.is_prefix_of(p0 + exp)) by { assert((p0 + exp).subrange(0, p0.len() as int) =~= p0); }
}

pub proof fn lemma_fold_start(e: model::Graph, g: model::Graph, p0: Seq<ActionShape>, v0: Seq<TransitionId>,
    terms: Seq<nat>, flat: TransitionId, cs: Seq<TransitionId>)
    requires xctx(e, g, ActionShape::Fold(terms, 0), p0, v0), all_nf(e, terms) ==> collect_out(g, terms, true, flat@),
        g.transitions[flat@ as int] == model::TransitionNode::Intersect(model::transition_ids(cs)), cs.len() > 0,
    ensures xeffect(g, ActionShape::Fold(terms, 0), p0, v0,
        p0.push(ActionShape::Fold(model::transition_ids(cs), 1)), v0.push(cs[0])),
{
    reveal(xpre); reveal(xeffect); reveal(xrun); reveal(xcfg); reveal(xstep);
    let task = ActionShape::Fold(terms, 0);
    lemma_xpre_stable(e, g, task, p0, v0);
    let ds = model::transition_ids(cs);
    assert(ds[0] == cs[0]@);
    let base = |w: R| any_x(avs(g, terms), w);
    assert(g.transitions[flat@ as int] == model::TransitionNode::Intersect(ds));
    let ds2 = g.transitions[flat@ as int]->Intersect_0;
    assert(ds2 == ds);
    assert(forall|j: int| 0 <= j < ds2.len() ==> #[trigger] elem_ok(g, terms, true, ds2[j]));
    assert forall|j: int| 0 <= j < ds.len() implies #[trigger] elem_ok(g, terms, true, ds[j]) by { assert(ds2[j] == ds[j]); }
    assert forall|j: int, w: R| 0 <= j < avs(g, ds).len() && #[trigger] (avs(g, ds)[j].x)(w) implies cl(true, base, w) by {
        assert(elem_ok(g, terms, true, ds[j]));
        assert(tcls(g, ds[j], w));
    }
    assert(all_nf(g, ds)) by {
        assert forall|k: int| 0 <= k < ds.len() implies nf_sum(g, #[trigger] ds[k]) by { assert(elem_ok(g, terms, true, ds[k])); }
    }
    assert(elem_ok(g, terms, true, ds[0]));
    let s = vavs(g, v0);
    lemma_vavs_push(g, v0, cs[0]);
    let s1 = s.push(av_of(g, ds[0]));
    let t = ActionShape::Fold(ds, 1);
    lemma_arun_one(g, t, s1);
    let tp = push_av(g, task);
    let y = if 1 < ds.len() { av_meet(avs(g, ds)) } else { av_of(g, ds[0]) };
    if 1 < ds.len() {
        assert(seq![s1.last()] + avs(g, ds.subrange(1, ds.len() as int)) =~= avs(g, ds));
        assert(s1.drop_last() =~= s);
        lemma_meet_le_cl(avs(g, ds), base);
    } else {
        assert forall|w: R| #[trigger] tcls(g, ds[0], w) implies (tp.x)(w) by {}
    }
    assert(arun(g, seq![t], vavs(g, v0.push(cs[0]))) == Some(s.push(y)));
    lemma_aref_push(s, tp, y);
    lemma_aapply_push(g, task, s);
    lemma_xnf1(g, t);
    lemma_xnf_values_push(g, v0, cs[0]);
    lemma_effect_raw(e, g, task, p0, v0, seq![t], v0.push(cs[0]));
    assert(p0 + seq![t] =~= p0.push(t));
}

pub proof fn lemma_fold_flat(e: model::Graph, g: model::Graph, p0: Seq<ActionShape>, v0: Seq<TransitionId>,
    terms: Seq<nat>, flat: TransitionId)
    requires xctx(e, g, ActionShape::Fold(terms, 0), p0, v0), all_nf(e, terms) ==> collect_out(g, terms, true, flat@),
        !(g.transitions[flat@ as int] is Intersect),
    ensures xeffect(g, ActionShape::Fold(terms, 0), p0, v0, p0, v0.push(flat)),
{
    reveal(xpre); reveal(xeffect); reveal(xrun); reveal(xcfg); reveal(xstep);
    let task = ActionShape::Fold(terms, 0);
    assert(nf_sum(g, flat@));
    assert forall|v: R| #[trigger] tcls(g, flat@, v) implies (push_av(g, task).x)(v) by { assert(cbound(g, terms, true, v)); }
    lemma_effect_value(e, g, task, p0, v0, flat);
}

pub proof fn lemma_fold_next(e: model::Graph, g: model::Graph, p0: Seq<ActionShape>, v0: Seq<TransitionId>,
    terms: Seq<nat>, index: nat, a: TransitionId, b: TransitionId)
    requires xctx(e, g, ActionShape::Fold(terms, index), p0, v0), 0 < index < terms.len(),
        v0.len() > 0, a == v0.last(), b@ == terms[index as int],
    ensures xeffect(g, ActionShape::Fold(terms, index), p0, v0,
        p0.push(ActionShape::Fold(terms, index + 1)).push(ActionShape::Pair(a@, b@)), v0.drop_last()),
{
    reveal(xpre); reveal(xeffect); reveal(xrun); reveal(xcfg); reveal(xstep);
    let task = ActionShape::Fold(terms, index);
    lemma_xpre_stable(e, g, task, p0, v0);
    let s = vavs(g, v0);
    let n = v0.len() as int;
    lemma_vavs_take(g, v0, n - 1);
    assert(v0.drop_last() == v0.take(n - 1));
    lemma_vavs_index(g, v0, n - 1);
    let s0 = vavs(g, v0.drop_last());
    assert(s0 =~= s.drop_last());
    assert(s.last() == av_of(g, a@));
    let rest = avs(g, terms.subrange(index as int, terms.len() as int));
    let tl = seq![s.last()] + rest;
    let tgt = av_meet(tl);
    let base = |w: R| any_x(tl, w);
    assert(rest[0] == av_of(g, b@));
    assert(tl[0] == av_of(g, a@));
    assert(tl[1] == av_of(g, b@));
    let mab = av_meet(seq![av_of(g, a@), av_of(g, b@)]);
    // `mab` is below the target
    lemma_any_x_pair(seq![av_of(g, a@), av_of(g, b@)], tl);
    assert forall|w: R| #[trigger] (mab.x)(w) implies cl(true, base, w) by {
        lemma_cl_mono(true, |u: R| any_x(seq![av_of(g, a@), av_of(g, b@)], u), base, w);
    }
    let tpair = ActionShape::Pair(a@, b@);
    let tfold = ActionShape::Fold(terms, index + 1);
    let exp = seq![tfold, tpair];
    assert(exp =~= seq![tfold].push(tpair));
    lemma_arun_push(g, seq![tfold], tpair, s0);
    lemma_aapply_push(g, tpair, s0);
    let s1 = s0.push(mab);
    lemma_arun_one(g, tfold, s1);
    let y = if index + 1 < terms.len() {
        av_meet(seq![mab] + avs(g, terms.subrange((index + 1) as int, terms.len() as int)))
    } else { mab };
    if index + 1 < terms.len() {
        assert(s1.drop_last() =~= s0);
        let rest2 = avs(g, terms.subrange((index + 1) as int, terms.len() as int));
        let l2 = seq![mab] + rest2;
        assert forall|j: int, w: R| 0 <= j < l2.len() && #[trigger] (l2[j].x)(w) implies cl(true, base, w) by {
            if j == 0 { assert(l2[0] == mab); } else {
                assert(l2[j] == rest2[j - 1]);
                assert(rest2[j - 1] == tl[j + 1]);
                assert(base(w));
                lemma_cl_base(true, base, w);
            }
        }
        lemma_meet_le_cl(l2, base);
    }
    assert(av_le(y, tgt));
    assert(aapply(g, task, s) == Some(s.drop_last().push(tgt)));
    lemma_aref_push(s0, tgt, y);
    lemma_vavs_take(g, v0, n - 1);
    lemma_xnf_values_sub(g, v0, 0, n - 1);
    assert(xnf_values(g, v0.drop_last()));
    assert(nf_sum(g, a@)) by { assert(v0[n - 1] == a); }
    lemma_xnf2(g, tfold, tpair);
    lemma_effect_raw(e, g, task, p0, v0, exp, v0.drop_last());
    assert(p0 + exp =~= p0.push(tfold).push(tpair));
}

pub proof fn lemma_fold_noop(e: model::Graph, g: model::Graph, p0: Seq<ActionShape>, v0: Seq<TransitionId>,
    terms: Seq<nat>, index: nat)
    requires xctx(e, g, ActionShape::Fold(terms, index), p0, v0), index != 0, index >= terms.len(),
    ensures xeffect(g, ActionShape::Fold(terms, index), p0, v0, p0, v0),
{
    reveal(xpre); reveal(xeffect); reveal(xrun); reveal(xcfg); reveal(xstep);
    let task = ActionShape::Fold(terms, index);
    lemma_xpre_stable(e, g, task, p0, v0);
    lemma_aref_refl(vavs(g, v0));
    assert(xnf_tasks(g, Seq::<ActionShape>::empty()));
    lemma_effect_raw(e, g, task, p0, v0, Seq::empty(), v0);
    assert(p0 + Seq::<ActionShape>::empty() =~= p0);
}

// ===== step =====

pub proof fn lemma_step_union(e: model::Graph, g: model::Graph, p0: Seq<ActionShape>, v0: Seq<TransitionId>, n: nat, out: TransitionId)
    requires xctx(e, g, ActionShape::Union(n), p0, v0), n <= v0.len(),
        all_nf(e, model::transition_ids(v0.subrange(v0.len() - n, v0.len() as int)))
            ==> collect_out(g, model::transition_ids(v0.subrange(v0.len() - n, v0.len() as int)), false, out@),
    ensures xeffect(g, ActionShape::Union(n), p0, v0, p0, v0.take(v0.len() - n).push(out)),
{
    reveal(xpre); reveal(xeffect); reveal(xrun); reveal(xcfg); reveal(xstep);
    let task = ActionShape::Union(n);
    lemma_xpre_stable(e, g, task, p0, v0);
    let start = v0.len() - n;
    lemma_xnf_values_sub(e, v0, start, v0.len() as int);
    let s = vavs(g, v0);
    lemma_vavs_sub(g, v0, start, v0.len() as int);
    lemma_vavs_take(g, v0, start);
    let cs = model::transition_ids(v0.subrange(start, v0.len() as int));
    let y = av_union(avs(g, cs));
    assert(av_le(av_of(g, out@), y)) by {
        assert forall|v: R| #[trigger] tcls(g, out@, v) implies (y.x)(v) by { assert(cbound(g, cs, false, v)); }
    }
    let v1 = v0.take(start).push(out);
    lemma_vavs_push(g, v0.take(start), out);
    lemma_aref_push(s.take(start), y, av_of(g, out@));
    lemma_xnf_values_sub(g, v0, 0, start);
    lemma_xnf_values_push(g, v0.take(start), out);
    assert(xnf_tasks(g, Seq::<ActionShape>::empty()));
    lemma_effect_raw(e, g, task, p0, v0, Seq::empty(), v1);
    assert(p0 + Seq::<ActionShape>::empty() =~= p0);
}

pub proof fn lemma_step_intersect(e: model::Graph, g: model::Graph, p0: Seq<ActionShape>, v0: Seq<TransitionId>, n: nat)
    requires xctx(e, g, ActionShape::Intersect(n), p0, v0), n <= v0.len(),
    ensures xeffect(g, ActionShape::Intersect(n), p0, v0,
        p0.push(ActionShape::Fold(model::transition_ids(v0.subrange(v0.len() - n, v0.len() as int)), 0)), v0.take(v0.len() - n)),
{
    reveal(xpre); reveal(xeffect); reveal(xrun); reveal(xcfg); reveal(xstep);
    let task = ActionShape::Intersect(n);
    lemma_xpre_stable(e, g, task, p0, v0);
    let start = v0.len() - n;
    let s = vavs(g, v0);
    lemma_vavs_sub(g, v0, start, v0.len() as int);
    lemma_vavs_take(g, v0, start);
    let cs = model::transition_ids(v0.subrange(start, v0.len() as int));
    let t = ActionShape::Fold(cs, 0);
    lemma_arun_one(g, t, s.take(start));
    lemma_aref_refl(s.take(start).push(av_meet(avs(g, cs))));
    lemma_xnf_values_sub(g, v0, start, v0.len() as int);
    lemma_xnf_values_sub(g, v0, 0, start);
    lemma_xnf1(g, t);
    lemma_effect_raw(e, g, task, p0, v0, seq![t], v0.take(start));
    assert(p0 + seq![t] =~= p0.push(t));
}

pub proof fn lemma_step_if(e: model::Graph, g: model::Graph, p0: Seq<ActionShape>, v0: Seq<TransitionId>, test: nat, out: TransitionId)
    requires xctx(e, g, ActionShape::If(test), p0, v0), v0.len() >= 2,
        out@ == v0[v0.len() - 2]@ || out@ == v0.last()@
            || (out@ < g.transitions.len() && g.transitions[out@ as int] == model::TransitionNode::If(test, v0[v0.len() - 2]@, v0.last()@)),
    ensures xeffect(g, ActionShape::If(test), p0, v0, p0, v0.take(v0.len() - 2).push(out)),
{
    reveal(xpre); reveal(xeffect); reveal(xrun); reveal(xcfg); reveal(xstep);
    let task = ActionShape::If(test);
    lemma_xpre_stable(e, g, task, p0, v0);
    let n = v0.len() as int;
    let a = v0[n - 2];
    let b = v0[n - 1];
    lemma_values_stable(e, g, v0);
    lemma_local_if(g, test, a@, b@, out@);
    let s = vavs(g, v0);
    lemma_vavs_index(g, v0, n - 2);
    lemma_vavs_index(g, v0, n - 1);
    lemma_vavs_take(g, v0, n - 2);
    lemma_vavs_push(g, v0.take(n - 2), out);
    lemma_aref_push(s.take(n - 2), av_if(av_of(g, a@), av_of(g, b@)), av_of(g, out@));
    lemma_xnf_values_sub(g, v0, 0, n - 2);
    lemma_xnf_values_push(g, v0.take(n - 2), out);
    assert(xnf_tasks(g, Seq::<ActionShape>::empty()));
    lemma_effect_raw(e, g, task, p0, v0, Seq::empty(), v0.take(n - 2).push(out));
    assert(p0 + Seq::<ActionShape>::empty() =~= p0);
}

pub proof fn lemma_step_clean_if(e: model::Graph, g: model::Graph, p0: Seq<ActionShape>, v0: Seq<TransitionId>,
    test: nat, path: nat, out: TransitionId)
    requires xctx(e, g, ActionShape::CleanIf(test, path), p0, v0), v0.len() >= 2,
        out@ == v0[v0.len() - 2]@ || out@ == v0.last()@
            || (out@ < g.transitions.len() && g.transitions[out@ as int] == model::TransitionNode::If(test, v0[v0.len() - 2]@, v0.last()@)),
    ensures xeffect(g, ActionShape::CleanIf(test, path), p0, v0, p0.push(ActionShape::Clean(out@, path)), v0.take(v0.len() - 2)),
{
    reveal(xpre); reveal(xeffect); reveal(xrun); reveal(xcfg); reveal(xstep);
    let task = ActionShape::CleanIf(test, path);
    lemma_xpre_stable(e, g, task, p0, v0);
    let n = v0.len() as int;
    let a = v0[n - 2];
    let b = v0[n - 1];
    lemma_values_stable(e, g, v0);
    lemma_local_if(g, test, a@, b@, out@);
    let s = vavs(g, v0);
    lemma_vavs_index(g, v0, n - 2);
    lemma_vavs_index(g, v0, n - 1);
    lemma_vavs_take(g, v0, n - 2);
    let t = ActionShape::Clean(out@, path);
    lemma_arun_one(g, t, s.take(n - 2));
    lemma_aref_push(s.take(n - 2), av_if(av_of(g, a@), av_of(g, b@)), av_of(g, out@));
    lemma_xnf_values_sub(g, v0, 0, n - 2);
    lemma_xnf1(g, t);
    lemma_effect_raw(e, g, task, p0, v0, seq![t], v0.take(n - 2));
    assert(p0 + seq![t] =~= p0.push(t));
}

/// `NotResult` and `AppendResult(r)`: the unary action on the last value.
pub proof fn lemma_step_result(e: model::Graph, g: model::Graph, p0: Seq<ActionShape>, v0: Seq<TransitionId>, suffix: Option<nat>)
    requires xctx(e, g, match suffix { Some(r) => ActionShape::AppendResult(r), None => ActionShape::NotResult }, p0, v0), v0.len() > 0,
    ensures xeffect(g, match suffix { Some(r) => ActionShape::AppendResult(r), None => ActionShape::NotResult }, p0, v0,
        p0.push(match suffix { Some(r) => ActionShape::Append(v0.last()@, r), None => ActionShape::Not(v0.last()@) }), v0.drop_last()),
{
    reveal(xpre); reveal(xeffect); reveal(xrun); reveal(xcfg); reveal(xstep);
    let task = match suffix { Some(r) => ActionShape::AppendResult(r), None => ActionShape::NotResult };
    lemma_xpre_stable(e, g, task, p0, v0);
    let n = v0.len() as int;
    let s = vavs(g, v0);
    lemma_vavs_index(g, v0, n - 1);
    lemma_vavs_take(g, v0, n - 1);
    assert(v0.drop_last() == v0.take(n - 1));
    assert(s.drop_last() =~= s.take(n - 1));
    let t = match suffix { Some(r) => ActionShape::Append(v0.last()@, r), None => ActionShape::Not(v0.last()@) };
    lemma_arun_one(g, t, s.take(n - 1));
    lemma_aref_refl(s.take(n - 1).push(push_av(g, t)));
    lemma_xnf_values_sub(g, v0, 0, n - 1);
    assert(nf_sum(g, v0.last()@)) by { assert(v0[n - 1] == v0.last()); }
    lemma_xnf1(g, t);
    lemma_effect_raw(e, g, task, p0, v0, seq![t], v0.drop_last());
    assert(p0 + seq![t] =~= p0.push(t));
}

pub proof fn lemma_step_swap(e: model::Graph, g: model::Graph, p0: Seq<ActionShape>, v0: Seq<TransitionId>)
    requires xctx(e, g, ActionShape::SwapThen, p0, v0), v0.len() >= 2,
    ensures xeffect(g, ActionShape::SwapThen, p0, v0, p0, v0.take(v0.len() - 2).push(v0[v0.len() - 1]).push(v0[v0.len() - 2])),
{
    reveal(xpre); reveal(xeffect); reveal(xrun); reveal(xcfg); reveal(xstep);
    let task = ActionShape::SwapThen;
    lemma_xpre_stable(e, g, task, p0, v0);
    let n = v0.len() as int;
    let v1 = v0.take(n - 2).push(v0[n - 1]).push(v0[n - 2]);
    let s = vavs(g, v0);
    lemma_vavs_index(g, v0, n - 2);
    lemma_vavs_index(g, v0, n - 1);
    lemma_vavs_take(g, v0, n - 2);
    lemma_vavs_push(g, v0.take(n - 2), v0[n - 1]);
    lemma_vavs_push(g, v0.take(n - 2).push(v0[n - 1]), v0[n - 2]);
    lemma_aref_refl(vavs(g, v1));
    lemma_xnf_values_sub(g, v0, 0, n - 2);
    lemma_xnf_values_push(g, v0.take(n - 2), v0[n - 1]);
    lemma_xnf_values_push(g, v0.take(n - 2).push(v0[n - 1]), v0[n - 2]);
    assert(xnf_tasks(g, Seq::<ActionShape>::empty()));
    lemma_effect_raw(e, g, task, p0, v0, Seq::empty(), v1);
    assert(p0 + Seq::<ActionShape>::empty() =~= p0);
}

// ===== next and run =====

/// One machine step keeps the typing and lowers the abstract run (frame rule).
pub proof fn lemma_next(e: model::Graph, g: model::Graph, pending: Seq<ActionShape>, shape: ActionShape, v0: Seq<TransitionId>,
    tasks: Seq<ActionShape>, values: Seq<TransitionId>)
    requires xcfg(e, pending.push(shape), v0),
        xpre(e, shape, pending, v0) ==> xeffect(g, shape, pending, v0, tasks, values),
    ensures xnf_tasks(g, tasks), xnf_values(g, values),
        aref(arun(g, pending.push(shape), vavs(g, v0)), arun(g, tasks, vavs(g, values))),
        xstep(g, pending.push(shape), v0, tasks, values),
{
    reveal(xpre); reveal(xeffect); reveal(xrun); reveal(xcfg); reveal(xstep);
    lemma_xnf_tasks_pop(e, pending, shape);
    let exp = tasks.subrange(pending.len() as int, tasks.len() as int);
    lemma_frame(g, pending, exp, shape, vavs(g, v0), vavs(g, values));
    assert(pending + exp =~= tasks) by {
        assert(tasks.subrange(0, pending.len() as int) =~= pending);
    }
}

pub proof fn lemma_run_start(g: model::Graph, shape: ActionShape)
    requires xnf_task(g, shape),
    ensures xrun(g, shape, seq![shape], Seq::empty()),
{
    reveal(xpre); reveal(xeffect); reveal(xrun); reveal(xcfg); reveal(xstep);
    lemma_xnf1(g, shape);
    assert(vavs(g, Seq::<TransitionId>::empty()) =~= Seq::<AV>::empty());
    match arun(g, seq![shape], Seq::empty()) {
        Some(s) => lemma_stack_le_refl(s),
        None => {},
    }
}

pub proof fn lemma_run_step(e: model::Graph, b: model::Graph, g: model::Graph, shape: ActionShape, t0: Seq<ActionShape>, v0: Seq<TransitionId>,
    t1: Seq<ActionShape>, v1: Seq<TransitionId>)
    requires model::graph_wf(e), model::graph_extends(e, b), norm::transition_action_valid(e, shape),
        model::graph_wf(b), model::graph_extends(b, g),
        norm::transition_configuration_valid(b, t0, v0), xrun(b, shape, t0, v0),
        xcfg(b, t0, v0) ==> xstep(g, t0, v0, t1, v1),
    ensures xrun(g, shape, t1, v1),
{
    reveal(xpre); reveal(xeffect); reveal(xrun); reveal(xcfg); reveal(xstep);
    lemma_tasks_valid1(e, seq![shape], shape);
    lemma_tasks_valid_stable(e, b, seq![shape]);
    lemma_arun_stable(b, g, seq![shape], Seq::empty());
    lemma_values_stable(b, g, v0);
    lemma_arun_stable(b, g, t0, vavs(b, v0));
    lemma_aref_trans(arun(g, seq![shape], Seq::empty()), arun(g, t0, vavs(g, v0)), arun(g, t1, vavs(g, v1)));
}

pub proof fn lemma_run_end(g: model::Graph, shape: ActionShape, values: Seq<TransitionId>)
    requires xrun(g, shape, Seq::empty(), values), norm::transition_action_pushes(shape),
    ensures values.len() == 1, run_bound(g, shape, values[0]@), values.last() == values[0],
{
    reveal(xpre); reveal(xeffect); reveal(xrun); reveal(xcfg); reveal(xstep);
    lemma_arun_one(g, shape, Seq::empty());
    lemma_aapply_push(g, shape, Seq::empty());
    let s = vavs(g, values);
    assert(arun(g, Seq::<ActionShape>::empty(), s) == Some(s));
    let l = Seq::<AV>::empty().push(push_av(g, shape));
    assert(l[0] == push_av(g, shape));
    assert(stack_le(s, l));
    assert(s.len() == 1);
    assert(av_le(s[0], l[0]));
    lemma_vavs_index(g, values, 0);
    assert(nf_sum(g, values[0]@));
}

// ===== entry points =====

/// After `local_if`, cleaning its result gives the class bound of `if_then_else`.
pub proof fn lemma_ite_future(g1: model::Graph, a: nat, b: nat, id1: nat, path: nat)
    requires model::graph_wf(g1), a < g1.transitions.len(), b < g1.transitions.len(), id1 < g1.transitions.len(),
        av_le(av_of(g1, id1), av_if(av_of(g1, a), av_of(g1, b))),
    ensures forall|h: model::Graph, out: nat| model::graph_extends(g1, h) && #[trigger] run_bound(h, ActionShape::Clean(id1, path), out)
        ==> ite_bound(h, out, a, b),
{
    assert forall|h: model::Graph, out: nat| model::graph_extends(g1, h) && #[trigger] run_bound(h, ActionShape::Clean(id1, path), out)
        implies ite_bound(h, out, a, b) by {
        lemma_av_stable(g1, h, id1);
        lemma_av_stable(g1, h, a);
        lemma_av_stable(g1, h, b);
        lemma_av_le_trans(av_of(h, out), av_of(h, id1), av_if(av_of(h, a), av_of(h, b)));
    }
}

/// `if_then_else` before running the clean action: the local conditional is typed and bounded.
pub proof fn lemma_ite_start(e: model::Graph, g1: model::Graph, test: nat, a: nat, b: nat, id1: nat, path: nat)
    requires model::graph_wf(e), model::graph_wf(g1), model::graph_extends(e, g1), a < e.transitions.len(), b < e.transitions.len(),
        nf_sum(e, a), nf_sum(e, b),
        id1 == a || id1 == b || (id1 < g1.transitions.len() && g1.transitions[id1 as int] == model::TransitionNode::If(test, a, b)),
    ensures xnf_task(g1, ActionShape::Clean(id1, path)),
        forall|h: model::Graph, out: nat| model::graph_extends(g1, h) && #[trigger] run_bound(h, ActionShape::Clean(id1, path), out)
            ==> ite_bound(h, out, a, b),
{
    lemma_nf_sum_stable(e, g1, a);
    lemma_nf_sum_stable(e, g1, b);
    lemma_local_if(g1, test, a, b, id1);
    lemma_ite_future(g1, a, b, id1, path);
}

/// `append` before running the append action: the action is typed, and its run bound is the
/// class bound of `append` over the lifted suffix.
pub proof fn lemma_app_future(e: model::Graph, g1: model::Graph, this: nat, suffix: Seq<RegexId>, r: nat)
    requires model::graph_wf(e), model::graph_wf(g1), model::graph_extends(e, g1), this < e.transitions.len(),
        nf_sum(e, this), ids_nf(e, suffix), norm::regex_ids_valid(e, suffix),
        r < g1.regexes.len(), norm::regex_concat_result(e, g1, suffix, r),
    ensures xnf_task(g1, ActionShape::Append(this, r)),
        forall|h: model::Graph, out: nat| model::graph_extends(g1, h) && #[trigger] run_bound(h, ActionShape::Append(this, r), out)
            ==> app_bound(h, out, this, lifts(h, suffix)),
{
    lemma_nf_sum_stable(e, g1, this);
    lemma_concat_link(e, g1, suffix, r);
    let ys = lifts(e, suffix);
    assert(all_rnf(ys)) by {
        assert forall|i: int| 0 <= i < ys.len() implies regex_nf(#[trigger] ys[i]) by {}
    }
    lemma_cat_nf(ys);
    assert forall|h: model::Graph, out: nat| model::graph_extends(g1, h) && #[trigger] run_bound(h, ActionShape::Append(this, r), out)
        implies app_bound(h, out, this, lifts(h, suffix)) by {
        lemma_regex_nf_stable(g1, h, r);
        lemma_lifts_ids(e, h, suffix);
        lemma_nf_sum_stable(g1, h, this);
        norm::transition_lemma_extends_transitive(e, g1, h);
        let z = model::lift_regex(h, r);
        assert forall|v: R| #[trigger] tcls(h, out, v) implies rconst(v) || exists|w: R| tcls(h, this, w) && v == #[trigger] cat_front(w, ys) by {
            assert((av_of(h, out).x)(v));
            if !rconst(v) {
                let w = choose|w: R| (av_of(h, this).x)(w) && v == #[trigger] cat_r(w, z);
                lemma_cls_nf(h, this, w);
                lemma_cat_nest(w, ys);
                assert(tcls(h, this, w) && v == cat_front(w, ys));
            }
        }
    }
}
} // verus!
