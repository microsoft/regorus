//! The machine typing invariant of the transition normalizer (`normalize.rs` `Action`): every
//! task and stack value is a normal form ([`xnf_task`], [`xnf_values`]), and each step replaces
//! its action by an expansion whose abstract run (`verify::finite_machine::arun`) is below the
//! action's abstract effect ([`xeffect`]). With the frame rule this bounds the class of the
//! result of `Action::run` by the abstract effect of the original action ([`run_bound`]), which
//! gives the class bounds of the transition constructors `intersect`, `not`, `append`, and
//! `if_then_else`. (N4′) for `r_cat` on normal forms is [`lemma_cat_inline`].
use crate::normalize::verify::{self as norm, ActionShape, ChildShape};
use crate::verify::finite_collect::*;
use crate::verify::finite_impl::*;
use crate::verify::finite_link::*;
use crate::verify::finite_machine::*;
use crate::verify::finite_states::*;
use crate::verify::finite_trans::*;
use junco_core::kernel::verify as model;
use junco_core::kernel::{RegexId, TestId, TransitionId};
use junco_core::verify::history_specs::Regex;
use vstd::prelude::*;

verus! {

broadcast use junco_core::kernel::verify::group_kernel_views;

// ===== the invariant =====

/// A task over normal-form transitions and suffixes.
pub open spec fn xnf_task(g: model::Graph, a: ActionShape) -> bool {
    match a {
        ActionShape::Clean(id, _) => nf_sum(g, id),
        ActionShape::Not(id) => nf_sum(g, id),
        ActionShape::Append(id, r) => nf_sum(g, id) && r < g.regexes.len() && regex_nf(model::lift_regex(g, r)),
        ActionShape::Pair(a, b) => nf_sum(g, a) && nf_sum(g, b),
        ActionShape::Fold(terms, _) => all_nf(g, terms),
        ActionShape::AppendResult(r) => r < g.regexes.len() && regex_nf(model::lift_regex(g, r)),
        _ => true,
    }
}

pub open spec fn xnf_tasks(g: model::Graph, ts: Seq<ActionShape>) -> bool {
    forall|i: int| 0 <= i < ts.len() ==> #[trigger] xnf_task(g, ts[i])
}

pub open spec fn xnf_values(g: model::Graph, vs: Seq<TransitionId>) -> bool {
    forall|i: int| #![trigger vs[i]] 0 <= i < vs.len() ==> nf_sum(g, vs[i]@)
}

/// Abstract stack of a value stack.
pub open spec fn vavs(g: model::Graph, vs: Seq<TransitionId>) -> Seq<AV> {
    avs(g, model::transition_ids(vs))
}

/// The configuration before a step of `task` is typed.
#[verifier::opaque]
pub open spec fn xpre(g: model::Graph, task: ActionShape, pending: Seq<ActionShape>, prior: Seq<TransitionId>) -> bool {
    xnf_tasks(g, pending) && xnf_task(g, task) && xnf_values(g, prior)
}

/// The configuration after a step of `task` is typed, and the step's expansion is below the
/// abstract effect of `task`.
#[verifier::opaque]
pub open spec fn xeffect(g: model::Graph, task: ActionShape, pending: Seq<ActionShape>, prior: Seq<TransitionId>,
    tasks: Seq<ActionShape>, values: Seq<TransitionId>) -> bool {
    &&& pending.is_prefix_of(tasks)
    &&& xnf_tasks(g, tasks) && xnf_values(g, values)
    &&& aref(aapply(g, task, vavs(g, prior)), arun(g, tasks.subrange(pending.len() as int, tasks.len() as int), vavs(g, values)))
}

/// The run invariant: the remaining run is below the original action's.
#[verifier::opaque]
pub open spec fn xrun(g: model::Graph, shape: ActionShape, tasks: Seq<ActionShape>, values: Seq<TransitionId>) -> bool {
    &&& xnf_tasks(g, tasks) && xnf_values(g, values)
    &&& aref(arun(g, seq![shape], Seq::empty()), arun(g, tasks, vavs(g, values)))
}

/// The abstract value pushed by an action that pushes one value.
pub open spec fn push_av(g: model::Graph, task: ActionShape) -> AV {
    match task {
        ActionShape::Clean(id, _) => av_of(g, id),
        ActionShape::Not(id) => av_neg(av_of(g, id)),
        ActionShape::Append(id, r) => av_app(av_of(g, id), model::lift_regex(g, r)),
        ActionShape::Pair(a, b) => av_meet(seq![av_of(g, a), av_of(g, b)]),
        ActionShape::Fold(terms, _) => av_meet(avs(g, terms)),
        _ => av_of(g, 0),
    }
}

/// The result `id` of `Action::run` for `shape` is a normal form whose abstract value is below
/// the abstract effect of `shape`.
pub open spec fn run_bound(g: model::Graph, shape: ActionShape, id: nat) -> bool {
    nf_sum(g, id) && av_le(av_of(g, id), push_av(g, shape))
}

/// The class bound of `if_then_else(test, a, b)`.
pub open spec fn ite_bound(g: model::Graph, out: nat, a: nat, b: nat) -> bool {
    nf_sum(g, out) && av_le(av_of(g, out), av_if(av_of(g, a), av_of(g, b)))
}

/// `N(w ys)`.
pub open spec fn cat_front(w: R, ys: Seq<R>) -> R {
    r_cat(seq![w] + ys)
}

/// The class bound of `append(t, s)` with lifted suffix `ys`: constants and `N(w ys)` for members
/// `w` of `t`'s class.
pub open spec fn app_bound(g: model::Graph, out: nat, t: nat, ys: Seq<R>) -> bool {
    &&& nf_sum(g, out)
    &&& forall|v: R| #[trigger] tcls(g, out, v) ==> rconst(v) || exists|w: R| tcls(g, t, w) && v == #[trigger] cat_front(w, ys)
}

/// A typed configuration.
#[verifier::opaque]
pub open spec fn xcfg(g: model::Graph, tasks: Seq<ActionShape>, values: Seq<TransitionId>) -> bool {
    xnf_tasks(g, tasks) && xnf_values(g, values)
}

/// A machine step from `(t0, v0)` to `(t1, v1)` keeps the typing and lowers the abstract run.
#[verifier::opaque]
pub open spec fn xstep(g: model::Graph, t0: Seq<ActionShape>, v0: Seq<TransitionId>, t1: Seq<ActionShape>, v1: Seq<TransitionId>) -> bool {
    xcfg(g, t1, v1) && aref(arun(g, t0, vavs(g, v0)), arun(g, t1, vavs(g, v1)))
}

// ===== sequences =====

pub proof fn lemma_vavs_index(g: model::Graph, vs: Seq<TransitionId>, i: int)
    requires 0 <= i < vs.len(),
    ensures vavs(g, vs).len() == vs.len(), vavs(g, vs)[i] == av_of(g, vs[i]@),
{
    assert(model::transition_ids(vs)[i] == vs[i]@);
}

pub proof fn lemma_vavs_push(g: model::Graph, vs: Seq<TransitionId>, x: TransitionId)
    ensures vavs(g, vs.push(x)) == vavs(g, vs).push(av_of(g, x@)),
{
    assert(model::transition_ids(vs.push(x)) =~= model::transition_ids(vs).push(x@));
    assert(vavs(g, vs.push(x)) =~= vavs(g, vs).push(av_of(g, x@)));
}

pub proof fn lemma_vavs_sub(g: model::Graph, vs: Seq<TransitionId>, i: int, j: int)
    requires 0 <= i <= j <= vs.len(),
    ensures vavs(g, vs.subrange(i, j)) == vavs(g, vs).subrange(i, j),
        model::transition_ids(vs.subrange(i, j)) == model::transition_ids(vs).subrange(i, j),
{
    assert(model::transition_ids(vs.subrange(i, j)) =~= model::transition_ids(vs).subrange(i, j));
    assert(vavs(g, vs.subrange(i, j)) =~= vavs(g, vs).subrange(i, j));
}

pub proof fn lemma_vavs_take(g: model::Graph, vs: Seq<TransitionId>, i: int)
    requires 0 <= i <= vs.len(),
    ensures vavs(g, vs.take(i)) == vavs(g, vs).take(i),
{
    lemma_vavs_sub(g, vs, 0, i);
    assert(vs.take(i) == vs.subrange(0, i));
    assert(vavs(g, vs).take(i) == vavs(g, vs).subrange(0, i));
}

pub proof fn lemma_xnf_values_push(g: model::Graph, vs: Seq<TransitionId>, x: TransitionId)
    requires xnf_values(g, vs), nf_sum(g, x@),
    ensures xnf_values(g, vs.push(x)),
{
    assert forall|i: int| #![trigger vs.push(x)[i]] 0 <= i < vs.push(x).len() implies nf_sum(g, vs.push(x)[i]@) by {
        if i < vs.len() { assert(vs.push(x)[i] == vs[i]); }
    }
}

pub proof fn lemma_xnf_values_sub(g: model::Graph, vs: Seq<TransitionId>, i: int, j: int)
    requires xnf_values(g, vs), 0 <= i <= j <= vs.len(),
    ensures xnf_values(g, vs.subrange(i, j)), xnf_values(g, vs.take(j)), all_nf(g, model::transition_ids(vs.subrange(i, j))),
{
    assert forall|k: int| #![trigger vs.subrange(i, j)[k]] 0 <= k < vs.subrange(i, j).len() implies nf_sum(g, vs.subrange(i, j)[k]@) by {
        assert(vs.subrange(i, j)[k] == vs[i + k]);
    }
    assert forall|k: int| #![trigger vs.take(j)[k]] 0 <= k < vs.take(j).len() implies nf_sum(g, vs.take(j)[k]@) by {
        assert(vs.take(j)[k] == vs[k]);
    }
    assert forall|k: int| 0 <= k < model::transition_ids(vs.subrange(i, j)).len()
        implies nf_sum(g, #[trigger] model::transition_ids(vs.subrange(i, j))[k]) by {
        assert(vs.subrange(i, j)[k] == vs[i + k]);
    }
}

pub proof fn lemma_xnf_tasks_append(g: model::Graph, a: Seq<ActionShape>, b: Seq<ActionShape>)
    requires xnf_tasks(g, a), xnf_tasks(g, b),
    ensures xnf_tasks(g, a + b),
{
    assert forall|i: int| 0 <= i < (a + b).len() implies #[trigger] xnf_task(g, (a + b)[i]) by {
        if i < a.len() { assert((a + b)[i] == a[i]); } else { assert((a + b)[i] == b[i - a.len()]); }
    }
}

pub proof fn lemma_xnf_tasks_push(g: model::Graph, a: Seq<ActionShape>, t: ActionShape)
    requires xnf_tasks(g, a), xnf_task(g, t),
    ensures xnf_tasks(g, a.push(t)),
{
    assert forall|i: int| 0 <= i < a.push(t).len() implies #[trigger] xnf_task(g, a.push(t)[i]) by {
        if i < a.len() { assert(a.push(t)[i] == a[i]); }
    }
}

pub proof fn lemma_xnf_tasks_pop(g: model::Graph, a: Seq<ActionShape>, t: ActionShape)
    requires xnf_tasks(g, a.push(t)),
    ensures xnf_tasks(g, a), xnf_task(g, t),
{
    assert(a.push(t)[a.len() as int] == t);
    assert forall|i: int| 0 <= i < a.len() implies #[trigger] xnf_task(g, a[i]) by {
        assert(a.push(t)[i] == a[i]);
    }
}

pub proof fn lemma_xnf1(g: model::Graph, a: ActionShape)
    requires xnf_task(g, a),
    ensures xnf_tasks(g, seq![a]),
{
    assert(xnf_tasks(g, Seq::<ActionShape>::empty()));
    lemma_xnf_tasks_push(g, Seq::empty(), a);
}

pub proof fn lemma_xnf2(g: model::Graph, a: ActionShape, b: ActionShape)
    requires xnf_task(g, a), xnf_task(g, b),
    ensures xnf_tasks(g, seq![a, b]),
{
    lemma_xnf1(g, a);
    lemma_xnf_tasks_push(g, seq![a], b);
}

pub proof fn lemma_xnf3(g: model::Graph, a: ActionShape, b: ActionShape, c: ActionShape)
    requires xnf_task(g, a), xnf_task(g, b), xnf_task(g, c),
    ensures xnf_tasks(g, seq![a, b, c]),
{
    lemma_xnf2(g, a, b);
    lemma_xnf_tasks_push(g, seq![a, b], c);
}

/// A pair whose elements are the first two of `t` contributes classes of `t`.
pub proof fn lemma_any_x_pair(s: Seq<AV>, t: Seq<AV>)
    requires s.len() == 2, t.len() >= 2, s[0] == t[0], s[1] == t[1],
    ensures forall|w: R| #[trigger] any_x(s, w) ==> any_x(t, w),
{
    assert forall|w: R| #[trigger] any_x(s, w) implies any_x(t, w) by {
        let i = choose|i: int| #![trigger s[i]] 0 <= i < s.len() && (s[i].x)(w);
        assert(t[i] == s[i]);
    }
}

pub proof fn lemma_tasks_valid1(g: model::Graph, s: Seq<ActionShape>, t: ActionShape)
    requires s.len() == 1, s[0] == t, norm::transition_action_valid(g, t),
    ensures norm::transition_tasks_valid(g, s),
{
    assert forall|i: int| 0 <= i < s.len() implies norm::transition_action_valid(g, s[i]) by { assert(i == 0); }
}

pub proof fn lemma_rnf_seq2(s: Seq<R>)
    requires s.len() == 2, regex_nf(s[0]), regex_nf(s[1]),
    ensures all_rnf(s),
{
    assert forall|i: int| 0 <= i < s.len() implies regex_nf(#[trigger] s[i]) by { if i == 0 {} else { assert(i == 1); } }
}

// ===== stability =====

pub proof fn lemma_nf_sum_stable(a: model::Graph, b: model::Graph, t: nat)
    requires model::graph_wf(a), model::graph_extends(a, b), t < a.transitions.len(),
    ensures nf_sum(a, t) == nf_sum(b, t), nf_prod(a, t) == nf_prod(b, t), nf_lit(a, t) == nf_lit(b, t),
        av_of(a, t) == av_of(b, t), b.transitions[t as int] == a.transitions[t as int], t < b.transitions.len(),
{
    lemma_trans_stable(a, b, t);
    lemma_av_stable(a, b, t);
    assert(a.transitions == b.transitions.subrange(0, a.transitions.len() as int));
}

pub proof fn lemma_regex_nf_stable(a: model::Graph, b: model::Graph, r: nat)
    requires model::graph_wf(a), model::graph_extends(a, b), r < a.regexes.len(),
    ensures model::lift_regex(a, r) == model::lift_regex(b, r), r < b.regexes.len(),
{
    model::lemma_graph_wf_elim(a);
    model::lemma_lift_regex_stable(a, b, r);
}

pub proof fn lemma_all_nf_stable(a: model::Graph, b: model::Graph, ts: Seq<nat>)
    requires model::graph_wf(a), model::graph_extends(a, b), model::bounded(ts, a.transitions.len()), all_nf(a, ts),
    ensures all_nf(b, ts), avs(a, ts) == avs(b, ts),
{
    assert forall|k: int| 0 <= k < ts.len() implies nf_sum(b, #[trigger] ts[k]) by {
        lemma_nf_sum_stable(a, b, ts[k]);
    }
    lemma_avs_stable(a, b, ts);
}

pub proof fn lemma_xnf_task_stable(a: model::Graph, b: model::Graph, t: ActionShape)
    requires model::graph_wf(a), model::graph_extends(a, b), norm::transition_action_valid(a, t), xnf_task(a, t),
    ensures xnf_task(b, t), norm::transition_action_valid(b, t),
{
    model::lemma_graph_wf_elim(a);
    match t {
        ActionShape::Clean(id, _) => { lemma_nf_sum_stable(a, b, id); },
        ActionShape::Not(id) => { lemma_nf_sum_stable(a, b, id); },
        ActionShape::Append(id, r) => { lemma_nf_sum_stable(a, b, id); lemma_regex_nf_stable(a, b, r); },
        ActionShape::Pair(x, y) => { lemma_nf_sum_stable(a, b, x); lemma_nf_sum_stable(a, b, y); },
        ActionShape::Fold(terms, _) => {
            lemma_all_nf_stable(a, b, terms);
            assert(model::bounded(terms, b.transitions.len())) by {
                assert forall|k: int| 0 <= k < terms.len() implies #[trigger] terms[k] < b.transitions.len() by {}
            }
        },
        ActionShape::AppendResult(r) => { lemma_regex_nf_stable(a, b, r); },
        _ => {},
    }
}

pub proof fn lemma_xnf_tasks_stable(a: model::Graph, b: model::Graph, ts: Seq<ActionShape>)
    requires model::graph_wf(a), model::graph_extends(a, b), norm::transition_tasks_valid(a, ts), xnf_tasks(a, ts),
    ensures xnf_tasks(b, ts),
{
    assert forall|i: int| 0 <= i < ts.len() implies #[trigger] xnf_task(b, ts[i]) by {
        assert(norm::transition_action_valid(a, ts[i]));
        assert(xnf_task(a, ts[i]));
        lemma_xnf_task_stable(a, b, ts[i]);
    }
}

pub proof fn lemma_values_stable(a: model::Graph, b: model::Graph, vs: Seq<TransitionId>)
    requires model::graph_wf(a), model::graph_extends(a, b), norm::transition_ids_valid(a, vs),
    ensures vavs(a, vs) == vavs(b, vs), xnf_values(a, vs) ==> xnf_values(b, vs),
        norm::transition_ids_valid(b, vs), model::bounded(model::transition_ids(vs), a.transitions.len()),
{
    assert(model::bounded(model::transition_ids(vs), a.transitions.len())) by {
        assert forall|k: int| 0 <= k < model::transition_ids(vs).len() implies #[trigger] model::transition_ids(vs)[k] < a.transitions.len() by {
            assert(model::transition_ids(vs)[k] == vs[k]@);
        }
    }
    lemma_avs_stable(a, b, model::transition_ids(vs));
    if xnf_values(a, vs) {
        assert forall|i: int| #![trigger vs[i]] 0 <= i < vs.len() implies nf_sum(b, vs[i]@) by {
            lemma_nf_sum_stable(a, b, vs[i]@);
        }
    }
    assert forall|i: int| 0 <= i < vs.len() implies vs[i]@ < b.transitions.len() by {
        lemma_nf_sum_stable(a, b, vs[i]@);
    }
}

pub proof fn lemma_tasks_valid_stable(a: model::Graph, b: model::Graph, ts: Seq<ActionShape>)
    requires model::graph_wf(a), model::graph_extends(a, b), norm::transition_tasks_valid(a, ts),
    ensures norm::transition_tasks_valid(b, ts),
{
    assert forall|i: int| 0 <= i < ts.len() implies norm::transition_action_valid(b, ts[i]) by {
        assert(norm::transition_action_valid(a, ts[i]));
        match ts[i] {
            ActionShape::Fold(terms, _) => {
                assert forall|k: int| 0 <= k < terms.len() implies #[trigger] terms[k] < b.transitions.len() by {}
            },
            _ => {},
        }
    }
}

/// The typed configuration before a step survives graph extension, with the same abstract effect.
pub proof fn lemma_xpre_stable(a: model::Graph, b: model::Graph, task: ActionShape, pending: Seq<ActionShape>, prior: Seq<TransitionId>)
    requires model::graph_wf(a), model::graph_extends(a, b), norm::transition_tasks_valid(a, pending),
        norm::transition_action_valid(a, task), norm::transition_ids_valid(a, prior), xpre(a, task, pending, prior),
    ensures xpre(b, task, pending, prior), vavs(a, prior) == vavs(b, prior),
        aapply(a, task, vavs(a, prior)) == aapply(b, task, vavs(b, prior)),
        norm::transition_action_valid(b, task), norm::transition_tasks_valid(b, pending), norm::transition_ids_valid(b, prior),
{
    reveal(xpre);
    lemma_xnf_tasks_stable(a, b, pending);
    lemma_xnf_task_stable(a, b, task);
    lemma_values_stable(a, b, prior);
    lemma_aapply_stable(a, b, task, vavs(a, prior));
    lemma_tasks_valid_stable(a, b, pending);
}

// ===== the generic step =====

pub proof fn lemma_aapply_push(g: model::Graph, task: ActionShape, s: Seq<AV>)
    requires norm::transition_action_pushes(task),
    ensures aapply(g, task, s) == Some(s.push(push_av(g, task))),
{}

pub proof fn lemma_aref_refl(s: Seq<AV>)
    ensures aref(Some(s), Some(s)),
{
    lemma_stack_le_refl(s);
}

pub proof fn lemma_aref_push(s: Seq<AV>, x: AV, y: AV)
    requires av_le(y, x),
    ensures aref(Some(s.push(x)), Some(s.push(y))),
{
    lemma_stack_le_refl(s);
    lemma_stack_le_push(s, s, y, x);
}

pub open spec fn xctx(e: model::Graph, g: model::Graph, task: ActionShape, p0: Seq<ActionShape>, v0: Seq<TransitionId>) -> bool {
    &&& model::graph_wf(e) && model::graph_wf(g) && model::graph_extends(e, g)
    &&& norm::transition_configuration_valid(e, p0, v0) && norm::transition_action_valid(e, task)
    &&& xpre(e, task, p0, v0)
}

/// A pushing step whose expansion `exp` run on the new values `v1` pushes `y` below the action's
/// effect.
pub proof fn lemma_effect(e: model::Graph, g: model::Graph, task: ActionShape, p0: Seq<ActionShape>, v0: Seq<TransitionId>,
    exp: Seq<ActionShape>, v1: Seq<TransitionId>, y: AV)
    requires xctx(e, g, task, p0, v0), norm::transition_action_pushes(task),
        xnf_tasks(g, exp), xnf_values(g, v1),
        arun(g, exp, vavs(g, v1)) == Some(vavs(g, v0).push(y)),
        av_le(y, push_av(g, task)),
    ensures xeffect(g, task, p0, v0, p0 + exp, v1),
{
    reveal(xpre); reveal(xeffect);
    lemma_xpre_stable(e, g, task, p0, v0);
    lemma_xnf_tasks_append(g, p0, exp);
    assert((p0 + exp).subrange(p0.len() as int, (p0 + exp).len() as int) =~= exp);
    assert(p0.is_prefix_of(p0 + exp)) by { assert((p0 + exp).subrange(0, p0.len() as int) =~= p0); }
    lemma_aapply_push(g, task, vavs(g, v0));
    lemma_aref_push(vavs(g, v0), push_av(g, task), y);
}

/// A pushing step that pushes the value `out`.
pub proof fn lemma_effect_value(e: model::Graph, g: model::Graph, task: ActionShape, p0: Seq<ActionShape>, v0: Seq<TransitionId>,
    out: TransitionId)
    requires xctx(e, g, task, p0, v0), norm::transition_action_pushes(task), nf_sum(g, out@),
        av_le(av_of(g, out@), push_av(g, task)),
    ensures xeffect(g, task, p0, v0, p0, v0.push(out)),
{
    reveal(xpre); reveal(xeffect);
    lemma_xpre_stable(e, g, task, p0, v0);
    lemma_xnf_values_push(g, v0, out);
    lemma_vavs_push(g, v0, out);
    assert(xnf_tasks(g, Seq::<ActionShape>::empty()));
    lemma_effect(e, g, task, p0, v0, Seq::empty(), v0.push(out), av_of(g, out@));
    assert(p0 + Seq::<ActionShape>::empty() =~= p0);
}

// ===== runs of short expansions =====

pub proof fn lemma_arun_one(g: model::Graph, t: ActionShape, s: Seq<AV>)
    ensures arun(g, seq![t], s) == aapply(g, t, s),
{
    assert(seq![t].drop_last() =~= Seq::<ActionShape>::empty());
    assert(seq![t].last() == t);
    match aapply(g, t, s) {
        Some(n) => { assert(arun(g, Seq::<ActionShape>::empty(), n) == Some(n)); },
        None => {},
    }
}

/// `arun(p.push(t), s)` runs `t` first.
pub proof fn lemma_arun_push(g: model::Graph, p: Seq<ActionShape>, t: ActionShape, s: Seq<AV>)
    ensures arun(g, p.push(t), s) == match aapply(g, t, s) { Some(n) => arun(g, p, n), None => None },
{
    assert(p.push(t).drop_last() =~= p);
    assert(p.push(t).last() == t);
}

// ===== classes of nodes =====

pub proof fn lemma_tc(g: model::Graph, t: nat, v: R)
    ensures (tc(g))(t, v) == tcls(g, t, v), (yc(g))(t, v) == ycls(g, t, v),
{}

/// A conditional's abstract value is the join of its branches'.
pub proof fn lemma_if_cls(g: model::Graph, t: nat, test: nat, a: nat, b: nat)
    requires model::graph_wf(g), t < g.transitions.len(), g.transitions[t as int] == model::TransitionNode::If(test, a, b),
    ensures av_le(av_if(av_of(g, a), av_of(g, b)), av_of(g, t)), av_le(av_of(g, a), av_of(g, t)), av_le(av_of(g, b), av_of(g, t)),
        av_le(av_of(g, t), av_if(av_of(g, a), av_of(g, b))), a < t, b < t,
{
    model::lemma_graph_transition_wf(g, t);
    assert forall|v: R| #[trigger] tcls(g, a, v) implies tcls(g, t, v) by { lemma_tcls(g, t, v); }
    assert forall|v: R| #[trigger] tcls(g, b, v) implies tcls(g, t, v) by { lemma_tcls(g, t, v); }
    assert forall|v: R| #[trigger] ycls(g, a, v) implies ycls(g, t, v) by { lemma_ycls(g, t, v); }
    assert forall|v: R| #[trigger] ycls(g, b, v) implies ycls(g, t, v) by { lemma_ycls(g, t, v); }
    assert forall|v: R| #[trigger] tcls(g, t, v) implies tcls(g, a, v) || tcls(g, b, v) by { lemma_tcls(g, t, v); }
    assert forall|v: R| #[trigger] ycls(g, t, v) implies ycls(g, a, v) || ycls(g, b, v) by { lemma_ycls(g, t, v); }
}

/// A union's abstract value is the union of its children's; children are below it.
pub proof fn lemma_union_cls(g: model::Graph, t: nat, cs: Seq<nat>)
    requires model::graph_wf(g), t < g.transitions.len(), g.transitions[t as int] == model::TransitionNode::Union(cs),
    ensures av_le(av_union(avs(g, cs)), av_of(g, t)),
        forall|i: int| 0 <= i < cs.len() ==> #[trigger] av_le(av_of(g, cs[i]), av_of(g, t)),
        model::bounded(cs, t),
{
    model::lemma_graph_transition_wf(g, t);
    let s = avs(g, cs);
    assert forall|v: R| #[trigger] (av_union(s).x)(v) implies tcls(g, t, v) by {
        lemma_tcls(g, t, v);
        if any_x(s, v) {
            let i = choose|i: int| #![trigger s[i]] 0 <= i < s.len() && (s[i].x)(v);
            assert(s[i] == av_of(g, cs[i]));
            assert(cs[i] < t);
            assert(kids(tc(g), t, cs, v));
        }
    }
    let yb = |w: R| kids(yc(g), t, cs, w);
    assert forall|v: R| #[trigger] (av_union(s).y)(v) implies ycls(g, t, v) by {
        lemma_ycls(g, t, v);
        assert forall|w: R| #[trigger] any_y(s, w) implies yb(w) by {
            let i = choose|i: int| #![trigger s[i]] 0 <= i < s.len() && (s[i].y)(w);
            assert(s[i] == av_of(g, cs[i]));
            assert(cs[i] < t);
        }
        lemma_cl_mono(false, |w: R| any_y(s, w), yb, v);
    }
    assert forall|i: int| 0 <= i < cs.len() implies #[trigger] av_le(av_of(g, cs[i]), av_of(g, t)) by {
        assert(cs[i] < t);
        assert forall|v: R| #[trigger] tcls(g, cs[i], v) implies tcls(g, t, v) by {
            lemma_tcls(g, t, v);
            assert(kids(tc(g), t, cs, v));
        }
        assert forall|v: R| #[trigger] ycls(g, cs[i], v) implies ycls(g, t, v) by {
            lemma_ycls(g, t, v);
            assert(yb(v));
            lemma_cl_base(false, yb, v);
        }
    }
}

/// An intersection's abstract value is the closure of its children's.
pub proof fn lemma_inter_cls(g: model::Graph, t: nat, cs: Seq<nat>)
    requires model::graph_wf(g), t < g.transitions.len(), g.transitions[t as int] == model::TransitionNode::Intersect(cs),
    ensures av_le(av_meet(avs(g, cs)), av_of(g, t)),
        forall|v: R| #[trigger] ycls(g, t, v),
        forall|i: int, v: R| 0 <= i < cs.len() && #[trigger] tcls(g, cs[i], v) ==> tcls(g, t, v),
        model::bounded(cs, t),
{
    model::lemma_graph_transition_wf(g, t);
    let s = avs(g, cs);
    let kb = |w: R| kids(tc(g), t, cs, w);
    assert forall|w: R| #[trigger] any_x(s, w) implies kb(w) by {
        let i = choose|i: int| #![trigger s[i]] 0 <= i < s.len() && (s[i].x)(w);
        assert(s[i] == av_of(g, cs[i]));
        assert(cs[i] < t);
    }
    assert forall|v: R| #[trigger] (av_meet(s).x)(v) implies tcls(g, t, v) by {
        lemma_tcls(g, t, v);
        lemma_cl_mono(true, |w: R| any_x(s, w), kb, v);
    }
    assert forall|v: R| #[trigger] ycls(g, t, v) by { lemma_ycls(g, t, v); }
    assert forall|i: int, v: R| 0 <= i < cs.len() && #[trigger] tcls(g, cs[i], v) implies tcls(g, t, v) by {
        assert(cs[i] < t);
        lemma_tcls(g, t, v);
        assert(kb(v));
        lemma_cl_base(true, kb, v);
    }
}

/// A complement node's abstract value is the complement of its operand's (both ways).
pub proof fn lemma_not_cls(g: model::Graph, t: nat, k: nat)
    requires model::graph_wf(g), t < g.transitions.len(), g.transitions[t as int] == model::TransitionNode::Not(k),
    ensures av_le(av_neg(av_of(g, k)), av_of(g, t)), av_le(av_of(g, t), av_neg(av_of(g, k))), k < t,
{
    model::lemma_graph_transition_wf(g, t);
    let nb = |w: R| negs(tc(g), t, k, w);
    let ob = |w: R| neg_of(av_of(g, k), w);
    assert forall|w: R| #[trigger] nb(w) <==> ob(w) by {
        if nb(w) { let x = choose|x: R| k < t && (tc(g))(k, x) && w == #[trigger] r_not(x); assert((av_of(g, k).x)(x)); }
        if ob(w) { let x = choose|x: R| (av_of(g, k).x)(x) && w == #[trigger] r_not(x); assert((tc(g))(k, x)); }
    }
    assert forall|v: R| #[trigger] tcls(g, t, v) <==> (av_neg(av_of(g, k)).x)(v) by {
        lemma_tcls(g, t, v);
        if cl(true, nb, v) { lemma_cl_mono(true, nb, ob, v); }
        if cl(true, ob, v) { lemma_cl_mono(true, ob, nb, v); }
    }
    assert forall|v: R| #[trigger] ycls(g, t, v) by { lemma_ycls(g, t, v); }
}

/// An append node's class: constants and `N(w s)` for members `w` of its body's class.
pub proof fn lemma_append_cls(g: model::Graph, t: nat, k: nat, rs: Seq<nat>)
    requires model::graph_wf(g), t < g.transitions.len(), g.transitions[t as int] == model::TransitionNode::Append(k, rs),
    ensures forall|v: R| #[trigger] tcls(g, t, v) <==> (rconst(v) || exists|w: R| tcls(g, k, w) && v == #[trigger] ccat(g, w, rs)),
        forall|v: R| #[trigger] ycls(g, t, v), k < t,
{
    model::lemma_graph_transition_wf(g, t);
    assert forall|v: R| #[trigger] tcls(g, t, v) <==> (rconst(v) || exists|w: R| tcls(g, k, w) && v == #[trigger] ccat(g, w, rs)) by {
        lemma_tcls(g, t, v);
        if exists|w: R| tcls(g, k, w) && v == #[trigger] ccat(g, w, rs) {
            let w = choose|w: R| tcls(g, k, w) && v == #[trigger] ccat(g, w, rs);
            assert((tc(g))(k, w));
        }
    }
    assert forall|v: R| #[trigger] ycls(g, t, v) by { lemma_ycls(g, t, v); }
}

/// A constant node's class: constants and its regex.
pub proof fn lemma_const_cls(g: model::Graph, t: nat, r: nat)
    requires t < g.transitions.len(), g.transitions[t as int] == model::TransitionNode::Const(r),
    ensures forall|v: R| #[trigger] tcls(g, t, v) <==> (rconst(v) || v == model::lift_regex(g, r)),
        forall|v: R| #[trigger] ycls(g, t, v) <==> v == model::lift_regex(g, r),
{
    assert forall|v: R| #[trigger] tcls(g, t, v) <==> (rconst(v) || v == model::lift_regex(g, r)) by { lemma_tcls(g, t, v); }
    assert forall|v: R| #[trigger] ycls(g, t, v) <==> v == model::lift_regex(g, r) by { lemma_ycls(g, t, v); }
}

/// The constant transitions have constant classes.
pub proof fn lemma_const_transitions(g: model::Graph)
    requires model::graph_wf(g),
    ensures
        forall|v: R| #[trigger] tcls(g, g.constants.transition_empty, v) ==> rconst(v),
        forall|v: R| #[trigger] tcls(g, g.constants.transition_all, v) ==> rconst(v),
        forall|v: R| #[trigger] tcls(g, g.constants.transition_epsilon, v) ==> rconst(v),
        forall|v: R| #[trigger] ycls(g, g.constants.transition_empty, v) ==> v == Regex::<model::Test>::Empty,
        forall|v: R| #[trigger] ycls(g, g.constants.transition_epsilon, v) ==> v == Regex::<model::Test>::Epsilon,
        nf_sum(g, g.constants.transition_empty), nf_sum(g, g.constants.transition_all), nf_sum(g, g.constants.transition_epsilon),
        g.constants.transition_empty < g.transitions.len(), g.constants.transition_all < g.transitions.len(),
        g.constants.transition_epsilon < g.transitions.len(),
{
    model::lemma_graph_wf_elim(g);
    norm::regex_constants(g);
    let c = g.constants;
    lemma_const_cls(g, c.transition_empty, c.empty);
    lemma_const_cls(g, c.transition_all, c.all);
    lemma_const_cls(g, c.transition_epsilon, c.epsilon);
}

// ===== normal forms =====

pub proof fn lemma_nf_weaken(g: model::Graph, t: nat)
    ensures nf_lit(g, t) ==> nf_prod(g, t), nf_prod(g, t) ==> nf_sum(g, t),
{
    if t < g.transitions.len() {
        match g.transitions[t as int] {
            model::TransitionNode::Intersect(cs) => {},
            model::TransitionNode::If(_, _, _) => {},
            model::TransitionNode::Union(_) => {},
            _ => {},
        }
    }
}

/// Children of normal forms are normal forms.
pub proof fn lemma_nf_children(g: model::Graph, t: nat)
    requires nf_sum(g, t),
    ensures match g.transitions[t as int] {
        model::TransitionNode::If(_, a, b) => nf_sum(g, a) && nf_sum(g, b),
        model::TransitionNode::Union(cs) => all_nf(g, cs),
        model::TransitionNode::Intersect(cs) => all_nf(g, cs) && forall|i: int| 0 <= i < cs.len() ==> nf_lit(g, #[trigger] cs[i]),
        model::TransitionNode::Not(k) => nf_lit(g, k) && nf_sum(g, k),
        model::TransitionNode::Append(k, rs) => nf_prod(g, k) && nf_sum(g, k) && nats_nf(g, rs) && model::bounded(rs, g.regexes.len()),
        model::TransitionNode::Const(r) => r < g.regexes.len() && regex_nf(model::lift_regex(g, r)),
    },
{
    match g.transitions[t as int] {
        model::TransitionNode::Intersect(cs) => {
            assert forall|k: int| 0 <= k < cs.len() implies nf_sum(g, #[trigger] cs[k]) by {
                lemma_nf_weaken(g, cs[k]);
            }
        },
        model::TransitionNode::Not(k) => { lemma_nf_weaken(g, k); },
        model::TransitionNode::Append(k, rs) => { lemma_nf_weaken(g, k); },
        _ => {},
    }
}

/// Members of the class of a normal form are normal forms.
pub proof fn lemma_cls_nf(g: model::Graph, t: nat, v: R)
    requires nf_sum(g, t), tcls(g, t, v),
    ensures regex_nf(v),
{
    lemma_tcls_nf(g, t, v);
}

pub proof fn lemma_not_not(v: R)
    requires regex_nf(v),
    ensures r_not(r_not(v)) == v,
{
    match v {
        Regex::Not(b) => {},
        _ => {},
    }
}

// ===== (N4′) =====

pub proof fn lemma_has_empty_concat(m: Model<R>, a: Seq<R>, b: Seq<R>)
    ensures m.has_empty(a + b) == (m.has_empty(a) || m.has_empty(b)),
{
    if m.has_empty(a + b) {
        let i = choose|i: int| 0 <= i < (a + b).len() && (a + b)[i] == m.empty;
        if i < a.len() { assert(a[i] == (a + b)[i]); } else { assert(b[i - a.len()] == (a + b)[i]); }
    }
    if m.has_empty(a) {
        let i = choose|i: int| 0 <= i < a.len() && a[i] == m.empty;
        assert((a + b)[i] == a[i]);
    }
    if m.has_empty(b) {
        let i = choose|i: int| 0 <= i < b.len() && b[i] == m.empty;
        assert((a + b)[a.len() + i] == b[i]);
    }
}

pub open spec fn all_rnf(xs: Seq<R>) -> bool {
    forall|i: int| 0 <= i < xs.len() ==> regex_nf(#[trigger] xs[i])
}

pub proof fn lemma_all_rnf_concat(a: Seq<R>, b: Seq<R>)
    requires all_rnf(a), all_rnf(b),
    ensures all_rnf(a + b),
{
    assert forall|i: int| 0 <= i < (a + b).len() implies regex_nf(#[trigger] (a + b)[i]) by {
        if i < a.len() { assert((a + b)[i] == a[i]); } else { assert((a + b)[i] == b[i - a.len()]); }
    }
}

/// (N4′): inlining a normalized concatenation of normal forms does not change `N`.
pub proof fn lemma_cat_inline(xs: Seq<R>, ys: Seq<R>, zs: Seq<R>)
    requires all_rnf(xs), all_rnf(ys), all_rnf(zs),
    ensures r_cat(xs + seq![r_cat(ys)] + zs) == r_cat(xs + ys + zs),
{
    let m = m_impl();
    theorem_impl_contract();
    lemma_models_agree();
    let z = r_cat(ys);
    lemma_cat_nf(ys);
    let l = xs + seq![z] + zs;
    let r = xs + ys + zs;
    assert(all_rnf(seq![z])) by { assert forall|i: int| 0 <= i < 1 implies regex_nf(#[trigger] seq![z][i]) by {} }
    lemma_all_rnf_concat(xs, seq![z]);
    lemma_all_rnf_concat(xs + seq![z], zs);
    lemma_all_rnf_concat(xs, ys);
    lemma_all_rnf_concat(xs + ys, zs);
    assert(m.states(l)) by { assert forall|i: int| 0 <= i < l.len() implies m.st(#[trigger] l[i]) by {} }
    assert(m.states(r)) by { assert forall|i: int| 0 <= i < r.len() implies m.st(#[trigger] r[i]) by {} }
    assert(m.states(ys)) by { assert forall|i: int| 0 <= i < ys.len() implies m.st(#[trigger] ys[i]) by {} }
    assert(m.cat_shape(l));
    assert(m.cat_shape(r));
    assert(m.cat_shape(ys));
    lemma_flat_agree(m, pre(), l);
    lemma_flat_agree(m, pre(), r);
    lemma_flat_agree(m, pre(), ys);
    lemma_has_empty_concat(m, xs, seq![z]);
    lemma_has_empty_concat(m, xs + seq![z], zs);
    lemma_has_empty_concat(m, xs, ys);
    lemma_has_empty_concat(m, xs + ys, zs);
    let hz = m.has_empty(seq![z]);
    if m.has_empty(ys) {
        assert(z == m.empty);
        assert(seq![z][0] == m.empty);
    } else if m.has_empty(xs) || m.has_empty(zs) {
    } else {
        lemma_cat_piece(m, ys);
        assert(!hz) by {
            if hz { let i = choose|i: int| 0 <= i < 1 && seq![z][i] == m.empty; }
        }
        lemma_flat_append(m, xs, seq![z]);
        lemma_flat_append(m, xs + seq![z], zs);
        lemma_flat_append(m, xs, ys);
        lemma_flat_append(m, xs + ys, zs);
        lemma_flat_single(m, z);
        lemma_cat_flat_eq(m, l, r);
    }
}

/// `N(w N(ys)) = N(w ys)`.
pub proof fn lemma_cat_nest(w: R, ys: Seq<R>)
    requires regex_nf(w), all_rnf(ys),
    ensures r_cat(seq![w, r_cat(ys)]) == r_cat(seq![w] + ys),
{
    assert(all_rnf(seq![w])) by { assert forall|i: int| 0 <= i < 1 implies regex_nf(#[trigger] seq![w][i]) by {} }
    assert(all_rnf(Seq::<R>::empty()));
    lemma_cat_inline(seq![w], ys, Seq::empty());
    assert(seq![w] + seq![r_cat(ys)] + Seq::<R>::empty() =~= seq![w, r_cat(ys)]);
    assert(seq![w] + ys + Seq::<R>::empty() =~= seq![w] + ys);
}

/// `N(w ε) = w`.
pub proof fn lemma_cat_eps(w: R)
    requires regex_nf(w),
    ensures r_cat(seq![w, Regex::Epsilon]) == w,
{
    theorem_impl_contract();
    lemma_models_agree();
    assert(all_rnf(Seq::<R>::empty()));
    assert(pre().flat(Seq::<R>::empty()) =~= Seq::<R>::empty());
    assert(!pre().has_empty(Seq::<R>::empty()));
    assert(r_cat(Seq::<R>::empty()) == Regex::<model::Test>::Epsilon);
    lemma_cat_nest(w, Seq::empty());
    assert(seq![w] + Seq::<R>::empty() =~= seq![w]);
    lemma_cat_single(m_impl(), w);
}

/// `N(N(w ys) z) = N(w N(ys z))`.
pub proof fn lemma_cat_shift(w: R, ys: Seq<R>, z: R)
    requires regex_nf(w), all_rnf(ys), regex_nf(z),
    ensures r_cat(seq![r_cat(seq![w] + ys), z]) == r_cat(seq![w, r_cat(ys.push(z))]),
{
    let ws = seq![w];
    let zs = seq![z];
    assert(all_rnf(ws)) by { assert forall|i: int| 0 <= i < 1 implies regex_nf(#[trigger] ws[i]) by {} }
    assert(all_rnf(zs)) by { assert forall|i: int| 0 <= i < 1 implies regex_nf(#[trigger] zs[i]) by {} }
    assert(all_rnf(Seq::<R>::empty()));
    lemma_all_rnf_concat(ws, ys);
    lemma_all_rnf_concat(ys, zs);
    assert(ys.push(z) =~= ys + zs);
    lemma_cat_inline(Seq::empty(), ws + ys, zs);
    assert(Seq::<R>::empty() + seq![r_cat(ws + ys)] + zs =~= seq![r_cat(seq![w] + ys), z]);
    assert(Seq::<R>::empty() + (ws + ys) + zs =~= ws + ys + zs);
    lemma_cat_inline(ws, ys + zs, Seq::empty());
    assert(ws + seq![r_cat(ys + zs)] + Seq::<R>::empty() =~= seq![w, r_cat(ys.push(z))]);
    assert(ws + (ys + zs) + Seq::<R>::empty() =~= ws + ys + zs);
}

/// A list state is the normal form of its elements.
pub proof fn lemma_cat_list(ls: Seq<R>)
    requires regex_nf(Regex::Concat(ls)),
    ensures r_cat(ls) == Regex::Concat(ls), all_rnf(ls),
{
    theorem_impl_contract();
    lemma_models_agree();
    let m = m_impl();
    assert(m.atoms(ls)) by {
        assert forall|i: int| 0 <= i < ls.len() implies m.atom(#[trigger] ls[i]) by {}
    }
    lemma_cat_atoms(m, ls);
    assert(all_rnf(ls)) by { assert forall|i: int| 0 <= i < ls.len() implies regex_nf(#[trigger] ls[i]) by {} }
}

} // verus!
