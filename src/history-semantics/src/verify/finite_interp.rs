//! Values of the implemented interpretation (`symbolic.rs` `TransitionId::interpret`): for a
//! normal-form transition `t` (`finite_trans::nf_sum`), the regex returned by `interpret` lifts to
//! a value of `t` (`finite_trans::tval`), i.e. a value under some selection of the branches of
//! its conditionals.
//!
//! The proof mirrors `symbolic::verify::interp_action`/`interp_run` with abstract stacks of value
//! sets ([`iapply`], [`irun`]; a stack entry is a `finite_machine::AV` whose `x` component is the
//! set): an unfinished task pushes the values of its transition ([`vav`]), a finished set node
//! applies the model's set constructor to members of its operands ([`set_av`]), `Not` applies
//! `r_not` ([`not_av`]) and `Append` applies `ccat` ([`cat_av`]). The concrete stack is the
//! stack of singletons of the lifted values ([`lits`]). Every concrete step stays below
//! (`finite_machine::aref`) the abstract run of the configuration it came from ([`istep`]), so
//! the loop keeps the abstract run below the values of the root ([`iinv`]).
use crate::normalize::verify as norm;
use crate::symbolic::verify::{
    child_interp_tasks, interp_append_ids, interp_tasks_wf, transition_children, transition_suffix,
};
use crate::verify::finite_collect::*;
use crate::verify::finite_impl::*;
use crate::verify::finite_link::*;
use crate::verify::finite_machine::*;
use crate::verify::finite_steps::*;
use crate::verify::finite_trans::*;
use junco_core::kernel::verify as model;
use junco_core::kernel::{RegexId, TransitionId};
use vstd::prelude::*;

verus! {

broadcast use junco_core::kernel::verify::group_kernel_views;

pub type Task = (TransitionId, bool);

/// The values of transition `t`.
pub open spec fn vav(g: model::Graph, t: nat) -> AV {
    AV { x: |v: R| tval(g, t, v), y: top_cls() }
}

/// The single value `v`.
pub open spec fn lit_av(v: R) -> AV {
    AV { x: |w: R| w == v, y: top_cls() }
}

pub open spec fn vavs(g: model::Graph, cs: Seq<nat>) -> Seq<AV> {
    Seq::new(cs.len(), |i: int| vav(g, cs[i]))
}

/// `vs` picks a member of every entry of `s`.
pub open spec fn members(s: Seq<AV>, vs: Seq<R>) -> bool {
    vs.len() == s.len() && forall|i: int| #![trigger vs[i]] 0 <= i < s.len() ==> (s[i].x)(vs[i])
}

pub open spec fn set_av(s: Seq<AV>, inter: bool) -> AV {
    AV { x: |v: R| exists|vs: Seq<R>| #[trigger] members(s, vs) && (core().nset)(inter, vs.to_set(), v), y: top_cls() }
}

pub open spec fn not_av(a: AV) -> AV {
    AV { x: |v: R| exists|x: R| (a.x)(x) && v == #[trigger] r_not(x), y: top_cls() }
}

pub open spec fn cat_av(g: model::Graph, a: AV, rs: Seq<nat>) -> AV {
    AV { x: |v: R| exists|w: R| (a.x)(w) && v == #[trigger] ccat(g, w, rs), y: top_cls() }
}

/// Abstract `interp_action`.
pub open spec fn iapply(g: model::Graph, task: Task, s: Seq<AV>) -> Option<Seq<AV>> {
    if !task.1 { Some(s.push(vav(g, task.0@))) } else {
        match g.transitions[task.0@ as int] {
            model::TransitionNode::Union(cs) => if cs.len() > s.len() { None }
                else { Some(s.take(s.len() - cs.len()).push(set_av(s.skip(s.len() - cs.len()), false))) },
            model::TransitionNode::Intersect(cs) => if cs.len() > s.len() { None }
                else { Some(s.take(s.len() - cs.len()).push(set_av(s.skip(s.len() - cs.len()), true))) },
            model::TransitionNode::Not(_) => if s.len() == 0 { None } else { Some(s.drop_last().push(not_av(s.last()))) },
            model::TransitionNode::Append(_, rs) => if s.len() == 0 { None }
                else { Some(s.drop_last().push(cat_av(g, s.last(), rs))) },
            _ => Some(s.push(vav(g, task.0@))),
        }
    }
}

/// Abstract `interp_run`.
pub open spec fn irun(g: model::Graph, tasks: Seq<Task>, s: Seq<AV>) -> Option<Seq<AV>>
    decreases tasks.len(),
{
    if tasks.len() == 0 { Some(s) } else {
        match iapply(g, tasks.last(), s) {
            Some(n) => irun(g, tasks.drop_last(), n),
            None => None,
        }
    }
}

/// The concrete stack: singletons of the lifted values.
pub open spec fn lits(g: model::Graph, values: Seq<RegexId>) -> Seq<AV> {
    Seq::new(values.len(), |i: int| lit_av(model::lift_regex(g, values[i]@)))
}

pub open spec fn itasks(g: model::Graph, tasks: Seq<Task>) -> bool {
    forall|i: int| #![trigger tasks[i]] 0 <= i < tasks.len() ==> nf_sum(g, tasks[i].0@)
}

pub open spec fn ivalues(g: model::Graph, values: Seq<RegexId>) -> bool {
    forall|i: int| #![trigger values[i]] 0 <= i < values.len()
        ==> values[i]@ < g.regexes.len() && regex_nf(model::lift_regex(g, values[i]@))
}

/// A typed configuration: normal-form tasks and values.
#[verifier::opaque]
pub open spec fn ipre(g: model::Graph, tasks: Seq<Task>, values: Seq<RegexId>) -> bool {
    itasks(g, tasks) && ivalues(g, values)
}

/// One step from `(tasks0, values0)` to the typed `(tasks1, values1)`, below its abstract run.
#[verifier::opaque]
pub open spec fn istep(g: model::Graph, tasks0: Seq<Task>, tasks1: Seq<Task>, values0: Seq<RegexId>, values1: Seq<RegexId>) -> bool {
    &&& itasks(g, tasks1) && ivalues(g, values1)
    &&& aref(irun(g, tasks0, lits(g, values0)), irun(g, tasks1, lits(g, values1)))
}

/// The loop invariant of `interpret`: the abstract run is below the values of the root `this`.
#[verifier::opaque]
pub open spec fn iinv(g: model::Graph, this: nat, tasks: Seq<Task>, values: Seq<RegexId>) -> bool {
    &&& itasks(g, tasks) && ivalues(g, values)
    &&& aref(Some(seq![vav(g, this)]), irun(g, tasks, lits(g, values)))
}

// ===== the abstract machine =====

pub proof fn lemma_irun_push(g: model::Graph, tasks: Seq<Task>, task: Task, s: Seq<AV>)
    ensures irun(g, tasks.push(task), s) == match iapply(g, task, s) {
        Some(n) => irun(g, tasks, n),
        None => None,
    },
{
    assert(tasks.push(task).drop_last() =~= tasks);
    assert(tasks.push(task).last() == task);
}

pub proof fn lemma_irun_prefix(g: model::Graph, prefix: Seq<Task>, suffix: Seq<Task>, s: Seq<AV>)
    ensures irun(g, prefix + suffix, s) == match irun(g, suffix, s) {
        Some(next) => irun(g, prefix, next),
        None => None,
    },
    decreases suffix.len(),
{
    if suffix.len() > 0 {
        assert((prefix + suffix).last() == suffix.last());
        assert((prefix + suffix).drop_last() =~= prefix + suffix.drop_last());
        match iapply(g, suffix.last(), s) {
            Some(next) => lemma_irun_prefix(g, prefix, suffix.drop_last(), next),
            None => {},
        }
    } else {
        assert(prefix + suffix =~= prefix);
    }
}

pub proof fn lemma_set_mono(s1: Seq<AV>, s2: Seq<AV>, inter: bool)
    requires stack_le(s1, s2),
    ensures av_le(set_av(s1, inter), set_av(s2, inter)),
{
    assert forall|v: R| #[trigger] (set_av(s1, inter).x)(v) implies (set_av(s2, inter).x)(v) by {
        let vs = choose|vs: Seq<R>| #[trigger] members(s1, vs) && (core().nset)(inter, vs.to_set(), v);
        assert forall|i: int| #![trigger vs[i]] 0 <= i < s2.len() implies (s2[i].x)(vs[i]) by {
            assert(av_le(s1[i], s2[i]));
        }
        assert(members(s2, vs));
    }
}

pub proof fn lemma_not_mono(a: AV, b: AV)
    requires av_le(a, b),
    ensures av_le(not_av(a), not_av(b)),
{
    assert forall|v: R| #[trigger] (not_av(a).x)(v) implies (not_av(b).x)(v) by {
        let x = choose|x: R| (a.x)(x) && v == #[trigger] r_not(x);
        assert((b.x)(x));
    }
}

pub proof fn lemma_cat_mono(g: model::Graph, a: AV, b: AV, rs: Seq<nat>)
    requires av_le(a, b),
    ensures av_le(cat_av(g, a, rs), cat_av(g, b, rs)),
{
    assert forall|v: R| #[trigger] (cat_av(g, a, rs).x)(v) implies (cat_av(g, b, rs).x)(v) by {
        let w = choose|w: R| (a.x)(w) && v == #[trigger] ccat(g, w, rs);
        assert((b.x)(w));
    }
}

pub proof fn lemma_set_step_mono(s1: Seq<AV>, s2: Seq<AV>, k: nat, inter: bool)
    requires stack_le(s1, s2), k <= s2.len(),
    ensures stack_le(s1.take(s1.len() - k).push(set_av(s1.skip(s1.len() - k), inter)),
        s2.take(s2.len() - k).push(set_av(s2.skip(s2.len() - k), inter))),
{
    let start = s2.len() - k;
    lemma_stack_le_sub(s1, s2, 0, start);
    lemma_stack_le_sub(s1, s2, start, s2.len() as int);
    assert(s1.take(start) == s1.subrange(0, start));
    assert(s2.take(start) == s2.subrange(0, start));
    assert(s1.skip(start) == s1.subrange(start, s1.len() as int));
    assert(s2.skip(start) == s2.subrange(start, s2.len() as int));
    lemma_set_mono(s1.skip(start), s2.skip(start), inter);
    lemma_stack_le_push(s1.take(start), s2.take(start), set_av(s1.skip(start), inter), set_av(s2.skip(start), inter));
}

pub proof fn lemma_iapply_mono(g: model::Graph, task: Task, s1: Seq<AV>, s2: Seq<AV>)
    requires stack_le(s1, s2),
    ensures aref(iapply(g, task, s2), iapply(g, task, s1)),
{
    let t = task.0@;
    lemma_av_le_refl(vav(g, t));
    if !task.1 {
        lemma_stack_le_push(s1, s2, vav(g, t), vav(g, t));
    } else {
        match g.transitions[t as int] {
            model::TransitionNode::Union(cs) => { if cs.len() <= s2.len() { lemma_set_step_mono(s1, s2, cs.len(), false); } },
            model::TransitionNode::Intersect(cs) => { if cs.len() <= s2.len() { lemma_set_step_mono(s1, s2, cs.len(), true); } },
            model::TransitionNode::Not(_) => {
                if s2.len() > 0 {
                    let n = s1.len() as int;
                    assert(av_le(s1[n - 1], s2[n - 1]));
                    lemma_not_mono(s1.last(), s2.last());
                    lemma_stack_le_sub(s1, s2, 0, n - 1);
                    assert(s1.drop_last() == s1.subrange(0, n - 1));
                    assert(s2.drop_last() == s2.subrange(0, n - 1));
                    lemma_stack_le_push(s1.drop_last(), s2.drop_last(), not_av(s1.last()), not_av(s2.last()));
                }
            },
            model::TransitionNode::Append(_, rs) => {
                if s2.len() > 0 {
                    let n = s1.len() as int;
                    assert(av_le(s1[n - 1], s2[n - 1]));
                    lemma_cat_mono(g, s1.last(), s2.last(), rs);
                    lemma_stack_le_sub(s1, s2, 0, n - 1);
                    assert(s1.drop_last() == s1.subrange(0, n - 1));
                    assert(s2.drop_last() == s2.subrange(0, n - 1));
                    lemma_stack_le_push(s1.drop_last(), s2.drop_last(), cat_av(g, s1.last(), rs), cat_av(g, s2.last(), rs));
                }
            },
            _ => { lemma_stack_le_push(s1, s2, vav(g, t), vav(g, t)); },
        }
    }
}

pub proof fn lemma_irun_mono(g: model::Graph, tasks: Seq<Task>, s1: Seq<AV>, s2: Seq<AV>)
    requires stack_le(s1, s2),
    ensures aref(irun(g, tasks, s2), irun(g, tasks, s1)),
    decreases tasks.len(),
{
    if tasks.len() > 0 {
        lemma_iapply_mono(g, tasks.last(), s1, s2);
        match iapply(g, tasks.last(), s2) {
            Some(n2) => {
                let n1 = iapply(g, tasks.last(), s1).unwrap();
                lemma_irun_mono(g, tasks.drop_last(), n1, n2);
            },
            None => {},
        }
    }
}

/// Frame rule: replacing a task by an expansion whose abstract run is below the task's abstract
/// action keeps the whole run below.
pub proof fn lemma_iframe(g: model::Graph, prefix: Seq<Task>, expansion: Seq<Task>, task: Task, before: Seq<AV>, after: Seq<AV>)
    requires aref(iapply(g, task, before), irun(g, expansion, after)),
    ensures aref(irun(g, prefix.push(task), before), irun(g, prefix + expansion, after)),
{
    lemma_irun_push(g, prefix, task, before);
    lemma_irun_prefix(g, prefix, expansion, after);
    match iapply(g, task, before) {
        Some(n) => {
            let m = irun(g, expansion, after).unwrap();
            lemma_irun_mono(g, prefix, m, n);
        },
        None => {},
    }
}

/// The unfinished children tasks of a set node push the values of the children in order.
pub proof fn lemma_child_irun(g: model::Graph, id: TransitionId, remaining: nat, s: Seq<AV>)
    requires model::graph_wf(g), id@ < g.transitions.len(), remaining <= transition_children(g, id).len(),
    ensures irun(g, child_interp_tasks(g, id, remaining), s) == Some(s + vavs(g, transition_children(g, id)).skip(remaining as int)),
    decreases transition_children(g, id).len() - remaining,
{
    model::lemma_graph_transition_wf(g, id@);
    let tasks = child_interp_tasks(g, id, remaining);
    let vals = vavs(g, transition_children(g, id));
    if remaining < transition_children(g, id).len() {
        let child = TransitionId::from_view(transition_children(g, id)[remaining as int] as u32);
        assert(child@ == transition_children(g, id)[remaining as int]);
        assert(tasks.last() == (child, false));
        assert(tasks.drop_last() =~= child_interp_tasks(g, id, remaining + 1));
        assert(vav(g, child@) == vals[remaining as int]);
        lemma_child_irun(g, id, remaining + 1, s.push(vals[remaining as int]));
        assert(s.push(vals[remaining as int]) + vals.skip(remaining as int + 1) =~= s + vals.skip(remaining as int));
    } else {
        assert(tasks =~= Seq::<Task>::empty());
        assert(s + vals.skip(remaining as int) =~= s);
    }
}

// ===== stability =====

pub proof fn lemma_vav_stable(a: model::Graph, b: model::Graph, t: nat)
    requires model::graph_wf(a), model::graph_extends(a, b), t < a.transitions.len(),
    ensures vav(a, t) == vav(b, t),
{
    lemma_trans_stable(a, b, t);
    assert(vav(a, t).x =~= vav(b, t).x);
}

pub proof fn lemma_node_stable(a: model::Graph, b: model::Graph, t: nat)
    requires model::graph_extends(a, b), t < a.transitions.len(),
    ensures t < b.transitions.len(), a.transitions[t as int] == b.transitions[t as int],
{
    assert(a.transitions == b.transitions.subrange(0, a.transitions.len() as int));
}

#[verifier::spinoff_prover]
pub proof fn lemma_cat_av_stable(a: model::Graph, b: model::Graph, x: AV, rs: Seq<nat>)
    requires model::graph_wf(a), model::graph_extends(a, b), model::bounded(rs, a.regexes.len()),
    ensures cat_av(a, x, rs) == cat_av(b, x, rs),
{
    hide(r_cat);
    model::lemma_graph_wf_elim(a);
    assert(model::lift_regexes(a, rs) =~= model::lift_regexes(b, rs)) by {
        assert forall|i: int| 0 <= i < rs.len() implies model::lift_regexes(a, rs)[i] == model::lift_regexes(b, rs)[i] by {
            model::lemma_lift_regex_stable(a, b, rs[i]);
        }
    }
    let la = model::lift_regexes(a, rs);
    assert forall|w: R| #[trigger] ccat(a, w, rs) == ccat(b, w, rs) by {
        assert(ccat(a, w, rs) == r_cat(seq![w] + la));
        assert(ccat(b, w, rs) == r_cat(seq![w] + la));
    }
    assert forall|v: R| #[trigger] (cat_av(a, x, rs).x)(v) == (cat_av(b, x, rs).x)(v) by {
        if (cat_av(a, x, rs).x)(v) {
            let w = choose|w: R| (x.x)(w) && v == #[trigger] ccat(a, w, rs);
            assert(v == ccat(b, w, rs));
        }
        if (cat_av(b, x, rs).x)(v) {
            let w = choose|w: R| (x.x)(w) && v == #[trigger] ccat(b, w, rs);
            assert(v == ccat(a, w, rs));
        }
    }
    assert(cat_av(a, x, rs).x =~= cat_av(b, x, rs).x);
}

#[verifier::spinoff_prover]
pub proof fn lemma_iapply_stable(a: model::Graph, b: model::Graph, task: Task, s: Seq<AV>)
    requires model::graph_wf(a), model::graph_extends(a, b), task.0@ < a.transitions.len(),
    ensures iapply(a, task, s) == iapply(b, task, s),
{
    let t = task.0@;
    lemma_node_stable(a, b, t);
    lemma_vav_stable(a, b, t);
    if let model::TransitionNode::Append(_, rs) = a.transitions[t as int] {
        model::lemma_graph_transition_wf(a, t);
        if s.len() > 0 { lemma_cat_av_stable(a, b, s.last(), rs); }
    }
}

pub proof fn lemma_irun_stable(a: model::Graph, b: model::Graph, tasks: Seq<Task>, s: Seq<AV>)
    requires model::graph_wf(a), model::graph_extends(a, b), interp_tasks_wf(a, tasks),
    ensures irun(a, tasks, s) == irun(b, tasks, s),
    decreases tasks.len(),
{
    if tasks.len() > 0 {
        assert(tasks.last() == tasks[tasks.len() - 1]);
        lemma_iapply_stable(a, b, tasks.last(), s);
        assert(interp_tasks_wf(a, tasks.drop_last())) by {
            assert forall|i: int| 0 <= i < tasks.drop_last().len() implies tasks.drop_last()[i].0@ < a.transitions.len() by {
                assert(tasks.drop_last()[i] == tasks[i]);
            }
        }
        match iapply(a, tasks.last(), s) {
            Some(n) => lemma_irun_stable(a, b, tasks.drop_last(), n),
            None => {},
        }
    }
}

pub proof fn lemma_lits_stable(a: model::Graph, b: model::Graph, values: Seq<RegexId>)
    requires model::graph_wf(a), model::graph_extends(a, b), norm::regex_ids_valid(a, values),
    ensures lits(a, values) == lits(b, values),
{
    model::lemma_graph_wf_elim(a);
    assert forall|i: int| 0 <= i < values.len() implies #[trigger] lits(a, values)[i] == lits(b, values)[i] by {
        model::lemma_lift_regex_stable(a, b, values[i]@);
    }
    assert(lits(a, values) =~= lits(b, values));
}

pub proof fn lemma_itasks_valid(g: model::Graph, tasks: Seq<Task>)
    requires itasks(g, tasks),
    ensures interp_tasks_wf(g, tasks),
{
    assert forall|i: int| 0 <= i < tasks.len() implies tasks[i].0@ < g.transitions.len() by {
        assert(nf_sum(g, tasks[i].0@));
    }
}

/// A typed configuration stays typed under graph extension, with the same abstract run.
pub proof fn lemma_ipre_stable(a: model::Graph, b: model::Graph, tasks: Seq<Task>, values: Seq<RegexId>)
    requires model::graph_wf(a), model::graph_extends(a, b), itasks(a, tasks), ivalues(a, values),
    ensures itasks(b, tasks), ivalues(b, values), interp_tasks_wf(a, tasks), norm::regex_ids_valid(a, values),
        lits(a, values) == lits(b, values),
        forall|s: Seq<AV>| #[trigger] irun(a, tasks, s) == irun(b, tasks, s),
{
    model::lemma_graph_wf_elim(a);
    lemma_itasks_valid(a, tasks);
    assert forall|i: int| #![trigger tasks[i]] 0 <= i < tasks.len() implies nf_sum(b, tasks[i].0@) by {
        lemma_trans_stable(a, b, tasks[i].0@);
    }
    assert forall|i: int| #![trigger values[i]] 0 <= i < values.len()
        implies values[i]@ < b.regexes.len() && regex_nf(model::lift_regex(b, values[i]@)) by {
        model::lemma_lift_regex_stable(a, b, values[i]@);
    }
    assert(norm::regex_ids_valid(a, values)) by {
        assert forall|i: int| 0 <= i < values.len() implies values[i]@ < a.regexes.len() by { assert(values[i]@ < a.regexes.len()); }
    }
    lemma_lits_stable(a, b, values);
    assert forall|s: Seq<AV>| #[trigger] irun(a, tasks, s) == irun(b, tasks, s) by {
        lemma_irun_stable(a, b, tasks, s);
    }
}

// ===== stack helpers =====

pub proof fn lemma_lits_push(g: model::Graph, values: Seq<RegexId>, r: RegexId)
    ensures lits(g, values.push(r)) == lits(g, values).push(lit_av(model::lift_regex(g, r@))),
{
    assert(lits(g, values.push(r)) =~= lits(g, values).push(lit_av(model::lift_regex(g, r@))));
}

pub proof fn lemma_lits_split(g: model::Graph, values: Seq<RegexId>, start: int)
    requires 0 <= start <= values.len(),
    ensures lits(g, values.take(start)) == lits(g, values).take(start),
        lits(g, values.skip(start)) == lits(g, values).skip(start),
        start == values.len() - 1 ==> values.take(start) == values.drop_last(),
{
    assert(lits(g, values.take(start)) =~= lits(g, values).take(start));
    assert(lits(g, values.skip(start)) =~= lits(g, values).skip(start));
    if start == values.len() - 1 { assert(values.take(start) =~= values.drop_last()); }
}

pub proof fn lemma_lit_le(v: R, a: AV)
    requires (a.x)(v), a.y == top_cls(),
    ensures av_le(lit_av(v), a),
{}

pub proof fn lemma_itasks_sub(g: model::Graph, pending: Seq<Task>, task: Task)
    requires itasks(g, pending.push(task)),
    ensures itasks(g, pending), nf_sum(g, task.0@),
{
    assert forall|i: int| #![trigger pending[i]] 0 <= i < pending.len() implies nf_sum(g, pending[i].0@) by {
        assert(pending.push(task)[i] == pending[i]);
    }
    assert(pending.push(task)[pending.len() as int] == task);
}

pub proof fn lemma_itasks_push(g: model::Graph, pending: Seq<Task>, task: Task)
    requires itasks(g, pending), nf_sum(g, task.0@),
    ensures itasks(g, pending.push(task)),
{
    assert forall|i: int| #![trigger pending.push(task)[i]] 0 <= i < pending.push(task).len() implies nf_sum(g, pending.push(task)[i].0@) by {
        if i < pending.len() { assert(pending.push(task)[i] == pending[i]); }
    }
}

pub proof fn lemma_ivalues_replace(g: model::Graph, values: Seq<RegexId>, start: int, r: RegexId)
    requires ivalues(g, values), 0 <= start <= values.len(), r@ < g.regexes.len(), regex_nf(model::lift_regex(g, r@)),
    ensures ivalues(g, values.take(start).push(r)),
{
    let n = values.take(start).push(r);
    assert forall|i: int| #![trigger n[i]] 0 <= i < n.len() implies n[i]@ < g.regexes.len() && regex_nf(model::lift_regex(g, n[i]@)) by {
        if i < start { assert(n[i] == values[i]); }
    }
}

/// Shared tail of the step lemmas: the frame rule with the typing of the new configuration.
pub proof fn lemma_istep_close(g: model::Graph, pending: Seq<Task>, task: Task, prior: Seq<RegexId>,
    expansion: Seq<Task>, values: Seq<RegexId>)
    requires aref(iapply(g, task, lits(g, prior)), irun(g, expansion, lits(g, values))),
        itasks(g, pending + expansion), ivalues(g, values),
    ensures istep(g, pending.push(task), pending + expansion, prior, values),
{
    reveal(istep);
    lemma_iframe(g, pending, expansion, task, lits(g, prior), lits(g, values));
}

// ===== the steps of `interpret_step` and `interpret_branch` =====

/// `Const(r)`: push `r`.
pub proof fn lemma_istep_const(b: model::Graph, a: model::Graph, this: TransitionId, finish: bool,
    pending: Seq<Task>, prior: Seq<RegexId>, r: RegexId)
    requires model::graph_wf(b), model::graph_wf(a), model::graph_extends(b, a), this@ < b.transitions.len(),
        b.transitions[this@ as int] == model::TransitionNode::Const(r@),
        ipre(b, pending.push((this, finish)), prior),
    ensures istep(a, pending.push((this, finish)), pending, prior, prior.push(r)),
{
    reveal(ipre);
    let t = this@;
    lemma_ipre_stable(b, a, pending.push((this, finish)), prior);
    lemma_itasks_sub(a, pending, (this, finish));
    lemma_node_stable(b, a, t);
    lemma_nf_children(a, t);
    let l = lits(a, prior);
    let x = model::lift_regex(a, r@);
    lemma_tval(a, t, x);
    lemma_lit_le(x, vav(a, t));
    lemma_stack_le_refl(l);
    lemma_stack_le_push(l, l, lit_av(x), vav(a, t));
    lemma_lits_push(a, prior, r);
    assert(irun(a, Seq::<Task>::empty(), lits(a, prior.push(r))) == Some(lits(a, prior.push(r))));
    assert(pending + Seq::<Task>::empty() =~= pending);
    lemma_ivalues_replace(a, prior, prior.len() as int, r);
    assert(prior.take(prior.len() as int) =~= prior);
    lemma_istep_close(a, pending, (this, finish), prior, Seq::empty(), prior.push(r));
}

/// `If(test, x, y)`: schedule the chosen branch.
pub proof fn lemma_istep_if(b: model::Graph, a: model::Graph, this: TransitionId, finish: bool,
    pending: Seq<Task>, prior: Seq<RegexId>, test: nat, x: TransitionId, y: TransitionId, chosen: TransitionId)
    requires model::graph_wf(b), model::graph_wf(a), model::graph_extends(b, a), this@ < b.transitions.len(),
        b.transitions[this@ as int] == model::TransitionNode::If(test, x@, y@), chosen == x || chosen == y,
        ipre(b, pending.push((this, finish)), prior),
    ensures istep(a, pending.push((this, finish)), pending.push((chosen, false)), prior, prior),
{
    reveal(ipre);
    let t = this@;
    lemma_ipre_stable(b, a, pending.push((this, finish)), prior);
    lemma_itasks_sub(a, pending, (this, finish));
    lemma_node_stable(b, a, t);
    model::lemma_graph_transition_wf(b, t);
    lemma_nf_children(a, t);
    let l = lits(a, prior);
    assert(av_le(vav(a, chosen@), vav(a, t))) by {
        assert forall|v: R| #[trigger] (vav(a, chosen@).x)(v) implies (vav(a, t).x)(v) by {
            assert((tv(a))(chosen@, v) == tval(a, chosen@, v));
            lemma_tval(a, t, v);
        }
    }
    lemma_stack_le_refl(l);
    lemma_stack_le_push(l, l, vav(a, chosen@), vav(a, t));
    let e = seq![(chosen, false)];
    lemma_irun_push(a, Seq::<Task>::empty(), (chosen, false), l);
    assert(Seq::<Task>::empty().push((chosen, false)) == e);
    assert(pending + e =~= pending.push((chosen, false)));
    lemma_itasks_push(a, pending, (chosen, false));
    lemma_istep_close(a, pending, (this, finish), prior, e, prior);
}

/// Unfinished `Not(k)` / `Append(k, rs)`: finish task, then `k`.
pub proof fn lemma_istep_unary(b: model::Graph, a: model::Graph, this: TransitionId, finish: bool,
    pending: Seq<Task>, prior: Seq<RegexId>, inner: TransitionId)
    requires model::graph_wf(b), model::graph_wf(a), model::graph_extends(b, a), this@ < b.transitions.len(), !finish,
        b.transitions[this@ as int] == model::TransitionNode::Not(inner@)
            || b.transitions[this@ as int] == model::TransitionNode::Append(inner@, transition_suffix(b, this)),
        ipre(b, pending.push((this, finish)), prior),
    ensures istep(a, pending.push((this, finish)), pending.push((this, true)).push((inner, false)), prior, prior),
{
    reveal(ipre);
    let t = this@;
    let k = inner@;
    lemma_ipre_stable(b, a, pending.push((this, finish)), prior);
    lemma_itasks_sub(a, pending, (this, finish));
    lemma_node_stable(b, a, t);
    model::lemma_graph_transition_wf(b, t);
    lemma_nf_children(a, t);
    let l = lits(a, prior);
    let e1 = Seq::<Task>::empty().push((this, true));
    let e = e1.push((inner, false));
    lemma_irun_push(a, e1, (inner, false), l);
    lemma_irun_push(a, Seq::<Task>::empty(), (this, true), l.push(vav(a, k)));
    assert(l.push(vav(a, k)).drop_last() =~= l);
    assert(l.push(vav(a, k)).last() == vav(a, k));
    let pushed = match a.transitions[t as int] {
        model::TransitionNode::Not(_) => not_av(vav(a, k)),
        model::TransitionNode::Append(_, rs) => cat_av(a, vav(a, k), rs),
        _ => vav(a, t),
    };
    assert(irun(a, e, l) == Some(l.push(pushed)));
    assert(av_le(pushed, vav(a, t))) by {
        assert forall|v: R| #[trigger] (pushed.x)(v) implies (vav(a, t).x)(v) by {
            lemma_tval(a, t, v);
            match a.transitions[t as int] {
                model::TransitionNode::Not(_) => {
                    let w = choose|w: R| (vav(a, k).x)(w) && v == #[trigger] r_not(w);
                    assert((tv(a))(k, w) == tval(a, k, w));
                    assert(negs(tv(a), t, k, v));
                },
                model::TransitionNode::Append(_, rs) => {
                    let w = choose|w: R| (vav(a, k).x)(w) && v == #[trigger] ccat(a, w, rs);
                    assert((tv(a))(k, w) == tval(a, k, w));
                    assert(apps(a, tv(a), t, k, rs, v));
                },
                _ => {},
            }
        }
    }
    lemma_stack_le_refl(l);
    lemma_stack_le_push(l, l, pushed, vav(a, t));
    assert(pending + e =~= pending.push((this, true)).push((inner, false)));
    lemma_itasks_push(a, pending, (this, true));
    lemma_itasks_push(a, pending.push((this, true)), (inner, false));
    lemma_istep_close(a, pending, (this, finish), prior, e, prior);
}

/// Finished `Not`: replace the top value `x` by `N(¬x)`.
pub proof fn lemma_istep_not(b: model::Graph, a: model::Graph, this: TransitionId,
    pending: Seq<Task>, prior: Seq<RegexId>, out: RegexId)
    requires model::graph_wf(b), model::graph_wf(a), model::graph_extends(b, a), this@ < b.transitions.len(),
        b.transitions[this@ as int] is Not, prior.len() > 0, out@ < a.regexes.len(),
        norm::regex_not_result(a, prior.last()@, out@),
        ipre(b, pending.push((this, true)), prior),
    ensures istep(a, pending.push((this, true)), pending, prior, prior.drop_last().push(out)),
{
    reveal(ipre);
    let t = this@;
    lemma_ipre_stable(b, a, pending.push((this, true)), prior);
    lemma_itasks_sub(a, pending, (this, true));
    lemma_node_stable(b, a, t);
    let l = lits(a, prior);
    let n = prior.len() as int;
    let inner = prior.last();
    assert(prior[n - 1] == inner);
    lemma_not_link(a, inner@, out@);
    let x = model::lift_regex(a, inner@);
    let o = model::lift_regex(a, out@);
    lemma_lits_split(a, prior, n - 1);
    assert(l.last() == lit_av(x));
    assert(l.drop_last() =~= l.take(n - 1));
    let v1 = prior.drop_last().push(out);
    lemma_lits_push(a, prior.drop_last(), out);
    assert((not_av(lit_av(x)).x)(o));
    lemma_lit_le(o, not_av(lit_av(x)));
    lemma_stack_le_refl(l.drop_last());
    lemma_stack_le_push(l.drop_last(), l.drop_last(), lit_av(o), not_av(lit_av(x)));
    assert(iapply(a, (this, true), l) == Some(l.drop_last().push(not_av(l.last()))));
    assert(pending + Seq::<Task>::empty() =~= pending);
    lemma_ivalues_replace(a, prior, n - 1, out);
    lemma_istep_close(a, pending, (this, true), prior, Seq::empty(), v1);
}

/// Finished `Append(k, rs)`: replace the top value `w` by `N(w rs)`.
pub proof fn lemma_istep_append(b: model::Graph, a: model::Graph, this: TransitionId,
    pending: Seq<Task>, prior: Seq<RegexId>, xs: Seq<RegexId>, out: RegexId)
    requires model::graph_wf(b), model::graph_wf(a), model::graph_extends(b, a), this@ < b.transitions.len(),
        b.transitions[this@ as int] is Append, prior.len() > 0,
        norm::regex_ids_valid(b, xs), model::regex_ids(xs) == seq![prior.last()@] + transition_suffix(b, this),
        out@ < a.regexes.len(), norm::regex_concat_result(b, a, xs, out@),
        ipre(b, pending.push((this, true)), prior),
    ensures istep(a, pending.push((this, true)), pending, prior, prior.drop_last().push(out)),
{
    reveal(ipre);
    let t = this@;
    model::lemma_graph_wf_elim(b);
    lemma_ipre_stable(b, a, pending.push((this, true)), prior);
    lemma_itasks_sub(a, pending, (this, true));
    lemma_node_stable(b, a, t);
    lemma_nf_children(a, t);
    model::lemma_graph_transition_wf(b, t);
    let rs = transition_suffix(b, this);
    let l = lits(a, prior);
    let n = prior.len() as int;
    let head = prior.last();
    assert(prior[n - 1] == head);
    lemma_concat_link(b, a, xs, out@);
    interp_append_ids(b, xs, head, rs);
    assert(lifts(b, xs) =~= crate::symbolic::verify::lifted_values(b, xs));
    model::lemma_lift_regex_stable(b, a, head@);
    assert(model::lift_regexes(b, rs) =~= model::lift_regexes(a, rs)) by {
        assert forall|i: int| 0 <= i < rs.len() implies model::lift_regexes(b, rs)[i] == model::lift_regexes(a, rs)[i] by {
            model::lemma_lift_regex_stable(b, a, rs[i]);
        }
    }
    let w = model::lift_regex(a, head@);
    let o = model::lift_regex(a, out@);
    assert(o == ccat(a, w, rs));
    lemma_ccat_nf(a, w, rs);
    lemma_lits_split(a, prior, n - 1);
    assert(l.last() == lit_av(w));
    assert(l.drop_last() =~= l.take(n - 1));
    let v1 = prior.drop_last().push(out);
    lemma_lits_push(a, prior.drop_last(), out);
    assert((cat_av(a, lit_av(w), rs).x)(o));
    lemma_lit_le(o, cat_av(a, lit_av(w), rs));
    lemma_stack_le_refl(l.drop_last());
    lemma_stack_le_push(l.drop_last(), l.drop_last(), lit_av(o), cat_av(a, lit_av(w), rs));
    assert(iapply(a, (this, true), l) == Some(l.drop_last().push(cat_av(a, l.last(), rs))));
    assert(pending + Seq::<Task>::empty() =~= pending);
    lemma_ivalues_replace(a, prior, n - 1, out);
    lemma_istep_close(a, pending, (this, true), prior, Seq::empty(), v1);
}

/// Unfinished set node: finish task, then the children in source order.
pub proof fn lemma_istep_expand(b: model::Graph, a: model::Graph, id: TransitionId, finish: bool,
    pending: Seq<Task>, prior: Seq<RegexId>)
    requires model::graph_wf(b), model::graph_wf(a), model::graph_extends(b, a), id@ < b.transitions.len(), !finish,
        b.transitions[id@ as int] is Union || b.transitions[id@ as int] is Intersect,
        ipre(b, pending.push((id, finish)), prior),
    ensures istep(a, pending.push((id, finish)), pending.push((id, true)) + child_interp_tasks(b, id, 0), prior, prior),
{
    reveal(ipre);
    model::lemma_graph_wf_elim(a);
    let t = id@;
    lemma_ipre_stable(b, a, pending.push((id, finish)), prior);
    lemma_itasks_sub(a, pending, (id, finish));
    lemma_node_stable(b, a, t);
    model::lemma_graph_transition_wf(b, t);
    lemma_nf_children(a, t);
    let cs = transition_children(a, id);
    assert(transition_children(b, id) == cs);
    assert(child_interp_tasks(b, id, 0) =~= child_interp_tasks(a, id, 0));
    let c = child_interp_tasks(a, id, 0);
    let l = lits(a, prior);
    let vals = vavs(a, cs);
    lemma_child_irun(a, id, 0, l);
    assert(vals.skip(0) =~= vals);
    let e0 = Seq::<Task>::empty().push((id, true));
    let e = e0 + c;
    lemma_irun_prefix(a, e0, c, l);
    lemma_irun_push(a, Seq::<Task>::empty(), (id, true), l + vals);
    let inter = a.transitions[t as int] is Intersect;
    assert((l + vals).take(l.len() as int) =~= l);
    assert((l + vals).skip(l.len() as int) =~= vals);
    assert(irun(a, e, l) == Some(l.push(set_av(vals, inter))));
    assert(av_le(set_av(vals, inter), vav(a, t))) by {
        assert forall|v: R| #[trigger] (set_av(vals, inter).x)(v) implies (vav(a, t).x)(v) by {
            let vs = choose|vs: Seq<R>| #[trigger] members(vals, vs) && (core().nset)(inter, vs.to_set(), v);
            lemma_tval(a, t, v);
            assert(kid_vals(tv(a), t, cs, vs)) by {
                assert forall|i: int| 0 <= i < cs.len() implies #[trigger] cs[i] < t && (tv(a))(cs[i], vs[i]) by {
                    assert((vals[i].x)(vs[i]));
                    assert((tv(a))(cs[i], vs[i]) == tval(a, cs[i], vs[i]));
                }
            }
        }
    }
    lemma_stack_le_refl(l);
    lemma_stack_le_push(l, l, set_av(vals, inter), vav(a, t));
    assert(pending + e =~= pending.push((id, true)) + c);
    assert(itasks(a, pending + e)) by {
        let all = pending + e;
        assert forall|i: int| #![trigger all[i]] 0 <= i < all.len() implies nf_sum(a, all[i].0@) by {
            if i < pending.len() { assert(all[i] == pending[i]); }
            else if i == pending.len() { assert(all[i] == (id, true)); }
            else {
                let j = i - pending.len() - 1;
                assert(all[i] == c[j]);
                assert(c[j].0@ == cs[cs.len() - 1 - j]);
                assert(nf_sum(a, cs[cs.len() - 1 - j]));
            }
        }
    }
    lemma_istep_close(a, pending, (id, finish), prior, e, prior);
}

/// The output of the set constructor is a member of the abstract set of its operands.
#[verifier::spinoff_prover]
pub proof fn lemma_set_value(b: model::Graph, a: model::Graph, inter: bool, prior: Seq<RegexId>, start: int, out: RegexId)
    requires model::graph_wf(b), model::graph_wf(a), model::graph_extends(b, a), ivalues(b, prior),
        0 <= start <= prior.len(), out@ < a.regexes.len(),
        norm::regex_set_flat_inputs(b, prior.skip(start), inter) ==> norm::regex_set_shape(b, a, prior.skip(start), inter, out@),
    ensures regex_nf(model::lift_regex(a, out@)),
        av_le(lit_av(model::lift_regex(a, out@)), set_av(lits(a, prior.skip(start)), inter)),
{
    let ch = prior.skip(start);
    model::lemma_graph_wf_elim(b);
    assert(norm::regex_ids_valid(b, ch)) by {
        assert forall|i: int| 0 <= i < ch.len() implies ch[i]@ < b.regexes.len() by {
            assert(ch[i] == prior[start + i]);
        }
    }
    assert(ids_nf(b, ch)) by {
        assert forall|i: int| 0 <= i < ch.len() implies regex_nf(#[trigger] model::lift_regex(b, ch[i]@)) by {
            assert(ch[i] == prior[start + i]);
        }
    }
    lemma_flat_inputs(b, ch, inter);
    lemma_set_link(b, a, ch, inter, out@);
    let o = model::lift_regex(a, out@);
    let vs = lifts(a, ch);
    assert(lifts(b, ch) =~= vs) by {
        assert forall|i: int| 0 <= i < ch.len() implies lifts(b, ch)[i] == vs[i] by {
            assert(ch[i] == prior[start + i]);
            model::lemma_lift_regex_stable(b, a, ch[i]@);
        }
    }
    let s = lits(a, ch);
    assert(members(s, vs)) by {
        assert forall|i: int| #![trigger vs[i]] 0 <= i < s.len() implies (s[i].x)(vs[i]) by {}
    }
    assert((set_av(s, inter).x)(o));
    lemma_lit_le(o, set_av(s, inter));
}

/// Finished set node: replace the operands by the set constructor's output.
#[verifier::spinoff_prover]
pub proof fn lemma_istep_set(b: model::Graph, a: model::Graph, id: TransitionId, inter: bool,
    pending: Seq<Task>, prior: Seq<RegexId>, start: int, out: RegexId)
    requires model::graph_wf(b), model::graph_wf(a), model::graph_extends(b, a), id@ < b.transitions.len(),
        b.transitions[id@ as int] == (if inter { model::TransitionNode::Intersect(transition_children(b, id)) }
            else { model::TransitionNode::Union(transition_children(b, id)) }),
        0 <= start <= prior.len(), prior.len() - start == transition_children(b, id).len(),
        out@ < a.regexes.len(),
        norm::regex_set_flat_inputs(b, prior.skip(start), inter) ==> norm::regex_set_shape(b, a, prior.skip(start), inter, out@),
        ipre(b, pending.push((id, true)), prior),
    ensures istep(a, pending.push((id, true)), pending, prior, prior.take(start).push(out)),
{
    reveal(ipre);
    let t = id@;
    lemma_ipre_stable(b, a, pending.push((id, true)), prior);
    lemma_itasks_sub(a, pending, (id, true));
    lemma_node_stable(b, a, t);
    lemma_set_value(b, a, inter, prior, start, out);
    let l = lits(a, prior);
    let o = model::lift_regex(a, out@);
    lemma_lits_split(a, prior, start);
    lemma_stack_le_refl(l.take(start));
    lemma_stack_le_push(l.take(start), l.take(start), lit_av(o), set_av(l.skip(start), inter));
    lemma_lits_push(a, prior.take(start), out);
    assert(iapply(a, (id, true), l) == Some(l.take(start).push(set_av(l.skip(start), inter))));
    assert(pending + Seq::<Task>::empty() =~= pending);
    lemma_ivalues_replace(a, prior, start, out);
    lemma_istep_close(a, pending, (id, true), prior, Seq::empty(), prior.take(start).push(out));
}

// ===== the loop of `interpret` =====

pub proof fn lemma_iinit(g: model::Graph, this: TransitionId)
    requires nf_sum(g, this@),
    ensures iinv(g, this@, seq![(this, false)], Seq::empty()),
{
    reveal(iinv);
    let ts = seq![(this, false)];
    assert(itasks(g, ts)) by {
        assert forall|i: int| #![trigger ts[i]] 0 <= i < ts.len() implies nf_sum(g, ts[i].0@) by { assert(ts[i] == (this, false)); }
    }
    lemma_irun_push(g, Seq::<Task>::empty(), (this, false), lits(g, Seq::empty()));
    assert(Seq::<Task>::empty().push((this, false)) == ts);
    assert(lits(g, Seq::<RegexId>::empty()) =~= Seq::<AV>::empty());
    assert(Seq::<AV>::empty().push(vav(g, this@)) == seq![vav(g, this@)]);
    lemma_stack_le_refl(seq![vav(g, this@)]);
}

/// One iteration of the loop of `interpret` keeps the invariant.
pub proof fn lemma_iloop(b: model::Graph, a: model::Graph, this: nat, pending: Seq<Task>, prior: Seq<RegexId>,
    tasks: Seq<Task>, values: Seq<RegexId>)
    requires model::graph_wf(b), model::graph_extends(b, a), this < b.transitions.len(),
        iinv(b, this, pending, prior),
        ipre(b, pending, prior) ==> istep(a, pending, tasks, prior, values),
    ensures iinv(a, this, tasks, values),
{
    reveal(iinv);
    reveal(ipre);
    reveal(istep);
    lemma_ipre_stable(b, a, pending, prior);
    lemma_vav_stable(b, a, this);
    lemma_aref_trans(Some(seq![vav(a, this)]), irun(a, pending, lits(a, prior)), irun(a, tasks, lits(a, values)));
}

/// At the end of the loop, the single value is a value of the root.
pub proof fn lemma_ifinal(g: model::Graph, this: nat, values: Seq<RegexId>)
    requires iinv(g, this, Seq::empty(), values),
    ensures values.len() == 1, tval(g, this, model::lift_regex(g, values[0]@)),
{
    reveal(iinv);
    let s = lits(g, values);
    assert(irun(g, Seq::<Task>::empty(), s) == Some(s));
    assert(stack_le(s, seq![vav(g, this)]));
    assert(av_le(s[0], seq![vav(g, this)][0]));
    assert((s[0].x)(model::lift_regex(g, values[0]@)));
}

// ===== successor cache entries =====

/// A successor-cache entry `r` for transition `t` is a value of `t` when `t` is a normal form
/// (`progress::verify::successor_entries_wf`).
#[verifier::opaque]
pub open spec fn entry_val(g: model::Graph, t: nat, r: nat) -> bool {
    nf_sum(g, t) ==> tval(g, t, model::lift_regex(g, r))
}

pub proof fn lemma_entry_val_intro(a: model::Graph, b: model::Graph, t: nat, r: nat)
    requires model::graph_wf(a), model::graph_extends(a, b), t < a.transitions.len(),
        nf_sum(a, t) ==> tval(b, t, model::lift_regex(b, r)),
    ensures entry_val(b, t, r),
{
    reveal(entry_val);
    lemma_trans_stable(a, b, t);
}

pub proof fn lemma_entry_val_stable(a: model::Graph, b: model::Graph, t: nat, r: nat)
    requires model::graph_wf(a), model::graph_extends(a, b), t < a.transitions.len(), r < a.regexes.len(), entry_val(a, t, r),
    ensures entry_val(b, t, r),
{
    reveal(entry_val);
    model::lemma_graph_wf_elim(a);
    lemma_trans_stable(a, b, t);
    model::lemma_lift_regex_stable(a, b, r);
}

pub proof fn lemma_entry_val_elim(g: model::Graph, t: nat, r: nat)
    requires entry_val(g, t, r), nf_sum(g, t),
    ensures tval(g, t, model::lift_regex(g, r)),
{
    reveal(entry_val);
}

} // verus!
