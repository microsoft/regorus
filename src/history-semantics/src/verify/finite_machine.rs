//! Abstract interpretation of the transition normalizer's action machine (`normalize.rs`
//! `Action`): every stack value is abstracted by its class and sum class ([`av_of`]), every
//! action by the corresponding operation on classes ([`aapply`], mirroring
//! `normalize::verify::guarded_apply`), and a run by [`arun`]. The machine invariant is that the
//! abstract run of the remaining tasks on the abstract stack is below (`aref`) the abstract run
//! of the original action: then the result's class is bounded by the original action's
//! abstract effect.
use crate::normalize::verify::{self as norm, ActionShape};
use crate::verify::finite_impl::*;
use crate::verify::finite_trans::*;
use junco_core::kernel::verify as model;
use junco_core::verify::history_specs::Regex;
use vstd::prelude::*;

verus! {

/// An abstract value: a class and a sum class.
pub struct AV { pub x: spec_fn(R) -> bool, pub y: spec_fn(R) -> bool }

pub open spec fn av_le(a: AV, b: AV) -> bool {
    &&& forall|v: R| #[trigger] (a.x)(v) ==> (b.x)(v)
    &&& forall|v: R| #[trigger] (a.y)(v) ==> (b.y)(v)
}

pub open spec fn stack_le(s: Seq<AV>, t: Seq<AV>) -> bool {
    s.len() == t.len() && forall|i: int| 0 <= i < s.len() ==> #[trigger] av_le(s[i], t[i])
}

/// `after` is defined whenever `before` is, and below it pointwise.
pub open spec fn aref(before: Option<Seq<AV>>, after: Option<Seq<AV>>) -> bool {
    match before {
        None => true,
        Some(l) => match after { Some(r) => stack_le(r, l), None => false },
    }
}

pub open spec fn av_of(g: model::Graph, t: nat) -> AV {
    AV { x: |v: R| tcls(g, t, v), y: |v: R| ycls(g, t, v) }
}

pub open spec fn avs(g: model::Graph, ids: Seq<nat>) -> Seq<AV> {
    ids.map(|i: int, t: nat| av_of(g, t))
}

pub open spec fn any_x(s: Seq<AV>, w: R) -> bool {
    exists|i: int| #![trigger s[i]] 0 <= i < s.len() && (s[i].x)(w)
}

pub open spec fn any_y(s: Seq<AV>, w: R) -> bool {
    exists|i: int| #![trigger s[i]] 0 <= i < s.len() && (s[i].y)(w)
}

pub open spec fn neg_of(a: AV, w: R) -> bool {
    exists|x: R| (a.x)(x) && w == #[trigger] r_not(x)
}

/// `N(w s)`.
pub open spec fn cat_r(w: R, s: R) -> R {
    r_cat(seq![w, s])
}

pub open spec fn app_of(a: AV, s: R, v: R) -> bool {
    exists|w: R| (a.x)(w) && v == #[trigger] cat_r(w, s)
}

pub open spec fn top_cls() -> spec_fn(R) -> bool {
    |v: R| true
}

pub open spec fn av_if(a: AV, b: AV) -> AV {
    AV { x: |v: R| (a.x)(v) || (b.x)(v), y: |v: R| (a.y)(v) || (b.y)(v) }
}

pub open spec fn av_union(s: Seq<AV>) -> AV {
    AV { x: |v: R| rconst(v) || any_x(s, v), y: |v: R| cl(false, |w: R| any_y(s, w), v) }
}

pub open spec fn av_meet(s: Seq<AV>) -> AV {
    AV { x: |v: R| cl(true, |w: R| any_x(s, w), v), y: top_cls() }
}

pub open spec fn av_neg(a: AV) -> AV {
    AV { x: |v: R| cl(true, |w: R| neg_of(a, w), v), y: top_cls() }
}

pub open spec fn av_app(a: AV, s: R) -> AV {
    AV { x: |v: R| rconst(v) || app_of(a, s, v), y: top_cls() }
}

/// Abstract effect of an action (mirrors `guarded_apply`).
pub open spec fn aapply(g: model::Graph, action: ActionShape, s: Seq<AV>) -> Option<Seq<AV>> {
    match action {
        ActionShape::Clean(id, path) => Some(s.push(av_of(g, id))),
        ActionShape::Not(id) => Some(s.push(av_neg(av_of(g, id)))),
        ActionShape::Append(id, r) => Some(s.push(av_app(av_of(g, id), model::lift_regex(g, r)))),
        ActionShape::Pair(a, b) => Some(s.push(av_meet(seq![av_of(g, a), av_of(g, b)]))),
        ActionShape::Union(count) => if count <= s.len() {
            let start = s.len() as int - count as int;
            Some(s.take(start).push(av_union(s.subrange(start, s.len() as int))))
        } else { None },
        ActionShape::Intersect(count) => if count <= s.len() {
            let start = s.len() as int - count as int;
            Some(s.take(start).push(av_meet(s.subrange(start, s.len() as int))))
        } else { None },
        ActionShape::If(test) => if s.len() >= 2 {
            Some(s.take(s.len() as int - 2).push(av_if(s[s.len() as int - 2], s.last())))
        } else { None },
        ActionShape::CleanIf(test, path) => if s.len() >= 2 {
            Some(s.take(s.len() as int - 2).push(av_if(s[s.len() as int - 2], s.last())))
        } else { None },
        ActionShape::Fold(terms, index) => if index == 0 {
            Some(s.push(av_meet(avs(g, terms))))
        } else if index < terms.len() {
            if s.len() > 0 {
                Some(s.drop_last().push(av_meet(seq![s.last()] + avs(g, terms.subrange(index as int, terms.len() as int)))))
            } else { None }
        } else { Some(s) },
        ActionShape::NotResult => if s.len() > 0 { Some(s.drop_last().push(av_neg(s.last()))) } else { None },
        ActionShape::AppendResult(r) => if s.len() > 0 {
            Some(s.drop_last().push(av_app(s.last(), model::lift_regex(g, r))))
        } else { None },
        ActionShape::SwapThen => if s.len() >= 2 {
            Some(s.take(s.len() as int - 2).push(s.last()).push(s[s.len() as int - 2]))
        } else { None },
    }
}

pub open spec fn arun(g: model::Graph, tasks: Seq<ActionShape>, s: Seq<AV>) -> Option<Seq<AV>>
    decreases tasks.len(),
{
    if tasks.len() == 0 { Some(s) } else {
        match aapply(g, tasks.last(), s) {
            Some(n) => arun(g, tasks.drop_last(), n),
            None => None,
        }
    }
}

// ===== order =====

pub proof fn lemma_av_le_refl(a: AV)
    ensures av_le(a, a),
{}

pub proof fn lemma_av_le_trans(a: AV, b: AV, c: AV)
    requires av_le(a, b), av_le(b, c),
    ensures av_le(a, c),
{
    assert forall|v: R| #[trigger] (a.x)(v) implies (c.x)(v) by { assert((b.x)(v)); }
    assert forall|v: R| #[trigger] (a.y)(v) implies (c.y)(v) by { assert((b.y)(v)); }
}

pub proof fn lemma_stack_le_refl(s: Seq<AV>)
    ensures stack_le(s, s),
{
    assert forall|i: int| 0 <= i < s.len() implies #[trigger] av_le(s[i], s[i]) by { lemma_av_le_refl(s[i]); }
}

pub proof fn lemma_stack_le_trans(a: Seq<AV>, b: Seq<AV>, c: Seq<AV>)
    requires stack_le(a, b), stack_le(b, c),
    ensures stack_le(a, c),
{
    assert forall|i: int| 0 <= i < a.len() implies #[trigger] av_le(a[i], c[i]) by {
        assert(av_le(a[i], b[i]));
        assert(av_le(b[i], c[i]));
        lemma_av_le_trans(a[i], b[i], c[i]);
    }
}

pub proof fn lemma_aref_trans(a: Option<Seq<AV>>, b: Option<Seq<AV>>, c: Option<Seq<AV>>)
    requires aref(a, b), aref(b, c),
    ensures aref(a, c),
{
    match a {
        None => {},
        Some(l) => match (b, c) {
            (Some(m), Some(r)) => lemma_stack_le_trans(r, m, l),
            _ => {},
        },
    }
}

pub proof fn lemma_stack_le_push(s: Seq<AV>, t: Seq<AV>, a: AV, b: AV)
    requires stack_le(s, t), av_le(a, b),
    ensures stack_le(s.push(a), t.push(b)),
{
    assert forall|i: int| 0 <= i < s.push(a).len() implies #[trigger] av_le(s.push(a)[i], t.push(b)[i]) by {
        if i < s.len() { assert(s.push(a)[i] == s[i]); assert(t.push(b)[i] == t[i]); }
    }
}

pub proof fn lemma_stack_le_sub(s: Seq<AV>, t: Seq<AV>, start: int, end: int)
    requires stack_le(s, t), 0 <= start <= end <= s.len(),
    ensures stack_le(s.subrange(start, end), t.subrange(start, end)),
{
    assert forall|i: int| 0 <= i < s.subrange(start, end).len()
        implies #[trigger] av_le(s.subrange(start, end)[i], t.subrange(start, end)[i]) by {
        assert(s.subrange(start, end)[i] == s[start + i]);
        assert(t.subrange(start, end)[i] == t[start + i]);
    }
}

// ===== monotonicity of the operations =====

pub proof fn lemma_any_mono(s: Seq<AV>, t: Seq<AV>)
    requires stack_le(s, t),
    ensures
        forall|w: R| #[trigger] any_x(s, w) ==> any_x(t, w),
        forall|w: R| #[trigger] any_y(s, w) ==> any_y(t, w),
{
    assert forall|w: R| #[trigger] any_x(s, w) implies any_x(t, w) by {
        let i = choose|i: int| #![trigger s[i]] 0 <= i < s.len() && (s[i].x)(w);
        assert(av_le(s[i], t[i]));
        assert((t[i].x)(w));
    }
    assert forall|w: R| #[trigger] any_y(s, w) implies any_y(t, w) by {
        let i = choose|i: int| #![trigger s[i]] 0 <= i < s.len() && (s[i].y)(w);
        assert(av_le(s[i], t[i]));
        assert((t[i].y)(w));
    }
}

pub proof fn lemma_union_mono(s: Seq<AV>, t: Seq<AV>)
    requires stack_le(s, t),
    ensures av_le(av_union(s), av_union(t)),
{
    lemma_any_mono(s, t);
    assert forall|v: R| #[trigger] (av_union(s).y)(v) implies (av_union(t).y)(v) by {
        lemma_cl_mono(false, |w: R| any_y(s, w), |w: R| any_y(t, w), v);
    }
}

pub proof fn lemma_meet_mono(s: Seq<AV>, t: Seq<AV>)
    requires stack_le(s, t),
    ensures av_le(av_meet(s), av_meet(t)),
{
    lemma_any_mono(s, t);
    assert forall|v: R| #[trigger] (av_meet(s).x)(v) implies (av_meet(t).x)(v) by {
        lemma_cl_mono(true, |w: R| any_x(s, w), |w: R| any_x(t, w), v);
    }
}

pub proof fn lemma_neg_mono(a: AV, b: AV)
    requires av_le(a, b),
    ensures av_le(av_neg(a), av_neg(b)),
{
    assert forall|w: R| #[trigger] neg_of(a, w) implies neg_of(b, w) by {
        let x = choose|x: R| (a.x)(x) && w == #[trigger] r_not(x);
        assert((b.x)(x));
    }
    assert forall|v: R| #[trigger] (av_neg(a).x)(v) implies (av_neg(b).x)(v) by {
        lemma_cl_mono(true, |w: R| neg_of(a, w), |w: R| neg_of(b, w), v);
    }
}

pub proof fn lemma_app_mono(a: AV, b: AV, s: R)
    requires av_le(a, b),
    ensures av_le(av_app(a, s), av_app(b, s)),
{
    assert forall|v: R| #[trigger] (av_app(a, s).x)(v) implies (av_app(b, s).x)(v) by {
        if app_of(a, s, v) {
            let w = choose|w: R| (a.x)(w) && v == #[trigger] cat_r(w, s);
            assert((b.x)(w));
        }
    }
}

pub proof fn lemma_if_mono(a: AV, b: AV, c: AV, d: AV)
    requires av_le(a, c), av_le(b, d),
    ensures av_le(av_if(a, b), av_if(c, d)),
{}

pub proof fn lemma_aapply_mono(g: model::Graph, action: ActionShape, s1: Seq<AV>, s2: Seq<AV>)
    requires stack_le(s1, s2),
    ensures aref(aapply(g, action, s2), aapply(g, action, s1)),
{
    match action {
        ActionShape::Clean(id, path) => { lemma_stack_le_push(s1, s2, av_of(g, id), av_of(g, id)); },
        ActionShape::Not(id) => { lemma_stack_le_push(s1, s2, av_neg(av_of(g, id)), av_neg(av_of(g, id))); },
        ActionShape::Append(id, r) => {
            let a = av_app(av_of(g, id), model::lift_regex(g, r));
            lemma_stack_le_push(s1, s2, a, a);
        },
        ActionShape::Pair(a, b) => {
            let m = av_meet(seq![av_of(g, a), av_of(g, b)]);
            lemma_stack_le_push(s1, s2, m, m);
        },
        ActionShape::Union(count) => {
            if count <= s2.len() {
                let start = s2.len() as int - count as int;
                lemma_stack_le_sub(s1, s2, 0, start);
                lemma_stack_le_sub(s1, s2, start, s2.len() as int);
                lemma_union_mono(s1.subrange(start, s1.len() as int), s2.subrange(start, s2.len() as int));
                assert(s1.take(start) == s1.subrange(0, start));
                assert(s2.take(start) == s2.subrange(0, start));
                lemma_stack_le_push(s1.take(start), s2.take(start),
                    av_union(s1.subrange(start, s1.len() as int)), av_union(s2.subrange(start, s2.len() as int)));
            }
        },
        ActionShape::Intersect(count) => {
            if count <= s2.len() {
                let start = s2.len() as int - count as int;
                lemma_stack_le_sub(s1, s2, 0, start);
                lemma_stack_le_sub(s1, s2, start, s2.len() as int);
                lemma_meet_mono(s1.subrange(start, s1.len() as int), s2.subrange(start, s2.len() as int));
                assert(s1.take(start) == s1.subrange(0, start));
                assert(s2.take(start) == s2.subrange(0, start));
                lemma_stack_le_push(s1.take(start), s2.take(start),
                    av_meet(s1.subrange(start, s1.len() as int)), av_meet(s2.subrange(start, s2.len() as int)));
            }
        },
        ActionShape::If(test) => { lemma_aapply_if(s1, s2); },
        ActionShape::CleanIf(test, path) => { lemma_aapply_if(s1, s2); },
        ActionShape::Fold(terms, index) => {
            if index == 0 {
                lemma_stack_le_push(s1, s2, av_meet(avs(g, terms)), av_meet(avs(g, terms)));
            } else if index < terms.len() {
                if s2.len() > 0 {
                    let rest = avs(g, terms.subrange(index as int, terms.len() as int));
                    lemma_stack_le_sub(s1, s2, 0, s1.len() - 1);
                    assert(av_le(s1[s1.len() - 1], s2[s2.len() - 1]));
                    let l1 = seq![s1.last()] + rest;
                    let l2 = seq![s2.last()] + rest;
                    assert(stack_le(l1, l2)) by {
                        assert forall|i: int| 0 <= i < l1.len() implies #[trigger] av_le(l1[i], l2[i]) by {
                            if i == 0 { } else { assert(l1[i] == rest[i - 1]); assert(l2[i] == rest[i - 1]); lemma_av_le_refl(rest[i - 1]); }
                        }
                    }
                    lemma_meet_mono(l1, l2);
                    assert(s1.drop_last() == s1.subrange(0, s1.len() - 1));
                    assert(s2.drop_last() == s2.subrange(0, s2.len() - 1));
                    lemma_stack_le_push(s1.drop_last(), s2.drop_last(), av_meet(l1), av_meet(l2));
                }
            }
        },
        ActionShape::NotResult => {
            if s2.len() > 0 {
                assert(av_le(s1[s1.len() - 1], s2[s2.len() - 1]));
                lemma_neg_mono(s1.last(), s2.last());
                lemma_stack_le_sub(s1, s2, 0, s1.len() - 1);
                assert(s1.drop_last() == s1.subrange(0, s1.len() - 1));
                assert(s2.drop_last() == s2.subrange(0, s2.len() - 1));
                lemma_stack_le_push(s1.drop_last(), s2.drop_last(), av_neg(s1.last()), av_neg(s2.last()));
            }
        },
        ActionShape::AppendResult(r) => {
            if s2.len() > 0 {
                assert(av_le(s1[s1.len() - 1], s2[s2.len() - 1]));
                lemma_app_mono(s1.last(), s2.last(), model::lift_regex(g, r));
                lemma_stack_le_sub(s1, s2, 0, s1.len() - 1);
                assert(s1.drop_last() == s1.subrange(0, s1.len() - 1));
                assert(s2.drop_last() == s2.subrange(0, s2.len() - 1));
                lemma_stack_le_push(s1.drop_last(), s2.drop_last(),
                    av_app(s1.last(), model::lift_regex(g, r)), av_app(s2.last(), model::lift_regex(g, r)));
            }
        },
        ActionShape::SwapThen => {
            if s2.len() >= 2 {
                let n = s1.len() as int;
                lemma_stack_le_sub(s1, s2, 0, n - 2);
                assert(s1.take(n - 2) == s1.subrange(0, n - 2));
                assert(s2.take(n - 2) == s2.subrange(0, n - 2));
                assert(av_le(s1[n - 1], s2[n - 1]));
                assert(av_le(s1[n - 2], s2[n - 2]));
                lemma_stack_le_push(s1.take(n - 2), s2.take(n - 2), s1.last(), s2.last());
                lemma_stack_le_push(s1.take(n - 2).push(s1.last()), s2.take(n - 2).push(s2.last()), s1[n - 2], s2[n - 2]);
            }
        },
    }
}

pub proof fn lemma_aapply_if(s1: Seq<AV>, s2: Seq<AV>)
    requires stack_le(s1, s2),
    ensures s2.len() >= 2 ==> stack_le(
        s1.take(s1.len() as int - 2).push(av_if(s1[s1.len() as int - 2], s1.last())),
        s2.take(s2.len() as int - 2).push(av_if(s2[s2.len() as int - 2], s2.last()))),
{
    if s2.len() >= 2 {
        let n = s1.len() as int;
        lemma_stack_le_sub(s1, s2, 0, n - 2);
        assert(s1.take(n - 2) == s1.subrange(0, n - 2));
        assert(s2.take(n - 2) == s2.subrange(0, n - 2));
        assert(av_le(s1[n - 1], s2[n - 1]));
        assert(av_le(s1[n - 2], s2[n - 2]));
        lemma_if_mono(s1[n - 2], s1.last(), s2[n - 2], s2.last());
        lemma_stack_le_push(s1.take(n - 2), s2.take(n - 2), av_if(s1[n - 2], s1.last()), av_if(s2[n - 2], s2.last()));
    }
}

pub proof fn lemma_arun_mono(g: model::Graph, tasks: Seq<ActionShape>, s1: Seq<AV>, s2: Seq<AV>)
    requires stack_le(s1, s2),
    ensures aref(arun(g, tasks, s2), arun(g, tasks, s1)),
    decreases tasks.len(),
{
    if tasks.len() > 0 {
        lemma_aapply_mono(g, tasks.last(), s1, s2);
        match aapply(g, tasks.last(), s2) {
            Some(n2) => {
                let n1 = aapply(g, tasks.last(), s1).unwrap();
                lemma_arun_mono(g, tasks.drop_last(), n1, n2);
            },
            None => {},
        }
    }
}

pub proof fn lemma_arun_prefix(g: model::Graph, prefix: Seq<ActionShape>, suffix: Seq<ActionShape>, s: Seq<AV>)
    ensures arun(g, prefix + suffix, s) == match arun(g, suffix, s) {
        Some(next) => arun(g, prefix, next),
        None => None,
    },
    decreases suffix.len(),
{
    if suffix.len() > 0 {
        assert((prefix + suffix).last() == suffix.last());
        assert((prefix + suffix).drop_last() =~= prefix + suffix.drop_last());
        match aapply(g, suffix.last(), s) {
            Some(next) => lemma_arun_prefix(g, prefix, suffix.drop_last(), next),
            None => {},
        }
    } else {
        assert(prefix + suffix =~= prefix);
    }
}

/// Frame rule: replacing an action by an expansion whose abstract run is below the action's
/// abstract effect keeps the whole run below.
pub proof fn lemma_frame(g: model::Graph, prefix: Seq<ActionShape>, expansion: Seq<ActionShape>, action: ActionShape,
    before: Seq<AV>, after: Seq<AV>)
    requires aref(aapply(g, action, before), arun(g, expansion, after)),
    ensures aref(arun(g, prefix.push(action), before), arun(g, prefix + expansion, after)),
{
    lemma_arun_prefix(g, prefix, seq![action], before);
    lemma_arun_prefix(g, prefix, expansion, after);
    assert(prefix.push(action) =~= prefix + seq![action]);
    assert(seq![action].last() == action);
    assert(seq![action].drop_last() =~= Seq::<ActionShape>::empty());
    match aapply(g, action, before) {
        Some(n) => {
            assert(arun(g, seq![action], before) == arun(g, Seq::<ActionShape>::empty(), n));
            let m = arun(g, expansion, after).unwrap();
            lemma_arun_mono(g, prefix, m, n);
        },
        None => {
            assert(arun(g, seq![action], before) is None);
        },
    }
}

// ===== stability =====

pub proof fn lemma_av_stable(a: model::Graph, b: model::Graph, t: nat)
    requires model::graph_wf(a), model::graph_extends(a, b), t < a.transitions.len(),
    ensures av_of(a, t) == av_of(b, t),
{
    lemma_trans_stable(a, b, t);
    assert(av_of(a, t).x =~= av_of(b, t).x);
    assert(av_of(a, t).y =~= av_of(b, t).y);
}

pub proof fn lemma_avs_stable(a: model::Graph, b: model::Graph, ids: Seq<nat>)
    requires model::graph_wf(a), model::graph_extends(a, b), model::bounded(ids, a.transitions.len()),
    ensures avs(a, ids) == avs(b, ids),
{
    assert forall|i: int| 0 <= i < ids.len() implies #[trigger] avs(a, ids)[i] == avs(b, ids)[i] by {
        lemma_av_stable(a, b, ids[i]);
    }
    assert(avs(a, ids) =~= avs(b, ids));
}

pub proof fn lemma_aapply_stable(a: model::Graph, b: model::Graph, action: ActionShape, s: Seq<AV>)
    requires model::graph_wf(a), model::graph_extends(a, b), norm::transition_action_valid(a, action),
    ensures aapply(a, action, s) == aapply(b, action, s),
{
    model::lemma_graph_wf_elim(a);
    match action {
        ActionShape::Clean(id, path) => { lemma_av_stable(a, b, id); },
        ActionShape::Not(id) => { lemma_av_stable(a, b, id); },
        ActionShape::Append(id, r) => { lemma_av_stable(a, b, id); model::lemma_lift_regex_stable(a, b, r); },
        ActionShape::Pair(x, y) => { lemma_av_stable(a, b, x); lemma_av_stable(a, b, y); },
        ActionShape::Fold(terms, index) => {
            lemma_avs_stable(a, b, terms);
            if index < terms.len() {
                let sub = terms.subrange(index as int, terms.len() as int);
                assert(model::bounded(sub, a.transitions.len())) by {
                    assert forall|j: int| 0 <= j < sub.len() implies #[trigger] sub[j] < a.transitions.len() by {
                        assert(sub[j] == terms[index + j]);
                    }
                }
                lemma_avs_stable(a, b, sub);
            }
        },
        ActionShape::AppendResult(r) => { model::lemma_lift_regex_stable(a, b, r); },
        _ => {},
    }
}

pub proof fn lemma_arun_stable(a: model::Graph, b: model::Graph, tasks: Seq<ActionShape>, s: Seq<AV>)
    requires model::graph_wf(a), model::graph_extends(a, b), norm::transition_tasks_valid(a, tasks),
    ensures arun(a, tasks, s) == arun(b, tasks, s),
    decreases tasks.len(),
{
    if tasks.len() > 0 {
        assert(norm::transition_action_valid(a, tasks[tasks.len() - 1]));
        lemma_aapply_stable(a, b, tasks.last(), s);
        assert(norm::transition_tasks_valid(a, tasks.drop_last())) by {
            assert forall|i: int| 0 <= i < tasks.drop_last().len() implies norm::transition_action_valid(a, tasks.drop_last()[i]) by {
                assert(tasks.drop_last()[i] == tasks[i]);
            }
        }
        match aapply(a, tasks.last(), s) {
            Some(n) => lemma_arun_stable(a, b, tasks.drop_last(), n),
            None => {},
        }
    }
}

// ===== members of nested sets =====

/// `x` is reached from `t` through nested unions (`!inter`) or intersections (`inter`).
pub open spec fn tpiece(g: model::Graph, t: nat, inter: bool, x: nat) -> bool
    decreases t,
{
    x == t || (t < g.transitions.len() && match g.transitions[t as int] {
        model::TransitionNode::Union(cs) => !inter
            && exists|i: int| #![trigger cs[i]] 0 <= i < cs.len() && cs[i] < t && tpiece(g, cs[i], inter, x),
        model::TransitionNode::Intersect(cs) => inter
            && exists|i: int| #![trigger cs[i]] 0 <= i < cs.len() && cs[i] < t && tpiece(g, cs[i], inter, x),
        _ => false,
    })
}

/// `x` is a member of the nested sets of the inputs `orig`.
pub open spec fn piece_of(g: model::Graph, orig: Seq<nat>, inter: bool, x: nat) -> bool {
    exists|i: int| #![trigger orig[i]] 0 <= i < orig.len() && tpiece(g, orig[i], inter, x)
}

/// The node `id` (a child of a same-kind set node `x`) is reached as well.
pub proof fn lemma_tpiece_child(g: model::Graph, root: nat, inter: bool, x: nat, cs: Seq<nat>, i: int)
    requires model::graph_wf(g), root < g.transitions.len(), x < g.transitions.len(), tpiece(g, root, inter, x),
        g.transitions[x as int] == (if inter { model::TransitionNode::Intersect(cs) } else { model::TransitionNode::Union(cs) }),
        0 <= i < cs.len(),
    ensures tpiece(g, root, inter, cs[i]),
    decreases root,
{
    model::lemma_graph_transition_wf(g, x);
    assert(cs[i] < x);
    if x == root {
        assert(tpiece(g, cs[i], inter, cs[i]));
    } else {
        match g.transitions[root as int] {
            model::TransitionNode::Union(rs) => {
                let j = choose|j: int| #![trigger rs[j]] 0 <= j < rs.len() && rs[j] < root && tpiece(g, rs[j], inter, x);
                lemma_tpiece_child(g, rs[j], inter, x, cs, i);
                assert(tpiece(g, rs[j], inter, cs[i]));
            },
            model::TransitionNode::Intersect(rs) => {
                let j = choose|j: int| #![trigger rs[j]] 0 <= j < rs.len() && rs[j] < root && tpiece(g, rs[j], inter, x);
                lemma_tpiece_child(g, rs[j], inter, x, cs, i);
                assert(tpiece(g, rs[j], inter, cs[i]));
            },
            _ => {},
        }
    }
}

/// Members have smaller classes and sum classes (for unions), and inherit normal forms.
pub proof fn lemma_tpiece_class(g: model::Graph, root: nat, inter: bool, x: nat)
    requires model::graph_wf(g), root < g.transitions.len(), tpiece(g, root, inter, x),
    ensures
        x < g.transitions.len(),
        forall|v: R| #[trigger] tcls(g, x, v) ==> tcls(g, root, v),
        !inter ==> forall|v: R| #[trigger] ycls(g, x, v) ==> ycls(g, root, v),
        nf_sum(g, root) ==> nf_sum(g, x),
        inter && nf_prod(g, root) && x != root ==> nf_lit(g, x),
    decreases root,
{
    if x != root {
        model::lemma_graph_transition_wf(g, root);
        match g.transitions[root as int] {
            model::TransitionNode::Union(cs) => {
                let j = choose|j: int| #![trigger cs[j]] 0 <= j < cs.len() && cs[j] < root && tpiece(g, cs[j], inter, x);
                lemma_tpiece_class(g, cs[j], inter, x);
                assert forall|v: R| #[trigger] tcls(g, x, v) implies tcls(g, root, v) by {
                    lemma_tcls(g, root, v);
                    assert(tcls(g, cs[j], v));
                }
                assert forall|v: R| #[trigger] ycls(g, x, v) implies ycls(g, root, v) by {
                    lemma_ycls(g, root, v);
                    assert(ycls(g, cs[j], v));
                    assert(kids(yc(g), root, cs, v));
                    lemma_cl_base(false, |w: R| kids(yc(g), root, cs, w), v);
                }
            },
            model::TransitionNode::Intersect(cs) => {
                let j = choose|j: int| #![trigger cs[j]] 0 <= j < cs.len() && cs[j] < root && tpiece(g, cs[j], inter, x);
                lemma_tpiece_class(g, cs[j], inter, x);
                assert forall|v: R| #[trigger] tcls(g, x, v) implies tcls(g, root, v) by {
                    lemma_tcls(g, root, v);
                    assert(tcls(g, cs[j], v));
                    assert(kids(tc(g), root, cs, v));
                    lemma_cl_base(true, |w: R| kids(tc(g), root, cs, w), v);
                }
                if nf_prod(g, root) {
                    assert(nf_lit(g, cs[j]));
                    // a literal is not a set, so it reaches only itself
                    assert(x == cs[j]);
                }
            },
            _ => {},
        }
    }
}

} // verus!
