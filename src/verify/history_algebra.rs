// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Paper-shaped regex-language theorems for the source policy language:
//! similarity preserves language, symbolic derivative correctness, matcher correctness.

use super::history_specs as language;
use super::history_specs::{Head, Regex, SrcTest, Subst, Term, Transition};
use super::value_specs::Data;
use crate::builtins::history::kernel::verify as model;
use alloc::boxed::Box;
use vstd::prelude::*;

verus! {

broadcast use {vstd::string::group_string_axioms, vstd::seq::group_seq_lemmas};

pub open spec fn src_sem(theta: Subst) -> spec_fn(SrcTest, Data) -> bool {
    |test: SrcTest, event: Data| language::src_test_holds(theta, test, event)
}

/// The paper's δ, without runtime normalization or graph representation.
pub open spec fn symbolic_derivative<L>(r: Regex<L>) -> Transition<L>
    decreases r, 1nat, 0nat,
{
    match r {
        Regex::Empty | Regex::Epsilon => Transition::Const(Regex::Empty),
        Regex::All => Transition::Const(Regex::All),
        Regex::Test(l) => Transition::If(l, Box::new(Transition::Const(Regex::Epsilon)), Box::new(Transition::Const(Regex::Empty))),
        Regex::Union(cs) => Transition::Union(Seq::new(cs.len(), |i: int| if 0 <= i < cs.len() { symbolic_derivative(cs[i]) } else { Transition::Const(Regex::Empty) })),
        Regex::Intersect(cs) => Transition::Intersect(Seq::new(cs.len(), |i: int| if 0 <= i < cs.len() { symbolic_derivative(cs[i]) } else { Transition::Const(Regex::Empty) })),
        Regex::Not(c) => Transition::Not(Box::new(symbolic_derivative(*c))),
        Regex::Star(c) => Transition::Append(Box::new(symbolic_derivative(*c)), seq![Regex::Star(c)]),
        Regex::Concat(cs) => symbolic_derivative_concat(r, cs),
    }
}

pub open spec fn symbolic_derivative_concat<L>(bound: Regex<L>, cs: Seq<Regex<L>>) -> Transition<L>
    decreases bound, 0nat, cs.len(),
    when forall|i: int| 0 <= i < cs.len() ==> is_smaller_than(cs[i], bound)
{
    if cs.len() == 0 { Transition::Const(Regex::Empty) }
    else {
        Transition::Union(seq![Transition::Append(Box::new(symbolic_derivative(cs[0])), cs.drop_first())]
            + if language::nullable(cs[0]) { seq![symbolic_derivative_concat(bound, cs.drop_first())] } else { Seq::empty() })
    }
}

pub proof fn lemma_symbolic_derivative_concat_interp<L>(sem: spec_fn(L, Data) -> bool, e: Data, bound: Regex<L>, cs: Seq<Regex<L>>)
    requires
        forall|i: int| 0 <= i < cs.len() ==> is_smaller_than(cs[i], bound),
        forall|i: int| 0 <= i < cs.len() ==> #[trigger] language::interp_transition(sem, e, symbolic_derivative(cs[i])) == language::derivative(sem, e, cs[i]),
    ensures language::interp_transition(sem, e, symbolic_derivative_concat(bound, cs)) == language::derivative_concat(sem, e, bound, cs),
    decreases cs.len(),
{
    reveal_with_fuel(language::interp_transition, 3);
    if cs.len() > 0 {
        let rest = cs.drop_first();
        assert(rest.len() == cs.len() - 1);
        assert forall|i: int| 0 <= i < rest.len() implies is_smaller_than(rest[i], bound) by {
            assert(rest[i] == cs[i + 1]);
        }
        assert forall|i: int| 0 <= i < rest.len() implies language::interp_transition(sem, e, symbolic_derivative(rest[i])) == language::derivative(sem, e, rest[i]) by {
            assert(rest[i] == cs[i + 1]);
        }
        lemma_symbolic_derivative_concat_interp(sem, e, bound, rest);
        let ts = seq![Transition::Append(Box::new(symbolic_derivative(cs[0])), rest)]
            + if language::nullable(cs[0]) { seq![symbolic_derivative_concat(bound, rest)] } else { Seq::empty() };
        let ds = seq![Regex::Concat(seq![language::derivative(sem, e, cs[0])] + rest)]
            + if language::nullable(cs[0]) { seq![language::derivative_concat(sem, e, bound, rest)] } else { Seq::empty() };
        let out = language::interp_transition(sem, e, Transition::Union(ts));
        assert(out is Union);
        assert(ts.len() == ds.len());
        assert forall|i: int| 0 <= i < ts.len() implies language::interp_transition(sem, e, ts[i]) == ds[i] by {
            assert(i == 0 || (language::nullable(cs[0]) && i == 1));
            if i == 0 {
                assert(ts[i] == Transition::Append(Box::new(symbolic_derivative(cs[0])), rest));
                assert(ds[i] == Regex::Concat(seq![language::derivative(sem, e, cs[0])] + rest));
                assert(language::interp_transition(sem, e, symbolic_derivative(cs[0])) == language::derivative(sem, e, cs[0]));
                assert(language::interp_transition(sem, e, ts[i])->Concat_0 =~= seq![language::derivative(sem, e, cs[0])] + rest);
            } else {
                assert(ts[i] == symbolic_derivative_concat(bound, rest));
                assert(ds[i] == language::derivative_concat(sem, e, bound, rest));
            }
        }
        assert(out->Union_0 =~= ds);
    }
}

pub proof fn lemma_symbolic_derivative_interp<L>(sem: spec_fn(L, Data) -> bool, e: Data, r: Regex<L>)
    ensures language::interp_transition(sem, e, symbolic_derivative(r)) == language::derivative(sem, e, r),
    decreases r,
{
    reveal_with_fuel(language::interp_transition, 2);
    reveal_with_fuel(symbolic_derivative, 2);
    reveal_with_fuel(language::derivative, 2);
    match r {
        Regex::Union(cs) | Regex::Intersect(cs) => {
            let ts = Seq::new(cs.len(), |i: int| if 0 <= i < cs.len() { symbolic_derivative(cs[i]) } else { Transition::Const(Regex::Empty) });
            let ds = Seq::new(cs.len(), |i: int| if 0 <= i < cs.len() { language::derivative(sem, e, cs[i]) } else { Regex::Empty });
            assert forall|i: int| 0 <= i < cs.len() implies language::interp_transition(sem, e, ts[i]) == ds[i] by {
                lemma_symbolic_derivative_interp(sem, e, cs[i]);
            }
            let interpreted = Seq::new(ts.len(), |i: int| if 0 <= i < ts.len() { language::interp_transition(sem, e, ts[i]) } else { Regex::Empty });
            assert(interpreted =~= ds);
            if r is Union {
                assert(symbolic_derivative(r)->Union_0 =~= ts);
                assert(language::interp_transition(sem, e, Transition::Union(ts))->Union_0 =~= interpreted);
                assert(language::derivative(sem, e, r)->Union_0 =~= ds);
            } else {
                assert(symbolic_derivative(r)->Intersect_0 =~= ts);
                assert(language::interp_transition(sem, e, Transition::Intersect(ts))->Intersect_0 =~= interpreted);
                assert(language::derivative(sem, e, r)->Intersect_0 =~= ds);
            }
        },
        Regex::Not(c) => lemma_symbolic_derivative_interp(sem, e, *c),
        Regex::Star(c) => {
            lemma_symbolic_derivative_interp(sem, e, *c);
            assert(seq![language::derivative(sem, e, *c)] + seq![Regex::Star(c)] =~= seq![language::derivative(sem, e, *c), Regex::Star(c)]);
        },
        Regex::Concat(cs) => {
            assert forall|i: int| 0 <= i < cs.len() implies is_smaller_than(cs[i], r) by { }
            assert forall|i: int| 0 <= i < cs.len() implies language::interp_transition(sem, e, symbolic_derivative(cs[i])) == language::derivative(sem, e, cs[i]) by {
                lemma_symbolic_derivative_interp(sem, e, cs[i]);
            }
            lemma_symbolic_derivative_concat_interp(sem, e, r, cs);
            assert(language::interp_transition(sem, e, symbolic_derivative(r)) == language::derivative(sem, e, r));
        },
        Regex::Test(l) => language::lemma_interp_if(sem, e, l, Transition::Const(Regex::Epsilon), Transition::Const(Regex::Empty)),
        _ => {},
    }
}

/// Paper, Theorem (Symbolic derivative correctness), modulo language rather than Norm.
pub proof fn theorem_symbolic_derivative_correct<L>(sem: spec_fn(L, Data) -> bool, e: Data, r: Regex<L>, w: Seq<Data>)
    ensures language::lang(sem, language::interp_transition(sem, e, symbolic_derivative(r)), w) == language::lang(sem, r, seq![e] + w),
{
    lemma_symbolic_derivative_interp(sem, e, r);
    language::lemma_derivative_correct(sem, e, r, w);
}

/// The paper's state sequence q, consuming events oldest first.
pub open spec fn symbolic_run<L>(sem: spec_fn(L, Data) -> bool, u: Seq<Data>, r: Regex<L>) -> Regex<L>
    decreases u.len(),
{
    if u.len() == 0 { r }
    else { symbolic_run(sem, u.drop_first(), language::interp_transition(sem, u[0], symbolic_derivative(r))) }
}

pub proof fn lemma_symbolic_run_is_derive_word<L>(sem: spec_fn(L, Data) -> bool, u: Seq<Data>, r: Regex<L>)
    ensures symbolic_run(sem, u, r) == language::derive_word(sem, u, r),
    decreases u.len(),
{
    if u.len() > 0 {
        lemma_symbolic_derivative_interp(sem, u[0], r);
        lemma_symbolic_run_is_derive_word(sem, u.drop_first(), language::derivative(sem, u[0], r));
    }
}

/// Paper, Theorem (Matcher correctness), steps 2–3.
pub proof fn theorem_matcher_correct<L>(sem: spec_fn(L, Data) -> bool, u: Seq<Data>, r: Regex<L>)
    ensures language::nullable(symbolic_run(sem, u, r)) == language::lang(sem, r, u),
{
    lemma_symbolic_run_is_derive_word(sem, u, r);
    language::lemma_derive_word_nullable(sem, u, r);
}

/// A fired rule uses its unique complete head substitution.
pub proof fn theorem_rule_decision(head: Head, tail: Regex<SrcTest>, request: Data, history: Seq<Data>, theta: Subst)
    requires language::head_match(head, request, theta), theta.dom() == language::head_vars(head),
    ensures language::pair_lang(head, tail, request, history) == language::nullable(symbolic_run(src_sem(theta), history, tail)),
{
    language::lemma_pair_lang_substitutions(head, tail, request, history, theta);
    theorem_matcher_correct(src_sem(theta), history, tail);
}

/// Paper, step 1: without a complete matching substitution the rule is not fired.
pub proof fn theorem_not_fired(head: Head, tail: Regex<SrcTest>, request: Data, history: Seq<Data>)
    requires forall|theta: Subst| !(language::head_match(head, request, theta) && theta.dom() == language::head_vars(head)),
    ensures !language::pair_lang(head, tail, request, history),
{ }

pub enum TestRule {
    AndSet(Seq<SrcTest>, Seq<SrcTest>),
    OrSet(Seq<SrcTest>, Seq<SrcTest>),
    AndFlatten(Seq<SrcTest>, int),
    OrFlatten(Seq<SrcTest>, int),
    AndTrue(Seq<SrcTest>, int),
    OrFalse(Seq<SrcTest>, int),
    AndFalse(Seq<SrcTest>, int),
    OrTrue(Seq<SrcTest>, int),
    AndSingleton(SrcTest),
    OrSingleton(SrcTest),
    AndNil,
    OrNil,
    AndAbsorb(SrcTest, Seq<SrcTest>),
    OrAbsorb(SrcTest, Seq<SrcTest>),
    AndDistrib(SrcTest, Seq<SrcTest>),
    OrDistrib(SrcTest, Seq<SrcTest>),
    AndExclusive(Seq<SrcTest>, int, int),
    AndDistinctConstants(Seq<SrcTest>, int, int),
}

pub open spec fn test_rule_lhs(rule: TestRule) -> SrcTest {
    match rule {
        TestRule::AndSet(cs, _)
        | TestRule::AndFlatten(cs, _)
        | TestRule::AndTrue(cs, _)
        | TestRule::AndFalse(cs, _)
        | TestRule::AndExclusive(cs, _, _)
        | TestRule::AndDistinctConstants(cs, _, _) => SrcTest::And(cs),
        TestRule::OrSet(cs, _)
        | TestRule::OrFlatten(cs, _)
        | TestRule::OrFalse(cs, _)
        | TestRule::OrTrue(cs, _) => SrcTest::Or(cs),
        TestRule::AndSingleton(t) => SrcTest::And(seq![t]),
        TestRule::OrSingleton(t) => SrcTest::Or(seq![t]),
        TestRule::AndNil => SrcTest::And(Seq::empty()),
        TestRule::OrNil => SrcTest::Or(Seq::empty()),
        TestRule::AndAbsorb(t, cs)
        | TestRule::AndDistrib(t, cs) => SrcTest::And(seq![t, SrcTest::Or(cs)]),
        TestRule::OrAbsorb(t, cs)
        | TestRule::OrDistrib(t, cs) => SrcTest::Or(seq![t, SrcTest::And(cs)]),
    }
}

pub open spec fn test_rule_rhs(rule: TestRule) -> SrcTest {
    match rule {
        TestRule::AndSet(_, ds) => SrcTest::And(ds),
        TestRule::OrSet(_, ds) => SrcTest::Or(ds),
        TestRule::AndFlatten(cs, i) => {
            if 0 <= i < cs.len() {
                match cs[i] {
                    SrcTest::And(ds) => SrcTest::And(cs.take(i) + ds + cs.skip(i + 1)),
                    _ => SrcTest::And(cs),
                }
            } else { SrcTest::And(cs) }
        },
        TestRule::OrFlatten(cs, i) => {
            if 0 <= i < cs.len() {
                match cs[i] {
                    SrcTest::Or(ds) => SrcTest::Or(cs.take(i) + ds + cs.skip(i + 1)),
                    _ => SrcTest::Or(cs),
                }
            } else { SrcTest::Or(cs) }
        },
        TestRule::AndTrue(cs, i) => {
            SrcTest::And(if 0 <= i < cs.len() { cs.remove(i) } else { cs })
        },
        TestRule::OrFalse(cs, i) => {
            SrcTest::Or(if 0 <= i < cs.len() { cs.remove(i) } else { cs })
        },
        TestRule::AndFalse(_, _)
        | TestRule::OrNil
        | TestRule::AndExclusive(_, _, _)
        | TestRule::AndDistinctConstants(_, _, _) => SrcTest::Bool(false),
        TestRule::OrTrue(_, _)
        | TestRule::AndNil => SrcTest::Bool(true),
        TestRule::AndSingleton(t)
        | TestRule::OrSingleton(t)
        | TestRule::AndAbsorb(t, _)
        | TestRule::OrAbsorb(t, _) => t,
        TestRule::AndDistrib(t, cs) => SrcTest::Or(
            Seq::new(cs.len(), |k: int| SrcTest::And(seq![t, cs[k]]))),
        TestRule::OrDistrib(t, cs) => SrcTest::And(
            Seq::new(cs.len(), |k: int| SrcTest::Or(seq![t, cs[k]]))),
    }
}

pub open spec fn test_rule_valid(rule: TestRule) -> bool {
    match rule {
        TestRule::AndSet(cs, ds)
        | TestRule::OrSet(cs, ds) => cs.to_set() == ds.to_set(),
        TestRule::AndFlatten(cs, i) => 0 <= i < cs.len() && cs[i] is And,
        TestRule::OrFlatten(cs, i) => 0 <= i < cs.len() && cs[i] is Or,
        TestRule::AndTrue(cs, i) => 0 <= i < cs.len() && cs[i] == SrcTest::Bool(true),
        TestRule::OrFalse(cs, i) => 0 <= i < cs.len() && cs[i] == SrcTest::Bool(false),
        TestRule::AndFalse(cs, i) => 0 <= i < cs.len() && cs[i] == SrcTest::Bool(false),
        TestRule::OrTrue(cs, i) => 0 <= i < cs.len() && cs[i] == SrcTest::Bool(true),
        TestRule::AndAbsorb(t, cs)
        | TestRule::OrAbsorb(t, cs) => cs.contains(t),
        TestRule::AndExclusive(cs, i, j) => {
            0 <= i < cs.len() && 0 <= j < cs.len()
                && match (cs[i], cs[j]) {
                    (SrcTest::Eq(p, t), SrcTest::Neq(q, u)) => p == q && t == u,
                    _ => false,
                }
        },
        TestRule::AndDistinctConstants(cs, i, j) => {
            0 <= i < cs.len() && 0 <= j < cs.len()
                && match (cs[i], cs[j]) {
                    (SrcTest::Eq(p, Term::Constant(c)), SrcTest::Eq(q, Term::Constant(d))) =>
                        p == q && c != d,
                    _ => false,
                }
        },
        TestRule::AndSingleton(_)
        | TestRule::OrSingleton(_)
        | TestRule::AndNil
        | TestRule::OrNil
        | TestRule::AndDistrib(_, _)
        | TestRule::OrDistrib(_, _) => true,
    }
}

pub proof fn lemma_test_quantifiers_set<A>(p: spec_fn(A) -> bool, cs: Seq<A>, ds: Seq<A>)
    requires cs.to_set() == ds.to_set(),
    ensures
        (forall|k: int| 0 <= k < cs.len() ==> p(cs[k]))
            == (forall|k: int| 0 <= k < ds.len() ==> p(ds[k])),
        (exists|k: int| 0 <= k < cs.len() && p(cs[k]))
            == (exists|k: int| 0 <= k < ds.len() && p(ds[k])),
{
    broadcast use vstd::set::group_set_lemmas;
    cs.to_set_ensures();
    ds.to_set_ensures();
    if forall|k: int| 0 <= k < cs.len() ==> p(cs[k]) {
        assert forall|k: int| 0 <= k < ds.len() implies p(ds[k]) by {
            assert(ds.contains(ds[k]));
            assert(cs.to_set().contains(ds[k]));
            assert(cs.contains(ds[k]));
            let j = choose|j: int| 0 <= j < cs.len() && cs[j] == ds[k];
            assert(p(cs[j]));
        }
    }
    if forall|k: int| 0 <= k < ds.len() ==> p(ds[k]) {
        assert forall|k: int| 0 <= k < cs.len() implies p(cs[k]) by {
            assert(cs.contains(cs[k]));
            assert(ds.to_set().contains(cs[k]));
            assert(ds.contains(cs[k]));
            let j = choose|j: int| 0 <= j < ds.len() && ds[j] == cs[k];
            assert(p(ds[j]));
        }
    }
    if exists|k: int| 0 <= k < cs.len() && p(cs[k]) {
        let k = choose|k: int| 0 <= k < cs.len() && p(cs[k]);
        assert(ds.to_set().contains(cs[k]));
        assert(cs.contains(cs[k]));
        assert(ds.contains(cs[k]));
        let j = choose|j: int| 0 <= j < ds.len() && ds[j] == cs[k];
        assert(p(ds[j]));
        assert(exists|j: int| 0 <= j < ds.len() && p(ds[j]));
    }
    if exists|k: int| 0 <= k < ds.len() && p(ds[k]) {
        let k = choose|k: int| 0 <= k < ds.len() && p(ds[k]);
        assert(cs.to_set().contains(ds[k]));
        assert(ds.contains(ds[k]));
        assert(cs.contains(ds[k]));
        let j = choose|j: int| 0 <= j < cs.len() && cs[j] == ds[k];
        assert(p(cs[j]));
        assert(exists|j: int| 0 <= j < cs.len() && p(cs[j]));
    }
}

pub proof fn lemma_test_quantifiers_concat<A>(p: spec_fn(A) -> bool, cs: Seq<A>, ds: Seq<A>)
    ensures
        (forall|k: int| 0 <= k < (cs + ds).len() ==> p((cs + ds)[k]))
            == ((forall|k: int| 0 <= k < cs.len() ==> p(cs[k]))
                && (forall|k: int| 0 <= k < ds.len() ==> p(ds[k]))),
        (exists|k: int| 0 <= k < (cs + ds).len() && p((cs + ds)[k]))
            == ((exists|k: int| 0 <= k < cs.len() && p(cs[k]))
                || (exists|k: int| 0 <= k < ds.len() && p(ds[k]))),
{
    if forall|k: int| 0 <= k < (cs + ds).len() ==> p((cs + ds)[k]) {
        assert forall|k: int| 0 <= k < cs.len() implies p(cs[k]) by {
            assert((cs + ds)[k] == cs[k]);
        }
        assert forall|k: int| 0 <= k < ds.len() implies p(ds[k]) by {
            assert((cs + ds)[cs.len() + k] == ds[k]);
            assert(p((cs + ds)[cs.len() + k]));
        }
    }
    if (forall|k: int| 0 <= k < cs.len() ==> p(cs[k]))
        && (forall|k: int| 0 <= k < ds.len() ==> p(ds[k])) {
        assert forall|k: int| 0 <= k < (cs + ds).len() implies p((cs + ds)[k]) by {
            if k < cs.len() { assert((cs + ds)[k] == cs[k]); }
            else { assert((cs + ds)[k] == ds[k - cs.len()]); }
        }
    }
    if exists|k: int| 0 <= k < (cs + ds).len() && p((cs + ds)[k]) {
        let k = choose|k: int| 0 <= k < (cs + ds).len() && p((cs + ds)[k]);
        if k < cs.len() {
            assert((cs + ds)[k] == cs[k]);
            assert(exists|j: int| 0 <= j < cs.len() && p(cs[j]));
        } else {
            assert((cs + ds)[k] == ds[k - cs.len()]);
            assert(exists|j: int| 0 <= j < ds.len() && p(ds[j]));
        }
    }
    if exists|k: int| 0 <= k < cs.len() && p(cs[k]) {
        let k = choose|k: int| 0 <= k < cs.len() && p(cs[k]);
        assert((cs + ds)[k] == cs[k]);
        assert(exists|j: int| 0 <= j < (cs + ds).len() && p((cs + ds)[j]));
    }
    if exists|k: int| 0 <= k < ds.len() && p(ds[k]) {
        let k = choose|k: int| 0 <= k < ds.len() && p(ds[k]);
        assert((cs + ds)[cs.len() + k] == ds[k]);
        assert(p((cs + ds)[cs.len() + k]));
        assert(exists|j: int| 0 <= j < (cs + ds).len() && p((cs + ds)[j]));
    }
}

pub proof fn lemma_test_quantifiers_remove<A>(p: spec_fn(A) -> bool, cs: Seq<A>, i: int)
    requires 0 <= i < cs.len(),
    ensures
        (forall|k: int| 0 <= k < cs.len() ==> p(cs[k]))
            == (p(cs[i]) && (forall|k: int| 0 <= k < cs.remove(i).len() ==> p(cs.remove(i)[k]))),
        (exists|k: int| 0 <= k < cs.len() && p(cs[k]))
            == (p(cs[i]) || (exists|k: int| 0 <= k < cs.remove(i).len() && p(cs.remove(i)[k]))),
{
    let ds = cs.remove(i);
    assert(ds.len() == cs.len() - 1);
    assert forall|k: int| 0 <= k < ds.len()
        implies ds[k] == if k < i { cs[k] } else { cs[k + 1] } by {}
    if forall|k: int| 0 <= k < cs.len() ==> p(cs[k]) {
        assert(p(cs[i]));
        assert forall|k: int| 0 <= k < ds.len() implies p(ds[k]) by {
            let j = if k < i { k } else { k + 1 };
            assert(ds[k] == cs[j]);
            assert(p(cs[j]));
        }
    }
    if p(cs[i]) && (forall|k: int| 0 <= k < ds.len() ==> p(ds[k])) {
        assert forall|k: int| 0 <= k < cs.len() implies p(cs[k]) by {
            if k < i { assert(ds[k] == cs[k]); }
            else if k > i { assert(ds[k - 1] == cs[k]); }
        }
    }
    if exists|k: int| 0 <= k < cs.len() && p(cs[k]) {
        let k = choose|k: int| 0 <= k < cs.len() && p(cs[k]);
        if k != i {
            let j = if k < i { k } else { k - 1 };
            assert(ds[j] == cs[k]);
            assert(exists|j: int| 0 <= j < ds.len() && p(ds[j]));
        }
    }
    if p(cs[i]) {
        assert(exists|k: int| 0 <= k < cs.len() && p(cs[k]));
    }
    if exists|k: int| 0 <= k < ds.len() && p(ds[k]) {
        let k = choose|k: int| 0 <= k < ds.len() && p(ds[k]);
        let j = if k < i { k } else { k + 1 };
        assert(ds[k] == cs[j]);
        assert(exists|j: int| 0 <= j < cs.len() && p(cs[j]));
    }
}

pub proof fn lemma_test_quantifiers_splice<A>(p: spec_fn(A) -> bool, cs: Seq<A>, i: int, ds: Seq<A>)
    requires 0 <= i < cs.len(),
    ensures
        (forall|k: int| 0 <= k < (cs.take(i) + ds + cs.skip(i + 1)).len()
            ==> p(#[trigger] (cs.take(i) + ds + cs.skip(i + 1))[k]))
            == ((forall|k: int| 0 <= k < cs.remove(i).len() ==> p(cs.remove(i)[k]))
                && (forall|k: int| 0 <= k < ds.len() ==> p(ds[k]))),
        (exists|k: int| 0 <= k < (cs.take(i) + ds + cs.skip(i + 1)).len()
            && p(#[trigger] (cs.take(i) + ds + cs.skip(i + 1))[k]))
            == ((exists|k: int| 0 <= k < cs.remove(i).len() && p(cs.remove(i)[k]))
                || (exists|k: int| 0 <= k < ds.len() && p(ds[k]))),
{
    assert(cs.remove(i) =~= cs.take(i) + cs.skip(i + 1)) by {
        assert forall|k: int| 0 <= k < cs.remove(i).len()
            implies cs.remove(i)[k] == (cs.take(i) + cs.skip(i + 1))[k] by {
            if k < i { assert(cs.remove(i)[k] == cs[k]); }
            else { assert(cs.remove(i)[k] == cs[k + 1]); }
        }
    }
    lemma_test_quantifiers_concat(p, cs.take(i), cs.skip(i + 1));
    lemma_test_quantifiers_concat(p, cs.take(i), ds);
    lemma_test_quantifiers_concat(p, cs.take(i) + ds, cs.skip(i + 1));
}

pub proof fn lemma_test_connectives(theta: Subst, cs: Seq<SrcTest>, e: Data)
    ensures
        language::src_test_holds(theta, SrcTest::And(cs), e)
            == (forall|k: int| 0 <= k < cs.len() ==> language::src_test_holds(theta, cs[k], e)),
        language::src_test_holds(theta, SrcTest::Or(cs), e)
            == (exists|k: int| 0 <= k < cs.len() && language::src_test_holds(theta, cs[k], e)),
{
    if language::src_test_holds(theta, SrcTest::And(cs), e) {
        assert forall|k: int| 0 <= k < cs.len()
            implies language::src_test_holds(theta, cs[k], e) by {
            assert(language::src_test_holds(theta, SrcTest::And(cs), e));
        }
    }
    if language::src_test_holds(theta, SrcTest::Or(cs), e) {
        let k = choose|k: int| 0 <= k < cs.len() && language::src_test_holds(theta, cs[k], e);
        assert(exists|j: int| 0 <= j < cs.len() && language::src_test_holds(theta, cs[j], e));
    }
    if exists|k: int| 0 <= k < cs.len() && language::src_test_holds(theta, cs[k], e) {
        let k = choose|k: int| 0 <= k < cs.len() && language::src_test_holds(theta, cs[k], e);
        assert(language::src_test_holds(theta, SrcTest::Or(cs), e));
    }
}

pub proof fn lemma_test_binary(theta: Subst, a: SrcTest, b: SrcTest, e: Data)
    ensures
        language::src_test_holds(theta, SrcTest::And(seq![a, b]), e)
            == (language::src_test_holds(theta, a, e) && language::src_test_holds(theta, b, e)),
        language::src_test_holds(theta, SrcTest::Or(seq![a, b]), e)
            == (language::src_test_holds(theta, a, e) || language::src_test_holds(theta, b, e)),
{
    let cs = seq![a, b];
    lemma_test_connectives(theta, cs, e);
    if language::src_test_holds(theta, a, e) && language::src_test_holds(theta, b, e) {
        assert forall|k: int| 0 <= k < cs.len()
            implies language::src_test_holds(theta, cs[k], e) by {
            assert(k == 0 || k == 1);
        }
    }
    if language::src_test_holds(theta, SrcTest::And(cs), e) {
        assert(language::src_test_holds(theta, cs[0], e));
        assert(language::src_test_holds(theta, cs[1], e));
    }
    if language::src_test_holds(theta, SrcTest::Or(cs), e) {
        let k = choose|k: int| 0 <= k < cs.len() && language::src_test_holds(theta, cs[k], e);
        assert(k == 0 || k == 1);
    }
    if language::src_test_holds(theta, a, e) {
        assert(language::src_test_holds(theta, cs[0], e));
        assert(exists|k: int| 0 <= k < cs.len() && language::src_test_holds(theta, cs[k], e));
    }
    if language::src_test_holds(theta, b, e) {
        assert(language::src_test_holds(theta, cs[1], e));
        assert(exists|k: int| 0 <= k < cs.len() && language::src_test_holds(theta, cs[k], e));
    }
}

pub proof fn lemma_test_rule_sound(theta: Subst, rule: TestRule, e: Data)
    requires test_rule_valid(rule),
    ensures language::src_test_holds(theta, test_rule_lhs(rule), e)
        == language::src_test_holds(theta, test_rule_rhs(rule), e),
{
    let p = |t: SrcTest| language::src_test_holds(theta, t, e);
    match rule {
        TestRule::AndSet(cs, ds) | TestRule::OrSet(cs, ds) => {
            lemma_test_quantifiers_set(p, cs, ds);
            lemma_test_connectives(theta, cs, e);
            lemma_test_connectives(theta, ds, e);
        },
        TestRule::AndFlatten(cs, i) => {
            let ds = cs[i]->And_0;
            lemma_test_quantifiers_remove(p, cs, i);
            lemma_test_quantifiers_splice(p, cs, i, ds);
            lemma_test_connectives(theta, cs, e);
            lemma_test_connectives(theta, ds, e);
            lemma_test_connectives(theta, cs.take(i) + ds + cs.skip(i + 1), e);
        },
        TestRule::OrFlatten(cs, i) => {
            let ds = cs[i]->Or_0;
            lemma_test_quantifiers_remove(p, cs, i);
            lemma_test_quantifiers_splice(p, cs, i, ds);
            lemma_test_connectives(theta, cs, e);
            lemma_test_connectives(theta, ds, e);
            lemma_test_connectives(theta, cs.take(i) + ds + cs.skip(i + 1), e);
        },
        TestRule::AndTrue(cs, i) | TestRule::OrFalse(cs, i) => {
            lemma_test_quantifiers_remove(p, cs, i);
            lemma_test_connectives(theta, cs, e);
            lemma_test_connectives(theta, cs.remove(i), e);
        },
        TestRule::AndFalse(cs, i) => {
            lemma_test_connectives(theta, cs, e);
            assert(!language::src_test_holds(theta, cs[i], e));
        },
        TestRule::OrTrue(cs, i) => {
            lemma_test_connectives(theta, cs, e);
            assert(language::src_test_holds(theta, cs[i], e));
            assert(exists|k: int| 0 <= k < cs.len() && language::src_test_holds(theta, cs[k], e));
        },
        TestRule::AndSingleton(t) | TestRule::OrSingleton(t) => {
            let cs = seq![t];
            lemma_test_connectives(theta, cs, e);
            if language::src_test_holds(theta, SrcTest::And(cs), e) {
                assert(language::src_test_holds(theta, cs[0], e));
            }
            if language::src_test_holds(theta, t, e) {
                assert forall|k: int| 0 <= k < cs.len()
                    implies language::src_test_holds(theta, cs[k], e) by { assert(k == 0); }
                assert(exists|k: int| 0 <= k < cs.len() && language::src_test_holds(theta, cs[k], e));
            }
            if language::src_test_holds(theta, SrcTest::Or(cs), e) {
                let k = choose|k: int| 0 <= k < cs.len() && language::src_test_holds(theta, cs[k], e);
                assert(k == 0);
            }
        },
        TestRule::AndNil | TestRule::OrNil => {
            lemma_test_connectives(theta, Seq::empty(), e);
        },
        TestRule::AndAbsorb(t, cs) => {
            lemma_test_binary(theta, t, SrcTest::Or(cs), e);
            lemma_test_connectives(theta, cs, e);
            let k = choose|k: int| 0 <= k < cs.len() && cs[k] == t;
            if language::src_test_holds(theta, t, e) {
                assert(language::src_test_holds(theta, cs[k], e));
                assert(exists|j: int| 0 <= j < cs.len() && language::src_test_holds(theta, cs[j], e));
            }
        },
        TestRule::OrAbsorb(t, cs) => {
            lemma_test_binary(theta, t, SrcTest::And(cs), e);
            lemma_test_connectives(theta, cs, e);
            let k = choose|k: int| 0 <= k < cs.len() && cs[k] == t;
            if language::src_test_holds(theta, SrcTest::And(cs), e) {
                assert(language::src_test_holds(theta, cs[k], e));
            }
        },
        TestRule::AndDistrib(t, cs) => {
            let ds = Seq::new(cs.len(), |k: int| SrcTest::And(seq![t, cs[k]]));
            lemma_test_binary(theta, t, SrcTest::Or(cs), e);
            lemma_test_connectives(theta, cs, e);
            lemma_test_connectives(theta, ds, e);
            assert forall|k: int| 0 <= k < cs.len()
                implies language::src_test_holds(theta, ds[k], e)
                    == (language::src_test_holds(theta, t, e) && language::src_test_holds(theta, cs[k], e)) by {
                lemma_test_binary(theta, t, cs[k], e);
            }
            if language::src_test_holds(theta, SrcTest::And(seq![t, SrcTest::Or(cs)]), e) {
                let k = choose|k: int| 0 <= k < cs.len() && language::src_test_holds(theta, cs[k], e);
                assert(language::src_test_holds(theta, ds[k], e));
                assert(exists|j: int| 0 <= j < ds.len() && language::src_test_holds(theta, ds[j], e));
            }
            if language::src_test_holds(theta, SrcTest::Or(ds), e) {
                let k = choose|k: int| 0 <= k < ds.len() && language::src_test_holds(theta, ds[k], e);
                assert(language::src_test_holds(theta, t, e));
                assert(language::src_test_holds(theta, cs[k], e));
                assert(exists|j: int| 0 <= j < cs.len() && language::src_test_holds(theta, cs[j], e));
            }
        },
        TestRule::OrDistrib(t, cs) => {
            let ds = Seq::new(cs.len(), |k: int| SrcTest::Or(seq![t, cs[k]]));
            lemma_test_binary(theta, t, SrcTest::And(cs), e);
            lemma_test_connectives(theta, cs, e);
            lemma_test_connectives(theta, ds, e);
            assert forall|k: int| 0 <= k < cs.len()
                implies language::src_test_holds(theta, ds[k], e)
                    == (language::src_test_holds(theta, t, e) || language::src_test_holds(theta, cs[k], e)) by {
                lemma_test_binary(theta, t, cs[k], e);
            }
            if language::src_test_holds(theta, SrcTest::Or(seq![t, SrcTest::And(cs)]), e) {
                assert forall|k: int| 0 <= k < ds.len()
                    implies language::src_test_holds(theta, ds[k], e) by {
                    if !language::src_test_holds(theta, t, e) {
                        assert(language::src_test_holds(theta, cs[k], e));
                    }
                }
            }
            if language::src_test_holds(theta, SrcTest::And(ds), e)
                && !language::src_test_holds(theta, t, e) {
                assert forall|k: int| 0 <= k < cs.len()
                    implies language::src_test_holds(theta, cs[k], e) by {
                    assert(language::src_test_holds(theta, ds[k], e));
                }
            }
        },
        TestRule::AndExclusive(cs, i, j) => {
            lemma_test_connectives(theta, cs, e);
            if language::src_test_holds(theta, SrcTest::And(cs), e) {
                assert(language::src_test_holds(theta, cs[i], e));
                assert(language::src_test_holds(theta, cs[j], e));
                let path = cs[i]->Eq_0;
                let term = cs[i]->Eq_1;
                assert(cs[j] == SrcTest::Neq(path, term));
                match language::select(e, path) {
                    Some(value) => {
                        assert(value == language::term_value(theta, term));
                        assert(value != language::term_value(theta, term));
                    },
                    None => { assert(!language::src_test_holds(theta, cs[i], e)); },
                }
            }
        },
        TestRule::AndDistinctConstants(cs, i, j) => {
            lemma_test_connectives(theta, cs, e);
            if language::src_test_holds(theta, SrcTest::And(cs), e) {
                assert(language::src_test_holds(theta, cs[i], e));
                assert(language::src_test_holds(theta, cs[j], e));
                let path = cs[i]->Eq_0;
                let c = (cs[i]->Eq_1)->Constant_0;
                let d = (cs[j]->Eq_1)->Constant_0;
                assert(c != d);
                assert(cs[i] == SrcTest::Eq(path, Term::Constant(c)));
                assert(cs[j] == SrcTest::Eq(path, Term::Constant(d)));
                match language::select(e, path) {
                    Some(value) => {
                        assert(value == c);
                        assert(value == d);
                    },
                    None => { assert(!language::src_test_holds(theta, cs[i], e)); },
                }
            }
        },
    }
}

/// Equation groups 1 and 3; n-ary sequences expose indices and side conditions.
pub enum RegexRule {
    UnionSet(Seq<Regex<SrcTest>>, Seq<Regex<SrcTest>>),
    IntersectSet(Seq<Regex<SrcTest>>, Seq<Regex<SrcTest>>),
    UnionFlatten(Seq<Regex<SrcTest>>, int),
    IntersectFlatten(Seq<Regex<SrcTest>>, int),
    ConcatFlatten(Seq<Regex<SrcTest>>, int),
    UnionEmpty(Seq<Regex<SrcTest>>, int), UnionAll(Seq<Regex<SrcTest>>, int),
    IntersectAll(Seq<Regex<SrcTest>>, int), IntersectEmpty(Seq<Regex<SrcTest>>, int),
    ConcatEpsilon(Seq<Regex<SrcTest>>, int), ConcatEmpty(Seq<Regex<SrcTest>>, int),
    UnionSingleton(Regex<SrcTest>), IntersectSingleton(Regex<SrcTest>), ConcatSingleton(Regex<SrcTest>),
    UnionNil, IntersectNil, ConcatNil,
    StarStar(Regex<SrcTest>), StarEpsilon, StarEmpty, StarAll,
    NotNot(Regex<SrcTest>), NotEmpty, NotAll,
    TestUnion(Seq<SrcTest>), TestIntersect(Seq<SrcTest>), TestFalse,
    IntersectEpsilonTest(Seq<Regex<SrcTest>>, int, int), StarTrue,
}

pub open spec fn regex_rule_lhs(rule: RegexRule) -> Regex<SrcTest> {
    match rule {
        RegexRule::UnionSet(cs, _) | RegexRule::UnionFlatten(cs, _)
        | RegexRule::UnionEmpty(cs, _) | RegexRule::UnionAll(cs, _) => Regex::Union(cs),
        RegexRule::IntersectSet(cs, _) | RegexRule::IntersectFlatten(cs, _)
        | RegexRule::IntersectAll(cs, _) | RegexRule::IntersectEmpty(cs, _)
        | RegexRule::IntersectEpsilonTest(cs, _, _) => Regex::Intersect(cs),
        RegexRule::ConcatFlatten(cs, _) | RegexRule::ConcatEpsilon(cs, _)
        | RegexRule::ConcatEmpty(cs, _) => Regex::Concat(cs),
        RegexRule::UnionSingleton(c) => Regex::Union(seq![c]),
        RegexRule::IntersectSingleton(c) => Regex::Intersect(seq![c]),
        RegexRule::ConcatSingleton(c) => Regex::Concat(seq![c]),
        RegexRule::UnionNil => Regex::Union(Seq::empty()),
        RegexRule::IntersectNil => Regex::Intersect(Seq::empty()),
        RegexRule::ConcatNil => Regex::Concat(Seq::empty()),
        RegexRule::StarStar(c) => Regex::Star(Box::new(Regex::Star(Box::new(c)))),
        RegexRule::StarEpsilon => Regex::Star(Box::new(Regex::Epsilon)),
        RegexRule::StarEmpty => Regex::Star(Box::new(Regex::Empty)),
        RegexRule::StarAll => Regex::Star(Box::new(Regex::All)),
        RegexRule::NotNot(c) => Regex::Not(Box::new(Regex::Not(Box::new(c)))),
        RegexRule::NotEmpty => Regex::Not(Box::new(Regex::Empty)),
        RegexRule::NotAll => Regex::Not(Box::new(Regex::All)),
        RegexRule::TestUnion(phis) => Regex::Union(Seq::new(phis.len(), |k: int| Regex::Test(phis[k]))),
        RegexRule::TestIntersect(phis) => Regex::Intersect(Seq::new(phis.len(), |k: int| Regex::Test(phis[k]))),
        RegexRule::TestFalse => Regex::Test(SrcTest::Bool(false)),
        RegexRule::StarTrue => Regex::Star(Box::new(Regex::Test(SrcTest::Bool(true)))),
    }
}

pub open spec fn regex_rule_rhs(rule: RegexRule) -> Regex<SrcTest> {
    match rule {
        RegexRule::UnionSet(_, ds) => Regex::Union(ds),
        RegexRule::IntersectSet(_, ds) => Regex::Intersect(ds),
        RegexRule::UnionFlatten(cs, i) => Regex::Union(cs.take(i) + cs[i]->Union_0 + cs.skip(i + 1)),
        RegexRule::IntersectFlatten(cs, i) => Regex::Intersect(cs.take(i) + cs[i]->Intersect_0 + cs.skip(i + 1)),
        RegexRule::ConcatFlatten(cs, i) => Regex::Concat(cs.take(i) + cs[i]->Concat_0 + cs.skip(i + 1)),
        RegexRule::UnionEmpty(cs, i) => Regex::Union(cs.remove(i)),
        RegexRule::IntersectAll(cs, i) => Regex::Intersect(cs.remove(i)),
        RegexRule::ConcatEpsilon(cs, i) => Regex::Concat(cs.remove(i)),
        RegexRule::UnionAll(_, _) | RegexRule::IntersectNil | RegexRule::StarAll | RegexRule::NotEmpty | RegexRule::StarTrue => Regex::All,
        RegexRule::IntersectEmpty(_, _) | RegexRule::ConcatEmpty(_, _) | RegexRule::UnionNil
        | RegexRule::NotAll | RegexRule::TestFalse | RegexRule::IntersectEpsilonTest(_, _, _) => Regex::Empty,
        RegexRule::UnionSingleton(c) | RegexRule::IntersectSingleton(c) | RegexRule::ConcatSingleton(c) | RegexRule::NotNot(c) => c,
        RegexRule::ConcatNil | RegexRule::StarEpsilon | RegexRule::StarEmpty => Regex::Epsilon,
        RegexRule::StarStar(c) => Regex::Star(Box::new(c)),
        RegexRule::TestUnion(phis) => Regex::Test(SrcTest::Or(phis)),
        RegexRule::TestIntersect(phis) => Regex::Test(SrcTest::And(phis)),
    }
}

pub open spec fn regex_rule_valid(rule: RegexRule) -> bool {
    match rule {
        RegexRule::UnionSet(cs, ds) | RegexRule::IntersectSet(cs, ds) => cs.to_set() == ds.to_set(),
        RegexRule::UnionFlatten(cs, i) => 0 <= i < cs.len() && cs[i] is Union,
        RegexRule::IntersectFlatten(cs, i) => 0 <= i < cs.len() && cs[i] is Intersect,
        RegexRule::ConcatFlatten(cs, i) => 0 <= i < cs.len() && cs[i] is Concat,
        RegexRule::UnionEmpty(cs, i) | RegexRule::IntersectEmpty(cs, i) | RegexRule::ConcatEmpty(cs, i) => 0 <= i < cs.len() && cs[i] == Regex::Empty,
        RegexRule::UnionAll(cs, i) | RegexRule::IntersectAll(cs, i) => 0 <= i < cs.len() && cs[i] == Regex::All,
        RegexRule::ConcatEpsilon(cs, i) => 0 <= i < cs.len() && cs[i] == Regex::Epsilon,
        RegexRule::TestIntersect(phis) => phis.len() > 0,
        RegexRule::IntersectEpsilonTest(cs, i, j) => 0 <= i < cs.len() && 0 <= j < cs.len() && cs[i] == Regex::Epsilon && cs[j] is Test,
        _ => true,
    }
}

pub proof fn lemma_lang_union_set<L>(sem: spec_fn(L, Data) -> bool, cs: Seq<Regex<L>>, ds: Seq<Regex<L>>, w: Seq<Data>)
    requires cs.to_set() == ds.to_set(),
    ensures language::lang(sem, Regex::Union(cs), w) == language::lang(sem, Regex::Union(ds), w),
{
    lemma_test_quantifiers_set(|r: Regex<L>| language::lang(sem, r, w), cs, ds);
    language::lemma_lang_union(sem, cs, w); language::lemma_lang_union(sem, ds, w);
}

pub proof fn lemma_lang_intersect_set<L>(sem: spec_fn(L, Data) -> bool, cs: Seq<Regex<L>>, ds: Seq<Regex<L>>, w: Seq<Data>)
    requires cs.to_set() == ds.to_set(),
    ensures language::lang(sem, Regex::Intersect(cs), w) == language::lang(sem, Regex::Intersect(ds), w),
{
    lemma_test_quantifiers_set(|r: Regex<L>| language::lang(sem, r, w), cs, ds);
    language::lemma_lang_intersect(sem, cs, w); language::lemma_lang_intersect(sem, ds, w);
}


pub proof fn lemma_lang_union_splice<L>(sem: spec_fn(L, Data) -> bool, cs: Seq<Regex<L>>, i: int, w: Seq<Data>)
    requires 0 <= i < cs.len(), cs[i] is Union,
    ensures language::lang(sem, Regex::Union(cs), w) == language::lang(sem, Regex::Union(cs.take(i) + cs[i]->Union_0 + cs.skip(i + 1)), w),
{
    lemma_test_quantifiers_remove(|r: Regex<L>| language::lang(sem, r, w), cs, i);
    lemma_test_quantifiers_splice(|r: Regex<L>| language::lang(sem, r, w), cs, i, cs[i]->Union_0);
    language::lemma_lang_union(sem, cs, w);
    language::lemma_lang_union(sem, cs[i]->Union_0, w);
    language::lemma_lang_union(sem, cs.take(i) + cs[i]->Union_0 + cs.skip(i + 1), w);
}

pub proof fn lemma_lang_intersect_splice<L>(sem: spec_fn(L, Data) -> bool, cs: Seq<Regex<L>>, i: int, w: Seq<Data>)
    requires 0 <= i < cs.len(), cs[i] is Intersect,
    ensures language::lang(sem, Regex::Intersect(cs), w) == language::lang(sem, Regex::Intersect(cs.take(i) + cs[i]->Intersect_0 + cs.skip(i + 1)), w),
{
    lemma_test_quantifiers_remove(|r: Regex<L>| language::lang(sem, r, w), cs, i);
    lemma_test_quantifiers_splice(|r: Regex<L>| language::lang(sem, r, w), cs, i, cs[i]->Intersect_0);
    language::lemma_lang_intersect(sem, cs, w);
    language::lemma_lang_intersect(sem, cs[i]->Intersect_0, w);
    language::lemma_lang_intersect(sem, cs.take(i) + cs[i]->Intersect_0 + cs.skip(i + 1), w);
}

pub proof fn lemma_concat_split<L>(
    sem: spec_fn(L, Data) -> bool,
    cs: Seq<Regex<L>>,
    ds: Seq<Regex<L>>,
    w: Seq<Data>,
)
    ensures language::lang(sem, Regex::Concat(cs + ds), w) <==>
        exists|a: Seq<Data>, b: Seq<Data>| w == a + b
            && language::lang(sem, Regex::Concat(cs), a)
            && language::lang(sem, Regex::Concat(ds), b),
    decreases cs.len(),
{
    if language::lang(sem, Regex::Concat(cs + ds), w) {
        let parts = choose|p: Seq<Seq<Data>>| p.len() == (cs + ds).len()
            && w == p.flatten()
            && forall|k: int| 0 <= k < (cs + ds).len() ==>
                language::lang(sem, (cs + ds)[k], p[k]);
        let ap = parts.subrange(0, cs.len() as int);
        let bp = parts.subrange(cs.len() as int, parts.len() as int);
        assert(parts =~= ap + bp);
        vstd::seq_lib::lemma_flatten_concat(ap, bp);
        assert(parts.flatten() == ap.flatten() + bp.flatten());
        assert forall|k: int| 0 <= k < cs.len() implies
            language::lang(sem, cs[k], ap[k]) by {
            assert(cs[k] == (cs + ds)[k]);
            assert(ap[k] == parts[k]);
        }
        assert forall|k: int| 0 <= k < ds.len() implies
            language::lang(sem, ds[k], bp[k]) by {
            assert(ds[k] == (cs + ds)[cs.len() + k]);
            assert(bp[k] == parts[cs.len() + k]);
        }
        assert(language::lang(sem, Regex::Concat(cs), ap.flatten()));
        assert(language::lang(sem, Regex::Concat(ds), bp.flatten()));
    }
    if exists|a: Seq<Data>, b: Seq<Data>| w == a + b
        && language::lang(sem, Regex::Concat(cs), a)
        && language::lang(sem, Regex::Concat(ds), b) {
        let (a, b) = choose|a: Seq<Data>, b: Seq<Data>| w == a + b
            && language::lang(sem, Regex::Concat(cs), a)
            && language::lang(sem, Regex::Concat(ds), b);
        let ap = choose|p: Seq<Seq<Data>>| p.len() == cs.len()
            && a == p.flatten()
            && forall|k: int| 0 <= k < cs.len() ==> language::lang(sem, cs[k], p[k]);
        let bp = choose|p: Seq<Seq<Data>>| p.len() == ds.len()
            && b == p.flatten()
            && forall|k: int| 0 <= k < ds.len() ==> language::lang(sem, ds[k], p[k]);
        let parts = ap + bp;
        vstd::seq_lib::lemma_flatten_concat(ap, bp);
        assert(parts.flatten() == w);
        assert forall|k: int| 0 <= k < (cs + ds).len() implies
            language::lang(sem, (cs + ds)[k], parts[k]) by {
            if k < cs.len() {
                assert((cs + ds)[k] == cs[k]);
                assert(parts[k] == ap[k]);
            } else {
                assert((cs + ds)[k] == ds[k - cs.len()]);
                assert(parts[k] == bp[k - cs.len()]);
            }
        }
        assert(language::lang(sem, Regex::Concat(cs + ds), w));
    }
}

pub proof fn lemma_parts_star_nil<L>(sem: spec_fn(L, Data) -> bool, c: Regex<L>)
    ensures language::lang(sem, Regex::Star(Box::new(c)), Seq::empty()),
{
    let parts = Seq::<Seq<Data>>::empty();
    assert(parts.flatten() == Seq::<Data>::empty());
    assert(forall|k: int| 0 <= k < parts.len() ==> language::lang(sem, c, parts[k]));
}

pub proof fn lemma_parts_star_single<L>(
    sem: spec_fn(L, Data) -> bool, c: Regex<L>, w: Seq<Data>,
)
    requires language::lang(sem, c, w),
    ensures language::lang(sem, Regex::Star(Box::new(c)), w),
{
    let parts = seq![w];
    parts.lemma_flatten_one_element();
    assert forall|k: int| 0 <= k < parts.len() implies language::lang(sem, c, parts[k]) by {
        assert(k == 0);
    }
}

pub proof fn lemma_parts_star_join<L>(
    sem: spec_fn(L, Data) -> bool, c: Regex<L>, a: Seq<Data>, b: Seq<Data>,
)
    requires language::lang(sem, Regex::Star(Box::new(c)), a),
        language::lang(sem, Regex::Star(Box::new(c)), b),
    ensures language::lang(sem, Regex::Star(Box::new(c)), a + b),
{
    let ap = choose|p: Seq<Seq<Data>>| a == p.flatten()
        && forall|k: int| 0 <= k < p.len() ==> language::lang(sem, c, p[k]);
    let bp = choose|p: Seq<Seq<Data>>| b == p.flatten()
        && forall|k: int| 0 <= k < p.len() ==> language::lang(sem, c, p[k]);
    let parts = ap + bp;
    vstd::seq_lib::lemma_flatten_concat(ap, bp);
    assert(parts.flatten() == a + b);
    assert forall|k: int| 0 <= k < parts.len() implies language::lang(sem, c, parts[k]) by {
        if k < ap.len() {
            assert(parts[k] == ap[k]);
        } else {
            assert(parts[k] == bp[k - ap.len()]);
        }
    }
}

/// Concatenating finitely many words in c* remains in c*, including empty parts.
pub proof fn lemma_parts_star_flatten<L>(
    sem: spec_fn(L, Data) -> bool, c: Regex<L>, parts: Seq<Seq<Data>>,
)
    requires forall|k: int| 0 <= k < parts.len() ==>
        language::lang(sem, Regex::Star(Box::new(c)), parts[k]),
    ensures language::lang(sem, Regex::Star(Box::new(c)), parts.flatten()),
    decreases parts.len(),
{
    if parts.len() == 0 {
        lemma_parts_star_nil(sem, c);
    } else {
        assert forall|k: int| 0 <= k < parts.drop_first().len() implies
            language::lang(sem, Regex::Star(Box::new(c)), parts.drop_first()[k]) by {
            assert(parts.drop_first()[k] == parts[k + 1]);
        }
        lemma_parts_star_flatten(sem, c, parts.drop_first());
        lemma_parts_star_join(sem, c, parts[0], parts.drop_first().flatten());
    }
}

pub proof fn lemma_star_star<L>(sem: spec_fn(L, Data) -> bool, c: Regex<L>, w: Seq<Data>)
    ensures language::lang(sem, Regex::Star(Box::new(Regex::Star(Box::new(c)))), w)
        == language::lang(sem, Regex::Star(Box::new(c)), w),
{
    if language::lang(sem, Regex::Star(Box::new(Regex::Star(Box::new(c)))), w) {
        let parts = choose|p: Seq<Seq<Data>>| w == p.flatten()
            && forall|k: int| 0 <= k < p.len() ==>
                language::lang(sem, Regex::Star(Box::new(c)), p[k]);
        lemma_parts_star_flatten(sem, c, parts);
    }
    if language::lang(sem, Regex::Star(Box::new(c)), w) {
        lemma_parts_star_single(sem, Regex::Star(Box::new(c)), w);
    }
}

pub proof fn lemma_star_of_nullary<L>(
    sem: spec_fn(L, Data) -> bool, c: Regex<L>, w: Seq<Data>,
)
    requires forall|v: Seq<Data>| language::lang(sem, c, v) ==> v.len() == 0,
    ensures language::lang(sem, Regex::Star(Box::new(c)), w) == (w.len() == 0),
{
    if language::lang(sem, Regex::Star(Box::new(c)), w) {
        let parts = choose|p: Seq<Seq<Data>>| w == p.flatten()
            && forall|k: int| 0 <= k < p.len() ==> language::lang(sem, c, p[k]);
        assert forall|k: int| 0 <= k < parts.len() implies parts[k].len() == 0 by {
            assert(language::lang(sem, c, parts[k]));
        }
        language::lemma_flatten_empty(parts);
    }
    if w.len() == 0 {
        assert(w =~= Seq::<Data>::empty());
        lemma_parts_star_nil(sem, c);
    }
}

pub proof fn lemma_singletons_flatten(w: Seq<Data>)
    ensures Seq::new(w.len(), |k: int| seq![w[k]]).flatten() == w,
    decreases w.len(),
{
    if w.len() == 0 {
        assert(Seq::new(w.len(), |k: int| seq![w[k]]) =~= Seq::<Seq<Data>>::empty());
    } else {
        let prefix = w.drop_last();
        let parts = Seq::new(prefix.len(), |k: int| seq![prefix[k]]);
        lemma_singletons_flatten(prefix);
        assert(Seq::new(w.len(), |k: int| seq![w[k]]) =~= parts.push(seq![w.last()]));
        parts.lemma_flatten_push(seq![w.last()]);
        assert(prefix + seq![w.last()] =~= w);
    }
}

/// Equal tail languages can be substituted after the same first expression.
pub proof fn lemma_parts_concat_tail_congruent<L>(
    sem: spec_fn(L, Data) -> bool,
    c: Regex<L>,
    left: Seq<Regex<L>>,
    right: Seq<Regex<L>>,
    w: Seq<Data>,
)
    requires forall|v: Seq<Data>| language::lang(sem, Regex::Concat(left), v)
        == language::lang(sem, Regex::Concat(right), v),
    ensures language::lang(sem, Regex::Concat(seq![c] + left), w)
        == language::lang(sem, Regex::Concat(seq![c] + right), w),
{
    language::lemma_concat_prepend(sem, c, left, w);
    language::lemma_concat_prepend(sem, c, right, w);
    if language::lang(sem, Regex::Concat(seq![c] + left), w) {
        let (a, b) = choose|a: Seq<Data>, b: Seq<Data>| w == a + b
            && language::lang(sem, c, a)
            && language::lang(sem, Regex::Concat(left), b);
        assert(language::lang(sem, Regex::Concat(right), b));
        assert(exists|a: Seq<Data>, b: Seq<Data>| w == a + b
            && language::lang(sem, c, a)
            && language::lang(sem, Regex::Concat(right), b));
    }
    if language::lang(sem, Regex::Concat(seq![c] + right), w) {
        let (a, b) = choose|a: Seq<Data>, b: Seq<Data>| w == a + b
            && language::lang(sem, c, a)
            && language::lang(sem, Regex::Concat(right), b);
        assert(language::lang(sem, Regex::Concat(left), b));
        assert(exists|a: Seq<Data>, b: Seq<Data>| w == a + b
            && language::lang(sem, c, a)
            && language::lang(sem, Regex::Concat(left), b));
    }
}

pub proof fn lemma_lang_concat_splice<L>(
    sem: spec_fn(L, Data) -> bool, cs: Seq<Regex<L>>, i: int, w: Seq<Data>,
)
    requires 0 <= i < cs.len(), cs[i] is Concat,
    ensures language::lang(sem, Regex::Concat(cs), w)
        == language::lang(sem, Regex::Concat(cs.take(i) + cs[i]->Concat_0 + cs.skip(i + 1)), w),
    decreases i,
{
    let inner = cs[i]->Concat_0;
    let ds = cs.take(i) + inner + cs.skip(i + 1);
    if i == 0 {
        assert(ds =~= inner + cs.drop_first());
        language::lemma_concat_uncons(sem, cs, w);
        lemma_concat_split(sem, inner, cs.drop_first(), w);
        assert(cs[0] == Regex::Concat(inner));
    } else {
        let tail = cs.drop_first();
        assert(tail[i - 1] == cs[i]);
        let flat_tail = tail.take(i - 1) + inner + tail.skip(i);
        assert(cs =~= seq![cs[0]] + tail);
        assert(ds =~= seq![cs[0]] + flat_tail);
        assert forall|v: Seq<Data>| language::lang(sem, Regex::Concat(tail), v)
            == language::lang(sem, Regex::Concat(flat_tail), v) by {
            lemma_lang_concat_splice(sem, tail, i - 1, v);
        }
        lemma_parts_concat_tail_congruent(sem, cs[0], tail, flat_tail, w);
    }
}

pub proof fn lemma_parts_concat_nil<L>(sem: spec_fn(L, Data) -> bool, w: Seq<Data>)
    ensures language::lang(sem, Regex::Concat(Seq::<Regex<L>>::empty()), w) == (w.len() == 0),
{
    if language::lang(sem, Regex::Concat(Seq::<Regex<L>>::empty()), w) {
        let parts = choose|p: Seq<Seq<Data>>| p.len() == 0 && w == p.flatten()
            && forall|k: int| 0 <= k < 0 ==>
                language::lang(sem, Seq::<Regex<L>>::empty()[k], p[k]);
        assert(parts =~= Seq::<Seq<Data>>::empty());
    }
    if w.len() == 0 {
        let parts = Seq::<Seq<Data>>::empty();
        assert(w =~= parts.flatten());
        assert(forall|k: int| 0 <= k < 0 ==>
            language::lang(sem, Seq::<Regex<L>>::empty()[k], parts[k]));
    }
}

pub proof fn lemma_lang_concat_epsilon<L>(
    sem: spec_fn(L, Data) -> bool, cs: Seq<Regex<L>>, i: int, w: Seq<Data>,
)
    requires 0 <= i < cs.len(), cs[i] == Regex::Epsilon,
    ensures language::lang(sem, Regex::Concat(cs), w)
        == language::lang(sem, Regex::Concat(cs.remove(i)), w),
    decreases i,
{
    let tail = cs.drop_first();
    if i == 0 {
        assert(cs.remove(i) =~= tail);
        language::lemma_concat_uncons(sem, cs, w);
        if language::lang(sem, Regex::Concat(cs), w) {
            let (a, b) = choose|a: Seq<Data>, b: Seq<Data>| w == a + b
                && language::lang(sem, cs[0], a)
                && language::lang(sem, Regex::Concat(tail), b);
            assert(a =~= Seq::<Data>::empty());
            assert(b =~= w);
        }
        if language::lang(sem, Regex::Concat(tail), w) {
            let a = Seq::<Data>::empty();
            assert(w == a + w);
            assert(language::lang(sem, cs[0], a));
            assert(exists|a: Seq<Data>, b: Seq<Data>| w == a + b
                && language::lang(sem, cs[0], a)
                && language::lang(sem, Regex::Concat(tail), b));
        }
    } else {
        assert(tail[i - 1] == cs[i]);
        let shorter = tail.remove(i - 1);
        assert(cs =~= seq![cs[0]] + tail);
        assert(cs.remove(i) =~= seq![cs[0]] + shorter);
        assert forall|v: Seq<Data>| language::lang(sem, Regex::Concat(tail), v)
            == language::lang(sem, Regex::Concat(shorter), v) by {
            lemma_lang_concat_epsilon(sem, tail, i - 1, v);
        }
        lemma_parts_concat_tail_congruent(sem, cs[0], tail, shorter, w);
    }
}

pub proof fn lemma_lang_concat_empty<L>(
    sem: spec_fn(L, Data) -> bool, cs: Seq<Regex<L>>, i: int, w: Seq<Data>,
)
    requires 0 <= i < cs.len(), cs[i] == Regex::Empty,
    ensures !language::lang(sem, Regex::Concat(cs), w),
{
    if language::lang(sem, Regex::Concat(cs), w) {
        let parts = choose|p: Seq<Seq<Data>>| p.len() == cs.len() && w == p.flatten()
            && forall|k: int| 0 <= k < cs.len() ==> language::lang(sem, cs[k], p[k]);
        assert(language::lang(sem, cs[i], parts[i]));
    }
}

pub proof fn lemma_regex_rule_sound(theta: Subst, rule: RegexRule, w: Seq<Data>)
    requires regex_rule_valid(rule),
    ensures language::lang(src_sem(theta), regex_rule_lhs(rule), w) == language::lang(src_sem(theta), regex_rule_rhs(rule), w),
{
    let sem = src_sem(theta);
    reveal_with_fuel(language::lang, 3);
    match rule {
        RegexRule::UnionSet(cs, ds) => lemma_lang_union_set(sem, cs, ds, w),
        RegexRule::IntersectSet(cs, ds) => lemma_lang_intersect_set(sem, cs, ds, w),
        RegexRule::UnionFlatten(cs, i) => lemma_lang_union_splice(sem, cs, i, w),
        RegexRule::IntersectFlatten(cs, i) => lemma_lang_intersect_splice(sem, cs, i, w),
        RegexRule::ConcatFlatten(cs, i) => lemma_lang_concat_splice(sem, cs, i, w),
        RegexRule::UnionEmpty(cs, i) | RegexRule::IntersectAll(cs, i) => {
            lemma_test_quantifiers_remove(|r: Regex<SrcTest>| language::lang(sem, r, w), cs, i);
            if rule is UnionEmpty {
                language::lemma_lang_union(sem, cs, w);
                language::lemma_lang_union(sem, cs.remove(i), w);
            } else {
                language::lemma_lang_intersect(sem, cs, w);
                language::lemma_lang_intersect(sem, cs.remove(i), w);
            }
        },
        RegexRule::UnionAll(cs, i) => {
            language::lemma_lang_union(sem, cs, w);
            assert(language::lang(sem, cs[i], w));
        },
        RegexRule::IntersectEmpty(cs, i) => {
            language::lemma_lang_intersect(sem, cs, w);
            assert(!language::lang(sem, cs[i], w));
        },
        RegexRule::ConcatEpsilon(cs, i) => lemma_lang_concat_epsilon(sem, cs, i, w),
        RegexRule::ConcatEmpty(cs, i) => lemma_lang_concat_empty(sem, cs, i, w),
        RegexRule::UnionSingleton(c) => {
            language::lemma_union_optional(sem, c, c, false, w);
            assert(seq![c] + Seq::empty() =~= seq![c]);
        },
        RegexRule::IntersectSingleton(c) => {
            language::lemma_lang_intersect(sem, seq![c], w);
            assert forall|i: int| 0 <= i < 1 implies seq![c][i] == c by { assert(i == 0); }
            if language::lang(sem, Regex::Intersect(seq![c]), w) {
                assert(language::lang(sem, seq![c][0], w));
            }
        },
        RegexRule::ConcatSingleton(c) => language::lemma_concat_singleton(sem, c, w),
        RegexRule::ConcatNil => lemma_parts_concat_nil(sem, w),
        RegexRule::StarStar(c) => lemma_star_star(sem, c, w),
        RegexRule::StarEpsilon => {
            assert forall|v: Seq<Data>| language::lang(sem, Regex::Epsilon, v) implies v.len() == 0 by { }
            lemma_star_of_nullary(sem, Regex::Epsilon, w);
        },
        RegexRule::StarEmpty => {
            assert forall|v: Seq<Data>| language::lang(sem, Regex::Empty, v) implies v.len() == 0 by { }
            lemma_star_of_nullary(sem, Regex::Empty, w);
        },
        RegexRule::StarAll | RegexRule::StarTrue => {
            let c = if rule is StarAll { Regex::All } else { Regex::Test(SrcTest::Bool(true)) };
            let parts = Seq::new(w.len(), |k: int| seq![w[k]]);
            lemma_singletons_flatten(w);
            assert forall|k: int| 0 <= k < parts.len() implies language::lang(sem, c, parts[k]) by {
                assert(parts[k].len() == 1); assert(parts[k][0] == w[k]);
            }
            assert(language::lang(sem, Regex::Star(Box::new(c)), w));
        },
        RegexRule::TestUnion(phis) => {
            let cs = Seq::new(phis.len(), |k: int| Regex::Test(phis[k]));
            assert(regex_rule_lhs(rule)->Union_0 =~= cs);
            if w.len() == 1 { lemma_test_connectives(theta, phis, w[0]); }
            language::lemma_lang_union(sem, cs, w);
            if language::lang(sem, Regex::Union(cs), w) {
                let k = choose|k: int| 0 <= k < cs.len() && language::lang(sem, cs[k], w);
                assert(w.len() == 1 && language::src_test_holds(theta, phis[k], w[0]));
                assert(language::src_test_holds(theta, SrcTest::Or(phis), w[0]));
            }
            if language::lang(sem, Regex::Test(SrcTest::Or(phis)), w) {
                let k = choose|k: int| 0 <= k < phis.len() && language::src_test_holds(theta, phis[k], w[0]);
                assert(language::lang(sem, cs[k], w));
            }
        },
        RegexRule::TestIntersect(phis) => {
            let cs = Seq::new(phis.len(), |k: int| Regex::Test(phis[k]));
            assert(regex_rule_lhs(rule)->Intersect_0 =~= cs);
            if w.len() == 1 { lemma_test_connectives(theta, phis, w[0]); }
            language::lemma_lang_intersect(sem, cs, w);
            if language::lang(sem, Regex::Intersect(cs), w) {
                assert(language::lang(sem, cs[0], w));
                assert(w.len() == 1);
                assert forall|k: int| 0 <= k < phis.len() implies language::src_test_holds(theta, phis[k], w[0]) by {
                    assert(language::lang(sem, cs[k], w));
                }
            }
            if language::lang(sem, Regex::Test(SrcTest::And(phis)), w) {
                assert forall|k: int| 0 <= k < cs.len() implies language::lang(sem, cs[k], w) by { }
            }
        },
        RegexRule::IntersectEpsilonTest(cs, i, j) => {
            language::lemma_lang_intersect(sem, cs, w);
            if language::lang(sem, Regex::Intersect(cs), w) {
                assert(language::lang(sem, cs[i], w));
                assert(language::lang(sem, cs[j], w));
            }
        },
        RegexRule::NotNot(c) => {
            assert(language::lang(sem, regex_rule_lhs(rule), w) == language::lang(sem, c, w));
        },
        RegexRule::UnionNil | RegexRule::IntersectNil | RegexRule::NotEmpty | RegexRule::NotAll | RegexRule::TestFalse => {
            assert(language::lang(sem, regex_rule_lhs(rule), w) == language::lang(sem, regex_rule_rhs(rule), w));
        },
    }
}

/// Finite derivations generate exactly the equivalence/congruence closure of the rules.
pub enum TestSim {
    Rule(TestRule), Refl(SrcTest), Sym(Box<TestSim>), Trans(Box<TestSim>, Box<TestSim>),
    And(Seq<TestSim>), Or(Seq<TestSim>),
}

pub enum Sim {
    Rule(RegexRule), Refl(Regex<SrcTest>), Sym(Box<Sim>), Trans(Box<Sim>, Box<Sim>),
    Test(TestSim), Union(Seq<Sim>), Concat(Seq<Sim>), Intersect(Seq<Sim>), Star(Box<Sim>), Not(Box<Sim>),
}

pub open spec fn test_sim_lhs(d: TestSim) -> SrcTest decreases d {
    match d {
        TestSim::Rule(rule) => test_rule_lhs(rule),
        TestSim::Refl(t) => t,
        TestSim::Sym(c) => test_sim_rhs(*c),
        TestSim::Trans(a, _) => test_sim_lhs(*a),
        TestSim::And(ds) => SrcTest::And(Seq::new(ds.len(), |k: int| if 0 <= k < ds.len() { test_sim_lhs(ds[k]) } else { SrcTest::Bool(true) })),
        TestSim::Or(ds) => SrcTest::Or(Seq::new(ds.len(), |k: int| if 0 <= k < ds.len() { test_sim_lhs(ds[k]) } else { SrcTest::Bool(true) })),
    }
}

pub open spec fn test_sim_rhs(d: TestSim) -> SrcTest decreases d {
    match d {
        TestSim::Rule(rule) => test_rule_rhs(rule),
        TestSim::Refl(t) => t,
        TestSim::Sym(c) => test_sim_lhs(*c),
        TestSim::Trans(_, b) => test_sim_rhs(*b),
        TestSim::And(ds) => SrcTest::And(Seq::new(ds.len(), |k: int| if 0 <= k < ds.len() { test_sim_rhs(ds[k]) } else { SrcTest::Bool(true) })),
        TestSim::Or(ds) => SrcTest::Or(Seq::new(ds.len(), |k: int| if 0 <= k < ds.len() { test_sim_rhs(ds[k]) } else { SrcTest::Bool(true) })),
    }
}

pub open spec fn test_sim_valid(d: TestSim) -> bool decreases d {
    match d {
        TestSim::Rule(rule) => test_rule_valid(rule),
        TestSim::Refl(_) => true,
        TestSim::Sym(c) => test_sim_valid(*c),
        TestSim::Trans(a, b) => test_sim_valid(*a) && test_sim_valid(*b) && test_sim_rhs(*a) == test_sim_lhs(*b),
        TestSim::And(ds) => forall|k: int| 0 <= k < ds.len() ==> test_sim_valid(#[trigger] ds[k]),
        TestSim::Or(ds) => forall|k: int| 0 <= k < ds.len() ==> test_sim_valid(#[trigger] ds[k]),
    }
}

pub open spec fn sim_lhs(d: Sim) -> Regex<SrcTest> decreases d {
    match d {
        Sim::Rule(rule) => regex_rule_lhs(rule),
        Sim::Refl(r) => r,
        Sim::Sym(c) => sim_rhs(*c),
        Sim::Trans(a, _) => sim_lhs(*a),
        Sim::Test(t) => Regex::Test(test_sim_lhs(t)),
        Sim::Union(ds) => Regex::Union(Seq::new(ds.len(), |k: int| if 0 <= k < ds.len() { sim_lhs(ds[k]) } else { Regex::Empty })),
        Sim::Concat(ds) => Regex::Concat(Seq::new(ds.len(), |k: int| if 0 <= k < ds.len() { sim_lhs(ds[k]) } else { Regex::Empty })),
        Sim::Intersect(ds) => Regex::Intersect(Seq::new(ds.len(), |k: int| if 0 <= k < ds.len() { sim_lhs(ds[k]) } else { Regex::Empty })),
        Sim::Star(c) => Regex::Star(Box::new(sim_lhs(*c))),
        Sim::Not(c) => Regex::Not(Box::new(sim_lhs(*c))),
    }
}

pub open spec fn sim_rhs(d: Sim) -> Regex<SrcTest> decreases d {
    match d {
        Sim::Rule(rule) => regex_rule_rhs(rule),
        Sim::Refl(r) => r,
        Sim::Sym(c) => sim_lhs(*c),
        Sim::Trans(_, b) => sim_rhs(*b),
        Sim::Test(t) => Regex::Test(test_sim_rhs(t)),
        Sim::Union(ds) => Regex::Union(Seq::new(ds.len(), |k: int| if 0 <= k < ds.len() { sim_rhs(ds[k]) } else { Regex::Empty })),
        Sim::Concat(ds) => Regex::Concat(Seq::new(ds.len(), |k: int| if 0 <= k < ds.len() { sim_rhs(ds[k]) } else { Regex::Empty })),
        Sim::Intersect(ds) => Regex::Intersect(Seq::new(ds.len(), |k: int| if 0 <= k < ds.len() { sim_rhs(ds[k]) } else { Regex::Empty })),
        Sim::Star(c) => Regex::Star(Box::new(sim_rhs(*c))),
        Sim::Not(c) => Regex::Not(Box::new(sim_rhs(*c))),
    }
}

pub open spec fn sim_valid(d: Sim) -> bool decreases d {
    match d {
        Sim::Rule(rule) => regex_rule_valid(rule),
        Sim::Refl(_) => true,
        Sim::Sym(c) => sim_valid(*c),
        Sim::Trans(a, b) => sim_valid(*a) && sim_valid(*b) && sim_rhs(*a) == sim_lhs(*b),
        Sim::Test(t) => test_sim_valid(t),
        Sim::Union(ds) => forall|k: int| 0 <= k < ds.len() ==> sim_valid(#[trigger] ds[k]),
        Sim::Concat(ds) => forall|k: int| 0 <= k < ds.len() ==> sim_valid(#[trigger] ds[k]),
        Sim::Intersect(ds) => forall|k: int| 0 <= k < ds.len() ==> sim_valid(#[trigger] ds[k]),
        Sim::Star(c) | Sim::Not(c) => sim_valid(*c),
    }
}

pub open spec fn test_similar(a: SrcTest, b: SrcTest) -> bool {
    exists|d: TestSim| #[trigger] test_sim_valid(d) && test_sim_lhs(d) == a && test_sim_rhs(d) == b
}

pub open spec fn similar(r: Regex<SrcTest>, s: Regex<SrcTest>) -> bool {
    exists|d: Sim| #[trigger] sim_valid(d) && sim_lhs(d) == r && sim_rhs(d) == s
}

pub proof fn lemma_test_sim_valid_children(ds: Seq<TestSim>)
    ensures
        test_sim_valid(TestSim::And(ds)) == (forall|k: int| 0 <= k < ds.len() ==> test_sim_valid(#[trigger] ds[k])),
        test_sim_valid(TestSim::Or(ds)) == (forall|k: int| 0 <= k < ds.len() ==> test_sim_valid(#[trigger] ds[k])),
{
    assert((TestSim::And(ds))->And_0 =~= ds);
    assert((TestSim::Or(ds))->Or_0 =~= ds);
}

pub proof fn lemma_sim_valid_children(ds: Seq<Sim>)
    ensures
        sim_valid(Sim::Union(ds)) == (forall|k: int| 0 <= k < ds.len() ==> sim_valid(#[trigger] ds[k])),
        sim_valid(Sim::Intersect(ds)) == (forall|k: int| 0 <= k < ds.len() ==> sim_valid(#[trigger] ds[k])),
        sim_valid(Sim::Concat(ds)) == (forall|k: int| 0 <= k < ds.len() ==> sim_valid(#[trigger] ds[k])),
{
    assert((Sim::Union(ds))->Union_0 =~= ds);
    assert((Sim::Intersect(ds))->Intersect_0 =~= ds);
    assert((Sim::Concat(ds))->Concat_0 =~= ds);
}

pub proof fn lemma_test_similar_preserves(theta: Subst, d: TestSim, e: Data)
    requires test_sim_valid(d),
    ensures language::src_test_holds(theta, test_sim_lhs(d), e) == language::src_test_holds(theta, test_sim_rhs(d), e),
    decreases d,
{
    reveal_with_fuel(test_sim_valid, 2);
    match d {
        TestSim::Rule(rule) => lemma_test_rule_sound(theta, rule, e),
        TestSim::Refl(_) => {},
        TestSim::Sym(c) => lemma_test_similar_preserves(theta, *c, e),
        TestSim::Trans(a, b) => {
            lemma_test_similar_preserves(theta, *a, e);
            lemma_test_similar_preserves(theta, *b, e);
        },
        TestSim::And(ds) => {
            lemma_test_sim_valid_children(ds);
            let cs = test_sim_lhs(d)->And_0;
            let es = test_sim_rhs(d)->And_0;
            assert(cs.len() == ds.len() && es.len() == ds.len());
            assert forall|k: int| 0 <= k < ds.len() implies language::src_test_holds(theta, cs[k], e) == language::src_test_holds(theta, es[k], e) by {
                assert(test_sim_valid(d));
                lemma_test_similar_preserves(theta, ds[k], e);
            }
            lemma_test_connectives(theta, cs, e); lemma_test_connectives(theta, es, e);
        },
        TestSim::Or(ds) => {
            lemma_test_sim_valid_children(ds);
            let cs = test_sim_lhs(d)->Or_0;
            let es = test_sim_rhs(d)->Or_0;
            assert(cs.len() == ds.len() && es.len() == ds.len());
            assert forall|k: int| 0 <= k < ds.len() implies language::src_test_holds(theta, cs[k], e) == language::src_test_holds(theta, es[k], e) by {
                assert(test_sim_valid(d));
                lemma_test_similar_preserves(theta, ds[k], e);
            }
            lemma_test_connectives(theta, cs, e); lemma_test_connectives(theta, es, e);
            if language::src_test_holds(theta, SrcTest::Or(cs), e) {
                let k = choose|k: int| 0 <= k < cs.len() && language::src_test_holds(theta, cs[k], e);
                assert(language::src_test_holds(theta, es[k], e));
            }
            if language::src_test_holds(theta, SrcTest::Or(es), e) {
                let k = choose|k: int| 0 <= k < es.len() && language::src_test_holds(theta, es[k], e);
                assert(language::src_test_holds(theta, cs[k], e));
            }
        },
    }
}

pub proof fn lemma_similar_preserves_lang(theta: Subst, d: Sim, w: Seq<Data>)
    requires sim_valid(d),
    ensures language::lang(src_sem(theta), sim_lhs(d), w) == language::lang(src_sem(theta), sim_rhs(d), w),
    decreases d,
{
    reveal_with_fuel(sim_valid, 2);
    let sem = src_sem(theta);
    match d {
        Sim::Rule(rule) => lemma_regex_rule_sound(theta, rule, w),
        Sim::Refl(_) => {},
        Sim::Sym(c) => lemma_similar_preserves_lang(theta, *c, w),
        Sim::Trans(a, b) => {
            lemma_similar_preserves_lang(theta, *a, w);
            lemma_similar_preserves_lang(theta, *b, w);
        },
        Sim::Test(t) => {
            if w.len() == 1 { lemma_test_similar_preserves(theta, t, w[0]); }
        },
        Sim::Not(c) => lemma_similar_preserves_lang(theta, *c, w),
        Sim::Star(c) => {
            assert forall|v: Seq<Data>| language::lang(sem, sim_lhs(*c), v) == language::lang(sem, sim_rhs(*c), v) by {
                lemma_similar_preserves_lang(theta, *c, v);
            }
            if language::lang(sem, sim_lhs(d), w) {
                let parts = choose|parts: Seq<Seq<Data>>| w == parts.flatten()
                    && forall|k: int| 0 <= k < parts.len() ==> language::lang(sem, sim_lhs(*c), parts[k]);
                assert forall|k: int| 0 <= k < parts.len() implies language::lang(sem, sim_rhs(*c), parts[k]) by { }
                assert(language::lang(sem, sim_rhs(d), w));
            }
            if language::lang(sem, sim_rhs(d), w) {
                let parts = choose|parts: Seq<Seq<Data>>| w == parts.flatten()
                    && forall|k: int| 0 <= k < parts.len() ==> language::lang(sem, sim_rhs(*c), parts[k]);
                assert forall|k: int| 0 <= k < parts.len() implies language::lang(sem, sim_lhs(*c), parts[k]) by { }
                assert(language::lang(sem, sim_lhs(d), w));
            }
        },
        Sim::Union(ds) => {
            lemma_sim_valid_children(ds);
            let cs = sim_lhs(d)->Union_0;
            let es = sim_rhs(d)->Union_0;
            assert(cs.len() == ds.len() && es.len() == ds.len());
            assert forall|k: int| 0 <= k < ds.len() implies language::lang(sem, cs[k], w) == language::lang(sem, es[k], w) by {
                assert(sim_valid(d));
                lemma_similar_preserves_lang(theta, ds[k], w);
            }
            language::lemma_lang_union(sem, cs, w); language::lemma_lang_union(sem, es, w);
            if language::lang(sem, Regex::Union(cs), w) {
                let k = choose|k: int| 0 <= k < cs.len() && language::lang(sem, cs[k], w);
                assert(language::lang(sem, es[k], w));
            }
            if language::lang(sem, Regex::Union(es), w) {
                let k = choose|k: int| 0 <= k < es.len() && language::lang(sem, es[k], w);
                assert(language::lang(sem, cs[k], w));
            }
        },
        Sim::Intersect(ds) => {
            lemma_sim_valid_children(ds);
            let cs = sim_lhs(d)->Intersect_0;
            let es = sim_rhs(d)->Intersect_0;
            assert(cs.len() == ds.len() && es.len() == ds.len());
            assert forall|k: int| 0 <= k < ds.len() implies language::lang(sem, cs[k], w) == language::lang(sem, es[k], w) by {
                assert(sim_valid(d));
                lemma_similar_preserves_lang(theta, ds[k], w);
            }
            language::lemma_lang_intersect(sem, cs, w); language::lemma_lang_intersect(sem, es, w);
        },
        Sim::Concat(ds) => {
            lemma_sim_valid_children(ds);
            let cs = sim_lhs(d)->Concat_0;
            let es = sim_rhs(d)->Concat_0;
            assert(cs.len() == ds.len() && es.len() == ds.len());
            assert forall|k: int, v: Seq<Data>| 0 <= k < ds.len() implies language::lang(sem, cs[k], v) == language::lang(sem, es[k], v) by {
                assert(sim_valid(d));
                lemma_similar_preserves_lang(theta, ds[k], v);
            }
            if language::lang(sem, Regex::Concat(cs), w) {
                let parts = choose|parts: Seq<Seq<Data>>| parts.len() == cs.len() && w == parts.flatten()
                    && forall|k: int| 0 <= k < cs.len() ==> language::lang(sem, cs[k], parts[k]);
                assert forall|k: int| 0 <= k < es.len() implies language::lang(sem, es[k], parts[k]) by { }
                assert(language::lang(sem, Regex::Concat(es), w));
            }
            if language::lang(sem, Regex::Concat(es), w) {
                let parts = choose|parts: Seq<Seq<Data>>| parts.len() == es.len() && w == parts.flatten()
                    && forall|k: int| 0 <= k < es.len() ==> language::lang(sem, es[k], parts[k]);
                assert forall|k: int| 0 <= k < cs.len() implies language::lang(sem, cs[k], parts[k]) by { }
                assert(language::lang(sem, Regex::Concat(cs), w));
            }
        },
    }
}

/// Paper, Lemma (Similarity preserves language).
pub proof fn theorem_similarity_preserves_language(r: Regex<SrcTest>, s: Regex<SrcTest>, theta: Subst, w: Seq<Data>)
    requires similar(r, s),
    ensures language::lang(src_sem(theta), r, w) == language::lang(src_sem(theta), s, w),
{
    let d = choose|d: Sim| sim_valid(d) && sim_lhs(d) == r && sim_rhs(d) == s;
    lemma_similar_preserves_lang(theta, d, w);
}

/// Similar tails give identical policy-visible decisions under every head.
pub proof fn theorem_similar_tails_same_decision(head: Head, r: Regex<SrcTest>, s: Regex<SrcTest>, request: Data, history: Seq<Data>)
    requires similar(r, s),
    ensures language::pair_lang(head, r, request, history) == language::pair_lang(head, s, request, history),
{
    if language::pair_lang(head, r, request, history) {
        let theta = choose|theta: Subst| language::head_match(head, request, theta) && theta.dom() == language::head_vars(head)
            && language::lang(src_sem(theta), r, history);
        theorem_similarity_preserves_language(r, s, theta, history);
        assert(language::pair_lang(head, s, request, history));
    }
    if language::pair_lang(head, s, request, history) {
        let theta = choose|theta: Subst| language::head_match(head, request, theta) && theta.dom() == language::head_vars(head)
            && language::lang(src_sem(theta), s, history);
        theorem_similarity_preserves_language(r, s, theta, history);
        assert(language::pair_lang(head, r, request, history));
    }
}

/// Regorus deviation: missing paths make both Eq and Neq false, not complements.
pub proof fn theorem_eq_or_neq_not_similar_to_true()
    ensures !test_similar(
        SrcTest::Or(seq![SrcTest::Eq(seq![Data::String(seq!['k'])], Term::Constant(Data::Null)),
                         SrcTest::Neq(seq![Data::String(seq!['k'])], Term::Constant(Data::Null))]),
        SrcTest::Bool(true)),
{
    let path = seq![Data::String(seq!['k'])];
    let cs = seq![SrcTest::Eq(path, Term::Constant(Data::Null)), SrcTest::Neq(path, Term::Constant(Data::Null))];
    let lhs = SrcTest::Or(cs);
    let rhs = SrcTest::Bool(true);
    let theta = Map::empty();
    let event = Data::Object(Map::empty());
    reveal_with_fuel(language::select, 2);
    assert(language::select(event, path) is None);
    lemma_test_connectives(theta, cs, event);
    assert forall|k: int| 0 <= k < cs.len() implies !language::src_test_holds(theta, cs[k], event) by {
        assert(k == 0 || k == 1);
    }
    if test_similar(lhs, rhs) {
        let d = choose|d: TestSim| test_sim_valid(d) && test_sim_lhs(d) == lhs && test_sim_rhs(d) == rhs;
        lemma_test_similar_preserves(theta, d, event);
    }
}

/// Only signed kernel primitives have complements; source Eq/Neq do not.
pub open spec fn test_complement(t: model::Test) -> model::Test
    decreases t,
{
    match t {
        model::Test::True => model::Test::False,
        model::Test::False => model::Test::True,
        model::Test::Atom(p, positive) => model::Test::Atom(p, !positive),
        model::Test::And(cs) => model::Test::Or(Seq::new(cs.len(), |k: int| if 0 <= k < cs.len() { test_complement(cs[k]) } else { model::Test::True })),
        model::Test::Or(cs) => model::Test::And(Seq::new(cs.len(), |k: int| if 0 <= k < cs.len() { test_complement(cs[k]) } else { model::Test::False })),
    }
}

pub proof fn lemma_test_complement_holds(s: model::Symbols, theta: Seq<Data>, t: model::Test, e: Data)
    ensures model::test_holds(s, theta, test_complement(t), e) == !model::test_holds(s, theta, t, e),
    decreases t,
{
    match t {
        model::Test::And(cs) => {
            let ds = test_complement(t)->Or_0;
            assert(ds.len() == cs.len());
            assert((model::Test::And(cs))->And_0 =~= cs);
            assert((model::Test::Or(ds))->Or_0 =~= ds);
            assert forall|k: int| 0 <= k < cs.len() implies model::test_holds(s, theta, ds[k], e) == !model::test_holds(s, theta, cs[k], e) by {
                lemma_test_complement_holds(s, theta, cs[k], e);
            }
            if !model::test_holds(s, theta, t, e) {
                let k = choose|k: int| 0 <= k < cs.len() && !model::test_holds(s, theta, cs[k], e);
                assert(model::test_holds(s, theta, ds[k], e));
            }
            if model::test_holds(s, theta, test_complement(t), e) {
                let k = choose|k: int| 0 <= k < ds.len() && model::test_holds(s, theta, ds[k], e);
                assert(!model::test_holds(s, theta, cs[k], e));
            }
        },
        model::Test::Or(cs) => {
            let ds = test_complement(t)->And_0;
            assert(ds.len() == cs.len());
            assert((model::Test::Or(cs))->Or_0 =~= cs);
            assert((model::Test::And(ds))->And_0 =~= ds);
            assert forall|k: int| 0 <= k < cs.len() implies model::test_holds(s, theta, ds[k], e) == !model::test_holds(s, theta, cs[k], e) by {
                lemma_test_complement_holds(s, theta, cs[k], e);
            }
        },
        _ => {},
    }
}

pub proof fn lemma_test_complement_involutive(t: model::Test)
    ensures test_complement(test_complement(t)) == t,
    decreases t,
{
    reveal_with_fuel(test_complement, 2);
    match t {
        model::Test::And(cs) => {
            assert forall|k: int| 0 <= k < cs.len() implies test_complement(test_complement(cs[k])) == cs[k] by {
                lemma_test_complement_involutive(cs[k]);
            }
            assert(test_complement(test_complement(t))->And_0 =~= cs);
        },
        model::Test::Or(cs) => {
            assert forall|k: int| 0 <= k < cs.len() implies test_complement(test_complement(cs[k])) == cs[k] by {
                lemma_test_complement_involutive(cs[k]);
            }
            assert(test_complement(test_complement(t))->Or_0 =~= cs);
        },
        _ => {},
    }
}

}
