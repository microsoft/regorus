//! Layer 0: proofs about the typed semantics and the policy questions
//! (`junco_core::spec::{semantics, questions}`; paper `sec:rules`, `sec:policy`, appendix
//! `app:policy-reduction`), plus the constants of a rule, which the analyzer specification reads.
//!
//! The valuation `θ` of the paper is the candidate itself; histories are oldest first and never
//! contain the candidate. Component equality is `PartialEqSpec::eq_spec`. A policy is a finite
//! sequence of rules; its order is irrelevant to every predicate below.
use alloc::boxed::Box;
use history_syntax::Comparison;
use history_syntax::Event;
use history_syntax::event::specs::EventSpec;
use history_syntax::spec::events::{HeadView, PatternView, RegexView, RuleView, TestView};
use junco_core::spec::questions::{
    DomainsView, constants_union, covers, in_domains, pattern_constant, refines, regex_constant_at,
    regex_constant_forest, regex_constants, rule_constants, test_constant_at, test_constant_forest,
    test_constants,
};
use junco_core::spec::semantics as tdsl;
use junco_core::spec::semantics::{policy_denies, rule_violated, rule_wf};
use vstd::prelude::*;
use vstd::std_specs::cmp::PartialEqSpec;

verus! {

broadcast use {vstd::std_specs::vec::group_vec_axioms, vstd::seq::group_seq_lemmas};

// ----- theorem statements -----

/// `P ⊑ Q` iff `P` covers every rule of `Q` (appendix `app:policy-reduction`).
pub open spec fn stmt_refines_iff_covers<E: Event>() -> bool {
    forall|domains: DomainsView<E::Component>, p: Seq<RuleView<E::Component>>, q: Seq<RuleView<E::Component>>|
        #[trigger] refines::<E>(domains, p, q) <==> forall|i: int| 0 <= i < q.len() ==> covers::<E>(domains, p, #[trigger] q[i])
}

/// Removing a covered rule changes no decision (appendix `app:policy-reduction`): with `others` the policy
/// without the rule, the two policies deny the same pairs iff `others` covers the rule.
pub open spec fn stmt_redundant_iff_covered<E: Event>() -> bool {
    forall|domains: DomainsView<E::Component>, others: Seq<RuleView<E::Component>>, rule: RuleView<E::Component>|
        #[trigger] covers::<E>(domains, others, rule) <==> forall|c: E, h: Seq<E>|
            in_domains::<E>(domains, c, h)
                ==> (#[trigger] policy_denies(others.push(rule), c, h) == policy_denies(others, c, h))
}

/// Genericity: semantics depends only on which values are equal and on equality with the
/// rules' constants. Hence a property proved for every pair over one set of values holds for
/// every pair over any other: map the finitely many values of a pair injectively, fixing the
/// constants. Stated for one rule; policies follow pointwise.
pub open spec fn renaming_preserves_eq<C: PartialEq>(f: spec_fn(C) -> C, fixed: Set<C>, values: ISet<C>) -> bool {
    &&& forall|x: C, y: C| values.contains(x) && values.contains(y) ==> (#[trigger] f(x).eq_spec(&#[trigger] f(y)) == x.eq_spec(&y))
    &&& forall|x: C, k: C| values.contains(x) && fixed.contains(k) ==> (#[trigger] f(x).eq_spec(&k) == #[trigger] x.eq_spec(&k))
}

/// A renaming that also keeps every value's coordinate tag.
pub open spec fn renaming_preserves<E: Event>(f: spec_fn(E::Component) -> E::Component, fixed: Set<E::Component>, values: ISet<E::Component>) -> bool {
    renaming_preserves_eq(f, fixed, values)
        && forall|x: E::Component| values.contains(x) ==> E::coordinate_spec(#[trigger] f(x)) == E::coordinate_spec(x)
}

pub open spec fn rename_event<C>(f: Seq<spec_fn(C) -> C>, e: Seq<C>) -> Seq<C> {
    Seq::new(e.len(), |i: int| f[i](e[i]))
}

pub open spec fn rename_history<C>(f: Seq<spec_fn(C) -> C>, h: Seq<Seq<C>>) -> Seq<Seq<C>> {
    h.map(|i: int, e: Seq<C>| rename_event(f, e))
}

/// The values used at one coordinate of a candidate and its history.
pub open spec fn pair_values<C>(candidate: Seq<C>, history: Seq<Seq<C>>, coordinate: int) -> ISet<C> {
    ISet::new(|x: C| (0 <= coordinate < candidate.len() && x == candidate[coordinate])
        || exists|i: int| 0 <= i < history.len() && 0 <= coordinate < history[i].len()
            && #[trigger] history[i][coordinate] == x)
}

/// Rule violation (`rule_violated_view`) is invariant under tag-preserving renamings of the
/// pair's values that fix the rule's constants.
pub open spec fn stmt_genericity<E: Event>() -> bool {
    forall|rule: RuleView<E::Component>, candidate: Seq<E::Component>, history: Seq<Seq<E::Component>>, f: Seq<spec_fn(E::Component) -> E::Component>|
        rule_wf(rule) && candidate.len() == rule.head.len()
            && (forall|i: int| 0 <= i < history.len() ==> history[i].len() == candidate.len())
            && renamings_preserve::<E>(f, rule_constants(rule),
                Seq::new(candidate.len(), |i: int| pair_values(candidate, history, i)))
            ==> (tdsl::rule_violated_view(rule, candidate, history)
                == #[trigger] tdsl::rule_violated_view(rule, rename_event(f, candidate), rename_history(f, history)))
}

pub proof fn lemma_constants_union<C>(sets: Seq<Set<C>>, i: int)
    requires 0 <= i < sets.len(),
    ensures sets[i].subset_of(constants_union(sets)),
    decreases sets.len(),
{
    if i < sets.len() - 1 {
        lemma_constants_union(sets.drop_last(), i);
        assert(sets[i] == sets.drop_last()[i]);
    } else {
        assert(sets[i] == sets.last());
    }
}

proof fn lemma_test_constant_forest_index<C>(tests: Seq<TestView<C>>, arity: nat, j: int)
    requires 0 <= j < arity,
    ensures test_constant_forest(tests, j) == constants_union(Seq::new(tests.len(), |i: int|
        if 0 <= i < tests.len() { test_constants(tests[i], arity)[j] } else { Set::empty() })),
    decreases tests.len(),
{
    if tests.len() > 0 {
        let prior = tests.drop_last();
        lemma_test_constant_forest_index(prior, arity, j);
        let values = Seq::new(tests.len(), |i: int|
            if 0 <= i < tests.len() { test_constants(tests[i], arity)[j] } else { Set::empty() });
        let prefix = Seq::new(prior.len(), |i: int|
            if 0 <= i < prior.len() { test_constants(prior[i], arity)[j] } else { Set::empty() });
        assert(values.drop_last() =~= prefix);
        assert(values.last() == test_constant_at(tests.last(), j));
    }
}

proof fn lemma_regex_constant_forest_index<C>(regexes: Seq<RegexView<C>>, arity: nat, j: int)
    requires 0 <= j < arity,
    ensures regex_constant_forest(regexes, j) == constants_union(Seq::new(regexes.len(), |i: int|
        if 0 <= i < regexes.len() { regex_constants(regexes[i], arity)[j] } else { Set::empty() })),
    decreases regexes.len(),
{
    if regexes.len() > 0 {
        let prior = regexes.drop_last();
        lemma_regex_constant_forest_index(prior, arity, j);
        let values = Seq::new(regexes.len(), |i: int|
            if 0 <= i < regexes.len() { regex_constants(regexes[i], arity)[j] } else { Set::empty() });
        let prefix = Seq::new(prior.len(), |i: int|
            if 0 <= i < prior.len() { regex_constants(prior[i], arity)[j] } else { Set::empty() });
        assert(values.drop_last() =~= prefix);
        assert(values.last() == regex_constant_at(regexes.last(), j));
    }
}

/// One coordinate of a test's constants, with recursive calls left at their own fuel level.
pub proof fn lemma_test_constants_index<C>(test: TestView<C>, arity: nat, j: int)
    requires 0 <= j < arity,
    ensures test_constants(test, arity)[j] == match test {
        TestView::True | TestView::False => Set::empty(),
        TestView::Atom { pattern, .. } =>
            if j == pattern.component { pattern_constant(pattern.pattern) } else { Set::empty() },
        TestView::And(cs) | TestView::Or(cs) => constants_union(Seq::new(cs.len(), |i: int|
            if 0 <= i < cs.len() { test_constants(cs[i], arity)[j] } else { Set::empty() })),
    },
{
    reveal_with_fuel(test_constant_at, 2);
    match test {
        TestView::And(cs) | TestView::Or(cs) => lemma_test_constant_forest_index(cs, arity, j),
        _ => {},
    }
}

/// The analogous indexed unfolding for regex constants.
pub proof fn lemma_regex_constants_index<C>(regex: RegexView<C>, arity: nat, j: int)
    requires 0 <= j < arity,
    ensures regex_constants(regex, arity)[j] == match regex {
        RegexView::Empty | RegexView::All | RegexView::Epsilon => Set::empty(),
        RegexView::Test(test) => test_constants(test, arity)[j],
        RegexView::Union(cs) | RegexView::Concat(cs) | RegexView::Intersect(cs) =>
            constants_union(Seq::new(cs.len(), |i: int|
                if 0 <= i < cs.len() { regex_constants(cs[i], arity)[j] } else { Set::empty() })),
        RegexView::Star(child) | RegexView::Not(child) => regex_constants(*child, arity)[j],
    },
{
    reveal_with_fuel(regex_constant_at, 2);
    match regex {
        RegexView::Union(cs) | RegexView::Concat(cs) | RegexView::Intersect(cs) =>
            lemma_regex_constant_forest_index(cs, arity, j),
        _ => {},
    }
}
// ----- proofs -----

/// Appending a rule to a policy adds exactly that rule's violations.
pub proof fn lemma_policy_denies_push<E: Event>(
    policy: Seq<RuleView<E::Component>>, rule: RuleView<E::Component>, c: E, h: Seq<E>,
)
    ensures
        policy_denies(policy.push(rule), c, h)
            == (policy_denies(policy, c, h) || rule_violated(rule, c, h)),
{
    let q = policy.push(rule);
    if policy_denies(policy, c, h) {
        let i = choose|i: int| 0 <= i < policy.len() && #[trigger] rule_violated(policy[i], c, h);
        assert(q[i] == policy[i]);
        assert(rule_violated(q[i], c, h));
    }
    if rule_violated(rule, c, h) {
        let n = policy.len() as int;
        assert(q[n] == rule);
        assert(rule_violated(q[n], c, h));
    }
    if policy_denies(q, c, h) {
        let i = choose|i: int| 0 <= i < q.len() && #[trigger] rule_violated(q[i], c, h);
        if i < policy.len() {
            assert(q[i] == policy[i]);
            assert(rule_violated(policy[i], c, h));
        }
    }
}

pub proof fn theorem_refines_iff_covers<E: Event>()
    ensures stmt_refines_iff_covers::<E>(),
{
    assert forall|domains: DomainsView<E::Component>, p: Seq<RuleView<E::Component>>, q: Seq<RuleView<E::Component>>|
        #[trigger] refines::<E>(domains, p, q) <==> forall|i: int| 0 <= i < q.len() ==> covers::<E>(domains, p, #[trigger] q[i])
    by {
        if refines::<E>(domains, p, q) {
            assert forall|i: int| 0 <= i < q.len() implies covers::<E>(domains, p, #[trigger] q[i]) by {
                assert forall|c: E, h: Seq<E>|
                    in_domains::<E>(domains, c, h) && #[trigger] rule_violated(q[i], c, h)
                    implies policy_denies(p, c, h) by {
                    assert(policy_denies(q, c, h));
                    assert(!tdsl::policy_permits(q, c, h));
                }
            }
        }
        if forall|i: int| 0 <= i < q.len() ==> covers::<E>(domains, p, #[trigger] q[i]) {
            assert forall|c: E, h: Seq<E>|
                in_domains::<E>(domains, c, h) && tdsl::policy_permits(p, c, h)
                implies #[trigger] tdsl::policy_permits(q, c, h) by {
                if policy_denies(q, c, h) {
                    let i = choose|i: int| 0 <= i < q.len() && #[trigger] rule_violated(q[i], c, h);
                    assert(covers::<E>(domains, p, q[i]));
                }
            }
        }
    }
}

pub proof fn theorem_redundant_iff_covered<E: Event>()
    ensures stmt_redundant_iff_covered::<E>(),
{
    assert forall|domains: DomainsView<E::Component>, others: Seq<RuleView<E::Component>>, rule: RuleView<E::Component>|
        #[trigger] covers::<E>(domains, others, rule) <==> forall|c: E, h: Seq<E>|
            in_domains::<E>(domains, c, h)
                ==> (#[trigger] policy_denies(others.push(rule), c, h) == policy_denies(others, c, h))
    by {
        if covers::<E>(domains, others, rule) {
            assert forall|c: E, h: Seq<E>|
                in_domains::<E>(domains, c, h)
                implies (#[trigger] policy_denies(others.push(rule), c, h)
                    == policy_denies(others, c, h)) by {
                lemma_policy_denies_push(others, rule, c, h);
            }
        }
        if forall|c: E, h: Seq<E>|
            in_domains::<E>(domains, c, h)
                ==> (#[trigger] policy_denies(others.push(rule), c, h) == policy_denies(others, c, h))
        {
            assert forall|c: E, h: Seq<E>|
                in_domains::<E>(domains, c, h) && #[trigger] rule_violated(rule, c, h)
                implies policy_denies(others, c, h) by {
                lemma_policy_denies_push(others, rule, c, h);
                assert(policy_denies(others.push(rule), c, h) == policy_denies(others, c, h));
            }
        }
    }
}

// ----- genericity -----

/// Every component lies in its corresponding value set, at exactly that arity.
pub open spec fn values_in<C>(e: Seq<C>, values: Seq<ISet<C>>) -> bool {
    e.len() == values.len() && forall|i: int| 0 <= i < e.len() ==> #[trigger] values[i].contains(e[i])
}

pub open spec fn word_values_in<C>(w: Seq<Seq<C>>, values: Seq<ISet<C>>) -> bool {
    forall|i: int| 0 <= i < w.len() ==> #[trigger] values_in(w[i], values)
}

pub open spec fn renamings_preserve_eq<C: PartialEq>(
    f: Seq<spec_fn(C) -> C>, fixed: Seq<Set<C>>, values: Seq<ISet<C>>,
) -> bool {
    f.len() == fixed.len() && values.len() == fixed.len()
        && forall|i: int| 0 <= i < f.len() ==> renaming_preserves_eq(#[trigger] f[i], fixed[i], values[i])
}

pub open spec fn renamings_preserve<E: Event>(
    f: Seq<spec_fn(E::Component) -> E::Component>, fixed: Seq<Set<E::Component>>, values: Seq<ISet<E::Component>>,
) -> bool {
    f.len() == fixed.len() && values.len() == fixed.len()
        && forall|i: int| 0 <= i < f.len() ==> renaming_preserves::<E>(#[trigger] f[i], fixed[i], values[i])
}

pub open spec fn rename_parts<C>(f: Seq<spec_fn(C) -> C>, parts: Seq<Seq<Seq<C>>>) -> Seq<Seq<Seq<C>>> {
    parts.map(|i: int, part: Seq<Seq<C>>| rename_history(f, part))
}

pub proof fn lemma_renaming_mono<T: PartialEq>(f: spec_fn(T) -> T, small: Set<T>, big: Set<T>, values: ISet<T>)
    requires
        renaming_preserves_eq(f, big, values),
        forall|x: T| #[trigger] small.contains(x) ==> big.contains(x),
    ensures renaming_preserves_eq(f, small, values),
{
    assert forall|x: T, k: T| values.contains(x) && small.contains(k)
        implies (#[trigger] f(x).eq_spec(&k) == #[trigger] x.eq_spec(&k)) by {
        assert(big.contains(k));
    }
}

pub proof fn lemma_renamings_mono<C: PartialEq>(
    f: Seq<spec_fn(C) -> C>, small: Seq<Set<C>>, big: Seq<Set<C>>, values: Seq<ISet<C>>,
)
    requires renamings_preserve_eq(f, big, values), small.len() == big.len(),
        forall|i: int| 0 <= i < small.len() ==> #[trigger] small[i].subset_of(big[i]),
    ensures renamings_preserve_eq(f, small, values),
{
    assert forall|i: int| 0 <= i < f.len() implies renaming_preserves_eq(#[trigger] f[i], small[i], values[i]) by {
        assert(small[i].subset_of(big[i]));
        assert forall|x: C| #[trigger] small[i].contains(x) implies big[i].contains(x) by {}
        lemma_renaming_mono(f[i], small[i], big[i], values[i]);
    }
}

pub proof fn lemma_head_pattern_rename<T: PartialEq>(pattern: PatternView<T>, f: spec_fn(T) -> T, fixed: Set<T>, values: ISet<T>, x: T)
    requires
        renaming_preserves_eq(f, fixed, values),
        values.contains(x),
        forall|k: T| #[trigger] pattern_constant(pattern).contains(k) ==> fixed.contains(k),
    ensures tdsl::head_pattern_matches(pattern, f(x)) == tdsl::head_pattern_matches(pattern, x),
{
    if let PatternView::Constant(k) = pattern {
        assert(pattern_constant(pattern).contains(k));
        assert(f(x).eq_spec(&k) == x.eq_spec(&k));
    }
}

pub proof fn lemma_comparison_rename<T: PartialEq>(
    comparison: Comparison, pattern: PatternView<T>, head: PatternView<T>, f: spec_fn(T) -> T,
    fixed: Set<T>, values: ISet<T>, c: T, e: T,
)
    requires
        renaming_preserves_eq(f, fixed, values),
        values.contains(c),
        values.contains(e),
        forall|k: T| #[trigger] pattern_constant(pattern).contains(k) ==> fixed.contains(k),
    ensures
        tdsl::comparison_sem(comparison, f(e), tdsl::resolve_pattern(pattern, head, f(c)))
            == tdsl::comparison_sem(comparison, e, tdsl::resolve_pattern(pattern, head, c)),
{
    match pattern {
        PatternView::Constant(k) => {
            assert(pattern_constant(pattern).contains(k));
            assert(f(e).eq_spec(&k) == e.eq_spec(&k));
        },
        PatternView::Variable(_) => {
            assert(f(e).eq_spec(&f(c)) == e.eq_spec(&c));
        },
    }
}

pub proof fn lemma_test_rename<C: PartialEq>(
    test: TestView<C>, head: HeadView<C>, candidate: Seq<C>, event: Seq<C>,
    f: Seq<spec_fn(C) -> C>, values: Seq<ISet<C>>,
)
    requires renamings_preserve_eq(f, test_constants(test, head.len()), values),
        values_in(candidate, values), values_in(event, values),
    ensures tdsl::test_sem(test, head, rename_event(f, candidate), rename_event(f, event))
        == tdsl::test_sem(test, head, candidate, event),
    decreases test,
{
    let rc = rename_event(f, candidate);
    let re = rename_event(f, event);
    match test {
        TestView::True | TestView::False => {},
        TestView::Atom { comparison, pattern } => {
            let j = pattern.component as int;
            if j < head.len() {
                lemma_test_constants_index(test, head.len(), j);
                assert(test_constants(test, head.len())[j] == pattern_constant(pattern.pattern));
                lemma_comparison_rename(comparison, pattern.pattern, head[j], f[j],
                    test_constants(test, head.len())[j], values[j], candidate[j], event[j]);
            }
        },
        TestView::And(cs) | TestView::Or(cs) => {
            assert forall|i: int| 0 <= i < cs.len() implies
                tdsl::test_sem(cs[i], head, rc, re) == tdsl::test_sem(cs[i], head, candidate, event) by {
                assert forall|j: int| 0 <= j < head.len() implies
                    #[trigger] test_constants(cs[i], head.len())[j].subset_of(test_constants(test, head.len())[j]) by {
                    lemma_test_constants_index(test, head.len(), j);
                    let sets = Seq::new(cs.len(), |k: int| if 0 <= k < cs.len() { test_constants(cs[k], head.len())[j] } else { Set::empty() });
                    lemma_constants_union(sets, i);
                    assert(sets[i] == test_constants(cs[i], head.len())[j]);
                }
                lemma_renamings_mono(f, test_constants(cs[i], head.len()), test_constants(test, head.len()), values);
                lemma_test_rename(cs[i], head, candidate, event, f, values);
            }
        },
    }
}

/// Renaming commutes with flattening.
pub proof fn lemma_flatten_rename<C>(
    f: Seq<spec_fn(C) -> C>, parts: Seq<Seq<Seq<C>>>,
)
    ensures rename_history(f, parts.flatten()) == rename_parts(f, parts).flatten(),
    decreases parts.len(),
{
    let rp = rename_parts(f, parts);
    if parts.len() == 0 {
        assert(rename_history(f, parts.flatten()) =~= rp.flatten());
    } else {
        lemma_flatten_rename(f, parts.drop_first());
        assert(rp.drop_first() =~= rename_parts(f, parts.drop_first()));
        let a = parts.first();
        let b = parts.drop_first().flatten();
        assert(rename_history(f, a + b) =~= rename_history(f, a) + rename_history(f, b));
        assert(rp.first() == rename_history(f, a));
    }
}

/// A word whose renaming is split into parts splits into parts with those renamings.
pub proof fn lemma_unflatten_rename<C>(
    f: Seq<spec_fn(C) -> C>, rparts: Seq<Seq<Seq<C>>>,
    w: Seq<Seq<C>>,
) -> (parts: Seq<Seq<Seq<C>>>)
    requires rparts.flatten() == rename_history(f, w),
    ensures
        parts.len() == rparts.len(),
        parts.flatten() == w,
        forall|i: int| 0 <= i < parts.len() ==> rename_history(f, #[trigger] parts[i]) == rparts[i],
    decreases rparts.len(),
{
    if rparts.len() == 0 {
        assert(w =~= Seq::<Seq<C>>::empty());
        Seq::empty()
    } else {
        let first = rparts.first();
        let rest = rparts.drop_first();
        let k = first.len() as int;
        let rw = rename_history(f, w);
        assert(rw == first + rest.flatten());
        let w0 = w.subrange(0, k);
        let w1 = w.subrange(k, w.len() as int);
        assert(rename_history(f, w0) =~= first) by {
            assert forall|j: int| 0 <= j < k implies rename_history(f, w0)[j] == first[j] by {
                assert(rw[j] == (first + rest.flatten())[j]);
            }
        }
        assert(rename_history(f, w1) =~= rest.flatten()) by {
            assert forall|j: int| 0 <= j < w.len() - k implies rename_history(f, w1)[j] == rest.flatten()[j] by {
                assert(rw[k + j] == (first + rest.flatten())[k + j]);
            }
        }
        let tail = lemma_unflatten_rename(f, rest, w1);
        let parts = seq![w0] + tail;
        assert(parts.drop_first() =~= tail);
        assert(parts.first() == w0);
        assert(parts.flatten() == w0 + tail.flatten());
        assert(w0 + w1 =~= w);
        assert forall|i: int| 0 <= i < parts.len() implies rename_history(f, #[trigger] parts[i]) == rparts[i] by {
            if i > 0 {
                assert(parts[i] == tail[i - 1]);
                assert(rparts[i] == rest[i - 1]);
            }
        }
        parts
    }
}

/// The parts of a word only contain the word's values.
pub proof fn lemma_flatten_values_in<C>(parts: Seq<Seq<Seq<C>>>, values: Seq<ISet<C>>)
    requires word_values_in(parts.flatten(), values),
    ensures forall|i: int| 0 <= i < parts.len() ==> word_values_in(#[trigger] parts[i], values),
    decreases parts.len(),
{
    if parts.len() > 0 {
        let a = parts.first();
        let b = parts.drop_first().flatten();
        assert(parts.flatten() == a + b);
        assert forall|j: int| 0 <= j < a.len() implies #[trigger] values_in(a[j], values) by {
            assert((a + b)[j] == a[j]);
        }
        assert forall|j: int| 0 <= j < b.len() implies #[trigger] values_in(b[j], values) by {
            assert((a + b)[a.len() + j] == b[j]);
        }
        lemma_flatten_values_in(parts.drop_first(), values);
        assert forall|i: int| 0 <= i < parts.len() implies word_values_in(#[trigger] parts[i], values) by {
            if i > 0 {
                assert(parts[i] == parts.drop_first()[i - 1]);
            }
        }
    }
}

pub proof fn lemma_lang_rename<C: PartialEq>(
    regex: RegexView<C>, head: HeadView<C>, candidate: Seq<C>, w: Seq<Seq<C>>,
    f: Seq<spec_fn(C) -> C>, values: Seq<ISet<C>>,
)
    requires
        renamings_preserve_eq(f, regex_constants(regex, head.len()), values),
        values_in(candidate, values),
        word_values_in(w, values),
    ensures
        tdsl::lang(regex, head, rename_event(f, candidate), rename_history(f, w))
            == tdsl::lang(regex, head, candidate, w),
    decreases regex, 1nat,
{
    let rc = rename_event(f, candidate);
    let rw = rename_history(f, w);
    match regex {
        RegexView::Empty | RegexView::All | RegexView::Epsilon => {},
        RegexView::Test(t) => {
            assert(regex_constants(regex, head.len()) =~= test_constants(t, head.len()));
            if w.len() == 1 {
                assert(values_in(w[0], values));
                lemma_test_rename(t, head, candidate, w[0], f, values);
            }
        },
        RegexView::Star(b) | RegexView::Not(b) => {
            lemma_lang_rename_star_not(regex, *b, head, candidate, w, f, values);
        },
        RegexView::Union(cs) | RegexView::Concat(cs) | RegexView::Intersect(cs) => {
            assert forall|i: int| 0 <= i < cs.len() implies
                #[trigger] renamings_preserve_eq(f, regex_constants(cs[i], head.len()), values) by {
                assert forall|j: int| 0 <= j < head.len() implies
                    #[trigger] regex_constants(cs[i], head.len())[j].subset_of(regex_constants(regex, head.len())[j]) by {
                    lemma_regex_constants_index(regex, head.len(), j);
                    let sets = Seq::new(cs.len(), |k: int| if 0 <= k < cs.len() { regex_constants(cs[k], head.len())[j] } else { Set::empty() });
                    lemma_constants_union(sets, i);
                    assert(sets[i] == regex_constants(cs[i], head.len())[j]);
                }
                lemma_renamings_mono(f, regex_constants(cs[i], head.len()), regex_constants(regex, head.len()), values);
            }
            if regex is Concat {
                if tdsl::lang(regex, head, candidate, w) {
                    let parts = choose|parts: Seq<Seq<Seq<C>>>| parts.len() == cs.len() && w == parts.flatten()
                        && forall|i: int| 0 <= i < cs.len() ==> tdsl::lang(cs[i], head, candidate, parts[i]);
                    lemma_flatten_values_in(parts, values);
                    lemma_flatten_rename(f, parts);
                    let rp = rename_parts(f, parts);
                    assert forall|i: int| 0 <= i < cs.len() implies tdsl::lang(cs[i], head, rc, rp[i]) by {
                        assert(renamings_preserve_eq(f, regex_constants(cs[i], head.len()), values));
                        assert(word_values_in(parts[i], values));
                        lemma_lang_rename(cs[i], head, candidate, parts[i], f, values);
                    }
                    assert(rp.len() == cs.len() && rw == rp.flatten());
                }
                if tdsl::lang(regex, head, rc, rw) {
                    let rparts = choose|parts: Seq<Seq<Seq<C>>>| parts.len() == cs.len() && rw == parts.flatten()
                        && forall|i: int| 0 <= i < cs.len() ==> tdsl::lang(cs[i], head, rc, parts[i]);
                    let parts = lemma_unflatten_rename(f, rparts, w);
                    lemma_flatten_values_in(parts, values);
                    assert forall|i: int| 0 <= i < cs.len() implies tdsl::lang(cs[i], head, candidate, parts[i]) by {
                        assert(renamings_preserve_eq(f, regex_constants(cs[i], head.len()), values));
                        assert(word_values_in(parts[i], values));
                        assert(rename_history(f, parts[i]) == rparts[i]);
                        lemma_lang_rename(cs[i], head, candidate, parts[i], f, values);
                    }
                }
            } else {
                assert forall|i: int| 0 <= i < cs.len() implies
                    tdsl::lang(cs[i], head, rc, rw) == tdsl::lang(cs[i], head, candidate, w) by {
                    assert(renamings_preserve_eq(f, regex_constants(cs[i], head.len()), values));
                    lemma_lang_rename(cs[i], head, candidate, w, f, values);
                }
            }
        },
    }
}

proof fn lemma_lang_rename_star_not<C: PartialEq>(
    regex: RegexView<C>, b: RegexView<C>, head: HeadView<C>, candidate: Seq<C>,
    w: Seq<Seq<C>>, f: Seq<spec_fn(C) -> C>,
    values: Seq<ISet<C>>,
)
    requires
        regex == RegexView::Star(Box::new(b)) || regex == RegexView::Not(Box::new(b)),
        renamings_preserve_eq(f, regex_constants(regex, head.len()), values),
        values_in(candidate, values),
        word_values_in(w, values),
    ensures
        tdsl::lang(regex, head, rename_event(f, candidate), rename_history(f, w))
            == tdsl::lang(regex, head, candidate, w),
    decreases regex, 0nat,
{
    let rc = rename_event(f, candidate);
    let rw = rename_history(f, w);
    assert(regex_constants(b, head.len()) =~= regex_constants(regex, head.len()));
    if regex is Not {
        lemma_lang_rename(b, head, candidate, w, f, values);
    } else {
        if tdsl::lang(regex, head, candidate, w) {
            let parts = choose|parts: Seq<Seq<Seq<C>>>| w == parts.flatten()
                && forall|i: int| 0 <= i < parts.len() ==> tdsl::lang(b, head, candidate, parts[i]);
            lemma_flatten_values_in(parts, values);
            lemma_flatten_rename(f, parts);
            let rp = rename_parts(f, parts);
            assert forall|i: int| 0 <= i < rp.len() implies tdsl::lang(b, head, rc, rp[i]) by {
                assert(word_values_in(parts[i], values));
                lemma_lang_rename(b, head, candidate, parts[i], f, values);
            }
            assert(rw == rp.flatten());
        }
        if tdsl::lang(regex, head, rc, rw) {
            let rparts = choose|parts: Seq<Seq<Seq<C>>>| rw == parts.flatten()
                && forall|i: int| 0 <= i < parts.len() ==> tdsl::lang(b, head, rc, parts[i]);
            let parts = lemma_unflatten_rename(f, rparts, w);
            lemma_flatten_values_in(parts, values);
            assert forall|i: int| 0 <= i < parts.len() implies tdsl::lang(b, head, candidate, parts[i]) by {
                assert(word_values_in(parts[i], values));
                assert(rename_history(f, parts[i]) == rparts[i]);
                lemma_lang_rename(b, head, candidate, parts[i], f, values);
            }
        }
    }
}

/// Violation is invariant under renamings that preserve equality on the given values and with
/// the rule's constants.
pub proof fn lemma_violation_rename<C: PartialEq>(
    rule: RuleView<C>, candidate: Seq<C>, history: Seq<Seq<C>>,
    f: Seq<spec_fn(C) -> C>, values: Seq<ISet<C>>,
)
    requires
        renamings_preserve_eq(f, rule_constants(rule), values),
        values_in(candidate, values),
        word_values_in(history, values),
    ensures
        tdsl::rule_violated_view(rule, candidate, history)
            == tdsl::rule_violated_view(rule, rename_event(f, candidate), rename_history(f, history)),
{
    let k = rule_constants(rule);
    assert forall|i: int| 0 <= i < rule.head.len() implies
        tdsl::head_pattern_matches(rule.head[i], rename_event(f, candidate)[i])
            == tdsl::head_pattern_matches(rule.head[i], candidate[i]) by {
        lemma_head_pattern_rename(rule.head[i], f[i], k[i], values[i], candidate[i]);
    }
    assert(tdsl::head_matches(rule.head, candidate) == tdsl::head_matches(rule.head, rename_event(f, candidate)));
    assert forall|i: int| 0 <= i < rule.head.len() implies
        #[trigger] regex_constants(rule.tail, rule.head.len())[i].subset_of(k[i]) by {}
    lemma_renamings_mono(f, regex_constants(rule.tail, rule.head.len()), k, values);
    lemma_lang_rename(rule.tail, rule.head, candidate, history, f, values);
}

pub proof fn lemma_pair_values_contains<C>(candidate: Seq<C>, history: Seq<Seq<C>>, coordinate: int, i: int)
    requires 0 <= i < history.len(), 0 <= coordinate < history[i].len(),
    ensures pair_values(candidate, history, coordinate).contains(history[i][coordinate]),
{
    let x = history[i][coordinate];
    assert(exists|j: int| 0 <= j < history.len() && 0 <= coordinate < history[j].len()
        && #[trigger] history[j][coordinate] == x);
}

pub proof fn theorem_genericity<E: Event>()
    ensures stmt_genericity::<E>(),
{
    assert forall|rule: RuleView<E::Component>, candidate: Seq<E::Component>, history: Seq<Seq<E::Component>>, f: Seq<spec_fn(E::Component) -> E::Component>|
        rule_wf(rule) && candidate.len() == rule.head.len()
            && (forall|i: int| 0 <= i < history.len() ==> history[i].len() == candidate.len())
            && renamings_preserve::<E>(f, rule_constants(rule),
                Seq::new(candidate.len(), |i: int| pair_values(candidate, history, i)))
        implies (tdsl::rule_violated_view(rule, candidate, history)
            == #[trigger] tdsl::rule_violated_view(rule, rename_event(f, candidate), rename_history(f, history))) by {
        let values = Seq::new(candidate.len(), |i: int| pair_values(candidate, history, i));
        assert(values_in(candidate, values));
        assert forall|i: int| 0 <= i < history.len() implies #[trigger] values_in(history[i], values) by {
            assert forall|j: int| 0 <= j < candidate.len() implies #[trigger] values[j].contains(history[i][j]) by {
                lemma_pair_values_contains(candidate, history, j, i);
            }
        }
        assert(renamings_preserve_eq(f, rule_constants(rule), values));
        lemma_violation_rename(rule, candidate, history, f, values);
    }
}

} // verus!
