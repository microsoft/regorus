//! The policy questions the analyzer decides (paper Section 5, Definition
//! `def:policy-refinement`, appendix `app:policy-reduction`), declared domains, symbolic
//! counterexamples with their real instances, fresh-value capacity, and per-case minimality.
//! Everything is stated over real events `E` through the semantics (`junco_core::spec::semantics`).

use crate::spec::semantics::*;
use history_syntax::event::specs::EventSpec;
use history_syntax::spec::events::{
    AtomView, HeadView, PatternView, RegexView, RuleView, TestView, arity, event_view,
};
use history_syntax::{Event, MAX_ARITY, RuleMode};
use vstd::prelude::*;
use vstd::std_specs::cmp::PartialEqSpec;

verus! {

broadcast use vstd::seq::group_seq_lemmas;

// ----- declared domains -----

/// The values a coordinate ranges over: all values of its type (`None`), or a declared finite
/// set. The paper assumes infinite domains (`sec:events`); declared finite domains are an
/// implementation feature (`Domains::with_domain`).
pub type DomainsView<C> = Seq<Option<Set<C>>>;

/// `value` lies in the domain: always for an undeclared coordinate, up to `eq_spec` for a declared
/// set.
pub open spec fn in_domain<T: PartialEq>(domain: Option<Set<T>>, value: T) -> bool {
    match domain {
        None => true,
        Some(values) => exists|w: T| values.contains(w) && value.eq_spec(&w),
    }
}

/// A component tuple lies coordinate-wise in the domains.
pub open spec fn event_in<C: PartialEq>(domains: DomainsView<C>, event: Seq<C>) -> bool {
    1 <= domains.len() <= MAX_ARITY && event.len() == domains.len()
        && forall|i: int| 0 <= i < domains.len() ==> in_domain(#[trigger] domains[i], event[i])
}

/// Every event of a history lies in the domains.
pub open spec fn history_in<C: PartialEq>(domains: DomainsView<C>, history: Seq<Seq<C>>) -> bool {
    forall|i: int| 0 <= i < history.len() ==> #[trigger] event_in(domains, history[i])
}

/// `v` equals no member of `values`.
pub open spec fn misses<T: PartialEq>(values: Set<T>, v: T) -> bool {
    forall|w: T| values.contains(w) ==> !v.eq_spec(&w)
}

/// A real candidate and history inside the declared domains (undeclared coordinate = every
/// value of its type).
pub open spec fn in_domains<E: Event>(
    domains: DomainsView<E::Component>, candidate: E, history: Seq<E>,
) -> bool {
    event_in(domains, event_view(candidate)) && history_in(domains, history_view(history))
}

/// Declared domains: one slot per coordinate; a declared set is nonempty and tagged with its
/// coordinate; `Set` is finite by construction in this vstd.
pub open spec fn domains_wf<E: Event>(domains: DomainsView<E::Component>) -> bool {
    domains.len() == arity::<E>() && forall|i: int| 0 <= i < domains.len() ==> match #[trigger] domains[i] {
        None => true,
        Some(values) => values.len() > 0
            && forall|v: E::Component| values.contains(v) ==> E::coordinate_spec(v) == i,
    }
}

// ----- the questions (`def:policy-refinement`, `app:policy-reduction`) -----

/// `P ⊑ Q` (`def:policy-refinement`): every pair in the domains permitted by `P` is permitted by
/// `Q`.
pub open spec fn refines<E: Event>(
    domains: DomainsView<E::Component>, p: Seq<RuleView<E::Component>>, q: Seq<RuleView<E::Component>>,
) -> bool {
    forall|c: E, h: Seq<E>| in_domains::<E>(domains, c, h) && policy_permits(p, c, h)
        ==> #[trigger] policy_permits(q, c, h)
}

/// `P` covers `rule`: every pair the rule violates is denied by `P` (`app:policy-reduction`).
pub open spec fn covers<E: Event>(
    domains: DomainsView<E::Component>, p: Seq<RuleView<E::Component>>, rule: RuleView<E::Component>,
) -> bool {
    forall|c: E, h: Seq<E>| in_domains::<E>(domains, c, h) && #[trigger] rule_violated(rule, c, h)
        ==> policy_denies(p, c, h)
}

/// The rule violates no pair in the domains.
pub open spec fn never_denies<E: Event>(
    domains: DomainsView<E::Component>, rule: RuleView<E::Component>,
) -> bool {
    forall|c: E, h: Seq<E>| in_domains::<E>(domains, c, h) ==> !#[trigger] rule_violated(rule, c, h)
}

/// The rule violates every pair in the domains whose candidate matches its head.
pub open spec fn always_denies<E: Event>(
    domains: DomainsView<E::Component>, rule: RuleView<E::Component>,
) -> bool {
    forall|c: E, h: Seq<E>| in_domains::<E>(domains, c, h) && head_matches(rule.head, event_view(c))
        ==> #[trigger] rule_violated(rule, c, h)
}

/// `forbid head Univ`: denies every candidate matching `head` (vacuity through refinement).
pub open spec fn forbid_all<C>(head: HeadView<C>) -> RuleView<C> {
    RuleView { mode: RuleMode::Forbid, head, tail: RegexView::All }
}

/// Tail inclusion for every matching candidate in the domains: `L(left) ⊆ L(right)` read with
/// the head's bindings.
pub open spec fn tails_included<E: Event>(
    domains: DomainsView<E::Component>, head: HeadView<E::Component>,
    left: RegexView<E::Component>, right: RegexView<E::Component>,
) -> bool {
    forall|c: E, h: Seq<E>| in_domains::<E>(domains, c, h) && head_matches(head, event_view(c))
        && #[trigger] lang(left, head, event_view(c), history_view(h))
        ==> lang(right, head, event_view(c), history_view(h))
}

// ----- symbolic counterexamples and their real instances -----

/// `Value<T>`: a constant, or a numbered value of an undeclared coordinate that equals no
/// constant the analyzer knows.
pub enum ValueView<T> { Constant(T), Fresh(nat) }

pub type ComponentsView<C> = Seq<ValueView<C>>;

/// `Counterexample<E>`: a candidate and a history (oldest first).
pub struct CexView<C> { pub candidate: ComponentsView<C>, pub history: Seq<ComponentsView<C>> }

/// `Inclusion<E>`: the answer to a query.
pub enum InclusionView<C> { Holds, Counterexample(CexView<C>), Exhausted }

/// Per-coordinate choice of a value for each fresh number.
pub type FreshChoice<C> = Seq<spec_fn(nat) -> C>;

/// The real value a symbolic value denotes under the choice `f` of its coordinate.
pub open spec fn value_of<T>(v: ValueView<T>, f: spec_fn(nat) -> T) -> T {
    match v { ValueView::Constant(c) => c, ValueView::Fresh(n) => f(n) }
}

/// The real tuple a symbolic tuple denotes.
pub open spec fn event_of<C>(c: ComponentsView<C>, f: FreshChoice<C>) -> Seq<C> {
    Seq::new(c.len(), |i: int| value_of(c[i], f[i]))
}

/// The real history a symbolic history denotes.
pub open spec fn history_of<C>(cex: CexView<C>, f: FreshChoice<C>) -> Seq<Seq<C>> {
    cex.history.map(|i: int, c: ComponentsView<C>| event_of(c, f))
}

/// Fresh numbers used at one coordinate.
pub open spec fn fresh_used<C>(cex: CexView<C>, coordinate: int) -> ISet<nat> {
    ISet::new(|n: nat| (0 <= coordinate < cex.candidate.len()
        && cex.candidate[coordinate] == ValueView::<C>::Fresh(n))
        || exists|i: int| 0 <= i < cex.history.len() && 0 <= coordinate < cex.history[i].len()
            && #[trigger] cex.history[i][coordinate] == ValueView::<C>::Fresh(n))
}

/// Every symbolic tuple of the counterexample has `arity` coordinates.
pub open spec fn cex_arity<C>(cex: CexView<C>, arity: nat) -> bool {
    cex.candidate.len() == arity
        && forall|i: int| 0 <= i < cex.history.len() ==> #[trigger] cex.history[i].len() == arity
}

/// Fresh numbers at coordinate `i` map to pairwise distinct values tagged `i`, inside the
/// domain, equal to no known constant.
pub open spec fn choice_ok<E: Event>(
    f: spec_fn(nat) -> E::Component, used: ISet<nat>, known: Set<E::Component>,
    domain: Option<Set<E::Component>>, i: int,
) -> bool {
    &&& forall|m: nat, n: nat| #![trigger used.contains(m), used.contains(n)]
        used.contains(m) && used.contains(n) && m != n ==> !f(m).eq_spec(&f(n))
    &&& forall|n: nat, k: E::Component| #![trigger used.contains(n), known.contains(k)]
        used.contains(n) && known.contains(k) ==> !f(n).eq_spec(&k)
    &&& forall|n: nat| #[trigger] used.contains(n) ==> in_domain(domain, f(n)) && E::coordinate_spec(f(n)) == i
}

/// A choice of fresh values admissible at every coordinate of the counterexample.
pub open spec fn admissible<E: Event>(
    domains: DomainsView<E::Component>, known: Seq<Set<E::Component>>,
    cex: CexView<E::Component>, f: FreshChoice<E::Component>,
) -> bool {
    &&& domains.len() == arity::<E>() && known.len() == arity::<E>() && f.len() == arity::<E>()
    &&& cex_arity(cex, arity::<E>())
    &&& forall|i: int| 0 <= i < arity::<E>()
        ==> choice_ok::<E>(#[trigger] f[i], fresh_used(cex, i), known[i], domains[i], i)
}

/// `(c, h)` is the real pair the symbolic counterexample denotes under `f`.
pub open spec fn instantiates<E: Event>(
    cex: CexView<E::Component>, f: FreshChoice<E::Component>, c: E, h: Seq<E>,
) -> bool {
    event_view(c) == event_of(cex.candidate, f) && history_view(h) == history_of(cex, f)
}

/// Some admissible choice denotes a real pair.
pub open spec fn cex_has_instance<E: Event>(
    domains: DomainsView<E::Component>, known: Seq<Set<E::Component>>, cex: CexView<E::Component>,
) -> bool {
    exists|f: FreshChoice<E::Component>, c: E, h: Seq<E>|
        admissible::<E>(domains, known, cex, f) && #[trigger] instantiates::<E>(cex, f, c, h)
}

/// Every real instance lies in the domains and satisfies `fails`.
pub open spec fn every_instance<E: Event>(
    domains: DomainsView<E::Component>, known: Seq<Set<E::Component>>, cex: CexView<E::Component>,
    fails: spec_fn(E, Seq<E>) -> bool,
) -> bool {
    forall|f: FreshChoice<E::Component>, c: E, h: Seq<E>|
        admissible::<E>(domains, known, cex, f) && #[trigger] instantiates::<E>(cex, f, c, h)
        ==> in_domains::<E>(domains, c, h) && fails(c, h)
}

/// Coordinate `i` offers at least `k` pairwise distinct values tagged `i`, inside its domain,
/// equal to no known constant.
pub open spec fn fresh_capacity<E: Event>(
    domains: DomainsView<E::Component>, known: Seq<Set<E::Component>>, i: int, k: nat,
) -> bool {
    exists|vs: Seq<E::Component>| #[trigger] vs.len() == k
        && (forall|a: int, b: int| 0 <= a < b < vs.len() ==> !vs[a].eq_spec(&vs[b]))
        && forall|a: int| 0 <= a < vs.len() ==> E::coordinate_spec(#[trigger] vs[a]) == i
            && in_domain(domains[i], vs[a]) && misses(known[i], vs[a])
}

/// Capacity for exactly the fresh values the counterexample uses (zero at declared coordinates).
pub open spec fn capacity_for<E: Event>(
    domains: DomainsView<E::Component>, known: Seq<Set<E::Component>>, cex: CexView<E::Component>,
) -> bool {
    forall|i: int| 0 <= i < arity::<E>()
        ==> #[trigger] fresh_capacity::<E>(domains, known, i, fresh_used(cex, i).len())
}

// ----- minimality (over events) -----

/// `c2` agrees with `c` on equality with every known constant (so it lies in the same candidate
/// case of every split the analyzer makes).
pub open spec fn same_profile<C: PartialEq>(known: Seq<Set<C>>, c: Seq<C>, c2: Seq<C>) -> bool {
    &&& c.len() == known.len() && c2.len() == known.len()
    &&& forall|i: int, k: C| 0 <= i < known.len() && #[trigger] known[i].contains(k)
        ==> (c[i].eq_spec(&k) == c2[i].eq_spec(&k))
}

/// No failing pair in the domains has a history shorter than `n`.
pub open spec fn shortest<E: Event>(
    domains: DomainsView<E::Component>, n: nat, fails: spec_fn(E, Seq<E>) -> bool,
) -> bool {
    forall|c: E, h: Seq<E>| in_domains::<E>(domains, c, h) && h.len() < n ==> !#[trigger] fails(c, h)
}

/// No failing pair with the constant profile of `c` has a history shorter than `n` (minimum
/// length per inclusion query, Theorem `thm:search`).
pub open spec fn shortest_in_case<E: Event>(
    domains: DomainsView<E::Component>, known: Seq<Set<E::Component>>, c: E, n: nat,
    fails: spec_fn(E, Seq<E>) -> bool,
) -> bool {
    forall|c2: E, h: Seq<E>| in_domains::<E>(domains, c2, h) && h.len() < n
        && same_profile(known, event_view(c), event_view(c2)) ==> !#[trigger] fails(c2, h)
}

/// Per-case minimality: every real instance is shortest among candidates with its constant
/// profile.
pub open spec fn minimal_in_case<E: Event>(
    domains: DomainsView<E::Component>, known: Seq<Set<E::Component>>, cex: CexView<E::Component>,
    fails: spec_fn(E, Seq<E>) -> bool,
) -> bool {
    forall|f: FreshChoice<E::Component>, c: E, h: Seq<E>|
        admissible::<E>(domains, known, cex, f) && #[trigger] instantiates::<E>(cex, f, c, h)
        ==> shortest_in_case::<E>(domains, known, c, cex.history.len(), fails)
}

// ----- the constants a rule mentions (what `known` and freshness are relative to) -----

/// The constant of a head or atom pattern, if any.
pub open spec fn pattern_constant<C>(pattern: PatternView<C>) -> Set<C> {
    match pattern { PatternView::Constant(c) => Set::empty().insert(c), PatternView::Variable(_) => Set::empty() }
}

/// A finite union, built from finite sets rather than an unrestricted comprehension.
pub open spec fn constants_union<C>(sets: Seq<Set<C>>) -> Set<C>
    decreases sets.len(),
{
    if sets.len() == 0 { Set::empty() }
    else { constants_union(sets.drop_last()).union(sets.last()) }
}

/// The constants a test compares coordinate `coordinate` against.
pub open spec fn test_constant_at<C>(test: TestView<C>, coordinate: int) -> Set<C>
    decreases test,
{
    match test {
        TestView::True | TestView::False => Set::empty(),
        TestView::Atom { pattern, .. } =>
            if coordinate == pattern.component { pattern_constant(pattern.pattern) } else { Set::empty() },
        TestView::And(cs) | TestView::Or(cs) => test_constant_forest(cs, coordinate),
    }
}

pub open spec fn test_constant_forest<C>(tests: Seq<TestView<C>>, coordinate: int) -> Set<C>
    decreases tests,
{
    if tests.len() == 0 { Set::empty() }
    else { test_constant_forest(tests.drop_last(), coordinate).union(test_constant_at(tests.last(), coordinate)) }
}

/// The constants a test mentions, per coordinate.
pub open spec fn test_constants<C>(test: TestView<C>, arity: nat) -> Seq<Set<C>> {
    Seq::new(arity, |j: int| test_constant_at(test, j))
}

/// The constants a tail compares coordinate `coordinate` against.
pub open spec fn regex_constant_at<C>(regex: RegexView<C>, coordinate: int) -> Set<C>
    decreases regex,
{
    match regex {
        RegexView::Empty | RegexView::All | RegexView::Epsilon => Set::empty(),
        RegexView::Test(test) => test_constant_at(test, coordinate),
        RegexView::Union(cs) | RegexView::Concat(cs) | RegexView::Intersect(cs) => regex_constant_forest(cs, coordinate),
        RegexView::Star(child) | RegexView::Not(child) => regex_constant_at(*child, coordinate),
    }
}

pub open spec fn regex_constant_forest<C>(regexes: Seq<RegexView<C>>, coordinate: int) -> Set<C>
    decreases regexes,
{
    if regexes.len() == 0 { Set::empty() }
    else { regex_constant_forest(regexes.drop_last(), coordinate).union(regex_constant_at(regexes.last(), coordinate)) }
}

/// The constants a tail mentions, per coordinate.
pub open spec fn regex_constants<C>(regex: RegexView<C>, arity: nat) -> Seq<Set<C>> {
    Seq::new(arity, |j: int| regex_constant_at(regex, j))
}

/// The constants of a head, per coordinate.
pub open spec fn head_constants<C>(head: HeadView<C>) -> Seq<Set<C>> {
    head.map(|i: int, pattern: PatternView<C>| pattern_constant(pattern))
}

/// Exact finite constants of the head and tail, separately at every coordinate.
pub open spec fn rule_constants<C>(rule: RuleView<C>) -> Seq<Set<C>> {
    Seq::new(rule.head.len(), |i: int|
        regex_constants(rule.tail, rule.head.len())[i].union(head_constants(rule.head)[i]))
}

} // verus!
