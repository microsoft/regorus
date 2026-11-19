//! Layer 2: constraints, `Split`, constrained inclusion, and the policy reduction (`sec:policy`,
//! appendix `app:policy-reduction`, `app:mech-diff`), over numeric rules. The paper's
//! Proposition `prop:policy` reduces refinement to one inclusion of denial expressions; the
//! reduction proved here is the equivalent rule-by-rule form that the analyzer uses.
use super::encoding::*;
use super::search::{Outcome, follows, outcome_ok};
use crate::verify::finite_states::lemma_powerset_finite;
use alloc::boxed::Box;
use history_syntax::spec::events::{RegexView, RuleView, event_view};
use history_syntax::syntax::{Component, RuleMode};
use history_syntax::{Event, MAX_ARITY};
use junco_core::kernel::verify as model;
use junco_core::spec::questions::{
    DomainsView, always_denies, forbid_all, in_domains, never_denies, refines,
};
use junco_core::spec::semantics::{
    head_matches, history_view, lang, policy_denies, policy_permits, rule_violated, violated_by,
};
use junco_core::verify::history_specs as language;
use junco_core::verify::history_specs::{EventView, Regex, Subst};
use vstd::iset_lib::lemma_iset_subset_finite;
use vstd::prelude::*;

verus! {

/// `x_c = value` (`equal`) or `x_c ≠ value`.
pub struct Literal { pub component: Component, pub value: nat, pub equal: bool }

/// A finite conjunction of literals (Definition Constraints, `def:constraints`).
pub type Constraint = Set<Literal>;

pub open spec fn literal_holds(theta: Subst, l: Literal) -> bool {
    (language::field_value(theta, l.component) == l.value) == l.equal
}

/// `θ ⊨ Γ`.
pub open spec fn sat_by(theta: Subst, g: Constraint) -> bool {
    forall|l: Literal| #[trigger] g.contains(l) ==> literal_holds(theta, l)
}

/// Satisfiable by an admissible valuation of the domain.
pub open spec fn satisfiable(d: NDomains, g: Constraint) -> bool {
    exists|theta: Subst| n_theta_ok(d, theta) && #[trigger] sat_by(theta, g)
}

/// `Γ' ⊨ Γ`, relative to the admissible valuations of the domain.
pub open spec fn entails(d: NDomains, g1: Constraint, g2: Constraint) -> bool {
    forall|theta: Subst| n_theta_ok(d, theta) && #[trigger] sat_by(theta, g1) ==> sat_by(theta, g2)
}

pub open spec fn eq_literal(c: Component, v: nat) -> Literal { Literal { component: c, value: v, equal: true } }

pub open spec fn ne_literal(c: Component, v: nat) -> Literal { Literal { component: c, value: v, equal: false } }

/// `Γ` decides `(x_c, v)` (Definition Constraints, `def:constraints`).
pub open spec fn decides(d: NDomains, g: Constraint, c: Component, v: nat) -> bool {
    entails(d, g, set![eq_literal(c, v)]) || entails(d, g, set![ne_literal(c, v)])
}

/// A set of pairs `(x_c, v)`.
pub type Pairs = Set<(Component, nat)>;

/// What every use of `Split(Γ; Π)` relies on (Definition Splitting, `def:split`): finitely many satisfiable
/// cases, each entailing `Γ` and deciding `Π`, that partition the admissible valuations of `Γ`.
/// The paper's `Split` (`paper_split`) is one such family; the implementation's `split`
/// (`history-analysis/src/constraint.rs`) emits an equivalent one with at most `n + 1` cases per
/// register.
pub open spec fn split_ok(d: NDomains, g: Constraint, pi: Pairs, cases: Set<Constraint>) -> bool {
    &&& forall|g1: Constraint| #[trigger] cases.contains(g1) ==> satisfiable(d, g1) && entails(d, g1, g)
        && forall|p: (Component, nat)| pi.contains(p) ==> #[trigger] decides(d, g1, p.0, p.1)
    &&& forall|theta: Subst| n_theta_ok(d, theta) && #[trigger] sat_by(theta, g)
        ==> exists|g1: Constraint| #[trigger] cases.contains(g1) && sat_by(theta, g1)
    &&& forall|theta: Subst, g1: Constraint, g2: Constraint| n_theta_ok(d, theta) && cases.contains(g1) && cases.contains(g2)
        && #[trigger] sat_by(theta, g1) && #[trigger] sat_by(theta, g2) ==> g1 == g2
}

/// `Δ` has exactly one of `x_c = v`, `x_c ≠ v` for each pair of `Π` that `Γ` does not decide.
pub open spec fn split_delta(d: NDomains, g: Constraint, pi: Pairs, delta: Constraint) -> bool {
    &&& forall|l: Literal| #[trigger] delta.contains(l) ==> pi.contains((l.component, l.value)) && !decides(d, g, l.component, l.value)
    &&& forall|p: (Component, nat)| #[trigger] pi.contains(p) && !decides(d, g, p.0, p.1)
        ==> delta.contains(eq_literal(p.0, p.1)) != delta.contains(ne_literal(p.0, p.1))
}

/// The paper's `Split(Γ; Π)`: the satisfiable `Γ ∪ Δ`.
pub open spec fn paper_split(d: NDomains, g: Constraint, pi: Pairs) -> Set<Constraint> {
    Set::new(|g1: Constraint| exists|delta: Constraint| #[trigger] split_delta(d, g, pi, delta) && g1 == g.union(delta)
        && satisfiable(d, g1)).unwrap_or(Set::empty())
}

pub open spec fn stmt_paper_split_ok() -> bool {
    forall|d: NDomains, g: Constraint, pi: Pairs| #[trigger] split_ok(d, g, pi, paper_split(d, g, pi))
}

// ----- constrained inclusion (not defined in the paper's body; used by appendix `app:mech-diff`, "Reducing refinement") -----

/// `r ⊑_Γ s`.
pub open spec fn included_under(d: NDomains, g: Constraint, r: Regex<model::Test>, s: Regex<model::Test>) -> bool {
    forall|theta: Subst, w: Seq<EventView>| n_theta_ok(d, theta) && n_history_in(d, w) && sat_by(theta, g)
        && #[trigger] n_lang(theta, r, w) ==> n_lang(theta, s, w)
}

/// A counterexample: `θ ⊨ Γ` and `w ∈ L_θ(r & ¬s)`.
pub open spec fn inclusion_cex(d: NDomains, g: Constraint, r: Regex<model::Test>, s: Regex<model::Test>,
    theta: Subst, w: Seq<EventView>) -> bool {
    n_theta_ok(d, theta) && n_history_in(d, w) && sat_by(theta, g) && n_lang(theta, r, w) && !n_lang(theta, s, w)
}

/// Shortest counterexample length bound: no counterexample is shorter than `n`.
pub open spec fn no_cex_shorter(d: NDomains, g: Constraint, r: Regex<model::Test>, s: Regex<model::Test>, n: nat) -> bool {
    forall|theta: Subst, w: Seq<EventView>| w.len() < n ==> !#[trigger] inclusion_cex(d, g, r, s, theta, w)
}

// ----- policy reduction, rule by rule over split cases. This replaces Proposition Refinement as
// inclusion (`prop:policy`), which is not mechanized as stated; see appendix `app:mech-diff`. -----

/// Head constraint `Γ_R`.
pub open spec fn head_constraint(h: NHead) -> Constraint {
    Set::new(|l: Literal| l.equal && n_head_field(h, l.component) == Some(l.value)).unwrap_or(Set::empty())
}

/// Denial expression `ρ_R`: the tail for `forbid`, its complement for `require`.
pub open spec fn denial(rule: NRule) -> Regex<model::Test> {
    match rule.mode { RuleMode::Forbid => rule.tail, RuleMode::Require => Regex::Not(Box::new(rule.tail)) }
}

/// `Π` of the policy reduction (`app:mech-diff`): `(x_c, v)` for each head constant `v` at component `c` in `P`.
pub open spec fn head_pairs(p: Seq<NRule>) -> Pairs {
    Set::new(|pair: (Component, nat)| exists|i: int| 0 <= i < p.len() && #[trigger] n_head_field(p[i].head, pair.0) == Some(pair.1))
        .unwrap_or(Set::empty())
}

/// `Σ_{R' ∈ P, Γ' ⊨ Γ_R'} ρ_R'` (the empty sum is `∅`).
pub open spec fn firing_denials(d: NDomains, p: Seq<NRule>, g1: Constraint) -> Regex<model::Test> {
    let firing = p.filter(|r: NRule| entails(d, g1, head_constraint(r.head)));
    Regex::Union(firing.map(|i: int, r: NRule| denial(r)))
}

pub open spec fn n_covers(d: NDomains, p: Seq<NRule>, rule: NRule) -> bool {
    forall|theta: Subst, w: Seq<EventView>| n_theta_ok(d, theta) && n_history_in(d, w)
        && #[trigger] n_rule_denies(rule, theta, w) ==> n_policy_denies(p, theta, w)
}

/// The policy reduction (`app:mech-diff`), for any family of cases with `split_ok` (so it covers the implementation's
/// `split` as well as `paper_split`).
pub open spec fn stmt_policy_reduction() -> bool {
    forall|d: NDomains, p: Seq<NRule>, rule: NRule, cases: Set<Constraint>|
        rule.head.len() == d.len()
            && (forall|i: int| 0 <= i < p.len() ==> #[trigger] p[i].head.len() == d.len())
            && #[trigger] split_ok(d, head_constraint(rule.head), head_pairs(p), cases)
            ==> (n_covers(d, p, rule) <==> forall|g1: Constraint| #[trigger] cases.contains(g1)
                ==> included_under(d, g1, denial(rule), firing_denials(d, p, g1)))
}

/// No uncovered realization in the selected candidate case is shorter than `n`.
pub open spec fn n_no_uncovered_shorter(d: NDomains, p: Seq<NRule>, rule: NRule, g: Constraint, n: nat) -> bool {
    forall|theta: Subst, w: Seq<EventView>| n_theta_ok(d, theta) && n_history_in(d, w)
        && sat_by(theta, g) && w.len() < n
        ==> !(#[trigger] n_rule_denies(rule, theta, w) && !n_policy_denies(p, theta, w))
}

/// Numeric meaning of a decided policy case. Refutations are realizable even for declared
/// finite domains, because `outcome_ok` supplies both a candidate and a following history.
pub open spec fn policy_case_outcome_ok(d: NDomains, p: Seq<NRule>, rule: NRule,
    g0: Constraint, outcome: Outcome) -> bool {
    match outcome {
        Outcome::Holds => included_under(d, g0, denial(rule), firing_denials(d, p, g0)),
        Outcome::Refuted(g, letters) => {
            &&& !n_covers(d, p, rule)
            &&& exists|theta: Subst, w: Seq<EventView>| n_theta_ok(d, theta)
                && sat_by(theta, g) && #[trigger] follows(d, letters, theta, w)
            &&& forall|theta: Subst, w: Seq<EventView>| n_theta_ok(d, theta) && sat_by(theta, g)
                && #[trigger] follows(d, letters, theta, w)
                ==> n_rule_denies(rule, theta, w) && !n_policy_denies(p, theta, w)
            &&& n_no_uncovered_shorter(d, p, rule, g0, letters.len())
        },
        Outcome::Exhausted => true,
    }
}

/// A valid case family together with its individual search contracts.
pub open spec fn policy_search_outcomes_ok(d: NDomains, p: Seq<NRule>, rule: NRule,
    cases: Set<Constraint>, outcomes: spec_fn(Constraint) -> Outcome) -> bool {
    &&& rule.head.len() == d.len()
    &&& forall|i: int| 0 <= i < p.len() ==> #[trigger] p[i].head.len() == d.len()
    &&& split_ok(d, head_constraint(rule.head), head_pairs(p), cases)
    &&& forall|g: Constraint| #[trigger] cases.contains(g)
        ==> outcome_ok(d, g, denial(rule), firing_denials(d, p, g), outcomes(g))
}

/// Search outcomes compose with the policy reduction for any valid split family. No
/// unrestricted-domain premise is needed: realizability is part of each search outcome.
pub open spec fn stmt_policy_search_composition() -> bool {
    forall|d: NDomains, p: Seq<NRule>, rule: NRule, cases: Set<Constraint>,
        outcomes: spec_fn(Constraint) -> Outcome|
        #[trigger] policy_search_outcomes_ok(d, p, rule, cases, outcomes)
        ==> {
            &&& ((forall|g: Constraint| #[trigger] cases.contains(g) ==> outcomes(g) is Holds)
                ==> n_covers(d, p, rule))
            &&& forall|g: Constraint| #[trigger] cases.contains(g)
                ==> policy_case_outcome_ok(d, p, rule, g, outcomes(g))
        }
}

/// `R` never denies iff `ρ_R ⊑_{Γ_R} ∅`; `R` denies every matching candidate and history iff
/// `Univ ⊑_{Γ_R} ρ_R`. These are constrained forms of the vacuity reductions of appendix
/// `app:policy-reduction`, which use denial expressions. No executable vacuity query exists; the
/// typed vacuity questions go through `at_least_as_strict` by `stmt_vacuity_via_refinement`.
pub open spec fn stmt_vacuity_reductions() -> bool {
    forall|d: NDomains, rule: NRule| rule.head.len() == d.len() ==> {
        &&& (forall|theta: Subst, w: Seq<EventView>| n_theta_ok(d, theta) && n_history_in(d, w) ==> !#[trigger] n_rule_denies(rule, theta, w))
            <==> included_under(d, head_constraint(rule.head), denial(rule), Regex::Empty)
        &&& (forall|theta: Subst, w: Seq<EventView>| n_theta_ok(d, theta) && n_history_in(d, w) && n_head_matches(rule.head, theta)
                ==> #[trigger] n_rule_denies(rule, theta, w))
            <==> #[trigger] included_under(d, head_constraint(rule.head), Regex::All, denial(rule))
    }
}

/// Vacuity through refinement (`app:policy-reduction`): a rule never denies iff the
/// empty policy refines `[R]`, and denies every matching candidate iff `[R]` refines
/// `[forbid head(R) Univ]`; both are `at_least_as_strict` queries.
pub open spec fn stmt_vacuity_via_refinement<E: Event>() -> bool {
    forall|d: DomainsView<E::Component>, r: RuleView<E::Component>| {
        &&& #[trigger] never_denies::<E>(d, r) <==> refines::<E>(d, Seq::empty(), seq![r])
        &&& #[trigger] always_denies::<E>(d, r) <==> refines::<E>(d, seq![r], seq![forbid_all(r.head)])
    }
}

// ----- proofs: finiteness of the constructed sets -----

/// A predicate bounded by a finite set defines a `Set` with exactly its members.
pub proof fn lemma_set_new_bounded<A>(f: spec_fn(A) -> bool, bound: ISet<A>)
    requires
        bound.finite(),
        forall|a: A| f(a) ==> bound.contains(a),
    ensures
        Set::new(f) is Some,
        forall|a: A| #[trigger] Set::new(f).unwrap().contains(a) == f(a),
{
    assert(ISet::new(f).subset_of(bound));
    lemma_iset_subset_finite(bound, ISet::new(f));
    assert(Set::new(f) is Some);
}

pub open spec fn head_value(h: NHead, c: Component) -> nat {
    match n_head_field(h, c) { Some(v) => v, None => 0 }
}

/// A finite coordinate-indexed bound on a head's constant pairs.
pub open spec fn head_coordinate_pairs(h: NHead) -> Set<(Component, nat)> {
    Seq::new(h.len(), |i: int| {
        let c = Component(i as u8);
        (c, head_value(h, c))
    }).to_set()
}

pub proof fn lemma_head_coordinate_pairs(h: NHead, c: Component, v: nat)
    requires n_head_field(h, c) == Some(v),
    ensures head_coordinate_pairs(h).contains((c, v)),
{
    let pairs = Seq::new(h.len(), |i: int| {
        let field = Component(i as u8);
        (field, head_value(h, field))
    });
    assert(c.0 < h.len());
    assert(pairs[c.0 as int] == (c, v));
    assert(pairs.contains((c, v)));
}

/// `Γ_R` has exactly the equalities of the head's constant coordinates.
pub proof fn lemma_head_constraint(h: NHead)
    ensures
        forall|l: Literal| #[trigger] head_constraint(h).contains(l)
            <==> (l.equal && n_head_field(h, l.component) == Some(l.value)),
{
    let make = |p: (Component, nat)| eq_literal(p.0, p.1);
    let bound = head_coordinate_pairs(h).to_iset().map(make);
    head_coordinate_pairs(h).to_iset().lemma_map_finite(make);
    let f = |l: Literal| l.equal && n_head_field(h, l.component) == Some(l.value);
    assert forall|l: Literal| f(l) implies bound.contains(l) by {
        lemma_head_coordinate_pairs(h, l.component, l.value);
        assert(l == make((l.component, l.value)));
    }
    lemma_set_new_bounded(f, bound);
    assert(head_constraint(h) == Set::new(f).unwrap());
}

/// A finite superset of `head_pairs(p)`.
pub open spec fn head_pairs_bound(p: Seq<NRule>) -> ISet<(Component, nat)>
    decreases p.len(),
{
    if p.len() == 0 {
        ISet::empty()
    } else {
        let h = p.last().head;
        head_pairs_bound(p.drop_last()).union(head_coordinate_pairs(h).to_iset())
    }
}

pub proof fn lemma_head_pairs_bound(p: Seq<NRule>)
    ensures
        head_pairs_bound(p).finite(),
        forall|pair: (Component, nat)| (exists|i: int| 0 <= i < p.len() && #[trigger] n_head_field(p[i].head, pair.0) == Some(pair.1))
            ==> #[trigger] head_pairs_bound(p).contains(pair),
    decreases p.len(),
{
    broadcast use vstd::iset::lemma_iset_union_finite, vstd::set::lemma_to_iset_finite;
    if p.len() > 0 {
        let q = p.drop_last();
        lemma_head_pairs_bound(q);
        let h = p.last().head;
        assert forall|pair: (Component, nat)| (exists|i: int| 0 <= i < p.len() && #[trigger] n_head_field(p[i].head, pair.0) == Some(pair.1))
            implies #[trigger] head_pairs_bound(p).contains(pair) by {
            let i = choose|i: int| 0 <= i < p.len() && #[trigger] n_head_field(p[i].head, pair.0) == Some(pair.1);
            if i < p.len() - 1 {
                assert(q[i] == p[i]);
                assert(n_head_field(q[i].head, pair.0) == Some(pair.1));
                assert(head_pairs_bound(q).contains(pair));
            } else {
                assert(n_head_field(h, pair.0) == Some(pair.1));
                lemma_head_coordinate_pairs(h, pair.0, pair.1);
            }
        }
    }
}

/// `Π` has exactly the head constants of `P` (finitely many).
pub proof fn lemma_head_pairs(p: Seq<NRule>)
    ensures
        forall|pair: (Component, nat)| #[trigger] head_pairs(p).contains(pair)
            <==> exists|i: int| 0 <= i < p.len() && #[trigger] n_head_field(p[i].head, pair.0) == Some(pair.1),
{
    lemma_head_pairs_bound(p);
    let f = |pair: (Component, nat)| exists|i: int| 0 <= i < p.len() && #[trigger] n_head_field(p[i].head, pair.0) == Some(pair.1);
    lemma_set_new_bounded(f, head_pairs_bound(p));
    assert(head_pairs(p) == Set::new(f).unwrap());
}

/// Both literals of every pair of `Π`.
pub open spec fn pair_literals(pi: Pairs) -> Set<Literal> {
    pi.map(|p: (Component, nat)| eq_literal(p.0, p.1)).union(pi.map(|p: (Component, nat)| ne_literal(p.0, p.1)))
}

/// Membership in the paper's `Split` (the defining set is finite).
pub proof fn lemma_paper_split_members(d: NDomains, g: Constraint, pi: Pairs)
    ensures
        forall|g1: Constraint| #[trigger] paper_split(d, g, pi).contains(g1)
            <==> exists|delta: Constraint| #[trigger] split_delta(d, g, pi, delta) && g1 == g.union(delta)
                && satisfiable(d, g1),
{
    let lits = pair_literals(pi);
    lemma_powerset_finite(lits);
    let pw = ISet::new(|s: Set<Literal>| s.subset_of(lits));
    let un = |delta: Set<Literal>| g.union(delta);
    pw.lemma_map_finite(un);
    let f = |g1: Constraint| exists|delta: Constraint| #[trigger] split_delta(d, g, pi, delta) && g1 == g.union(delta)
        && satisfiable(d, g1);
    assert forall|g1: Constraint| f(g1) implies pw.map(un).contains(g1) by {
        let delta = choose|delta: Constraint| #[trigger] split_delta(d, g, pi, delta) && g1 == g.union(delta)
            && satisfiable(d, g1);
        assert forall|l: Literal| delta.contains(l) implies lits.contains(l) by {
            let pr = (l.component, l.value);
            assert(pi.contains(pr));
            if l.equal {
                assert(l == eq_literal(pr.0, pr.1));
                assert(pi.map(|p: (Component, nat)| eq_literal(p.0, p.1)).contains(l));
            } else {
                assert(l == ne_literal(pr.0, pr.1));
                assert(pi.map(|p: (Component, nat)| ne_literal(p.0, p.1)).contains(l));
            }
        }
        assert(pw.contains(delta));
        assert(un(delta) == g1);
    }
    lemma_set_new_bounded(f, pw.map(un));
    assert(paper_split(d, g, pi) == Set::new(f).unwrap());
}

// ----- proofs: constraints -----

pub proof fn lemma_entails_subset(d: NDomains, g1: Constraint, g2: Constraint)
    requires g2.subset_of(g1),
    ensures entails(d, g1, g2),
{
    assert forall|theta: Subst| n_theta_ok(d, theta) && #[trigger] sat_by(theta, g1) implies sat_by(theta, g2) by {
        assert forall|l: Literal| #[trigger] g2.contains(l) implies literal_holds(theta, l) by {
            assert(g1.contains(l));
        }
    }
}

pub proof fn lemma_entails_trans(d: NDomains, a: Constraint, b: Constraint, c: Constraint)
    requires entails(d, a, b), entails(d, b, c),
    ensures entails(d, a, c),
{
    assert forall|theta: Subst| n_theta_ok(d, theta) && #[trigger] sat_by(theta, a) implies sat_by(theta, c) by {
        assert(sat_by(theta, b));
    }
}

/// A constraint satisfied by `θ0` that decides every literal of `gh` (all equalities, also
/// satisfied by `θ0`) entails `gh`.
pub proof fn lemma_decided_entails(d: NDomains, g1: Constraint, gh: Constraint, theta0: Subst)
    requires
        n_theta_ok(d, theta0),
        sat_by(theta0, g1),
        sat_by(theta0, gh),
        forall|l: Literal| #[trigger] gh.contains(l) ==> l.equal && decides(d, g1, l.component, l.value),
    ensures entails(d, g1, gh),
{
    assert forall|theta: Subst| n_theta_ok(d, theta) && #[trigger] sat_by(theta, g1) implies sat_by(theta, gh) by {
        assert forall|l: Literal| #[trigger] gh.contains(l) implies literal_holds(theta, l) by {
            let eq = eq_literal(l.component, l.value);
            let ne = ne_literal(l.component, l.value);
            assert(literal_holds(theta0, l));
            if entails(d, g1, set![ne]) {
                assert(sat_by(theta0, set![ne]));
                assert(set![ne].contains(ne));
                assert(false);
            }
            assert(entails(d, g1, set![eq]));
            assert(sat_by(theta, set![eq]));
            assert(set![eq].contains(eq));
            assert(l == eq);
        }
    }
}

/// Under a valuation, `Δ` is determined by `Π` and the undecided pairs.
pub proof fn lemma_delta_unique(d: NDomains, g: Constraint, pi: Pairs, d1: Constraint, d2: Constraint, theta: Subst)
    requires
        split_delta(d, g, pi, d1),
        split_delta(d, g, pi, d2),
        sat_by(theta, d1),
        sat_by(theta, d2),
    ensures d1 == d2,
{
    assert forall|l: Literal| d1.contains(l) implies d2.contains(l) by {
        lemma_delta_unique_one(d, g, pi, d1, d2, theta, l);
    }
    assert forall|l: Literal| d2.contains(l) implies d1.contains(l) by {
        lemma_delta_unique_one(d, g, pi, d2, d1, theta, l);
    }
    assert(d1 =~= d2);
}

proof fn lemma_delta_unique_one(d: NDomains, g: Constraint, pi: Pairs, d1: Constraint, d2: Constraint, theta: Subst, l: Literal)
    requires
        split_delta(d, g, pi, d1),
        split_delta(d, g, pi, d2),
        sat_by(theta, d1),
        sat_by(theta, d2),
        d1.contains(l),
    ensures d2.contains(l),
{
    let pr = (l.component, l.value);
    assert(pi.contains(pr) && !decides(d, g, pr.0, pr.1));
    let eq = eq_literal(pr.0, pr.1);
    let ne = ne_literal(pr.0, pr.1);
    assert(d2.contains(eq) != d2.contains(ne));
    assert(literal_holds(theta, l));
    if d2.contains(eq) {
        assert(literal_holds(theta, eq));
        assert(l == eq);
    } else {
        assert(literal_holds(theta, ne));
        assert(l == ne);
    }
}

pub proof fn lemma_paper_split_ok(d: NDomains, g: Constraint, pi: Pairs)
    ensures split_ok(d, g, pi, paper_split(d, g, pi)),
{
    let cases = paper_split(d, g, pi);
    lemma_paper_split_members(d, g, pi);
    assert forall|g1: Constraint| #[trigger] cases.contains(g1) implies satisfiable(d, g1) && entails(d, g1, g)
        && forall|p: (Component, nat)| pi.contains(p) ==> #[trigger] decides(d, g1, p.0, p.1) by {
        let delta = choose|delta: Constraint| #[trigger] split_delta(d, g, pi, delta) && g1 == g.union(delta)
            && satisfiable(d, g1);
        lemma_entails_subset(d, g1, g);
        assert forall|p: (Component, nat)| pi.contains(p) implies #[trigger] decides(d, g1, p.0, p.1) by {
            let eq = eq_literal(p.0, p.1);
            let ne = ne_literal(p.0, p.1);
            if decides(d, g, p.0, p.1) {
                if entails(d, g, set![eq]) {
                    lemma_entails_trans(d, g1, g, set![eq]);
                } else {
                    lemma_entails_trans(d, g1, g, set![ne]);
                }
            } else if delta.contains(eq) {
                lemma_entails_subset(d, g1, set![eq]);
            } else {
                assert(delta.contains(ne));
                lemma_entails_subset(d, g1, set![ne]);
            }
        }
    }
    assert forall|theta: Subst| n_theta_ok(d, theta) && #[trigger] sat_by(theta, g)
        implies exists|g1: Constraint| #[trigger] cases.contains(g1) && sat_by(theta, g1) by {
        let undecided = pi.filter(|p: (Component, nat)| !decides(d, g, p.0, p.1));
        let mk = |p: (Component, nat)| Literal { component: p.0, value: p.1, equal: language::field_value(theta, p.0) == p.1 };
        let delta = undecided.map(mk);
        assert forall|l: Literal| #[trigger] delta.contains(l) implies pi.contains((l.component, l.value))
            && !decides(d, g, l.component, l.value) && literal_holds(theta, l) by {
            let p = choose|p: (Component, nat)| undecided.contains(p) && l == mk(p);
            assert((l.component, l.value) == p);
        }
        assert forall|p: (Component, nat)| #[trigger] pi.contains(p) && !decides(d, g, p.0, p.1)
            implies delta.contains(eq_literal(p.0, p.1)) != delta.contains(ne_literal(p.0, p.1)) by {
            assert(undecided.contains(p));
            assert(delta.contains(mk(p)));
            if language::field_value(theta, p.0) == p.1 {
                assert(mk(p) == eq_literal(p.0, p.1));
                assert(!literal_holds(theta, ne_literal(p.0, p.1)));
            } else {
                assert(mk(p) == ne_literal(p.0, p.1));
                assert(!literal_holds(theta, eq_literal(p.0, p.1)));
            }
        }
        assert(split_delta(d, g, pi, delta));
        let g1 = g.union(delta);
        assert(sat_by(theta, g1));
        assert(satisfiable(d, g1));
        assert(cases.contains(g1));
    }
    assert forall|theta: Subst, g1: Constraint, g2: Constraint| n_theta_ok(d, theta) && cases.contains(g1) && cases.contains(g2)
        && #[trigger] sat_by(theta, g1) && #[trigger] sat_by(theta, g2) implies g1 == g2 by {
        let d1 = choose|delta: Constraint| #[trigger] split_delta(d, g, pi, delta) && g1 == g.union(delta)
            && satisfiable(d, g1);
        let d2 = choose|delta: Constraint| #[trigger] split_delta(d, g, pi, delta) && g2 == g.union(delta)
            && satisfiable(d, g2);
        lemma_entails_subset(d, g1, d1);
        lemma_entails_subset(d, g2, d2);
        assert forall|l: Literal| #[trigger] d1.contains(l) implies literal_holds(theta, l) by { assert(g1.contains(l)); }
        assert forall|l: Literal| #[trigger] d2.contains(l) implies literal_holds(theta, l) by { assert(g2.contains(l)); }
        lemma_delta_unique(d, g, pi, d1, d2, theta);
    }
}

pub proof fn theorem_paper_split_ok()
    ensures stmt_paper_split_ok(),
{
    assert forall|d: NDomains, g: Constraint, pi: Pairs| #[trigger] split_ok(d, g, pi, paper_split(d, g, pi)) by {
        lemma_paper_split_ok(d, g, pi);
    }
}

// ----- proofs: policy reduction -----

/// `θ ⊨ Γ_R` iff the head matches `θ`.
pub proof fn lemma_head_sat(h: NHead, theta: Subst)
    requires h.len() == theta.len(), h.len() <= MAX_ARITY,
    ensures sat_by(theta, head_constraint(h)) == n_head_matches(h, theta),
{
    lemma_head_constraint(h);
    if n_head_matches(h, theta) {
        assert forall|l: Literal| #[trigger] head_constraint(h).contains(l) implies literal_holds(theta, l) by {
            assert(n_head_field(h, l.component) == Some(l.value));
        }
    }
    if sat_by(theta, head_constraint(h)) {
        assert forall|i: int| #![trigger h[i]] 0 <= i < h.len() implies
            (h[i] matches Some(v) ==> theta[i] == v) by {
            let c = Component(i as u8);
            assert(c.0 as int == i);
            if let Some(v) = h[i] {
                assert(n_head_field(h, c) == Some(v));
                assert(head_constraint(h).contains(eq_literal(c, v)));
                assert(literal_holds(theta, eq_literal(c, v)));
            }
        }
    }
}

/// `L(ρ_R)` is the set of histories violating the rule's mode.
pub proof fn lemma_denial_lang(rule: NRule, theta: Subst, w: Seq<EventView>)
    ensures n_lang(theta, denial(rule), w) == violated_by(rule.mode, n_lang(theta, rule.tail, w)),
{
}

/// `R` denies iff `θ ⊨ Γ_R` and `w ∈ L_θ(ρ_R)`.
pub proof fn lemma_rule_denies_iff(rule: NRule, theta: Subst, w: Seq<EventView>)
    requires rule.head.len() == theta.len(), rule.head.len() <= MAX_ARITY,
    ensures n_rule_denies(rule, theta, w) == (sat_by(theta, head_constraint(rule.head)) && n_lang(theta, denial(rule), w)),
{
    lemma_head_sat(rule.head, theta);
    lemma_denial_lang(rule, theta, w);
}

/// The language of the firing denials under a case.
pub proof fn lemma_firing_lang(d: NDomains, p: Seq<NRule>, g1: Constraint, theta: Subst, w: Seq<EventView>)
    ensures
        n_lang(theta, firing_denials(d, p, g1), w) <==> exists|j: int| 0 <= j < p.len()
            && entails(d, g1, head_constraint(p[j].head)) && #[trigger] n_lang(theta, denial(p[j]), w),
{
    let firing = p.filter(|r: NRule| entails(d, g1, head_constraint(r.head)));
    let ms = firing.map(|i: int, r: NRule| denial(r));
    assert(firing_denials(d, p, g1) == Regex::Union(ms));
    if n_lang(theta, firing_denials(d, p, g1), w) {
        let i = choose|i: int| 0 <= i < ms.len() && language::numeric_lang(model::gsem(theta), ms[i], w);
        let r = firing[i];
        assert(entails(d, g1, head_constraint(r.head)));
        assert(firing.contains(r));
        p.lemma_filter_contains_rev(|r: NRule| entails(d, g1, head_constraint(r.head)), r);
        let j = choose|j: int| 0 <= j < p.len() && p[j] == r;
        assert(n_lang(theta, denial(p[j]), w));
    }
    if exists|j: int| 0 <= j < p.len() && entails(d, g1, head_constraint(p[j].head)) && #[trigger] n_lang(theta, denial(p[j]), w) {
        let j = choose|j: int| 0 <= j < p.len() && entails(d, g1, head_constraint(p[j].head)) && #[trigger] n_lang(theta, denial(p[j]), w);
        assert(firing.contains(p[j]));
        let i = choose|i: int| 0 <= i < firing.len() && firing[i] == p[j];
        assert(ms[i] == denial(p[j]));
        assert(language::numeric_lang(model::gsem(theta), ms[i], w));
        language::lemma_lang_union(model::gsem(theta), ms, w);
    }
}

/// In a case deciding every policy head constant, the firing language is exactly policy denial.
/// This single-case interface does not require constructing or retaining the entire split.
pub proof fn lemma_firing_policy_iff(d: NDomains, p: Seq<NRule>, g: Constraint,
    theta: Subst, w: Seq<EventView>)
    requires
        forall|i: int| 0 <= i < p.len() ==> #[trigger] p[i].head.len() == d.len(),
        n_theta_ok(d, theta),
        sat_by(theta, g),
        forall|pair: (Component, nat)| head_pairs(p).contains(pair)
            ==> #[trigger] decides(d, g, pair.0, pair.1),
    ensures n_lang(theta, firing_denials(d, p, g), w) == n_policy_denies(p, theta, w),
{
    lemma_head_pairs(p);
    lemma_firing_lang(d, p, g, theta, w);
    if n_policy_denies(p, theta, w) {
        let j = choose|j: int| 0 <= j < p.len() && #[trigger] n_rule_denies(p[j], theta, w);
        let gj = head_constraint(p[j].head);
        lemma_rule_denies_iff(p[j], theta, w);
        lemma_head_constraint(p[j].head);
        assert forall|l: Literal| #[trigger] gj.contains(l)
            implies l.equal && decides(d, g, l.component, l.value) by {
            assert(n_head_field(p[j].head, l.component) == Some(l.value));
            assert(head_pairs(p).contains((l.component, l.value)));
        }
        lemma_decided_entails(d, g, gj, theta);
    }
    if n_lang(theta, firing_denials(d, p, g), w) {
        let j = choose|j: int| 0 <= j < p.len()
            && entails(d, g, head_constraint(p[j].head)) && #[trigger] n_lang(theta, denial(p[j]), w);
        assert(sat_by(theta, head_constraint(p[j].head)));
        lemma_rule_denies_iff(p[j], theta, w);
        assert(n_rule_denies(p[j], theta, w));
    }
}

/// Transfer one numeric inclusion witness to an uncovered rule witness, including explicit
/// failure of coverage. This is shared by the reduction, search composition, and typed bridge.
pub proof fn lemma_policy_counterexample_transfer(d: NDomains, p: Seq<NRule>, rule: NRule,
    g: Constraint, theta: Subst, w: Seq<EventView>)
    requires
        rule.head.len() == d.len(),
        forall|i: int| 0 <= i < p.len() ==> #[trigger] p[i].head.len() == d.len(),
        entails(d, g, head_constraint(rule.head)),
        forall|pair: (Component, nat)| head_pairs(p).contains(pair)
            ==> #[trigger] decides(d, g, pair.0, pair.1),
        inclusion_cex(d, g, denial(rule), firing_denials(d, p, g), theta, w),
    ensures
        n_rule_denies(rule, theta, w),
        !n_policy_denies(p, theta, w),
        !n_covers(d, p, rule),
{
    assert(sat_by(theta, head_constraint(rule.head)));
    lemma_rule_denies_iff(rule, theta, w);
    lemma_firing_policy_iff(d, p, g, theta, w);
}

/// Per-case minimum length transfers in the reverse direction: any shorter uncovered pair
/// would be a shorter counterexample to the selected constrained inclusion.
pub proof fn lemma_policy_no_shorter(d: NDomains, p: Seq<NRule>, rule: NRule, g: Constraint, n: nat)
    requires
        rule.head.len() == d.len(),
        forall|i: int| 0 <= i < p.len() ==> #[trigger] p[i].head.len() == d.len(),
        forall|pair: (Component, nat)| head_pairs(p).contains(pair)
            ==> #[trigger] decides(d, g, pair.0, pair.1),
        no_cex_shorter(d, g, denial(rule), firing_denials(d, p, g), n),
    ensures n_no_uncovered_shorter(d, p, rule, g, n),
{
    assert forall|theta: Subst, w: Seq<EventView>| n_theta_ok(d, theta) && n_history_in(d, w)
        && sat_by(theta, g) && w.len() < n
        implies !(#[trigger] n_rule_denies(rule, theta, w) && !n_policy_denies(p, theta, w)) by {
        lemma_rule_denies_iff(rule, theta, w);
        lemma_firing_policy_iff(d, p, g, theta, w);
        if n_rule_denies(rule, theta, w) && !n_policy_denies(p, theta, w) {
            assert(inclusion_cex(d, g, denial(rule), firing_denials(d, p, g), theta, w));
        }
    }
}

/// Compose a single decided search case, independently of the other cases in the family.
pub proof fn lemma_policy_case_outcome(d: NDomains, p: Seq<NRule>, rule: NRule,
    g0: Constraint, outcome: Outcome)
    requires
        rule.head.len() == d.len(),
        forall|i: int| 0 <= i < p.len() ==> #[trigger] p[i].head.len() == d.len(),
        entails(d, g0, head_constraint(rule.head)),
        forall|pair: (Component, nat)| head_pairs(p).contains(pair)
            ==> #[trigger] decides(d, g0, pair.0, pair.1),
        outcome_ok(d, g0, denial(rule), firing_denials(d, p, g0), outcome),
    ensures policy_case_outcome_ok(d, p, rule, g0, outcome),
{
    match outcome {
        Outcome::Refuted(g, letters) => {
            let theta = choose|theta: Subst| n_theta_ok(d, theta) && #[trigger] sat_by(theta, g);
            let w = choose|w: Seq<EventView>| #[trigger] follows(d, letters, theta, w);
            lemma_policy_counterexample_transfer(d, p, rule, g0, theta, w);
            assert(exists|t: Subst, u: Seq<EventView>| n_theta_ok(d, t)
                && sat_by(t, g) && #[trigger] follows(d, letters, t, u));
            assert forall|t: Subst, u: Seq<EventView>| n_theta_ok(d, t) && sat_by(t, g)
                && #[trigger] follows(d, letters, t, u)
                implies n_rule_denies(rule, t, u) && !n_policy_denies(p, t, u) by {
                lemma_policy_counterexample_transfer(d, p, rule, g0, t, u);
            }
            lemma_policy_no_shorter(d, p, rule, g0, letters.len());
        },
        Outcome::Holds => {},
        Outcome::Exhausted => {},
    }
}

pub proof fn lemma_policy_reduction(d: NDomains, p: Seq<NRule>, rule: NRule, cases: Set<Constraint>)
    requires split_ok(d, head_constraint(rule.head), head_pairs(p), cases),
        rule.head.len() == d.len(),
        forall|i: int| 0 <= i < p.len() ==> #[trigger] p[i].head.len() == d.len(),
    ensures
        n_covers(d, p, rule) <==> forall|g1: Constraint| #[trigger] cases.contains(g1)
            ==> included_under(d, g1, denial(rule), firing_denials(d, p, g1)),
{
    let gr = head_constraint(rule.head);
    if n_covers(d, p, rule) {
        assert forall|g1: Constraint| #[trigger] cases.contains(g1)
            implies included_under(d, g1, denial(rule), firing_denials(d, p, g1)) by {
            assert forall|theta: Subst, w: Seq<EventView>| n_theta_ok(d, theta) && n_history_in(d, w) && sat_by(theta, g1)
                && #[trigger] n_lang(theta, denial(rule), w) implies n_lang(theta, firing_denials(d, p, g1), w) by {
                assert(entails(d, g1, gr));
                assert(sat_by(theta, gr));
                lemma_rule_denies_iff(rule, theta, w);
                assert(n_rule_denies(rule, theta, w));
                lemma_firing_policy_iff(d, p, g1, theta, w);
            }
        }
    }
    if forall|g1: Constraint| #[trigger] cases.contains(g1) ==> included_under(d, g1, denial(rule), firing_denials(d, p, g1)) {
        assert forall|theta: Subst, w: Seq<EventView>| n_theta_ok(d, theta) && n_history_in(d, w)
            && #[trigger] n_rule_denies(rule, theta, w) implies n_policy_denies(p, theta, w) by {
            lemma_rule_denies_iff(rule, theta, w);
            assert(sat_by(theta, gr));
            let g1 = choose|g1: Constraint| #[trigger] cases.contains(g1) && sat_by(theta, g1);
            assert(included_under(d, g1, denial(rule), firing_denials(d, p, g1)));
            assert(n_lang(theta, firing_denials(d, p, g1), w));
            lemma_firing_policy_iff(d, p, g1, theta, w);
        }
    }
}

pub proof fn theorem_policy_reduction()
    ensures stmt_policy_reduction(),
{
    assert forall|d: NDomains, p: Seq<NRule>, rule: NRule, cases: Set<Constraint>|
        rule.head.len() == d.len()
        && (forall|i: int| 0 <= i < p.len() ==> #[trigger] p[i].head.len() == d.len())
        && #[trigger] split_ok(d, head_constraint(rule.head), head_pairs(p), cases)
        implies (n_covers(d, p, rule) <==> forall|g1: Constraint| #[trigger] cases.contains(g1)
            ==> included_under(d, g1, denial(rule), firing_denials(d, p, g1))) by {
        lemma_policy_reduction(d, p, rule, cases);
    }
}

pub proof fn lemma_policy_search_composition(d: NDomains, p: Seq<NRule>, rule: NRule,
    cases: Set<Constraint>, outcomes: spec_fn(Constraint) -> Outcome)
    requires
        rule.head.len() == d.len(),
        forall|i: int| 0 <= i < p.len() ==> #[trigger] p[i].head.len() == d.len(),
        split_ok(d, head_constraint(rule.head), head_pairs(p), cases),
        forall|g: Constraint| #[trigger] cases.contains(g)
            ==> outcome_ok(d, g, denial(rule), firing_denials(d, p, g), outcomes(g)),
    ensures
        (forall|g: Constraint| #[trigger] cases.contains(g) ==> outcomes(g) is Holds)
            ==> n_covers(d, p, rule),
        forall|g: Constraint| #[trigger] cases.contains(g)
            ==> policy_case_outcome_ok(d, p, rule, g, outcomes(g)),
{
    lemma_policy_reduction(d, p, rule, cases);
    if forall|g: Constraint| #[trigger] cases.contains(g) ==> outcomes(g) is Holds {
        assert forall|g: Constraint| #[trigger] cases.contains(g)
            implies included_under(d, g, denial(rule), firing_denials(d, p, g)) by {
            assert(outcomes(g) == Outcome::Holds);
        }
    }
    assert forall|g: Constraint| #[trigger] cases.contains(g)
        implies policy_case_outcome_ok(d, p, rule, g, outcomes(g)) by {
        lemma_policy_case_outcome(d, p, rule, g, outcomes(g));
    }
}

pub proof fn theorem_policy_search_composition()
    ensures stmt_policy_search_composition(),
{
    assert forall|d: NDomains, p: Seq<NRule>, rule: NRule, cases: Set<Constraint>,
        outcomes: spec_fn(Constraint) -> Outcome|
        #[trigger] policy_search_outcomes_ok(d, p, rule, cases, outcomes)
        implies {
            &&& ((forall|g: Constraint| #[trigger] cases.contains(g) ==> outcomes(g) is Holds)
                ==> n_covers(d, p, rule))
            &&& forall|g: Constraint| #[trigger] cases.contains(g)
                ==> policy_case_outcome_ok(d, p, rule, g, outcomes(g))
        } by {
        lemma_policy_search_composition(d, p, rule, cases, outcomes);
    }
}

pub proof fn lemma_vacuity(d: NDomains, rule: NRule)
    requires rule.head.len() == d.len(),
    ensures
        (forall|theta: Subst, w: Seq<EventView>| n_theta_ok(d, theta) && n_history_in(d, w) ==> !#[trigger] n_rule_denies(rule, theta, w))
            <==> included_under(d, head_constraint(rule.head), denial(rule), Regex::Empty),
        (forall|theta: Subst, w: Seq<EventView>| n_theta_ok(d, theta) && n_history_in(d, w) && n_head_matches(rule.head, theta)
                ==> #[trigger] n_rule_denies(rule, theta, w))
            <==> included_under(d, head_constraint(rule.head), Regex::All, denial(rule)),
{
    let gr = head_constraint(rule.head);
    if forall|theta: Subst, w: Seq<EventView>| n_theta_ok(d, theta) && n_history_in(d, w) ==> !#[trigger] n_rule_denies(rule, theta, w) {
        assert forall|theta: Subst, w: Seq<EventView>| n_theta_ok(d, theta) && n_history_in(d, w) && sat_by(theta, gr)
            && #[trigger] n_lang(theta, denial(rule), w) implies n_lang(theta, Regex::Empty, w) by {
            lemma_rule_denies_iff(rule, theta, w);
        }
    }
    if included_under(d, gr, denial(rule), Regex::Empty) {
        assert forall|theta: Subst, w: Seq<EventView>| n_theta_ok(d, theta) && n_history_in(d, w)
            implies !#[trigger] n_rule_denies(rule, theta, w) by {
            lemma_rule_denies_iff(rule, theta, w);
            if n_rule_denies(rule, theta, w) {
                assert(n_lang(theta, denial(rule), w));
            }
        }
    }
    if forall|theta: Subst, w: Seq<EventView>| n_theta_ok(d, theta) && n_history_in(d, w) && n_head_matches(rule.head, theta)
        ==> #[trigger] n_rule_denies(rule, theta, w) {
        assert forall|theta: Subst, w: Seq<EventView>| n_theta_ok(d, theta) && n_history_in(d, w) && sat_by(theta, gr)
            && #[trigger] n_lang(theta, Regex::All, w) implies n_lang(theta, denial(rule), w) by {
            lemma_rule_denies_iff(rule, theta, w);
            lemma_head_sat(rule.head, theta);
            assert(n_rule_denies(rule, theta, w));
        }
    }
    if included_under(d, gr, Regex::All, denial(rule)) {
        assert forall|theta: Subst, w: Seq<EventView>| n_theta_ok(d, theta) && n_history_in(d, w) && n_head_matches(rule.head, theta)
            implies #[trigger] n_rule_denies(rule, theta, w) by {
            lemma_rule_denies_iff(rule, theta, w);
            lemma_head_sat(rule.head, theta);
            assert(n_lang(theta, Regex::All, w));
        }
    }
}

pub proof fn theorem_vacuity_reductions()
    ensures stmt_vacuity_reductions(),
{
    assert forall|d: NDomains, rule: NRule|
        #![trigger included_under(d, head_constraint(rule.head), denial(rule), Regex::Empty)]
        rule.head.len() == d.len() implies (
            (forall|theta: Subst, w: Seq<EventView>| n_theta_ok(d, theta) && n_history_in(d, w) ==> !#[trigger] n_rule_denies(rule, theta, w))
                <==> included_under(d, head_constraint(rule.head), denial(rule), Regex::Empty)) by {
        lemma_vacuity(d, rule);
    }
    assert forall|d: NDomains, rule: NRule|
        #![trigger included_under(d, head_constraint(rule.head), Regex::All, denial(rule))]
        rule.head.len() == d.len() implies (
            (forall|theta: Subst, w: Seq<EventView>| n_theta_ok(d, theta) && n_history_in(d, w) && n_head_matches(rule.head, theta)
                    ==> #[trigger] n_rule_denies(rule, theta, w))
                <==> included_under(d, head_constraint(rule.head), Regex::All, denial(rule))) by {
        lemma_vacuity(d, rule);
    }
}

pub proof fn theorem_vacuity_via_refinement<E: Event>()
    ensures stmt_vacuity_via_refinement::<E>(),
{
    assert forall|d: DomainsView<E::Component>, r: RuleView<E::Component>|
        #[trigger] never_denies::<E>(d, r) <==> refines::<E>(d, Seq::empty(), seq![r]) by {
        let single = seq![r];
        assert forall|c: E, h: Seq<E>| policy_denies(single, c, h) <==> rule_violated(r, c, h) by {
            assert(single[0] == r);
        }
        assert(forall|c: E, h: Seq<E>| !policy_denies(Seq::<RuleView<E::Component>>::empty(), c, h));
        if never_denies::<E>(d, r) {
            assert forall|c: E, h: Seq<E>| in_domains::<E>(d, c, h) && policy_permits(Seq::empty(), c, h)
                implies #[trigger] policy_permits(single, c, h) by {
                assert(!rule_violated(r, c, h));
            }
        }
        if refines::<E>(d, Seq::empty(), single) {
            assert forall|c: E, h: Seq<E>| in_domains::<E>(d, c, h) implies !#[trigger] rule_violated(r, c, h) by {
                assert(policy_permits(single, c, h));
            }
        }
    }
    assert forall|d: DomainsView<E::Component>, r: RuleView<E::Component>|
        #[trigger] always_denies::<E>(d, r) <==> refines::<E>(d, seq![r], seq![forbid_all(r.head)]) by {
        let single = seq![r];
        let all = seq![forbid_all(r.head)];
        assert forall|c: E, h: Seq<E>| policy_denies(single, c, h) <==> rule_violated(r, c, h) by {
            assert(single[0] == r);
        }
        assert forall|c: E, h: Seq<E>| policy_denies(all, c, h) <==> head_matches(r.head, event_view(c)) by {
            assert(all[0] == forbid_all(r.head));
            assert(lang(RegexView::<E::Component>::All, r.head, event_view(c), history_view(h)));
            assert(rule_violated(forbid_all(r.head), c, h) == head_matches(r.head, event_view(c)));
        }
        if always_denies::<E>(d, r) {
            assert forall|c: E, h: Seq<E>| in_domains::<E>(d, c, h) && policy_permits(single, c, h)
                implies #[trigger] policy_permits(all, c, h) by {
                assert(!rule_violated(r, c, h));
            }
        }
        if refines::<E>(d, single, all) {
            assert forall|c: E, h: Seq<E>| in_domains::<E>(d, c, h) && head_matches(r.head, event_view(c))
                implies #[trigger] rule_violated(r, c, h) by {
                assert(policy_denies(all, c, h));
                assert(!policy_permits(all, c, h));
            }
        }
    }
}

} // verus!
