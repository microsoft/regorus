//! Layer 3: the symbolic search (`sec:search-state`, `sec:search`; appendix `app:cases`,
//! `app:search-proof`; differences from the paper's presentation in `app:mech-diff`).
//!
//! States are abstract expressions `Regex<model::Test>`; the implementation's states are graph
//! ids, abstracted by `model::lift_regex` (see `implementation`). The search is specified by its
//! *traces*: the sequence of inserted items in insertion order, with parents and depths, as kept
//! by `history-analysis/src/search.rs` (`items`, `next`). Insertion-time discarding is specified
//! semantically (no witnesses, or witnesses contained in those of an earlier item); the `pruning`
//! layer shows the implemented checks imply it.
use super::encoding::*;
use super::inclusion::*;
use history_syntax::syntax::Component;
use junco_core::kernel::verify as model;
use junco_core::verify::history_specs as language;
use junco_core::verify::history_specs::{EventView, Regex, Subst};
use vstd::prelude::*;

verus! {

/// A search item `(Γ, q)`.
pub struct Item { pub constraint: Constraint, pub state: Regex<model::Test> }

/// `(θ, w) ∈ W(I)` (`sec:search-state`).
pub open spec fn witness(d: NDomains, item: Item, theta: Subst, w: Seq<EventView>) -> bool {
    n_theta_ok(d, theta) && n_history_in(d, w) && sat_by(theta, item.constraint) && n_lang(theta, item.state, w)
}

pub open spec fn no_witness(d: NDomains, item: Item) -> bool {
    forall|theta: Subst, w: Seq<EventView>| !#[trigger] witness(d, item, theta, w)
}

/// `W(J) ⊆ W(I)`.
pub open spec fn witnesses_within(d: NDomains, j: Item, i: Item) -> bool {
    forall|theta: Subst, w: Seq<EventView>| #[trigger] witness(d, j, theta, w) ==> witness(d, i, theta, w)
}

/// `W(I)` has a member of length `n` (used for the minimality argument).
pub open spec fn has_witness_of_length(d: NDomains, item: Item, n: nat) -> bool {
    exists|theta: Subst, w: Seq<EventView>| w.len() == n && #[trigger] witness(d, item, theta, w)
}

// ----- atoms, assignments, successor cases (`def:atoms`, `def:realize`, `def:successors`, `alg:succ`) -----

/// An atom assignment; its domain is the atom set.
pub type Assignment = Map<model::Primitive, bool>;

/// `(θ, e)` realizes `α`.
pub open spec fn realizes(theta: Subst, e: EventView, alpha: Assignment) -> bool {
    forall|p: model::Primitive| #[trigger] alpha.dom().contains(p) ==> alpha[p] == model::primitive_holds(theta, p, e)
}

/// The finite set of `a` with `f(a)`; empty if there are infinitely many (every use is bounded by
/// a finite set, see `inclusion::lemma_set_new_bounded`).
pub open spec fn finite_set<A>(f: spec_fn(A) -> bool) -> Set<A> {
    Set::new(f).unwrap_or(Set::empty())
}

/// `s` as a finite set; empty if `s` is infinite (every use is proved finite first).
pub open spec fn finite_of<A>(s: ISet<A>) -> Set<A> {
    Set::new_from_iset(s).unwrap_or(Set::empty())
}

/// `Π_q`: `(x_c, v)` such that `π_c = x_c` and `π_c = v` are both atoms.
pub open spec fn atom_pairs(atoms: Set<model::Primitive>) -> Pairs {
    finite_set(|p: (Component, nat)| atoms.contains(model::Primitive::Eq(p.0, model::GTerm::Variable(p.0)))
        && atoms.contains(model::Primitive::Eq(p.0, model::GTerm::Constant(p.1))))
}

/// `next` is the successor of `q` for `α`: `L_θ(next) = e⁻¹ L_θ(q)` whenever `(θ, e)` realizes `α`
/// (the implementation's `successor_entries_wf` in `history-semantics/src/progress.rs`).
pub open spec fn successor_ok(q: Regex<model::Test>, alpha: Assignment, next: Regex<model::Test>) -> bool {
    forall|theta: Subst, e: EventView, w: Seq<EventView>| language::event_wf(theta, theta.len()) && #[trigger] realizes(theta, e, alpha)
        ==> (#[trigger] n_lang(theta, next, w) == n_lang(theta, q, seq![e] + w))
}

/// One successor case `(Γ', α, q')`.
pub struct Case { pub constraint: Constraint, pub alpha: Assignment, pub next: Regex<model::Test> }

pub open spec fn case_item(c: Case) -> Item { Item { constraint: c.constraint, state: c.next } }

/// The conclusion of Lemmas `lem:succ` and `lem:uniform`, stated over successor cases
/// (`app:mech-diff`), for a set of cases of `item`.
pub open spec fn steps_ok(d: NDomains, item: Item, cases: Set<Case>) -> bool {
    &&& forall|c: Case| #[trigger] cases.contains(c) ==> {
        &&& satisfiable(d, c.constraint) && entails(d, c.constraint, item.constraint)
        &&& successor_ok(item.state, c.alpha, c.next)
        // uniform realizability
        &&& forall|theta: Subst| n_theta_ok(d, theta) && #[trigger] sat_by(theta, c.constraint)
            ==> exists|e: EventView| n_event_in(d, e) && #[trigger] realizes(theta, e, c.alpha)
    }
    // every (θ, e) belongs to exactly one case
    &&& forall|theta: Subst, e: EventView| n_theta_ok(d, theta) && #[trigger] n_event_in(d, e) && #[trigger] sat_by(theta, item.constraint)
        ==> exists|c: Case| #[trigger] cases.contains(c) && sat_by(theta, c.constraint) && realizes(theta, e, c.alpha)
    &&& forall|theta: Subst, e: EventView, c1: Case, c2: Case| n_theta_ok(d, theta)
        && cases.contains(c1) && cases.contains(c2) && #[trigger] sat_by(theta, c1.constraint) && #[trigger] sat_by(theta, c2.constraint)
        && #[trigger] realizes(theta, e, c1.alpha) && realizes(theta, e, c2.alpha) ==> c1 == c2
}

/// The paper's successors `succ(Γ, q)` as cases `(Γ', α, next(α))`, for an atom set and the
/// successors `next(α)`.
pub open spec fn paper_steps(d: NDomains, item: Item, atoms: Set<model::Primitive>,
    cases_split: Set<Constraint>, next: spec_fn(Assignment) -> Regex<model::Test>) -> ISet<Case> {
    ISet::new(|c: Case| cases_split.contains(c.constraint) && c.alpha.dom() == atoms && c.next == next(c.alpha)
        && exists|theta: Subst, e: EventView| n_theta_ok(d, theta) && n_event_in(d, e)
            && #[trigger] sat_by(theta, c.constraint) && #[trigger] realizes(theta, e, c.alpha))
}

/// The atoms determine `q`'s derivative: realizing the same assignment gives the same residual
/// language for bounded-arity valuations, including empty bindings (true for the atoms of
/// `δ(q)`'s conditions by Theorem Symbolic derivative correctness, `thm:sderiv`).
pub open spec fn atoms_complete(q: Regex<model::Test>, atoms: Set<model::Primitive>) -> bool {
    forall|theta: Subst, e1: EventView, e2: EventView, w: Seq<EventView>|
        theta.len() <= history_syntax::MAX_ARITY
            && (forall|p: model::Primitive| atoms.contains(p) ==> #[trigger] model::primitive_holds(theta, p, e1) == model::primitive_holds(theta, p, e2))
            ==> (#[trigger] n_lang(theta, q, seq![e1] + w) == #[trigger] n_lang(theta, q, seq![e2] + w))
}

/// Component-locality of atoms (`sec:events`): a variable atom compares a component only with the
/// candidate's value of the same component. The analyzer enforces it (`search.rs` `atom`).
pub open spec fn atoms_local(atoms: Set<model::Primitive>) -> bool {
    forall|c: Component, c2: Component| #[trigger] atoms.contains(model::Primitive::Eq(c, model::GTerm::Variable(c2))) ==> c2 == c
}

/// Every field and register read by an atom belongs to the event's arity.
pub open spec fn atoms_bounded(atoms: Set<model::Primitive>, arity: nat) -> bool {
    forall|p: model::Primitive| #[trigger] atoms.contains(p) ==> match p {
        model::Primitive::Eq(c, model::GTerm::Constant(_)) => c.0 < arity,
        model::Primitive::Eq(c, model::GTerm::Variable(v)) => c.0 < arity && v.0 < arity,
    }
}

/// `Π` of the search: the paper's `Π_q` (`atom_pairs`), plus, for a register compared at a
/// component with a declared finite domain, every declared value (as `split_register` in
/// `history-analysis/src/constraint.rs` does). Without declared domains it is `Π_q`.
pub open spec fn domain_pairs(d: NDomains, atoms: Set<model::Primitive>) -> Pairs {
    finite_set(|p: (Component, nat)| atom_pairs(atoms).contains(p)
        || (atoms.contains(model::Primitive::Eq(p.0, model::GTerm::Variable(p.0)))
            && match n_domain(d, p.0) { Some(values) => values.contains(p.1), None => false }))
}

/// Lemmas `lem:succ` and `lem:uniform` (one statement over successor cases, `app:mech-diff`):
/// with `Γ` satisfiable, complete atoms, correct successors for every realizable assignment, and
/// any `Split(Γ; Π)` family, the successor cases are finite and satisfy `steps_ok`. Declared
/// finite domains are covered (`domain_pairs`), beyond the paper.
pub open spec fn stmt_successor_cases() -> bool {
    forall|d: NDomains, item: Item, atoms: Set<model::Primitive>, cases_split: Set<Constraint>,
        next: spec_fn(Assignment) -> Regex<model::Test>|
        satisfiable(d, item.constraint) && atoms_local(atoms) && atoms_complete(item.state, atoms)
            && atoms_bounded(atoms, d.len())
            && split_ok(d, item.constraint, domain_pairs(d, atoms), cases_split)
            && (forall|alpha: Assignment| alpha.dom() == atoms ==> #[trigger] successor_ok(item.state, alpha, next(alpha)))
            ==> #[trigger] paper_steps(d, item, atoms, cases_split, next).finite()
                && steps_ok(d, item, finite_of(paper_steps(d, item, atoms, cases_split, next)))
}

// ----- the breadth-first search (Algorithm Inclusion search, `alg:search`) -----

pub struct Node { pub item: Item, pub parent: Option<(nat, Assignment)>, pub depth: nat }

/// The search state the implementation keeps: inserted nodes in insertion order (never removed)
/// and the number of expanded nodes.
pub struct Trace { pub nodes: Seq<Node>, pub expanded: nat }

pub enum Outcome { Holds, Refuted(Constraint, Seq<Assignment>), Exhausted }

pub open spec fn nullable_state(q: Regex<model::Test>) -> bool { language::nullable(q) }

/// A successor item may be dropped at insertion: its state is `∅`, or it has no witnesses
/// (dead), or an already inserted node of depth at most `depth` has all its witnesses
/// (an identical item or a dominating one).
pub open spec fn may_discard(d: NDomains, nodes: Seq<Node>, j: Item, depth: nat) -> bool {
    ||| j.state == Regex::<model::Test>::Empty
    ||| no_witness(d, j)
    ||| exists|k: int| 0 <= k < nodes.len() && nodes[k].depth <= depth && #[trigger] witnesses_within(d, j, nodes[k].item)
}

/// Assignments along the parent chain of node `n`, oldest first (`alg:search`).
pub open spec fn chain(nodes: Seq<Node>, n: int, fuel: nat) -> Seq<Assignment>
    decreases fuel,
{
    if fuel == 0 || n < 0 || n >= nodes.len() { Seq::empty() } else {
        match nodes[n].parent {
            None => Seq::empty(),
            Some((p, alpha)) => chain(nodes, p as int, (fuel - 1) as nat).push(alpha),
        }
    }
}

/// Node `j` is a successor case of an expanded earlier node, one level deeper.
pub open spec fn parent_ok(cases_of: spec_fn(Item) -> Set<Case>, t: Trace, j: int) -> bool {
    match t.nodes[j].parent {
        None => false,
        Some((p, alpha)) => p < t.expanded && p < j && t.nodes[j].depth == t.nodes[p as int].depth + 1
            && exists|c: Case| #[trigger] cases_of(t.nodes[p as int].item).contains(c) && c.alpha == alpha
                && t.nodes[j].item == case_item(c),
    }
}

/// `t` is a trace of the search from `(Γ₀, q₀)` that enumerates successor cases with `cases_of`.
pub open spec fn trace_wf(d: NDomains, g0: Constraint, q0: Regex<model::Test>,
    cases_of: spec_fn(Item) -> Set<Case>, t: Trace) -> bool {
    let nodes = t.nodes;
    &&& t.expanded <= nodes.len()
    // the root is inserted unless it may be discarded
    &&& if nodes.len() == 0 { may_discard(d, nodes, Item { constraint: g0, state: q0 }, 0) }
        else { nodes[0] == (Node { item: Item { constraint: g0, state: q0 }, parent: None, depth: 0 }) }
    // every other node is a successor case of an expanded node, one level deeper
    &&& forall|j: int| 0 < j < nodes.len() ==> #[trigger] parent_ok(cases_of, t, j)
    &&& forall|i: int, j: int| 0 <= i < j < nodes.len() ==> #[trigger] nodes[i].depth <= #[trigger] nodes[j].depth
        && nodes[i].item != nodes[j].item
    // expanded nodes are not nullable, and every one of their cases was inserted or discarded
    &&& forall|p: int| 0 <= p < t.expanded ==> !nullable_state(#[trigger] nodes[p].item.state)
        && forall|c: Case| #[trigger] cases_of(nodes[p].item).contains(c) ==>
            (exists|j: int| 0 < j < nodes.len() && nodes[j].parent == Some((p as nat, c.alpha)) && nodes[j].item == case_item(c))
            || may_discard(d, nodes, case_item(c), nodes[p].depth + 1)
}

/// The outcome a trace returns: a counterexample from the first unexpanded node if nullable,
/// `Holds` if every node was expanded, and `Exhausted` from a limit at any point.
pub open spec fn trace_outcome(t: Trace, outcome: Outcome) -> bool {
    match outcome {
        Outcome::Holds => t.expanded == t.nodes.len(),
        Outcome::Refuted(g, letters) => t.expanded < t.nodes.len() && nullable_state(t.nodes[t.expanded as int].item.state)
            && g == t.nodes[t.expanded as int].item.constraint
            && letters == chain(t.nodes, t.expanded as int, t.nodes[t.expanded as int].depth),
        Outcome::Exhausted => true,
    }
}

/// `(θ, u)` follows the recorded assignments.
pub open spec fn follows(d: NDomains, letters: Seq<Assignment>, theta: Subst, u: Seq<EventView>) -> bool {
    u.len() == letters.len() && n_history_in(d, u)
        && forall|j: int| 0 <= j < u.len() ==> #[trigger] realizes(theta, u[j], letters[j])
}

/// What a returned outcome means for the query `r ⊑_{Γ₀} s` (Theorem Inclusion search correctness, `thm:search`).
pub open spec fn outcome_ok(d: NDomains, g0: Constraint, r: Regex<model::Test>, s: Regex<model::Test>, outcome: Outcome) -> bool {
    match outcome {
        Outcome::Holds => included_under(d, g0, r, s),
        Outcome::Refuted(g, letters) =>
            // realizable, and every realization is a counterexample
            (exists|theta: Subst| n_theta_ok(d, theta) && #[trigger] sat_by(theta, g))
            && (forall|theta: Subst| n_theta_ok(d, theta) && #[trigger] sat_by(theta, g)
                ==> exists|u: Seq<EventView>| #[trigger] follows(d, letters, theta, u))
            && (forall|theta: Subst, u: Seq<EventView>| n_theta_ok(d, theta) && sat_by(theta, g) && #[trigger] follows(d, letters, theta, u)
                ==> inclusion_cex(d, g0, r, s, theta, u))
            // minimum length for this query
            && no_cex_shorter(d, g0, r, s, letters.len()),
        Outcome::Exhausted => true,
    }
}

/// `q₀ = N(r & ¬s)` has the language of `r & ¬s`.
pub open spec fn initial_ok(q0: Regex<model::Test>, r: Regex<model::Test>, s: Regex<model::Test>) -> bool {
    forall|theta: Subst, w: Seq<EventView>| language::event_wf(theta, theta.len())
        ==> (#[trigger] n_lang(theta, q0, w) == (n_lang(theta, r, w) && !n_lang(theta, s, w)))
}

/// Inclusion search correctness: every returned trace satisfies `outcome_ok`, with or without
/// pruning, for undeclared and declared finite domains alike. Complete successor cases are
/// required only for expanded trace nodes, exactly the premise established by the executable.
pub open spec fn stmt_search_correct() -> bool {
    forall|d: NDomains, g0: Constraint, r: Regex<model::Test>, s: Regex<model::Test>, q0: Regex<model::Test>,
        cases_of: spec_fn(Item) -> Set<Case>, t: Trace, outcome: Outcome|
        satisfiable(d, g0) && #[trigger] initial_ok(q0, r, s)
            && trace_steps_ok(d, cases_of, t)
            && #[trigger] trace_wf(d, g0, q0, cases_of, t) && #[trigger] trace_outcome(t, outcome)
            ==> outcome_ok(d, g0, r, s, outcome)
}

/// Items reachable from `start` through successor cases, in `n` steps.
pub open spec fn reachable_item(cases_of: spec_fn(Item) -> Set<Case>, start: Item, n: nat, j: Item) -> bool
    decreases n,
{
    if n == 0 { j == start } else {
        exists|i: Item, c: Case| reachable_item(cases_of, start, (n - 1) as nat, i)
            && #[trigger] cases_of(i).contains(c) && case_item(c) == j
    }
}

/// Hypothesis of termination: finitely many items are reachable. It follows from finitely many
/// reachable states (`finiteness::stmt_items_from_states`): constraints are `Γ₀` plus literals
/// over the atoms of reachable states. For the paper's model normalizer the states are bounded by
/// Lemma Finitely many residuals (`lem:finite-states`); for the implementation by the same
/// lemma instantiated with `verify::finite_impl::m_impl` (`finiteness::theorem_impl_finitely_many_items`,
/// with the implemented step abstracted by `finiteness::lemma_impl_successor_abstracts`).
pub open spec fn items_within(cases_of: spec_fn(Item) -> Set<Case>, start: Item, f: Set<Item>) -> bool {
    forall|n: nat, j: Item| #[trigger] reachable_item(cases_of, start, n, j) ==> f.contains(j)
}

pub open spec fn finitely_many_items(cases_of: spec_fn(Item) -> Set<Case>, start: Item) -> bool {
    exists|f: Set<Item>| #[trigger] items_within(cases_of, start, f)
}

/// Every trace from `(Γ₀, q₀)` has at most `bound` nodes.
pub open spec fn traces_bounded(g0: Constraint, q0: Regex<model::Test>, cases_of: spec_fn(Item) -> Set<Case>, bound: nat) -> bool {
    forall|d: NDomains, t: Trace| #[trigger] trace_wf(d, g0, q0, cases_of, t) ==> t.nodes.len() <= bound
}

/// Theorem Inclusion search correctness (`thm:search`), termination, *conditional* on finitely many reachable items: no trace has more
/// than `bound` nodes (nodes are distinct reachable items), so the search returns after at most
/// `bound` expansions.
pub open spec fn stmt_search_terminates() -> bool {
    forall|g0: Constraint, q0: Regex<model::Test>, cases_of: spec_fn(Item) -> Set<Case>|
        #[trigger] finitely_many_items(cases_of, Item { constraint: g0, state: q0 })
            ==> exists|bound: nat| #[trigger] traces_bounded(g0, q0, cases_of, bound)
}

// ----- proofs -----

pub open spec fn induced_assignment(theta: Subst, e: EventView,
    atoms: Set<model::Primitive>) -> Assignment {
    Map::new(atoms, |p: model::Primitive| model::primitive_holds(theta, p, e))
}

pub proof fn lemma_induced_realizes(theta: Subst, e: EventView, atoms: Set<model::Primitive>)
    ensures induced_assignment(theta, e, atoms).dom() == atoms,
        realizes(theta, e, induced_assignment(theta, e, atoms)),
{}

pub proof fn lemma_realizes_unique(theta: Subst, e: EventView,
    atoms: Set<model::Primitive>, a: Assignment, b: Assignment)
    requires a.dom() == atoms, b.dom() == atoms, realizes(theta, e, a), realizes(theta, e, b),
    ensures a == b,
{
    assert(a =~= b);
}

pub proof fn lemma_paper_steps_finite(d: NDomains, item: Item, atoms: Set<model::Primitive>,
    cases_split: Set<Constraint>, next: spec_fn(Assignment) -> Regex<model::Test>)
    ensures paper_steps(d, item, atoms, cases_split, next).finite(),
{
    crate::verify::finite_states::lemma_powerset_finite(atoms);
    let pw = ISet::new(|s: Set<model::Primitive>| s.subset_of(atoms));
    let assignment = |s: Set<model::Primitive>| Map::new(atoms,
        |p: model::Primitive| s.contains(p));
    pw.lemma_map_finite(assignment);
    let assignments = pw.map(assignment);
    let maker = |g: Constraint| assignments.map(|a: Assignment|
        Case { constraint: g, alpha: a, next: next(a) });
    assert forall|g: Constraint| cases_split.contains(g) implies #[trigger] maker(g).finite() by {
        assignments.lemma_map_finite(|a: Assignment|
            Case { constraint: g, alpha: a, next: next(a) });
    }
    crate::verify::finite_states::lemma_big_union_finite(cases_split, maker);
    let bound = ISet::new(|c: Case| exists|g: Constraint|
        cases_split.contains(g) && #[trigger] maker(g).contains(c));
    assert forall|c: Case| paper_steps(d, item, atoms, cases_split, next).contains(c)
        implies bound.contains(c) by {
        let yes = atoms.filter(|p: model::Primitive| c.alpha[p]);
        assert(yes.subset_of(atoms));
        assert(assignment(yes) =~= c.alpha);
        assert(pw.contains(yes));
        assert(assignments.contains(c.alpha));
        assert(maker(c.constraint).contains(c));
    }
    vstd::iset_lib::lemma_iset_subset_finite(bound,
        paper_steps(d, item, atoms, cases_split, next));
}

pub proof fn lemma_node_reachable(d: NDomains, g0: Constraint, q0: Regex<model::Test>,
    cases_of: spec_fn(Item) -> Set<Case>, t: Trace, j: int)
    requires trace_wf(d, g0, q0, cases_of, t), 0 <= j < t.nodes.len(),
    ensures reachable_item(cases_of, Item { constraint: g0, state: q0 },
        t.nodes[j].depth, t.nodes[j].item),
    decreases j,
{
    if j > 0 {
        assert(parent_ok(cases_of, t, j));
        let (p, alpha) = t.nodes[j].parent.unwrap();
        let c = choose|c: Case| #[trigger] cases_of(t.nodes[p as int].item).contains(c)
            && c.alpha == alpha && t.nodes[j].item == case_item(c);
        lemma_node_reachable(d, g0, q0, cases_of, t, p as int);
        assert(reachable_item(cases_of, Item { constraint: g0, state: q0 },
            (t.nodes[j].depth - 1) as nat, t.nodes[p as int].item));
    }
}

pub proof fn lemma_chain_len(d: NDomains, g0: Constraint, q0: Regex<model::Test>,
    cases_of: spec_fn(Item) -> Set<Case>, t: Trace, j: int, fuel: nat)
    requires trace_wf(d, g0, q0, cases_of, t), 0 <= j < t.nodes.len(),
        fuel >= t.nodes[j].depth,
    ensures chain(t.nodes, j, fuel).len() == t.nodes[j].depth,
        chain(t.nodes, j, fuel) == chain(t.nodes, j, t.nodes[j].depth),
    decreases j,
{
    if j > 0 {
        assert(parent_ok(cases_of, t, j));
        let (p, alpha) = t.nodes[j].parent.unwrap();
        lemma_chain_len(d, g0, q0, cases_of, t, p as int, (fuel - 1) as nat);
        lemma_chain_len(d, g0, q0, cases_of, t, p as int,
            (t.nodes[j].depth - 1) as nat);
    }
}

pub proof fn lemma_trace_nodes_bounded(g0: Constraint, q0: Regex<model::Test>,
    cases_of: spec_fn(Item) -> Set<Case>, f: Set<Item>, d: NDomains, t: Trace)
    requires items_within(cases_of, Item { constraint: g0, state: q0 }, f),
        trace_wf(d, g0, q0, cases_of, t),
    ensures t.nodes.len() <= f.len(),
{
    let items = t.nodes.map(|i: int, n: Node| n.item);
    assert(items.no_duplicates()) by {
        assert forall|i: int, j: int| 0 <= i < items.len() && 0 <= j < items.len()
            && i != j implies items[i] != items[j] by {
            if i < j {
                assert(t.nodes[i].depth <= t.nodes[j].depth);
                assert(t.nodes[i].item != t.nodes[j].item);
            } else {
                assert(t.nodes[j].depth <= t.nodes[i].depth);
                assert(t.nodes[j].item != t.nodes[i].item);
            }
        }
    }
    assert forall|j: int| 0 <= j < items.len() implies f.contains(#[trigger] items[j]) by {
        lemma_node_reachable(d, g0, q0, cases_of, t, j);
    }
    crate::verify::finite_impl::lemma_nodup_len(items, f);
}

pub proof fn theorem_search_terminates()
    ensures stmt_search_terminates(),
{
    assert forall|g0: Constraint, q0: Regex<model::Test>,
        cases_of: spec_fn(Item) -> Set<Case>|
        #[trigger] finitely_many_items(cases_of, Item { constraint: g0, state: q0 })
        implies exists|bound: nat| #[trigger] traces_bounded(g0, q0, cases_of, bound) by {
        let f = choose|f: Set<Item>| #[trigger] items_within(cases_of,
            Item { constraint: g0, state: q0 }, f);
        assert(traces_bounded(g0, q0, cases_of, f.len())) by {
            assert forall|d: NDomains, t: Trace| #[trigger] trace_wf(d, g0, q0, cases_of, t)
                implies t.nodes.len() <= f.len() by {
                lemma_trace_nodes_bounded(g0, q0, cases_of, f, d, t);
            }
        }
    }
}

pub open spec fn atom_pair_image(p: model::Primitive) -> (Component, nat) {
    match p {
        model::Primitive::Eq(c, model::GTerm::Constant(v)) => (c, v),
        model::Primitive::Eq(c, model::GTerm::Variable(_)) => (c, 0),
    }
}

pub proof fn lemma_atom_pairs_members(atoms: Set<model::Primitive>)
    ensures forall|p: (Component, nat)| #[trigger] atom_pairs(atoms).contains(p)
        <==> (atoms.contains(model::Primitive::Eq(p.0, model::GTerm::Variable(p.0)))
            && atoms.contains(model::Primitive::Eq(p.0, model::GTerm::Constant(p.1)))),
{
    let image = |p: model::Primitive| atom_pair_image(p);
    let bound = atoms.to_iset().map(image);
    atoms.to_iset().lemma_map_finite(image);
    let f = |p: (Component, nat)|
        atoms.contains(model::Primitive::Eq(p.0, model::GTerm::Variable(p.0)))
        && atoms.contains(model::Primitive::Eq(p.0, model::GTerm::Constant(p.1)));
    assert forall|p: (Component, nat)| f(p) implies bound.contains(p) by {
        let a = model::Primitive::Eq(p.0, model::GTerm::Constant(p.1));
        assert(atom_pair_image(a) == p);
    }
    lemma_set_new_bounded(f, bound);
}

/// Finite union of the per-coordinate declared-domain pairs.
pub open spec fn domain_pair_bound(d: NDomains) -> ISet<(Component, nat)>
    decreases d.len(),
{
    if d.len() == 0 { ISet::empty() } else {
        let c = Component((d.len() - 1) as u8);
        domain_pair_bound(d.drop_last()).union(
            d.last().unwrap_or(Set::empty()).to_iset().map(|v: nat| (c, v)))
    }
}

pub proof fn lemma_domain_pair_bound(d: NDomains)
    ensures domain_pair_bound(d).finite(),
        forall|p: (Component, nat)| (n_domain(d, p.0) matches Some(values) && values.contains(p.1))
            ==> #[trigger] domain_pair_bound(d).contains(p),
    decreases d.len(),
{
    broadcast use vstd::set::lemma_to_iset_finite, vstd::iset::lemma_iset_union_finite;
    if d.len() > 0 {
        let prefix = d.drop_last();
        lemma_domain_pair_bound(prefix);
        let c = Component((d.len() - 1) as u8);
        let values = d.last().unwrap_or(Set::empty());
        values.to_iset().lemma_map_finite(|v: nat| (c, v));
        assert forall|p: (Component, nat)| (n_domain(d, p.0) matches Some(vs) && vs.contains(p.1))
            implies #[trigger] domain_pair_bound(d).contains(p) by {
            assert(p.0.0 < d.len());
            if p.0.0 < prefix.len() {
                assert(n_domain(prefix, p.0) == n_domain(d, p.0));
            } else {
                assert(p.0 == c);
                assert(n_domain(d, p.0) == d.last());
                assert(values.to_iset().map(|v: nat| (c, v)).contains(p));
            }
        }
    }
}

pub proof fn lemma_domain_pairs_members(d: NDomains, atoms: Set<model::Primitive>)
    ensures forall|p: (Component, nat)| #[trigger] domain_pairs(d, atoms).contains(p)
        <==> (atom_pairs(atoms).contains(p)
            || (atoms.contains(model::Primitive::Eq(p.0, model::GTerm::Variable(p.0)))
                && match n_domain(d, p.0) {
                    Some(values) => values.contains(p.1), None => false,
                })),
{
    broadcast use vstd::set::lemma_to_iset_finite, vstd::iset::lemma_iset_union_finite;
    lemma_domain_pair_bound(d);
    let bound = atom_pairs(atoms).to_iset().union(domain_pair_bound(d));
    let f = |p: (Component, nat)| atom_pairs(atoms).contains(p)
        || (atoms.contains(model::Primitive::Eq(p.0, model::GTerm::Variable(p.0)))
            && match n_domain(d, p.0) { Some(values) => values.contains(p.1), None => false });
    assert forall|p: (Component, nat)| f(p) implies bound.contains(p) by {
        if !atom_pairs(atoms).contains(p) {
            assert(domain_pair_bound(d).contains(p));
        }
    }
    lemma_set_new_bounded(f, bound);
}

pub proof fn lemma_decided_agreement(d: NDomains, g: Constraint, k: Component, v: nat,
    theta0: Subst, theta: Subst)
    requires decides(d, g, k, v), n_theta_ok(d, theta0), n_theta_ok(d, theta),
        sat_by(theta0, g), sat_by(theta, g),
    ensures (language::field_value(theta0, k) == v) == (language::field_value(theta, k) == v),
{
    let eq = eq_literal(k, v);
    let ne = ne_literal(k, v);
    if entails(d, g, set![eq]) {
        assert(sat_by(theta0, set![eq]));
        assert(sat_by(theta, set![eq]));
        assert(set![eq].contains(eq));
    } else {
        assert(sat_by(theta0, set![ne]));
        assert(sat_by(theta, set![ne]));
        assert(set![ne].contains(ne));
    }
}

pub proof fn lemma_finite_nat_bound(s: Set<nat>) -> (bound: nat)
    ensures forall|v: nat| #[trigger] s.contains(v) ==> v < bound,
    decreases s.len(),
{
    if s.len() == 0 {
        s.lemma_len0_is_empty();
        assert forall|v: nat| #[trigger] s.contains(v) implies v < 0nat by {}
        0
    } else {
        let x = s.choose();
        let b = lemma_finite_nat_bound(s.remove(x));
        assert forall|v: nat| #[trigger] s.contains(v) implies v < b + x + 1 by {
            if v != x { assert(s.remove(x).contains(v)); }
        }
        b + x + 1
    }
}

/// One coordinate of a realization transported to a different candidate valuation.
pub open spec fn field_realizes(d: NDomains, atoms: Set<model::Primitive>, alpha: Assignment,
    theta: Subst, e0: EventView, k: Component, v: nat) -> bool {
    &&& (n_domain(d, k) matches Some(values) ==> values.contains(v))
    &&& forall|p: model::Primitive| #[trigger] atoms.contains(p)
        && (p matches model::Primitive::Eq(c, _) && c == k)
        ==> alpha[p] == model::primitive_holds(theta, p, e0.update(k.0 as int, v))
}

pub proof fn lemma_transport_field(d: NDomains, atoms: Set<model::Primitive>, pi: Pairs,
    g: Constraint, alpha: Assignment, theta0: Subst, e0: EventView, theta: Subst,
    k: Component) -> (v: nat)
    requires atoms_local(atoms), alpha.dom() == atoms, k.0 < d.len(),
        pi == domain_pairs(d, atoms),
        forall|p: (Component, nat)| pi.contains(p) ==> #[trigger] decides(d, g, p.0, p.1),
        n_theta_ok(d, theta0), n_event_in(d, e0), sat_by(theta0, g), realizes(theta0, e0, alpha),
        n_theta_ok(d, theta), sat_by(theta, g),
    ensures field_realizes(d, atoms, alpha, theta, e0, k, v),
{
    lemma_atom_pairs_members(atoms);
    lemma_domain_pairs_members(d, atoms);
    let reg = model::Primitive::Eq(k, model::GTerm::Variable(k));
    let x0 = language::field_value(theta0, k);
    let x = language::field_value(theta, k);
    let old = language::field_value(e0, k);
    let v;
    if n_domain(d, k) is Some {
        if atoms.contains(reg) {
            let values = n_domain(d, k).unwrap();
            assert(values.contains(x0));
            assert(pi.contains((k, x0)));
            lemma_decided_agreement(d, g, k, x0, theta0, theta);
            assert(x == x0);
        }
        v = old;
    } else if atoms.contains(reg) && alpha[reg] {
        v = x;
    } else if exists|c: nat| atoms.contains(model::Primitive::Eq(k, model::GTerm::Constant(c)))
        && alpha[model::Primitive::Eq(k, model::GTerm::Constant(c))] {
        let c = choose|c: nat| atoms.contains(model::Primitive::Eq(k, model::GTerm::Constant(c)))
            && alpha[model::Primitive::Eq(k, model::GTerm::Constant(c))];
        assert(old == c);
        if atoms.contains(reg) {
            assert(pi.contains((k, c)));
            lemma_decided_agreement(d, g, k, c, theta0, theta);
            assert(x != c);
        }
        v = c;
    } else {
        let codes = atoms.map(|p: model::Primitive| atom_pair_image(p).1).insert(x);
        let bound = lemma_finite_nat_bound(codes);
        assert(codes.contains(x));
        assert(x < bound);
        v = bound;
        assert(v != x);
        assert forall|c: nat| atoms.contains(model::Primitive::Eq(k, model::GTerm::Constant(c)))
            implies v != c by {
            assert(codes.contains(c));
        }
    }
    let event = e0.update(k.0 as int, v);
    assert(language::field_value(event, k) == v);
    assert forall|p: model::Primitive| #[trigger] atoms.contains(p)
        && (p matches model::Primitive::Eq(c, _) && c == k)
        implies alpha[p] == model::primitive_holds(theta, p, event) by {
        match p {
            model::Primitive::Eq(c, model::GTerm::Variable(c2)) => {
                assert(c == k && c2 == k);
                assert(p == reg);
            },
            model::Primitive::Eq(c, model::GTerm::Constant(code)) => {
                assert(alpha[p] == (old == code));
                if n_domain(d, k) is None && atoms.contains(reg) && alpha[reg] {
                    assert(old == x0);
                    assert(pi.contains((k, code)));
                    lemma_decided_agreement(d, g, k, code, theta0, theta);
                }
            },
        }
    }
    v
}

pub proof fn lemma_transport_realizer(d: NDomains, item: Item, atoms: Set<model::Primitive>,
    pi: Pairs, cases_split: Set<Constraint>, c: Case, theta: Subst)
    requires atoms_local(atoms), atoms_bounded(atoms, d.len()),
        split_ok(d, item.constraint, pi, cases_split),
        pi == domain_pairs(d, atoms),
        cases_split.contains(c.constraint), c.alpha.dom() == atoms,
        exists|t0: Subst, e0: EventView| n_theta_ok(d, t0) && n_event_in(d, e0)
            && sat_by(t0, c.constraint) && realizes(t0, e0, c.alpha),
        n_theta_ok(d, theta), sat_by(theta, c.constraint),
    ensures exists|e: EventView| n_event_in(d, e) && #[trigger] realizes(theta, e, c.alpha),
{
    let (t0, e0) = choose|t0: Subst, e0: EventView| n_theta_ok(d, t0) && n_event_in(d, e0)
        && sat_by(t0, c.constraint) && realizes(t0, e0, c.alpha);
    let pick = |i: int| choose|v: nat|
        #[trigger] field_realizes(d, atoms, c.alpha, theta, e0, Component(i as u8), v);
    let e = Seq::new(d.len(), pick);
    assert forall|i: int| #![trigger e[i]] 0 <= i < d.len() implies
        field_realizes(d, atoms, c.alpha, theta, e0, Component(i as u8), e[i]) by {
        let k = Component(i as u8);
        assert(k.0 as int == i);
        let v = lemma_transport_field(d, atoms, pi, c.constraint, c.alpha, t0, e0, theta, k);
        assert(field_realizes(d, atoms, c.alpha, theta, e0, k, v));
        assert(exists|v: nat| #[trigger] field_realizes(d, atoms, c.alpha, theta, e0, k, v));
    }
    assert(n_event_in(d, e)) by {
        assert forall|i: int| #![trigger d[i], e[i]] 0 <= i < d.len() implies
            (d[i] matches Some(values) ==> values.contains(e[i])) by {
            let k = Component(i as u8);
            assert(k.0 as int == i);
            assert(field_realizes(d, atoms, c.alpha, theta, e0, k, e[i]));
        }
    }
    assert(realizes(theta, e, c.alpha)) by {
        assert forall|p: model::Primitive| #[trigger] c.alpha.dom().contains(p)
            implies c.alpha[p] == model::primitive_holds(theta, p, e) by {
            match p {
                model::Primitive::Eq(k, term) => {
                    assert(k.0 < d.len());
                    assert(field_realizes(d, atoms, c.alpha, theta, e0, k, e[k.0 as int]));
                    assert(c.alpha[p] == model::primitive_holds(theta, p,
                        e0.update(k.0 as int, e[k.0 as int])));
                },
            }
        }
    }
}

pub proof fn lemma_successor_cases_common(d: NDomains, item: Item,
    atoms: Set<model::Primitive>, pi: Pairs, cases_split: Set<Constraint>,
    next: spec_fn(Assignment) -> Regex<model::Test>)
    requires atoms_local(atoms), atoms_bounded(atoms, d.len()),
        split_ok(d, item.constraint, pi, cases_split),
        pi == domain_pairs(d, atoms),
        forall|alpha: Assignment| alpha.dom() == atoms
            ==> #[trigger] successor_ok(item.state, alpha, next(alpha)),
    ensures paper_steps(d, item, atoms, cases_split, next).finite(),
        steps_ok(d, item, finite_of(paper_steps(d, item, atoms, cases_split, next))),
{
    hide(language::numeric_lang);
    hide(successor_ok);
    hide(realizes);
    hide(n_theta_ok);
    hide(n_event_in);
    hide(atoms_local);
    hide(atom_pairs);
    hide(domain_pairs);
    hide(satisfiable);
    hide(entails);
    broadcast use vstd::set::lemma_set_new_from_iset;
    lemma_paper_steps_finite(d, item, atoms, cases_split, next);
    let cases = finite_of(paper_steps(d, item, atoms, cases_split, next));
    assert(cases.to_iset() == paper_steps(d, item, atoms, cases_split, next));
    assert forall|c: Case| #[trigger] cases.contains(c) implies {
        &&& satisfiable(d, c.constraint) && entails(d, c.constraint, item.constraint)
        &&& successor_ok(item.state, c.alpha, c.next)
        &&& forall|theta: Subst| n_theta_ok(d, theta) && #[trigger] sat_by(theta, c.constraint)
            ==> exists|e: EventView| n_event_in(d, e) && #[trigger] realizes(theta, e, c.alpha)
    } by {
        assert(paper_steps(d, item, atoms, cases_split, next).contains(c));
        assert forall|theta: Subst| n_theta_ok(d, theta) && #[trigger] sat_by(theta, c.constraint)
            implies exists|e: EventView| n_event_in(d, e) && #[trigger] realizes(theta, e, c.alpha) by {
            lemma_transport_realizer(d, item, atoms, pi, cases_split, c, theta);
        }
    }
    assert forall|theta: Subst, e: EventView| n_theta_ok(d, theta)
        && #[trigger] n_event_in(d, e) && #[trigger] sat_by(theta, item.constraint)
        implies exists|c: Case| #[trigger] cases.contains(c)
            && sat_by(theta, c.constraint) && realizes(theta, e, c.alpha) by {
        let g = choose|g: Constraint| #[trigger] cases_split.contains(g) && sat_by(theta, g);
        let alpha = induced_assignment(theta, e, atoms);
        lemma_induced_realizes(theta, e, atoms);
        let c = Case { constraint: g, alpha, next: next(alpha) };
        assert(paper_steps(d, item, atoms, cases_split, next).contains(c));
        assert(cases.contains(c));
    }
    assert forall|theta: Subst, e: EventView, c1: Case, c2: Case| n_theta_ok(d, theta)
        && cases.contains(c1) && cases.contains(c2) && #[trigger] sat_by(theta, c1.constraint)
        && #[trigger] sat_by(theta, c2.constraint) && #[trigger] realizes(theta, e, c1.alpha)
        && realizes(theta, e, c2.alpha) implies c1 == c2 by {
        assert(paper_steps(d, item, atoms, cases_split, next).contains(c1));
        assert(paper_steps(d, item, atoms, cases_split, next).contains(c2));
        assert(c1.constraint == c2.constraint);
        lemma_realizes_unique(theta, e, atoms, c1.alpha, c2.alpha);
    }
}

pub proof fn theorem_successor_cases()
    ensures stmt_successor_cases(),
{
    hide(language::numeric_lang);
    hide(successor_ok);
    hide(atoms_complete);
    hide(steps_ok);
    hide(paper_steps);
    assert forall|d: NDomains, item: Item, atoms: Set<model::Primitive>,
        cases_split: Set<Constraint>, next: spec_fn(Assignment) -> Regex<model::Test>|
        satisfiable(d, item.constraint) && atoms_local(atoms) && atoms_complete(item.state, atoms)
        && atoms_bounded(atoms, d.len())
        && split_ok(d, item.constraint, domain_pairs(d, atoms), cases_split)
        && (forall|alpha: Assignment| alpha.dom() == atoms
            ==> #[trigger] successor_ok(item.state, alpha, next(alpha)))
        implies #[trigger] paper_steps(d, item, atoms, cases_split, next).finite()
            && steps_ok(d, item, finite_of(paper_steps(d, item, atoms, cases_split, next))) by {
        lemma_successor_cases_common(d, item, atoms, domain_pairs(d, atoms), cases_split, next);
    }
}

/// Only expanded nodes need complete cases; an implementation may retain their ghost evidence.
pub open spec fn trace_steps_ok(d: NDomains, cases_of: spec_fn(Item) -> Set<Case>,
    t: Trace) -> bool {
    forall|p: int| 0 <= p < t.expanded ==> #[trigger] steps_ok(d, t.nodes[p].item,
        cases_of(t.nodes[p].item))
}

pub proof fn lemma_follows_push(d: NDomains, letters: Seq<Assignment>, theta: Subst,
    u: Seq<EventView>, alpha: Assignment, e: EventView)
    requires follows(d, letters, theta, u), n_event_in(d, e), realizes(theta, e, alpha),
    ensures follows(d, letters.push(alpha), theta, u.push(e)),
{
    assert(n_history_in(d, u.push(e))) by {
        assert forall|i: int| 0 <= i < u.push(e).len()
            implies #[trigger] n_event_in(d, u.push(e)[i]) by {
            if i < u.len() { assert(u.push(e)[i] == u[i]); }
        }
    }
    assert forall|i: int| 0 <= i < u.push(e).len()
        implies #[trigger] realizes(theta, u.push(e)[i], letters.push(alpha)[i]) by {
        if i < u.len() { assert(u.push(e)[i] == u[i]); }
    }
}

pub proof fn lemma_follows_unpush(d: NDomains, letters: Seq<Assignment>, theta: Subst,
    u: Seq<EventView>, alpha: Assignment)
    requires follows(d, letters.push(alpha), theta, u),
    ensures follows(d, letters, theta, u.drop_last()), n_event_in(d, u.last()),
        realizes(theta, u.last(), alpha), u.drop_last().push(u.last()) == u,
{
    assert(u.len() > 0);
    assert(u.drop_last().push(u.last()) =~= u);
    assert(n_history_in(d, u.drop_last())) by {
        assert forall|i: int| 0 <= i < u.drop_last().len()
            implies #[trigger] n_event_in(d, u.drop_last()[i]) by {
            assert(u.drop_last()[i] == u[i]);
        }
    }
    assert forall|i: int| 0 <= i < u.drop_last().len()
        implies #[trigger] realizes(theta, u.drop_last()[i], letters[i]) by {
        assert(u.drop_last()[i] == u[i]);
        assert(letters.push(alpha)[i] == letters[i]);
    }
    assert(realizes(theta, u[u.len() - 1], letters.push(alpha)[letters.len() as int]));
}

pub proof fn lemma_node_realizable(d: NDomains, g0: Constraint, q0: Regex<model::Test>,
    cases_of: spec_fn(Item) -> Set<Case>, t: Trace, j: int)
    requires satisfiable(d, g0), trace_steps_ok(d, cases_of, t),
        trace_wf(d, g0, q0, cases_of, t), 0 <= j < t.nodes.len(),
    ensures entails(d, t.nodes[j].item.constraint, g0),
        satisfiable(d, t.nodes[j].item.constraint),
        forall|theta: Subst| n_theta_ok(d, theta) && sat_by(theta, t.nodes[j].item.constraint)
            ==> exists|u: Seq<EventView>| #[trigger] follows(d,
                chain(t.nodes, j, t.nodes[j].depth), theta, u),
    decreases j,
{
    hide(language::numeric_lang);
    hide(realizes);
    hide(successor_ok);
    hide(follows);
    hide(n_history_in);
    hide(n_event_in);
    hide(n_theta_ok);
    hide(satisfiable);
    hide(entails);
    hide(sat_by);
    lemma_chain_len(d, g0, q0, cases_of, t, j, t.nodes[j].depth);
    if j == 0 {
        assert(chain(t.nodes, j, t.nodes[j].depth) == Seq::<Assignment>::empty());
        assert(entails(d, g0, g0)) by { reveal(entails); }
        assert forall|theta: Subst| n_theta_ok(d, theta) && sat_by(theta, g0)
            implies exists|u: Seq<EventView>| #[trigger] follows(d,
                chain(t.nodes, j, t.nodes[j].depth), theta, u) by {
            assert(follows(d, Seq::empty(), theta, Seq::empty())) by {
                reveal(follows);
                reveal(n_history_in);
            }
        }
    } else {
        assert(parent_ok(cases_of, t, j));
        let (p, alpha) = t.nodes[j].parent.unwrap();
        let c = choose|c: Case| #[trigger] cases_of(t.nodes[p as int].item).contains(c)
            && c.alpha == alpha && t.nodes[j].item == case_item(c);
        assert(steps_ok(d, t.nodes[p as int].item, cases_of(t.nodes[p as int].item)));
        lemma_node_realizable(d, g0, q0, cases_of, t, p as int);
        lemma_entails_trans(d, c.constraint, t.nodes[p as int].item.constraint, g0);
        lemma_chain_len(d, g0, q0, cases_of, t, p as int,
            (t.nodes[j].depth - 1) as nat);
        let prefix = chain(t.nodes, p as int, t.nodes[p as int].depth);
        assert(chain(t.nodes, j, t.nodes[j].depth) == prefix.push(alpha));
        assert forall|theta: Subst| n_theta_ok(d, theta) && sat_by(theta, c.constraint)
            implies exists|u: Seq<EventView>| #[trigger] follows(d,
                chain(t.nodes, j, t.nodes[j].depth), theta, u) by {
            assert(sat_by(theta, t.nodes[p as int].item.constraint)) by { reveal(entails); }
            let u = choose|u: Seq<EventView>| #[trigger] follows(d, prefix, theta, u);
            let e = choose|e: EventView| n_event_in(d, e) && #[trigger] realizes(theta, e, c.alpha);
            lemma_follows_push(d, prefix, theta, u, alpha, e);
        }
    }
}

// Keep the suffix explicit to avoid recursively generating larger SMT language terms.
pub proof fn lemma_node_language(d: NDomains, g0: Constraint, q0: Regex<model::Test>,
    cases_of: spec_fn(Item) -> Set<Case>, t: Trace, j: int, theta: Subst,
    u: Seq<EventView>, w: Seq<EventView>)
    requires trace_steps_ok(d, cases_of, t), trace_wf(d, g0, q0, cases_of, t),
        0 <= j < t.nodes.len(), n_theta_ok(d, theta), sat_by(theta, t.nodes[j].item.constraint),
        follows(d, chain(t.nodes, j, t.nodes[j].depth), theta, u),
    ensures n_lang(theta, t.nodes[j].item.state, w) == n_lang(theta, q0, u + w),
    decreases j,
{
    hide(language::numeric_lang);
    hide(realizes);
    hide(successor_ok);
    hide(follows);
    hide(n_history_in);
    hide(n_event_in);
    hide(n_theta_ok);
    hide(satisfiable);
    hide(entails);
    hide(sat_by);
    lemma_chain_len(d, g0, q0, cases_of, t, j, t.nodes[j].depth);
    if j == 0 {
        assert(u =~= Seq::<EventView>::empty()) by { reveal(follows); }
        assert(u + w =~= w);
    } else {
        assert(parent_ok(cases_of, t, j));
        let (p, alpha) = t.nodes[j].parent.unwrap();
        let c = choose|c: Case| #[trigger] cases_of(t.nodes[p as int].item).contains(c)
            && c.alpha == alpha && t.nodes[j].item == case_item(c);
        assert(steps_ok(d, t.nodes[p as int].item, cases_of(t.nodes[p as int].item)));
        lemma_chain_len(d, g0, q0, cases_of, t, p as int,
            (t.nodes[j].depth - 1) as nat);
        let prefix = chain(t.nodes, p as int, t.nodes[p as int].depth);
        assert(chain(t.nodes, j, t.nodes[j].depth) == prefix.push(alpha));
        lemma_follows_unpush(d, prefix, theta, u, alpha);
        assert(sat_by(theta, t.nodes[p as int].item.constraint)) by { reveal(entails); }
        let e = u.last();
        let before = u.drop_last();
        assert(successor_ok(t.nodes[p as int].item.state, c.alpha, c.next));
        assert(n_lang(theta, c.next, w)
            == n_lang(theta, t.nodes[p as int].item.state, seq![e] + w)) by {
            reveal(successor_ok);
            reveal(n_theta_ok);
        }
        lemma_node_language(d, g0, q0, cases_of, t, p as int, theta, before, seq![e] + w);
        assert(before + (seq![e] + w) =~= u + w);
    }
}

pub proof fn lemma_node_semantics(d: NDomains, g0: Constraint, q0: Regex<model::Test>,
    cases_of: spec_fn(Item) -> Set<Case>, t: Trace, j: int)
    requires satisfiable(d, g0), trace_steps_ok(d, cases_of, t),
        trace_wf(d, g0, q0, cases_of, t), 0 <= j < t.nodes.len(),
    ensures entails(d, t.nodes[j].item.constraint, g0),
        satisfiable(d, t.nodes[j].item.constraint),
        forall|theta: Subst| n_theta_ok(d, theta) && sat_by(theta, t.nodes[j].item.constraint)
            ==> exists|u: Seq<EventView>| #[trigger] follows(d,
                chain(t.nodes, j, t.nodes[j].depth), theta, u),
        forall|theta: Subst, u: Seq<EventView>, w: Seq<EventView>|
            n_theta_ok(d, theta) && sat_by(theta, t.nodes[j].item.constraint)
            && #[trigger] follows(d, chain(t.nodes, j, t.nodes[j].depth), theta, u)
            ==> #[trigger] n_lang(theta, t.nodes[j].item.state, w) == n_lang(theta, q0, u + w),
{
    hide(language::numeric_lang);
    hide(follows);
    hide(n_theta_ok);
    hide(sat_by);
    hide(entails);
    hide(satisfiable);
    hide(successor_ok);
    lemma_node_realizable(d, g0, q0, cases_of, t, j);
    assert forall|theta: Subst, u: Seq<EventView>, w: Seq<EventView>|
        n_theta_ok(d, theta) && sat_by(theta, t.nodes[j].item.constraint)
        && #[trigger] follows(d, chain(t.nodes, j, t.nodes[j].depth), theta, u)
        implies #[trigger] n_lang(theta, t.nodes[j].item.state, w) == n_lang(theta, q0, u + w) by {
        lemma_node_language(d, g0, q0, cases_of, t, j, theta, u, w);
    }
}

pub proof fn lemma_no_witness_below(d: NDomains, g0: Constraint, q0: Regex<model::Test>,
    cases_of: spec_fn(Item) -> Set<Case>, t: Trace, j: int, theta: Subst, w: Seq<EventView>)
    requires trace_steps_ok(d, cases_of, t), trace_wf(d, g0, q0, cases_of, t),
        0 <= j < t.nodes.len(), witness(d, t.nodes[j].item, theta, w),
        forall|k: int| #![trigger t.nodes[k]] 0 <= k < t.nodes.len()
            && t.nodes[k].depth <= t.nodes[j].depth + w.len() ==> k < t.expanded,
    ensures false,
    decreases w.len(),
{
    hide(language::numeric_lang);
    hide(successor_ok);
    hide(realizes);
    hide(n_theta_ok);
    hide(n_event_in);
    hide(n_history_in);
    hide(sat_by);
    hide(entails);
    hide(satisfiable);
    assert(t.nodes[j].depth <= t.nodes[j].depth + w.len());
    assert(j < t.expanded);
    assert(!nullable_state(t.nodes[j].item.state));
    if w.len() == 0 {
        assert(w =~= Seq::<EventView>::empty());
        language::lemma_nullable_iff_nil(model::gsem(theta), t.nodes[j].item.state);
    } else {
        assert(steps_ok(d, t.nodes[j].item, cases_of(t.nodes[j].item)));
        let e = w[0];
        let tail = w.drop_first();
        assert(w =~= seq![e] + tail);
        assert(n_event_in(d, e)) by { reveal(n_history_in); }
        let c = choose|c: Case| #[trigger] cases_of(t.nodes[j].item).contains(c)
            && sat_by(theta, c.constraint) && realizes(theta, e, c.alpha);
        assert(n_lang(theta, c.next, tail)) by {
            reveal(successor_ok);
            reveal(n_theta_ok);
            assert(successor_ok(t.nodes[j].item.state, c.alpha, c.next));
        }
        assert(n_history_in(d, tail)) by {
            reveal(n_history_in);
            assert forall|i: int| 0 <= i < tail.len()
                implies #[trigger] n_event_in(d, tail[i]) by { assert(tail[i] == w[i + 1]); }
        }
        assert(witness(d, case_item(c), theta, tail));
        if exists|k: int| 0 < k < t.nodes.len()
            && t.nodes[k].parent == Some((j as nat, c.alpha)) && t.nodes[k].item == case_item(c) {
            let k = choose|k: int| 0 < k < t.nodes.len()
                && t.nodes[k].parent == Some((j as nat, c.alpha))
                && t.nodes[k].item == case_item(c);
            assert(parent_ok(cases_of, t, k));
            assert(t.nodes[k].depth == t.nodes[j].depth + 1);
            lemma_no_witness_below(d, g0, q0, cases_of, t, k, theta, tail);
        } else {
            assert(may_discard(d, t.nodes, case_item(c), t.nodes[j].depth + 1));
            if c.next == Regex::<model::Test>::Empty {
                reveal(language::numeric_lang);
            } else if no_witness(d, case_item(c)) {
                assert(!witness(d, case_item(c), theta, tail));
            } else {
                let k = choose|k: int| 0 <= k < t.nodes.len()
                    && t.nodes[k].depth <= t.nodes[j].depth + 1
                    && #[trigger] witnesses_within(d, case_item(c), t.nodes[k].item);
                assert(witness(d, t.nodes[k].item, theta, tail));
                assert forall|h: int| #![trigger t.nodes[h]] 0 <= h < t.nodes.len()
                    && t.nodes[h].depth <= t.nodes[k].depth + tail.len()
                    implies h < t.expanded by {
                    assert(t.nodes[h].depth <= t.nodes[j].depth + w.len());
                }
                lemma_no_witness_below(d, g0, q0, cases_of, t, k, theta, tail);
            }
        }
    }
}

pub proof fn lemma_search_correct(d: NDomains, g0: Constraint, r: Regex<model::Test>,
    s: Regex<model::Test>, q0: Regex<model::Test>, cases_of: spec_fn(Item) -> Set<Case>,
    t: Trace, outcome: Outcome)
    requires satisfiable(d, g0), initial_ok(q0, r, s), trace_steps_ok(d, cases_of, t),
        trace_wf(d, g0, q0, cases_of, t), trace_outcome(t, outcome),
    ensures outcome_ok(d, g0, r, s, outcome),
{
    hide(language::numeric_lang);
    match outcome {
        Outcome::Exhausted => {},
        Outcome::Holds => {
            assert forall|theta: Subst, w: Seq<EventView>| n_theta_ok(d, theta)
                && n_history_in(d, w) && sat_by(theta, g0) && #[trigger] n_lang(theta, r, w)
                implies n_lang(theta, s, w) by {
                if !n_lang(theta, s, w) {
                    let root = Item { constraint: g0, state: q0 };
                    assert(witness(d, root, theta, w));
                    if t.nodes.len() > 0 {
                        lemma_no_witness_below(d, g0, q0, cases_of, t, 0, theta, w);
                    } else {
                        assert(may_discard(d, t.nodes, root, 0));
                        if q0 == Regex::<model::Test>::Empty { reveal(language::numeric_lang); }
                        else { assert(no_witness(d, root)); }
                    }
                }
            }
        },
        Outcome::Refuted(g, letters) => {
            let j = t.expanded as int;
            lemma_node_realizable(d, g0, q0, cases_of, t, j);
            lemma_chain_len(d, g0, q0, cases_of, t, j, t.nodes[j].depth);
            assert(letters.len() == t.nodes[j].depth);
            assert forall|theta: Subst, u: Seq<EventView>| n_theta_ok(d, theta)
                && sat_by(theta, g) && #[trigger] follows(d, letters, theta, u)
                implies inclusion_cex(d, g0, r, s, theta, u) by {
                language::lemma_nullable_iff_nil(model::gsem(theta), t.nodes[j].item.state);
                assert(n_lang(theta, t.nodes[j].item.state, Seq::empty()));
                lemma_node_language(d, g0, q0, cases_of, t, j, theta, u, Seq::empty());
                assert(u + Seq::<EventView>::empty() =~= u);
                assert(n_lang(theta, q0, u));
                assert(sat_by(theta, g0));
            }
            assert(no_cex_shorter(d, g0, r, s, letters.len())) by {
                assert forall|theta: Subst, w: Seq<EventView>| w.len() < letters.len()
                    implies !#[trigger] inclusion_cex(d, g0, r, s, theta, w) by {
                    if inclusion_cex(d, g0, r, s, theta, w) {
                        assert(witness(d, t.nodes[0].item, theta, w));
                        assert forall|k: int| #![trigger t.nodes[k]] 0 <= k < t.nodes.len()
                            && t.nodes[k].depth <= t.nodes[0].depth + w.len()
                            implies k < t.expanded by {
                            if k >= j {
                                if k > j { assert(t.nodes[j].depth <= t.nodes[k].depth); }
                                assert(false);
                            }
                        }
                        lemma_no_witness_below(d, g0, q0, cases_of, t, 0, theta, w);
                    }
                }
            }
        },
    }
}

pub proof fn theorem_search_correct()
    ensures stmt_search_correct(),
{
    assert forall|d: NDomains, g0: Constraint, r: Regex<model::Test>, s: Regex<model::Test>,
        q0: Regex<model::Test>, cases_of: spec_fn(Item) -> Set<Case>, t: Trace, outcome: Outcome|
        satisfiable(d, g0) && #[trigger] initial_ok(q0, r, s)
        && trace_steps_ok(d, cases_of, t)
        && #[trigger] trace_wf(d, g0, q0, cases_of, t) && #[trigger] trace_outcome(t, outcome)
        implies outcome_ok(d, g0, r, s, outcome) by {
        lemma_search_correct(d, g0, r, s, q0, cases_of, t, outcome);
    }
}

} // verus!
