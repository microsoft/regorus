//! Layer 5: finitely many states (Lemma Finitely many residuals, `lem:finite-states`;
//! appendix `app:finiteness`), and finitely many items. `stmt_search_terminates` stays
//! conditional on `finitely_many_items`; this layer discharges that hypothesis for the
//! implementation's search (`theorem_impl_finitely_many_items`).
//!
//! The abstract development is `verify::finite_states` (`Model<S>`, `theorem_finite_reachable`),
//! proved against the contract `Model::contract` and the invariant `Model::good`. Their conjuncts
//! carry the code's numbers (N0)–(N5), (S0)–(S6), (C1)–(C4); the paper's appendix `app:finiteness`
//! outlines the construction informally and calls `C(q)` `Bound(q)`. The names, once, for both:
//!
//! | Code | Name | `Model` predicate | Meaning |
//! |---|---|---|---|
//! | (N0) | normal-form constants and substates | `constants_ok`, `substates_ok`, `fixpoints_ok` | `∅`, `ε`, `Univ` are the only states of their kinds; operands, bodies and list elements are smaller states, list elements atoms; `N(¬·)`/`N(·⋯·)` fix a complement/list state |
//! | (N1), (N2) | normalized union/intersection shape | `nset_ok` | an output of `N(ΣX)`/`N(&X)` is a constant or has operands drawn from the flattened operands of `X` or test combinations of them; finitely many such states over a finite operand set |
//! | (N3) | complement shape | `not_ok` | `N(¬x)` is a constant, the body of `x`, or `¬x` |
//! | (N4) | concatenation flattening | `cat_ok` | `N(x₁⋯xₖ)` absorbs `∅`, flattens, drops `ε`, returns `ε`, a single factor or the list of factors |
//! | (N5) | finite test closure | `tests_ok` | finitely many tests are reachable by `∨`/`∧` combination from a finite test set |
//! | (S0) | successors are unions of products | `succ_shape` (`built` case) | `∂(p)` evaluates to a normalized union of products of `p` |
//! | (S1) | base states are constant | `succ_shape`, `lit_shape`, `prod_shape` (`base_kind` case) | constants and tests have constant successors, literals and products |
//! | (S2) | union step | `lit_shape`/`prod_shape` (`Union` case) | literals are normalized unions of operand literals; a product is an operand's product or a literal |
//! | (S3) | intersection step | `lit_shape`/`prod_shape` (`Intersect` case) | normalized intersections of operand literals |
//! | (S4) | complement step | `lit_shape`/`prod_shape` (`Not` case) | literals are normalized intersections of complemented body literals; products normalized intersections of literals |
//! | (S5) | star step | `lit_shape`/`prod_shape` (`Star` case) | `N(v p)` for products `v` of the body |
//! | (S6) | list step | `lit_shape`/`prod_shape` (`List` case) | `N(v yᵢ₊₁⋯yₖ)` for products `v` of a non-final element, or literals/products of the final element |
//! | (C1) | finite, rooted, with constants | `good` (first two conjuncts) | `r` is finite, contains `q`, `∅`, `ε`, `Univ` |
//! | (C2) | closed under values | `vals_into(r, r)` | successors, literals and products of members stay in `r` |
//! | (C3) | closed under operands | `r_ops` | operands of set states and bodies of complements stay in `r` |
//! | (C4) | closed under list tails | `r_lists_in(r, r)` | `N(v yᵢ₊₁⋯yₖ)` for every list member and product `v` of its elements stays in `r` |
//!
//! The canonical-state abstraction maps a graph
//! id to its lifted tree `model::lift_regex(g, id)`: within one well-formed graph, interning makes
//! the lift injective, and graph extension preserves it (`model::lemma_lift_stable_under_extends`),
//! so identity of ids in the search's visited set is identity of abstract states.
//!
//! STATUS: every statement of
//! this module is proved (`theorem_lift_injective`, `theorem_reachable_states_finite`,
//! `theorem_items_from_states`). The implementation's model is `verify::finite_impl::m_impl`
//! (hereditary normal forms; `nset` relational and `lit`/`prod`/`succ` the largest relations
//! allowed by (S0)–(S6)); `theorem_impl_contract` proves its contract, and
//! `verify::finite_link` proves that the implemented regex constructors are its constructors on
//! lifted normal forms. `theorem_impl_finitely_many_items` gives `finitely_many_items` for every
//! search whose cases follow `m_impl` steps (`cases_follow`) and add literals only over atoms
//! (`cases_from_atoms`). The implemented step is abstracted: `RegexId::derivative` ensures the
//! class bound `verify::finite_deriv::dbound` of its transition, `TransitionId::interpret` and
//! `CompiledPair::successor` ensure that the successor is a value of that transition
//! (`finite_trans::tval`, `verify::finite_interp::entry_val`), and
//! `lemma_impl_successor_abstracts` / `lemma_impl_step_same` (guard cache) turn these into
//! `step_abstracts(m_impl(), ..)`; compiled tails are normal forms (`CompiledPair::compile`,
//! `theorem_impl_instantiation`). The remaining link, `cases_follow(m_impl, ·)` for the
//! analyzer's `cases_of`, is the invariant `archive_follows` of the executed search
//! (`history-analysis/src/verify/search_exec.rs`).
use super::encoding::*;
use super::inclusion::*;
use super::search::*;
use crate::verify::finite_states::{
    Model, lemma_big_union_finite, lemma_powerset_finite, reachable, theorem_finite_reachable,
};
use history_syntax::syntax::Component;
use junco_core::kernel::verify as model;
use junco_core::verify::history_specs::Regex;
use vstd::iset_lib::lemma_iset_subset_finite;
use vstd::prelude::*;

verus! {

/// Abstract state of a graph regex id.
pub open spec fn abs_state(g: model::Graph, id: nat) -> Regex<model::Test> {
    model::lift_regex(g, id)
}

/// Interning makes the abstraction injective on a well-formed graph.
pub open spec fn stmt_lift_injective() -> bool {
    forall|g: model::Graph, i: nat, j: nat| model::graph_wf(g) && i < g.regexes.len() && j < g.regexes.len()
        && #[trigger] abs_state(g, i) == #[trigger] abs_state(g, j) ==> i == j
}

/// The implemented step, as seen by the abstraction: the successor of `q` returned in graph
/// `after` is a model successor of `q`, or `q` itself (the guard cache returns the residual
/// unchanged, `progress.rs` `guard_wf`).
pub open spec fn step_abstracts(m: Model<Regex<model::Test>>, before: model::Graph, q: nat, after: model::Graph, v: nat) -> bool {
    (m.succ)(abs_state(before, q), abs_state(after, v)) || abs_state(after, v) == abs_state(before, q)
}

/// The instantiation obligation: a model whose states include the lifted normalized
/// tails, whose successor relation covers every implemented step, and which satisfies the
/// contract. With it, `theorem_finite_reachable` bounds the implementation's reachable states.
/// Its definition fixes the instantiation (states: hereditary normal form of lifted
/// trees; `nset` relational; `lit`/`prod`/`succ` the largest relations allowed by (S0)–(S6)).
pub open spec fn instantiation_ok(m: Model<Regex<model::Test>>, states_of_tails: spec_fn(Regex<model::Test>) -> bool) -> bool {
    &&& m.contract()
    &&& forall|q: Regex<model::Test>| #[trigger] states_of_tails(q) ==> m.st(q)
}

/// With the instantiation, every state reachable from a normalized tail lies in a finite set
/// independent of valuations and events (`theorem_finite_reachable`, already proved for any
/// model satisfying the contract).
pub open spec fn stmt_reachable_states_finite() -> bool {
    forall|m: Model<Regex<model::Test>>, q0: Regex<model::Test>| m.contract() && m.st(q0)
        ==> exists|f: Set<Regex<model::Test>>| #[trigger] bounds_reachable(m, q0, f)
}

pub open spec fn bounds_reachable(m: Model<Regex<model::Test>>, q0: Regex<model::Test>, f: Set<Regex<model::Test>>) -> bool {
    forall|n: nat, p: Regex<model::Test>| #[trigger] reachable(m, q0, n, p) ==> f.contains(p)
}

// ----- finitely many items -----

/// The codes compared by an atom set at component `c`.
pub open spec fn atom_codes(atoms: Set<model::Primitive>) -> ISet<nat> {
    ISet::new(|v: nat| exists|c: history_syntax::syntax::Component| #[trigger] atoms.contains(model::Primitive::Eq(c, model::GTerm::Constant(v))))
}

/// Each successor case only adds literals about codes compared by the atoms of the parent's
/// state, or about declared finite-domain values (`split` and `letters` in `history-analysis/src/constraint.rs`).
pub open spec fn cases_from_atoms(d: NDomains, cases_of: spec_fn(Item) -> Set<Case>,
    atoms_of: spec_fn(Regex<model::Test>) -> Set<model::Primitive>) -> bool {
    forall|i: Item, c: Case, l: Literal| #[trigger] cases_of(i).contains(c) && #[trigger] c.constraint.contains(l)
        ==> i.constraint.contains(l) || atom_codes(atoms_of(i.state)).contains(l.value)
            || match n_domain(d, l.component) { Some(values) => values.contains(l.value), None => false }
}

pub open spec fn states_within(cases_of: spec_fn(Item) -> Set<Case>, start: Item, f: Set<Regex<model::Test>>) -> bool {
    forall|n: nat, j: Item| #[trigger] reachable_item(cases_of, start, n, j) ==> f.contains(j.state)
}

/// Finitely many states give finitely many items (proof of Theorem Inclusion search correctness, `thm:search`).
pub open spec fn stmt_items_from_states() -> bool {
    forall|d: NDomains, cases_of: spec_fn(Item) -> Set<Case>, atoms_of: spec_fn(Regex<model::Test>) -> Set<model::Primitive>,
        start: Item, f: Set<Regex<model::Test>>|
        #[trigger] cases_from_atoms(d, cases_of, atoms_of) && #[trigger] states_within(cases_of, start, f)
            ==> finitely_many_items(cases_of, start)
}

// ===== proofs =====

/// Lifting tests is injective on a well-formed graph (unique nodes, children below parents).
pub proof fn lemma_lift_test_injective(g: model::Graph, i: nat, j: nat)
    requires model::graph_wf(g), i < g.tests.len(), j < g.tests.len(), model::lift_test(g, i) == model::lift_test(g, j),
    ensures i == j,
    decreases i + j, 1nat,
{
    model::lemma_graph_wf_elim(g);
    model::lemma_graph_test_wf(g, i);
    model::lemma_graph_test_wf(g, j);
    let ni = g.tests[i as int];
    let nj = g.tests[j as int];
    match ni {
        model::TestNode::And(a) => {
            if let model::TestNode::And(b) = nj {
                lemma_lift_tests_injective(g, a, i, b, j);
            }
        },
        model::TestNode::Or(a) => {
            if let model::TestNode::Or(b) = nj {
                lemma_lift_tests_injective(g, a, i, b, j);
            }
        },
        _ => {},
    }
    assert(ni == nj);
    if i != j {
        assert(g.tests.no_duplicates());
        assert(g.tests[i as int] != g.tests[j as int]);
    }
}

pub proof fn lemma_lift_tests_injective(g: model::Graph, a: Seq<nat>, i: nat, b: Seq<nat>, j: nat)
    requires model::graph_wf(g), i < g.tests.len(), j < g.tests.len(),
        model::bounded(a, i), model::bounded(b, j),
        model::lift_tests(g, a, i) == model::lift_tests(g, b, j),
    ensures a == b,
    decreases i + j, 0nat,
{
    let la = model::lift_tests(g, a, i);
    let lb = model::lift_tests(g, b, j);
    assert(la.len() == a.len() && lb.len() == b.len());
    assert forall|k: int| 0 <= k < a.len() implies a[k] == b[k] by {
        assert(la[k] == lb[k]);
        assert(a[k] < i);
        assert(b[k] < j);
        lemma_lift_test_injective(g, a[k], b[k]);
    }
    assert(a =~= b);
}

/// Lifting regexes is injective on a well-formed graph.
pub proof fn lemma_lift_regex_injective(g: model::Graph, i: nat, j: nat)
    requires model::graph_wf(g), i < g.regexes.len(), j < g.regexes.len(), model::lift_regex(g, i) == model::lift_regex(g, j),
    ensures i == j,
    decreases i + j, 1nat,
{
    model::lemma_graph_wf_elim(g);
    model::lemma_graph_regex_wf(g, i);
    model::lemma_graph_regex_wf(g, j);
    let ni = g.regexes[i as int];
    let nj = g.regexes[j as int];
    assert(model::lift_regex(g, i) == model::lift_regex_kind_bounded(g, ni.kind, i));
    assert(model::lift_regex(g, j) == model::lift_regex_kind_bounded(g, nj.kind, j));
    match ni.kind {
        model::RegexKindNode::Test(a) => {
            if let model::RegexKindNode::Test(b) = nj.kind {
                lemma_lift_test_injective(g, a, b);
            }
        },
        model::RegexKindNode::Union(a) => {
            if let model::RegexKindNode::Union(b) = nj.kind {
                lemma_lift_regexes_injective(g, a, i, b, j);
            }
        },
        model::RegexKindNode::Intersect(a) => {
            if let model::RegexKindNode::Intersect(b) = nj.kind {
                lemma_lift_regexes_injective(g, a, i, b, j);
            }
        },
        model::RegexKindNode::Concat(a) => {
            if let model::RegexKindNode::Concat(b) = nj.kind {
                lemma_lift_regexes_injective(g, a, i, b, j);
            }
        },
        model::RegexKindNode::Star(a) => {
            if let model::RegexKindNode::Star(b) = nj.kind {
                lemma_lift_regex_injective(g, a, b);
            }
        },
        model::RegexKindNode::Not(a) => {
            if let model::RegexKindNode::Not(b) = nj.kind {
                lemma_lift_regex_injective(g, a, b);
            }
        },
        _ => {},
    }
    assert(ni.kind == nj.kind);
    assert(ni == nj);
    if i != j {
        assert(g.regexes.no_duplicates());
        assert(g.regexes[i as int] != g.regexes[j as int]);
    }
}

pub proof fn lemma_lift_regexes_injective(g: model::Graph, a: Seq<nat>, i: nat, b: Seq<nat>, j: nat)
    requires model::graph_wf(g), i < g.regexes.len(), j < g.regexes.len(),
        model::bounded(a, i), model::bounded(b, j),
        model::lift_regexes_bounded(g, a, i) == model::lift_regexes_bounded(g, b, j),
    ensures a == b,
    decreases i + j, 0nat,
{
    let la = model::lift_regexes_bounded(g, a, i);
    let lb = model::lift_regexes_bounded(g, b, j);
    assert(la.len() == a.len() && lb.len() == b.len());
    assert forall|k: int| 0 <= k < a.len() implies a[k] == b[k] by {
        assert(la[k] == lb[k]);
        assert(a[k] < i);
        assert(b[k] < j);
        lemma_lift_regex_injective(g, a[k], b[k]);
    }
    assert(a =~= b);
}

pub proof fn theorem_lift_injective()
    ensures stmt_lift_injective(),
{
    assert forall|g: model::Graph, i: nat, j: nat| model::graph_wf(g) && i < g.regexes.len() && j < g.regexes.len()
        && #[trigger] abs_state(g, i) == #[trigger] abs_state(g, j) implies i == j by {
        lemma_lift_regex_injective(g, i, j);
    }
}

pub proof fn theorem_reachable_states_finite()
    ensures stmt_reachable_states_finite(),
{
    assert forall|m: Model<Regex<model::Test>>, q0: Regex<model::Test>| m.contract() && m.st(q0)
        implies exists|f: Set<Regex<model::Test>>| #[trigger] bounds_reachable(m, q0, f) by {
        let f = theorem_finite_reachable(m, q0);
        assert(bounds_reachable(m, q0, f));
    }
}

/// Codes that may appear in the literals of items whose states lie in `f`.
pub open spec fn item_codes(d: NDomains, atoms_of: spec_fn(Regex<model::Test>) -> Set<model::Primitive>,
    f: Set<Regex<model::Test>>) -> ISet<nat> {
    ISet::new(|v: nat| (exists|s: Regex<model::Test>| f.contains(s) && #[trigger] atom_codes(atoms_of(s)).contains(v))
        || (exists|c: Component| #[trigger] n_domain(d, c) matches Some(values) && values.contains(v)))
}

/// Literals over the codes of `item_codes`.
pub open spec fn item_literals(d: NDomains, atoms_of: spec_fn(Regex<model::Test>) -> Set<model::Primitive>,
    f: Set<Regex<model::Test>>) -> ISet<Literal> {
    ISet::new(|l: Literal| item_codes(d, atoms_of, f).contains(l.value))
}

pub open spec fn primitive_code(p: model::Primitive) -> nat {
    match p { model::Primitive::Eq(_, model::GTerm::Constant(v)) => v, _ => 0 }
}

pub proof fn lemma_atom_codes_finite(atoms: Set<model::Primitive>)
    ensures atom_codes(atoms).finite(),
{
    broadcast use vstd::set::lemma_to_iset_finite;
    let img = atoms.to_iset().map(|p: model::Primitive| primitive_code(p));
    atoms.to_iset().lemma_map_finite(|p: model::Primitive| primitive_code(p));
    assert forall|v: nat| atom_codes(atoms).contains(v) implies img.contains(v) by {
        let c = choose|c: Component| #[trigger] atoms.contains(model::Primitive::Eq(c, model::GTerm::Constant(v)));
        let p = model::Primitive::Eq(c, model::GTerm::Constant(v));
        assert(atoms.to_iset().contains(p));
        assert(primitive_code(p) == v);
    }
    lemma_iset_subset_finite(img, atom_codes(atoms));
}

pub open spec fn domain_values(d: NDomains) -> ISet<nat> {
    ISet::new(|v: nat| exists|c: Component| #[trigger] n_domain(d, c) matches Some(values) && values.contains(v))
}

pub open spec fn option_values(o: Option<Set<nat>>) -> ISet<nat> {
    match o { Some(values) => values.to_iset(), None => ISet::<nat>::empty() }
}

/// Union of every declared coordinate domain, folded over the policy's arity.
pub open spec fn domain_values_fold(d: NDomains) -> ISet<nat>
    decreases d.len(),
{
    if d.len() == 0 { ISet::empty() }
    else { domain_values_fold(d.drop_last()).union(option_values(d.last())) }
}

pub proof fn lemma_domain_values_fold(d: NDomains)
    ensures domain_values_fold(d).finite(),
        forall|i: int, v: nat| 0 <= i < d.len() && #[trigger] option_values(d[i]).contains(v)
            ==> domain_values_fold(d).contains(v),
    decreases d.len(),
{
    broadcast use vstd::set::lemma_to_iset_finite, vstd::iset::lemma_iset_empty_finite,
        vstd::iset::lemma_iset_union_finite;
    if d.len() > 0 {
        lemma_domain_values_fold(d.drop_last());
        assert(option_values(d.last()).finite());
        assert forall|i: int, v: nat| 0 <= i < d.len() && #[trigger] option_values(d[i]).contains(v)
            implies domain_values_fold(d).contains(v) by {
            if i < d.len() - 1 {
                assert(d.drop_last()[i] == d[i]);
            } else {
                assert(d[i] == d.last());
            }
        }
    }
}

pub proof fn lemma_domain_values_finite(d: NDomains)
    ensures domain_values(d).finite(),
{
    lemma_domain_values_fold(d);
    assert forall|v: nat| domain_values(d).contains(v) implies domain_values_fold(d).contains(v) by {
        let c = choose|c: Component| #[trigger] n_domain(d, c) matches Some(values) && values.contains(v);
        assert(c.0 < d.len());
        assert(option_values(d[c.0 as int]).contains(v));
    }
    lemma_iset_subset_finite(domain_values_fold(d), domain_values(d));
}

pub open spec fn literal_maker(codes: ISet<nat>) -> spec_fn((Component, bool)) -> ISet<Literal> {
    |cb: (Component, bool)| codes.map(|v: nat| Literal { component: cb.0, value: v, equal: cb.1 })
}

pub proof fn lemma_item_literals_finite(d: NDomains, atoms_of: spec_fn(Regex<model::Test>) -> Set<model::Primitive>,
    f: Set<Regex<model::Test>>)
    ensures item_literals(d, atoms_of, f).finite(),
{
    broadcast use vstd::iset::lemma_iset_union_finite;
    let codes = item_codes(d, atoms_of, f);
    let pick = |s: Regex<model::Test>| atom_codes(atoms_of(s));
    assert forall|s: Regex<model::Test>| f.contains(s) implies #[trigger] pick(s).finite() by {
        lemma_atom_codes_finite(atoms_of(s));
    }
    lemma_big_union_finite(f, pick);
    let ac = ISet::new(|v: nat| exists|s: Regex<model::Test>| f.contains(s) && #[trigger] pick(s).contains(v));
    lemma_domain_values_finite(d);
    let dv = domain_values(d);
    assert forall|v: nat| codes.contains(v) implies ac.union(dv).contains(v) by {
        if exists|s: Regex<model::Test>| f.contains(s) && #[trigger] atom_codes(atoms_of(s)).contains(v) {
            let s = choose|s: Regex<model::Test>| f.contains(s) && #[trigger] atom_codes(atoms_of(s)).contains(v);
            assert(pick(s).contains(v));
        } else {
            assert(dv.contains(v));
        }
    }
    lemma_iset_subset_finite(ac.union(dv), codes);
    let mk = literal_maker(codes);
    // Components are byte-sized indices. Bounding all representable indices also bounds
    // malformed literals, so termination needs no extra well-formedness assumption.
    let coordinates = Seq::new((u8::MAX as nat) + 1, |i: int| Component(i as u8));
    let coords = coordinates.to_set();
    let yes = |c: Component| (c, true);
    let no = |c: Component| (c, false);
    let idx = coords.map(yes).union(coords.map(no));
    assert forall|cb: (Component, bool)| idx.contains(cb) implies #[trigger] mk(cb).finite() by {
        codes.lemma_map_finite(|v: nat| Literal { component: cb.0, value: v, equal: cb.1 });
    }
    lemma_big_union_finite(idx, mk);
    let all = ISet::new(|l: Literal| exists|cb: (Component, bool)| idx.contains(cb) && #[trigger] mk(cb).contains(l));
    assert forall|l: Literal| item_literals(d, atoms_of, f).contains(l) implies all.contains(l) by {
        let cb = (l.component, l.equal);
        assert(idx.contains(cb)) by {
            assert(coordinates[l.component.0 as int] == l.component);
            assert(coords.contains(l.component));
            if l.equal { assert(coords.map(yes).contains(cb)); }
            else { assert(coords.map(no).contains(cb)); }
        }
        assert(codes.contains(l.value));
        assert(Literal { component: cb.0, value: l.value, equal: cb.1 } == l);
        assert(mk(cb).contains(l));
    }
    lemma_iset_subset_finite(all, item_literals(d, atoms_of, f));
}

/// Reachable items have states in `f` and constraints made of `Γ₀` and literals over the codes
/// of the atoms of states in `f` or of the declared domains.
pub proof fn lemma_reachable_item_shape(d: NDomains, cases_of: spec_fn(Item) -> Set<Case>,
    atoms_of: spec_fn(Regex<model::Test>) -> Set<model::Primitive>, start: Item, f: Set<Regex<model::Test>>, n: nat, j: Item)
    requires cases_from_atoms(d, cases_of, atoms_of), states_within(cases_of, start, f), reachable_item(cases_of, start, n, j),
    ensures f.contains(j.state),
        forall|l: Literal| #[trigger] j.constraint.contains(l) ==> start.constraint.contains(l) || item_literals(d, atoms_of, f).contains(l),
    decreases n,
{
    if n > 0 {
        let (i, c) = choose|i: Item, c: Case| reachable_item(cases_of, start, (n - 1) as nat, i)
            && #[trigger] cases_of(i).contains(c) && case_item(c) == j;
        lemma_reachable_item_shape(d, cases_of, atoms_of, start, f, (n - 1) as nat, i);
        assert forall|l: Literal| #[trigger] j.constraint.contains(l)
            implies start.constraint.contains(l) || item_literals(d, atoms_of, f).contains(l) by {
            assert(c.constraint.contains(l));
            if !i.constraint.contains(l) {
                if atom_codes(atoms_of(i.state)).contains(l.value) {
                    assert(item_codes(d, atoms_of, f).contains(l.value));
                } else {
                    assert(n_domain(d, l.component) matches Some(values) && values.contains(l.value));
                    assert(item_codes(d, atoms_of, f).contains(l.value));
                }
            }
        }
    }
}

pub open spec fn item_maker(pw: ISet<Set<Literal>>) -> spec_fn(Regex<model::Test>) -> ISet<Item> {
    |s: Regex<model::Test>| pw.map(|g: Set<Literal>| Item { constraint: g, state: s })
}

/// The items over the states `f`: constraints are `Γ₀` plus literals over the atoms of `f` or
/// over the declared domains. The set does not depend on `cases_of`, so it bounds every search
/// whose cases add only such literals and whose states stay within `f`.
pub proof fn lemma_items_bound(d: NDomains, atoms_of: spec_fn(Regex<model::Test>) -> Set<model::Primitive>,
    start: Item, f: Set<Regex<model::Test>>) -> (items: Set<Item>)
    ensures forall|cases_of: spec_fn(Item) -> Set<Case>|
        cases_from_atoms(d, cases_of, atoms_of) && states_within(cases_of, start, f)
            ==> #[trigger] items_within(cases_of, start, items),
{
    broadcast use vstd::set::lemma_to_iset_finite, vstd::set::lemma_set_new_from_iset, vstd::iset::lemma_iset_union_finite;
    lemma_item_literals_finite(d, atoms_of, f);
    let lits_i = start.constraint.to_iset().union(item_literals(d, atoms_of, f));
    let lits = Set::new_from_iset(lits_i).unwrap();
    assert(lits.to_iset() == lits_i);
    lemma_powerset_finite(lits);
    let pw = ISet::new(|s: Set<Literal>| s.subset_of(lits));
    let mk = item_maker(pw);
    assert forall|s: Regex<model::Test>| f.contains(s) implies #[trigger] mk(s).finite() by {
        pw.lemma_map_finite(|g: Set<Literal>| Item { constraint: g, state: s });
    }
    lemma_big_union_finite(f, mk);
    let items_i = ISet::new(|x: Item| exists|s: Regex<model::Test>| f.contains(s) && #[trigger] mk(s).contains(x));
    let items = Set::new_from_iset(items_i).unwrap();
    assert(items.to_iset() == items_i);
    assert forall|cases_of: spec_fn(Item) -> Set<Case>|
        cases_from_atoms(d, cases_of, atoms_of) && states_within(cases_of, start, f)
            implies #[trigger] items_within(cases_of, start, items) by {
        assert forall|n: nat, j: Item| #[trigger] reachable_item(cases_of, start, n, j) implies items.contains(j) by {
            lemma_reachable_item_shape(d, cases_of, atoms_of, start, f, n, j);
            assert(j.constraint.subset_of(lits)) by {
                assert forall|l: Literal| j.constraint.contains(l) implies lits.contains(l) by {
                    if start.constraint.contains(l) { assert(start.constraint.to_iset().contains(l)); }
                    assert(lits_i.contains(l));
                }
            }
            assert(pw.contains(j.constraint));
            assert(Item { constraint: j.constraint, state: j.state } == j);
            assert(mk(j.state).contains(j));
            assert(items_i.contains(j));
        }
    }
    items
}

pub proof fn lemma_items_from_states(d: NDomains, cases_of: spec_fn(Item) -> Set<Case>,
    atoms_of: spec_fn(Regex<model::Test>) -> Set<model::Primitive>, start: Item, f: Set<Regex<model::Test>>)
    requires cases_from_atoms(d, cases_of, atoms_of), states_within(cases_of, start, f),
    ensures finitely_many_items(cases_of, start),
{
    let items = lemma_items_bound(d, atoms_of, start, f);
    assert(items_within(cases_of, start, items));
}

pub proof fn theorem_items_from_states()
    ensures stmt_items_from_states(),
{
    assert forall|d: NDomains, cases_of: spec_fn(Item) -> Set<Case>, atoms_of: spec_fn(Regex<model::Test>) -> Set<model::Primitive>,
        start: Item, f: Set<Regex<model::Test>>|
        #[trigger] cases_from_atoms(d, cases_of, atoms_of) && #[trigger] states_within(cases_of, start, f)
        implies finitely_many_items(cases_of, start) by {
        lemma_items_from_states(d, cases_of, atoms_of, start, f);
    }
}

// ===== finitely many items for a model of the successor =====

/// Every case of a search item whose state is a model state moves to a model successor of the
/// state, or keeps the state (the guard cache, `step_abstracts`).
pub open spec fn cases_follow(m: Model<Regex<model::Test>>, cases_of: spec_fn(Item) -> Set<Case>) -> bool {
    forall|i: Item, c: Case| m.st(i.state) && #[trigger] cases_of(i).contains(c)
        ==> (m.succ)(i.state, c.next) || c.next == i.state
}

pub proof fn lemma_cases_follow_states(m: Model<Regex<model::Test>>, cases_of: spec_fn(Item) -> Set<Case>, start: Item,
    r: Set<Regex<model::Test>>, n: nat, j: Item)
    requires cases_follow(m, cases_of), r.contains(start.state), forall|p: Regex<model::Test>| r.contains(p) ==> m.st(p),
        forall|p: Regex<model::Test>, v: Regex<model::Test>| r.contains(p) && #[trigger] (m.succ)(p, v) ==> r.contains(v),
        reachable_item(cases_of, start, n, j),
    ensures r.contains(j.state),
    decreases n,
{
    if n > 0 {
        let (i, c) = choose|i: Item, c: Case| reachable_item(cases_of, start, (n - 1) as nat, i)
            && #[trigger] cases_of(i).contains(c) && case_item(c) == j;
        lemma_cases_follow_states(m, cases_of, start, r, (n - 1) as nat, i);
        assert(m.st(i.state));
    }
}

/// A bound on the items of every search whose cases follow a model satisfying the contract: the
/// items over the states reachable in the model (Lemma Finitely many residuals, `lem:finite-states`, lifted to items). It is fixed by the model, the start
/// item and the domains alone, before any case is computed.
pub proof fn lemma_model_items_bound(m: Model<Regex<model::Test>>, d: NDomains,
    atoms_of: spec_fn(Regex<model::Test>) -> Set<model::Primitive>, start: Item) -> (items: Set<Item>)
    requires m.contract(), m.st(start.state),
    ensures forall|cases_of: spec_fn(Item) -> Set<Case>|
        cases_follow(m, cases_of) && cases_from_atoms(d, cases_of, atoms_of)
            ==> #[trigger] items_within(cases_of, start, items),
{
    let r = theorem_finite_reachable(m, start.state);
    let items = lemma_items_bound(d, atoms_of, start, r);
    assert forall|cases_of: spec_fn(Item) -> Set<Case>|
        cases_follow(m, cases_of) && cases_from_atoms(d, cases_of, atoms_of)
            implies #[trigger] items_within(cases_of, start, items) by {
        assert(states_within(cases_of, start, r)) by {
            assert forall|n: nat, j: Item| #[trigger] reachable_item(cases_of, start, n, j) implies r.contains(j.state) by {
                lemma_cases_follow_states(m, cases_of, start, r, n, j);
            }
        }
    }
    items
}

/// Finitely many items for any search over a model satisfying the contract (Lemma Finitely
/// many residuals `lem:finite-states`, lifted to items as in the proof of `thm:search`): the start state is a model state, each case follows a model step
/// (or keeps the state), and each case adds only literals over the atoms of its parent's state or
/// over the declared domains.
pub proof fn theorem_model_finitely_many_items(m: Model<Regex<model::Test>>, d: NDomains,
    cases_of: spec_fn(Item) -> Set<Case>, atoms_of: spec_fn(Regex<model::Test>) -> Set<model::Primitive>, start: Item)
    requires m.contract(), m.st(start.state), cases_follow(m, cases_of), cases_from_atoms(d, cases_of, atoms_of),
    ensures finitely_many_items(cases_of, start),
{
    let items = lemma_model_items_bound(m, d, atoms_of, start);
    assert(items_within(cases_of, start, items));
}

/// Finitely many items for the implementation's model `m_impl` (`verify::finite_impl`): the
/// start state is a hereditary normal form (every lifted graph state produced by the normalizer
/// is, `verify::finite_link`), and every case moves along an implemented step, which
/// `step_abstracts` into `m_impl` (or keeps the state, the guard cache).
pub proof fn theorem_impl_finitely_many_items(d: NDomains, cases_of: spec_fn(Item) -> Set<Case>,
    atoms_of: spec_fn(Regex<model::Test>) -> Set<model::Primitive>, start: Item)
    requires
        crate::verify::finite_impl::regex_nf(start.state),
        cases_follow(crate::verify::finite_impl::m_impl(), cases_of),
        cases_from_atoms(d, cases_of, atoms_of),
    ensures finitely_many_items(cases_of, start),
{
    crate::verify::finite_impl::theorem_impl_contract();
    theorem_model_finitely_many_items(crate::verify::finite_impl::m_impl(), d, cases_of, atoms_of, start);
}

/// `lemma_model_items_bound` for the implementation's model `m_impl`: one item set, fixed before
/// the search starts, contains every item of every search whose cases follow implemented steps.
pub proof fn theorem_impl_items_bound(d: NDomains,
    atoms_of: spec_fn(Regex<model::Test>) -> Set<model::Primitive>, start: Item) -> (items: Set<Item>)
    requires crate::verify::finite_impl::regex_nf(start.state),
    ensures forall|cases_of: spec_fn(Item) -> Set<Case>|
        cases_follow(crate::verify::finite_impl::m_impl(), cases_of) && cases_from_atoms(d, cases_of, atoms_of)
            ==> #[trigger] items_within(cases_of, start, items),
{
    crate::verify::finite_impl::theorem_impl_contract();
    lemma_model_items_bound(crate::verify::finite_impl::m_impl(), d, atoms_of, start)
}

// ===== the implemented step abstracts into `m_impl` =====

/// The instantiation obligation for the implementation: `m_impl` satisfies the contract and its
/// states are the hereditary normal forms, which include every compiled tail
/// (`CompiledPair::compile` ensures `regex_nf` of its lifted root, `verify::finite_compile`).
pub proof fn theorem_impl_instantiation()
    ensures instantiation_ok(crate::verify::finite_impl::m_impl(), |q: Regex<model::Test>| crate::verify::finite_impl::regex_nf(q)),
{
    crate::verify::finite_impl::theorem_impl_contract();
}

/// A derivative `t` with the class bound of `q` (`finite_trans::dclass`, built in `before`) and
/// a value `v` of `t` (`finite_trans::tval`, read in the later graph `after`) form an `m_impl`
/// step.
pub proof fn lemma_impl_step_abstracts(before: model::Graph, q: nat, t: nat, after: model::Graph, v: nat)
    requires model::graph_wf(before), model::graph_extends(before, after), q < before.regexes.len(),
        crate::verify::finite_impl::regex_nf(abs_state(before, q)),
        crate::verify::finite_trans::dclass(before, t, abs_state(before, q)),
        crate::verify::finite_trans::tval(after, t, abs_state(after, v)),
    ensures step_abstracts(crate::verify::finite_impl::m_impl(), before, q, after, v),
{
    use crate::verify::finite_trans::*;
    let p = abs_state(before, q);
    model::lemma_graph_wf_elim(before);
    lemma_trans_stable(before, after, t);
    assert(dclass(after, t, p)) by {
        assert forall|w: Regex<model::Test>| #[trigger] tcls(after, t, w) implies
            (crate::verify::finite_impl::m_impl().lit)(p, w) && (crate::verify::finite_impl::m_impl().prod)(p, w) by {
            assert(tcls(before, t, w));
        }
        if crate::verify::finite_impl::m_impl().base_kind(p) {
            assert forall|w: Regex<model::Test>| #[trigger] ycls(after, t, w) implies rconst(w) by {
                assert(ycls(before, t, w));
            }
        }
    }
    lemma_succ_from_class(after, t, p, abs_state(after, v));
    model::lemma_lift_regex_stable(before, after, q);
}

/// The guard cache returns the residual unchanged: also a step in the sense of `step_abstracts`.
pub proof fn lemma_impl_step_same(before: model::Graph, q: nat, after: model::Graph)
    requires model::graph_wf(before), model::graph_extends(before, after), q < before.regexes.len(),
    ensures step_abstracts(crate::verify::finite_impl::m_impl(), before, q, after, q),
{
    model::lemma_graph_wf_elim(before);
    model::lemma_lift_regex_stable(before, after, q);
}

/// The implemented successor of a normal-form state: `RegexId::derivative` ensures
/// `finite_deriv::dbound(before, q, t)` for its result `t`, and `CompiledPair::successor` ensures
/// `finite_interp::entry_val(after, t, v)` for the successor `v` it returns (cached or freshly
/// interpreted); `fold`'s guard-cache path keeps `v = q` ([`lemma_impl_step_same`]).
pub proof fn lemma_impl_successor_abstracts(before: model::Graph, q: nat, t: nat, after: model::Graph, v: nat)
    requires model::graph_wf(before), model::graph_extends(before, after), q < before.regexes.len(),
        crate::verify::finite_impl::regex_nf(abs_state(before, q)),
        crate::verify::finite_deriv::dbound(before, q, t),
        crate::verify::finite_interp::entry_val(after, t, v),
    ensures step_abstracts(crate::verify::finite_impl::m_impl(), before, q, after, v),
{
    reveal(crate::verify::finite_deriv::dbound);
    let p = abs_state(before, q);
    assert(crate::verify::finite_trans::nf_sum(before, t));
    crate::verify::finite_trans::lemma_trans_stable(before, after, t);
    crate::verify::finite_interp::lemma_entry_val_elim(after, t, v);
    lemma_impl_step_abstracts(before, q, t, after, v);
}

} // verus!
