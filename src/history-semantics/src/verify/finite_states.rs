//! Finiteness of normalized derivative states (paper Lemma `lem:finite-states`, appendix `app:finiteness`).
//!
//! The development is abstract: a [`Model`] packages a set of states, their shapes, the
//! normalizing constructors `N(ΣX)`, `N(&X)`, `N(¬p)`, `N(p₁⋯pₖ)`, the test combination of
//! (N1)/(N2), and the implemented successor `p ↦ ∂p`, the evaluation of the *normalized* symbolic
//! derivative, over *all* valuations and events. Transition normalization distributes
//! concatenation and intersection over unions and conditionals, pushes complements inward, and
//! merges leaves, so evaluating a normalized transition selects a union of *products*, each an
//! intersection of *literals*. `lit(p, v)` and `prod(p, v)` hold when `v` is the value of a literal
//! or of a product of the transition of `p` under some valuation and event.
//!
//! [`Model::contract`] states (N0)–(N5) and the successor equations (S0)–(S6). These numbers, the
//! invariants (C1)–(C4) and the set `C(q)` are this development's; the paper's appendix
//! `app:finiteness` outlines the construction informally and calls `C(q)` `Bound(q)`. The table in
//! `refinement/finiteness.rs` names each condition and its predicate below. Under the
//! contract, [`lemma_finite_states`] builds `C(q)` and [`theorem_finite_reachable`] bounds every
//! state reachable from a state. [`lemma_uset_nset`] is the union-closure step, [`lemma_uset_closed`]
//! and [`lemma_dnf_closed`] are the successor-closure step, and [`lemma_cat_assoc`] is (N4′).
//! [`lemma_contract_satisfiable`] shows the contract is consistent.
//!
//! The implemented constructors establish (N1)–(N4) and the shape of (N5) in their postconditions
//! (`regex_set_shape`, `regex_not_result`, `regex_concat_result`, `test_connective_result` in
//! `normalize::verify`), and interning gives the (N0) fixpoints (`regex_kind_unique`,
//! `regex_not_fixpoint`, `regex_concat_fixpoint`).
use vstd::iset_lib::lemma_iset_subset_finite;
use vstd::prelude::*;
use vstd::set_lib::{lemma_int_range, lemma_set_empty_equivalency_len, set_int_range};

verus! {

/// Head of a state.
pub enum Kind { Empty, Epsilon, Universal, Test, Union, Intersect, Not, Star, List }

/// Abstract normalizer, states, and successors.
///
/// `nset(false, X, u)` holds when `u` is an output of `N(ΣX)` and `nset(true, X, u)` when it is
/// an output of `N(&X)`; the output is a relation because the implementation orders operands by
/// interning order, so the lifted tree depends on the graph. `combo(false, T, t)` holds when
/// the test `t` is obtained by combining the tests `T` with `∨` (`∧` for `true`). For some
/// valuation `θ` and event `e`, `succ(p, v)` holds when `v = ∂(p)_θ(e)`, and `lit(p, v)` and
/// `prod(p, v)` when `v` is the value of a literal or of a product of the evaluated normalized
/// transition of `p`.
#[verifier::reject_recursive_types(S)]
pub struct Model<S> {
    pub state: spec_fn(S) -> bool,
    pub kind: spec_fn(S) -> Kind,
    pub ops: spec_fn(S) -> Set<S>,
    pub body: spec_fn(S) -> S,
    pub elems: spec_fn(S) -> Seq<S>,
    pub size: spec_fn(S) -> nat,
    pub empty: S,
    pub epsilon: S,
    pub universal: S,
    pub nset: spec_fn(bool, Set<S>, S) -> bool,
    pub nnot: spec_fn(S) -> S,
    pub ncat: spec_fn(Seq<S>) -> S,
    pub combo: spec_fn(bool, Set<S>, S) -> bool,
    pub succ: spec_fn(S, S) -> bool,
    pub lit: spec_fn(S, S) -> bool,
    pub prod: spec_fn(S, S) -> bool,
}

pub open spec fn set_kind(inter: bool) -> Kind {
    if inter { Kind::Intersect } else { Kind::Union }
}

impl<S> Model<S> {
    pub open spec fn st(self, x: S) -> bool { (self.state)(x) }

    pub open spec fn k(self, x: S) -> Kind { (self.kind)(x) }

    /// `N(x y)`.
    pub open spec fn cat2(self, x: S, y: S) -> S { (self.ncat)(seq![x, y]) }

    pub open spec fn is_set(self, inter: bool, x: S) -> bool { self.k(x) == set_kind(inter) }

    pub open spec fn is_const(self, x: S) -> bool {
        x == self.empty || x == self.epsilon || x == self.universal
    }

    pub open spec fn is_test(self, x: S) -> bool { self.st(x) && self.k(x) == Kind::Test }

    /// Constants and tests.
    pub open spec fn base_kind(self, x: S) -> bool {
        self.k(x) == Kind::Empty || self.k(x) == Kind::Epsilon || self.k(x) == Kind::Universal
            || self.k(x) == Kind::Test
    }

    /// Union (`inter == false`) or intersection operands of a state; a state of another kind is
    /// its own only operand.
    pub open spec fn sops(self, inter: bool, x: S) -> Set<S> {
        if self.is_set(inter, x) { (self.ops)(x) } else { set![x] }
    }

    /// `o ∈ ops₊(X)` (resp. `ops_&(X)`).
    pub open spec fn in_sops_of(self, inter: bool, xs: Set<S>, o: S) -> bool {
        exists|x: S| xs.contains(x) && #[trigger] self.sops(inter, x).contains(o)
    }

    /// A possible list element: neither a concatenation, nor `ε`, nor `∅`.
    pub open spec fn atom(self, x: S) -> bool {
        self.st(x) && self.k(x) != Kind::List && x != self.epsilon && x != self.empty
    }

    pub open spec fn states(self, xs: Seq<S>) -> bool {
        forall|i: int| 0 <= i < xs.len() ==> self.st(#[trigger] xs[i])
    }

    pub open spec fn atoms(self, xs: Seq<S>) -> bool {
        forall|i: int| 0 <= i < xs.len() ==> self.atom(#[trigger] xs[i])
    }

    /// Contribution of one factor to a flattened concatenation.
    pub open spec fn piece(self, x: S) -> Seq<S> {
        if self.k(x) == Kind::List { (self.elems)(x) } else if x == self.epsilon { seq![] } else { seq![x] }
    }

    pub open spec fn flat(self, xs: Seq<S>) -> Seq<S>
        decreases xs.len(),
    {
        if xs.len() == 0 { seq![] } else { self.flat(xs.drop_last()) + self.piece(xs.last()) }
    }

    pub open spec fn has_empty(self, xs: Seq<S>) -> bool {
        exists|i: int| 0 <= i < xs.len() && xs[i] == self.empty
    }

    // ----- (N0)–(N5) -----

    /// (N0) constants.
    pub open spec fn constants_ok(self) -> bool {
        &&& self.st(self.empty) && self.k(self.empty) == Kind::Empty
        &&& self.st(self.epsilon) && self.k(self.epsilon) == Kind::Epsilon
        &&& self.st(self.universal) && self.k(self.universal) == Kind::Universal
        &&& forall|x: S| self.st(x) && #[trigger] self.k(x) == Kind::Empty ==> x == self.empty
        &&& forall|x: S| self.st(x) && #[trigger] self.k(x) == Kind::Epsilon ==> x == self.epsilon
        &&& forall|x: S| self.st(x) && #[trigger] self.k(x) == Kind::Universal ==> x == self.universal
    }

    /// (N0) sub-nodes of states are smaller states; list elements are atoms.
    pub open spec fn substates_ok(self) -> bool {
        &&& forall|x: S, o: S| self.st(x) && (self.k(x) == Kind::Union || self.k(x) == Kind::Intersect)
            && #[trigger] (self.ops)(x).contains(o) ==> self.st(o) && (self.size)(o) < (self.size)(x)
        &&& forall|x: S| self.st(x) && (self.k(x) == Kind::Not || self.k(x) == Kind::Star)
            ==> self.st(#[trigger] (self.body)(x)) && (self.size)((self.body)(x)) < (self.size)(x)
        &&& forall|x: S| self.st(x) && self.k(x) == Kind::List ==> {
            let es = #[trigger] (self.elems)(x);
            es.len() >= 2 && forall|i: int| 0 <= i < es.len()
                ==> self.atom(#[trigger] es[i]) && (self.size)(es[i]) < (self.size)(x)
        }
    }

    /// (N0) constructors applied to the parts of a list or complement state return it unchanged.
    pub open spec fn fixpoints_ok(self) -> bool {
        &&& forall|x: S| self.st(x) && self.k(x) == Kind::List ==> (self.ncat)(#[trigger] (self.elems)(x)) == x
        &&& forall|x: S| self.st(x) && self.k(x) == Kind::Not ==> (self.nnot)(#[trigger] (self.body)(x)) == x
    }

    /// `o` combines tests `ts` drawn from `ops₊(X)` (resp. `ops_&(X)`).
    pub open spec fn combo_from(self, inter: bool, xs: Set<S>, ts: Set<S>, o: S) -> bool {
        &&& forall|t: S| ts.contains(t) ==> self.is_test(t) && self.in_sops_of(inter, xs, t)
        &&& (self.combo)(inter, ts, o)
    }

    /// (N1)/(N2) for one operand set and one output `u`.
    pub open spec fn nset_shape(self, inter: bool, xs: Set<S>, u: S) -> bool {
        &&& self.st(u)
        &&& self.is_const(u) || forall|o: S| #[trigger] self.sops(inter, u).contains(o) ==>
            self.in_sops_of(inter, xs, o)
            || (self.is_test(o) && exists|ts: Set<S>| #[trigger] self.combo_from(inter, xs, ts, o))
    }

    /// The set `g` contains every union (`inter == false`) or intersection state whose operands lie in `f`.
    pub open spec fn set_states_within(self, inter: bool, f: Set<S>, g: Set<S>) -> bool {
        forall|x: S| self.st(x) && self.is_set(inter, x) && (self.ops)(x).subset_of(f) ==> #[trigger] g.contains(x)
    }

    pub open spec fn has_set_bound(self, inter: bool, f: Set<S>) -> bool {
        exists|g: Set<S>| #[trigger] self.set_states_within(inter, f, g)
    }

    /// (N1)/(N2): every output has the shape above, and finitely many union (intersection) states
    /// have their operands in a given finite set.
    pub open spec fn nset_ok(self) -> bool {
        &&& forall|inter: bool, xs: Set<S>, u: S| (forall|x: S| xs.contains(x) ==> self.st(x))
            && #[trigger] (self.nset)(inter, xs, u) ==> self.nset_shape(inter, xs, u)
        &&& forall|inter: bool, f: Set<S>| #[trigger] self.has_set_bound(inter, f)
    }

    /// (N3).
    pub open spec fn not_shape(self, x: S) -> bool {
        let r = (self.nnot)(x);
        &&& self.st(r)
        &&& self.is_const(r) || (self.k(x) == Kind::Not && r == (self.body)(x))
            || (self.k(r) == Kind::Not && (self.body)(r) == x)
    }

    pub open spec fn not_ok(self) -> bool {
        forall|x: S| self.st(x) ==> #[trigger] self.not_shape(x)
    }

    /// (N4): `N(x₁⋯xₖ)` absorbs `∅`, flattens, drops `ε`, and returns `ε`, a single state, or a
    /// list of the flattened factors.
    pub open spec fn cat_shape(self, xs: Seq<S>) -> bool {
        let r = (self.ncat)(xs);
        let f = self.flat(xs);
        &&& self.st(r)
        &&& if self.has_empty(xs) { r == self.empty } else if f.len() == 0 { r == self.epsilon }
            else if f.len() == 1 { r == f[0] } else { self.k(r) == Kind::List && (self.elems)(r) == f }
    }

    pub open spec fn cat_ok(self) -> bool {
        forall|xs: Seq<S>| self.states(xs) ==> #[trigger] self.cat_shape(xs)
    }

    /// A finite set of tests containing `ts` and closed under the combinations of (N1)/(N2).
    pub open spec fn closure_for(self, inter: bool, ts: ISet<S>, c: ISet<S>) -> bool {
        &&& c.finite()
        &&& ts.subset_of(c)
        &&& forall|t: S| c.contains(t) ==> self.is_test(t)
        &&& forall|us: Set<S>, t: S| (forall|u: S| us.contains(u) ==> c.contains(u))
            && #[trigger] (self.combo)(inter, us, t) ==> c.contains(t)
    }

    pub open spec fn has_closure(self, inter: bool, ts: ISet<S>) -> bool {
        exists|c: ISet<S>| #[trigger] self.closure_for(inter, ts, c)
    }

    /// (N5).
    pub open spec fn tests_ok(self) -> bool {
        forall|inter: bool, ts: ISet<S>| ts.finite() && (forall|t: S| ts.contains(t) ==> self.is_test(t))
            ==> #[trigger] self.has_closure(inter, ts)
    }

    /// `u` contains every output of `N(ΣX)` (`N(&X)`) for every finite `X ⊆ u`.
    pub open spec fn nset_closed(self, inter: bool, u: ISet<S>) -> bool {
        forall|xs: Set<S>, v: S| (forall|x: S| xs.contains(x) ==> u.contains(x)) && #[trigger] (self.nset)(inter, xs, v)
            ==> u.contains(v)
    }

    pub open spec fn has_consts(self, u: ISet<S>) -> bool {
        u.contains(self.empty) && u.contains(self.epsilon) && u.contains(self.universal)
    }

    /// `v` is obtained from the constants and the states satisfying `base` by normalized unions
    /// (`inter == false`) or intersections: it lies in every set that contains them and is closed
    /// under `N(Σ·)` (`N(&·)`). This covers every bracketing and the merging of leaves.
    pub open spec fn built(self, inter: bool, base: spec_fn(S) -> bool, v: S) -> bool {
        forall|u: ISet<S>| self.has_consts(u) && (forall|w: S| #[trigger] base(w) ==> u.contains(w))
            && self.nset_closed(inter, u) ==> #[trigger] u.contains(v)
    }

    // ----- successor equations (S0)–(S6) -----

    /// A literal of an operand.
    pub open spec fn ops_lit(self, p: S, w: S) -> bool {
        exists|o: S| (self.ops)(p).contains(o) && #[trigger] (self.lit)(o, w)
    }

    /// The complement `N(¬ℓ)` of a literal `ℓ` of the body.
    pub open spec fn not_lit(self, p: S, w: S) -> bool {
        exists|l: S| #[trigger] (self.lit)((self.body)(p), l) && w == (self.nnot)(l)
    }

    /// `N(v p)` for a product `v` of the body of the star `p`.
    pub open spec fn star_lit(self, p: S, w: S) -> bool {
        exists|a: S| #[trigger] (self.prod)((self.body)(p), a) && w == self.cat2(a, p)
    }

    /// `N(v yᵢ₊₁⋯yₖ)` for a product `v` of a non-final element `yᵢ` of the list `p`, or a literal
    /// of its final element (the nullability guards are left open).
    pub open spec fn list_lit(self, p: S, w: S) -> bool {
        let es = (self.elems)(p);
        (exists|i: int, a: S| 0 <= i < es.len() - 1 && #[trigger] (self.prod)(es[i], a)
            && w == (self.ncat)(seq![a] + es.skip(i + 1)))
        || (self.lit)(es.last(), w)
    }

    /// (S0), (S1).
    pub open spec fn succ_shape(self, p: S, v: S) -> bool {
        if self.base_kind(p) { self.is_const(v) } else { self.built(false, |w: S| (self.prod)(p, w), v) }
    }

    /// (S1)–(S6) for literals.
    pub open spec fn lit_shape(self, p: S, v: S) -> bool {
        if self.base_kind(p) {
            self.is_const(v)
        } else if self.k(p) == Kind::Union {
            self.built(false, |w: S| self.ops_lit(p, w), v)
        } else if self.k(p) == Kind::Intersect {
            self.built(true, |w: S| self.ops_lit(p, w), v)
        } else if self.k(p) == Kind::Not {
            self.built(true, |w: S| self.not_lit(p, w), v)
        } else if self.k(p) == Kind::Star {
            self.built(false, |w: S| self.star_lit(p, w), v)
        } else {
            self.built(false, |w: S| self.list_lit(p, w), v)
        }
    }

    /// (S1)–(S6) for products.
    pub open spec fn prod_shape(self, p: S, v: S) -> bool {
        if self.base_kind(p) {
            self.is_const(v)
        } else if self.k(p) == Kind::Union {
            (exists|o: S| (self.ops)(p).contains(o) && #[trigger] (self.prod)(o, v)) || (self.lit)(p, v)
        } else if self.k(p) == Kind::Intersect || self.k(p) == Kind::Not {
            self.built(true, |w: S| (self.lit)(p, w), v)
        } else if self.k(p) == Kind::Star {
            (self.lit)(p, v)
        } else {
            (self.lit)(p, v) || (self.prod)((self.elems)(p).last(), v)
        }
    }

    pub open spec fn succ_ok(self) -> bool {
        &&& forall|p: S, v: S| self.st(p) && #[trigger] (self.succ)(p, v) ==> self.st(v) && self.succ_shape(p, v)
        &&& forall|p: S, v: S| self.st(p) && #[trigger] (self.lit)(p, v) ==> self.st(v) && self.lit_shape(p, v)
        &&& forall|p: S, v: S| self.st(p) && #[trigger] (self.prod)(p, v) ==> self.st(v) && self.prod_shape(p, v)
    }

    /// Language-independent structural contract: (N0)–(N5) and the successor equations (S0)–(S6),
    /// named in the table of `refinement/finiteness.rs`.
    pub open spec fn contract(self) -> bool {
        &&& self.constants_ok()
        &&& self.substates_ok()
        &&& self.fixpoints_ok()
        &&& self.nset_ok()
        &&& self.not_ok()
        &&& self.cat_ok()
        &&& self.tests_ok()
        &&& self.succ_ok()
    }

    // ----- invariants (C1)–(C4) -----

    pub open spec fn r_states(self, r: ISet<S>) -> bool {
        forall|p: S| r.contains(p) ==> self.st(p)
    }

    /// Successors of members of `r` lie in `r`.
    pub open spec fn r_closed(self, r: ISet<S>) -> bool {
        forall|p: S, v: S| r.contains(p) && #[trigger] (self.succ)(p, v) ==> r.contains(v)
    }

    /// (C2) relative to a target set `u` (`good` uses `u == y`): successors, literals, and
    /// products of members of `y` lie in `u`.
    pub open spec fn vals_into(self, y: ISet<S>, u: ISet<S>) -> bool {
        &&& forall|p: S, v: S| y.contains(p) && #[trigger] (self.succ)(p, v) ==> u.contains(v)
        &&& forall|p: S, v: S| y.contains(p) && #[trigger] (self.lit)(p, v) ==> u.contains(v)
        &&& forall|p: S, v: S| y.contains(p) && #[trigger] (self.prod)(p, v) ==> u.contains(v)
    }

    /// (C3)
    pub open spec fn r_ops(self, r: ISet<S>) -> bool {
        &&& forall|p: S, o: S| r.contains(p) && (self.k(p) == Kind::Union || self.k(p) == Kind::Intersect)
            && #[trigger] (self.ops)(p).contains(o) ==> r.contains(o)
        &&& forall|p: S| r.contains(p) && self.k(p) == Kind::Not ==> r.contains(#[trigger] (self.body)(p))
    }

    /// (C4) for one list `p` relative to a target set `u`: `N(v yᵢ₊₁⋯yₖ)` for the products `v`
    /// of each element `yᵢ`.
    pub open spec fn list_in(self, p: S, u: ISet<S>) -> bool {
        forall|i: int, a: S| 0 <= i < (self.elems)(p).len() && #[trigger] (self.prod)((self.elems)(p)[i], a)
            ==> u.contains((self.ncat)(seq![a] + (self.elems)(p).skip(i + 1)))
    }

    /// (C4) relative to a target set `u` (`good` uses `u == r`).
    pub open spec fn r_lists_in(self, r: ISet<S>, u: ISet<S>) -> bool {
        forall|p: S| r.contains(p) && self.k(p) == Kind::List ==> #[trigger] self.list_in(p, u)
    }

    /// (C1)–(C4), named in the table of `refinement/finiteness.rs`.
    pub open spec fn good(self, r: ISet<S>, q: S) -> bool {
        &&& r.finite()
        &&& r.contains(q) && self.has_consts(r)
        &&& self.r_states(r)
        &&& self.vals_into(r, r)
        &&& self.r_ops(r)
        &&& self.r_lists_in(r, r)
    }

    pub open spec fn rset(self, q: S) -> ISet<S> {
        choose|r: ISet<S>| self.good(r, q)
    }

    // ----- U(Y), U_&(Y), and U(U_&(Y)) -----

    pub open spec fn tests_in(self, y: ISet<S>) -> ISet<S> {
        y.filter(|x: S| self.is_test(x))
    }

    pub open spec fn tclosure(self, inter: bool, y: ISet<S>) -> ISet<S> {
        choose|c: ISet<S>| self.closure_for(inter, self.tests_in(y), c)
    }

    /// `Y^∨` (resp. `Y^∧`).
    pub open spec fn yv(self, inter: bool, y: ISet<S>) -> ISet<S> {
        ISet::new(|x: S| y.contains(x) || self.is_const(x) || self.tclosure(inter, y).contains(x))
    }

    pub open spec fn ops_in(self, x: S, s: ISet<S>) -> bool {
        forall|o: S| #[trigger] (self.ops)(x).contains(o) ==> s.contains(o)
    }

    /// `U(Y)` for `inter == false`, `U_&(Y)` for `inter == true`.
    pub open spec fn uset(self, inter: bool, y: ISet<S>) -> ISet<S> {
        ISet::new(|x: S| self.yv(inter, y).contains(x)
            || (self.st(x) && self.is_set(inter, x) && self.ops_in(x, self.yv(inter, y))))
    }

    /// `U(U_&(Y))`.
    pub open spec fn dnf(self, y: ISet<S>) -> ISet<S> {
        self.uset(false, self.uset(true, y))
    }

    /// `Y` is finite, consists of states, and contains the operands of its members.
    pub open spec fn y_ok(self, inter: bool, y: ISet<S>) -> bool {
        &&& y.finite()
        &&& self.r_states(y)
        &&& forall|p: S, o: S| y.contains(p) && self.is_set(inter, p) && #[trigger] (self.ops)(p).contains(o)
            ==> y.contains(o)
    }

    // ----- lists -----

    /// `s_j = N(c_{j+1}⋯c_m)` in the list case.
    pub open spec fn suffix(self, c: Seq<S>, j: int) -> S {
        (self.ncat)(c.skip(j + 1))
    }

    /// `T` in the list case.
    pub open spec fn list_terms(self, c: Seq<S>) -> ISet<S> {
        ISet::new(|y: S| exists|j: int, x: S| 0 <= j < c.len() && self.rset(c[j]).contains(x)
            && y == #[trigger] self.cat2(x, self.suffix(c, j)))
    }

    /// `T` in the star case.
    pub open spec fn star_terms(self, q: S) -> ISet<S> {
        self.rset((self.body)(q)).map(|x: S| self.cat2(x, q))
    }

    /// `Y = ⋃ᵢ C(oᵢ)` in the union and intersection cases.
    pub open spec fn ops_union(self, q: S) -> ISet<S> {
        ISet::new(|x: S| exists|o: S| (self.ops)(q).contains(o) && #[trigger] self.rset(o).contains(x))
    }
}

/// States reachable from `q0` in `n` successor steps (over all valuations and events).
pub open spec fn reachable<S>(m: Model<S>, q0: S, n: nat, q: S) -> bool
    decreases n,
{
    if n == 0 { q == q0 } else { exists|p: S| reachable(m, q0, (n - 1) as nat, p) && #[trigger] (m.succ)(p, q) }
}

// ===== finiteness utilities =====

pub proof fn lemma_powerset_finite<A>(f: Set<A>)
    ensures ISet::new(|s: Set<A>| s.subset_of(f)).finite(),
    decreases f.len(),
{
    let p = ISet::new(|s: Set<A>| s.subset_of(f));
    if f.len() == 0 {
        f.lemma_len0_is_empty();
        assert(p =~= ISet::empty().insert(Set::<A>::empty())) by {
            assert forall|s: Set<A>| p.contains(s) implies s == Set::<A>::empty() by {
                assert(s =~= Set::<A>::empty());
            }
        }
    } else {
        let x = f.choose();
        assert(f.contains(x)) by { lemma_set_empty_equivalency_len(f); }
        let g = f.remove(x);
        lemma_powerset_finite(g);
        let pg = ISet::new(|s: Set<A>| s.subset_of(g));
        let ins = |s: Set<A>| s.insert(x);
        pg.lemma_map_finite(ins);
        assert(p.subset_of(pg.union(pg.map(ins)))) by {
            assert forall|s: Set<A>| p.contains(s) implies pg.union(pg.map(ins)).contains(s) by {
                if s.contains(x) {
                    let s0 = s.remove(x);
                    assert(pg.contains(s0));
                    assert(s0.insert(x) =~= s);
                    assert(pg.map(ins).contains(s));
                } else {
                    assert(pg.contains(s));
                }
            }
        }
        lemma_iset_subset_finite(pg.union(pg.map(ins)), p);
    }
}

pub proof fn lemma_big_union_finite<I, A>(idx: Set<I>, f: spec_fn(I) -> ISet<A>)
    requires forall|i: I| idx.contains(i) ==> #[trigger] f(i).finite(),
    ensures ISet::new(|x: A| exists|i: I| idx.contains(i) && #[trigger] f(i).contains(x)).finite(),
    decreases idx.len(),
{
    let u = ISet::new(|x: A| exists|i: I| idx.contains(i) && #[trigger] f(i).contains(x));
    if idx.len() == 0 {
        idx.lemma_len0_is_empty();
        assert(u =~= ISet::<A>::empty());
    } else {
        let i0 = idx.choose();
        assert(idx.contains(i0)) by { lemma_set_empty_equivalency_len(idx); }
        let rest = idx.remove(i0);
        lemma_big_union_finite(rest, f);
        let ur = ISet::new(|x: A| exists|i: I| rest.contains(i) && #[trigger] f(i).contains(x));
        assert(u =~= ur.union(f(i0))) by {
            assert forall|x: A| u.contains(x) implies ur.union(f(i0)).contains(x) by {
                let i = choose|i: I| idx.contains(i) && #[trigger] f(i).contains(x);
                if i != i0 { assert(rest.contains(i)); }
            }
        }
    }
}

// ===== U(Y) =====

pub proof fn lemma_tclosure<S>(m: Model<S>, inter: bool, y: ISet<S>)
    requires m.contract(), y.finite(),
    ensures m.closure_for(inter, m.tests_in(y), m.tclosure(inter, y)),
{
    let ts = m.tests_in(y);
    lemma_iset_subset_finite(y, ts);
    assert forall|t: S| ts.contains(t) implies m.is_test(t) by {}
    assert(m.has_closure(inter, ts));
}

pub proof fn lemma_yv<S>(m: Model<S>, inter: bool, y: ISet<S>)
    requires m.contract(), m.y_ok(inter, y),
    ensures
        m.yv(inter, y).finite(),
        m.r_states(m.yv(inter, y)),
        forall|x: S| m.yv(inter, y).contains(x) && m.is_test(x) ==> #[trigger] m.tclosure(inter, y).contains(x),
        forall|x: S| m.yv(inter, y).contains(x) && m.is_set(inter, x) ==> #[trigger] y.contains(x),
        forall|x: S| #[trigger] m.yv(inter, y).contains(x) ==> y.contains(x) || m.is_const(x) || m.is_test(x),
{
    lemma_tclosure(m, inter, y);
    let c = m.tclosure(inter, y);
    let consts = ISet::empty().insert(m.empty).insert(m.epsilon).insert(m.universal);
    assert(m.yv(inter, y) =~= y.union(consts).union(c));
    assert forall|x: S| m.yv(inter, y).contains(x) && m.is_test(x) implies #[trigger] c.contains(x) by {
        if y.contains(x) { assert(m.tests_in(y).contains(x)); }
    }
}

pub proof fn lemma_uset_basic<S>(m: Model<S>, inter: bool, y: ISet<S>)
    requires m.contract(), m.y_ok(inter, y),
    ensures
        m.uset(inter, y).finite(),
        m.r_states(m.uset(inter, y)),
        y.subset_of(m.uset(inter, y)),
        m.uset(inter, y).contains(m.empty), m.uset(inter, y).contains(m.epsilon),
        m.uset(inter, y).contains(m.universal),
        forall|x: S| m.uset(inter, y).contains(x) && !m.is_set(inter, x) ==> #[trigger] m.yv(inter, y).contains(x),
{
    lemma_yv(m, inter, y);
    let yv = m.yv(inter, y);
    let fy = Set::new_from_iset(yv).unwrap();
    assert(fy.to_iset() == yv);
    assert(m.has_set_bound(inter, fy));
    let g = choose|g: Set<S>| #[trigger] m.set_states_within(inter, fy, g);
    let sets = ISet::new(|x: S| m.st(x) && m.is_set(inter, x) && m.ops_in(x, yv));
    assert(sets.subset_of(g.to_iset())) by {
        assert forall|x: S| sets.contains(x) implies g.to_iset().contains(x) by {
            let s = (m.ops)(x);
            assert(s.subset_of(fy)) by {
                assert forall|o: S| s.contains(o) implies fy.contains(o) by { assert(m.ops_in(x, yv)); }
            }
            assert(g.contains(x));
        }
    }
    vstd::set::lemma_to_iset_finite(g);
    lemma_iset_subset_finite(g.to_iset(), sets);
    assert(m.uset(inter, y) =~= yv.union(sets));
}

/// Operands of members of `X ⊆ U(Y)` lie in `Y^∨`.
pub proof fn lemma_uset_sops<S>(m: Model<S>, inter: bool, y: ISet<S>, xs: Set<S>)
    requires
        m.contract(), m.y_ok(inter, y),
        forall|x: S| xs.contains(x) ==> m.uset(inter, y).contains(x),
    ensures forall|o: S| m.in_sops_of(inter, xs, o) ==> #[trigger] m.yv(inter, y).contains(o),
{
    lemma_uset_basic(m, inter, y);
    lemma_yv(m, inter, y);
    assert forall|o: S| m.in_sops_of(inter, xs, o) implies #[trigger] m.yv(inter, y).contains(o) by {
        let x = choose|x: S| xs.contains(x) && #[trigger] m.sops(inter, x).contains(o);
        assert(m.uset(inter, y).contains(x));
        if m.is_set(inter, x) {
            if m.yv(inter, y).contains(x) {
                assert(y.contains(x));
                assert((m.ops)(x).contains(o));
            } else {
                assert(m.ops_in(x, m.yv(inter, y)));
                assert((m.ops)(x).contains(o));
            }
        } else {
            assert(o == x);
        }
    }
}

/// `U(Y)` is closed under normalized unions (intersections) of its members.
pub proof fn lemma_uset_nset<S>(m: Model<S>, inter: bool, y: ISet<S>, xs: Set<S>, u: S)
    requires
        m.contract(), m.y_ok(inter, y),
        forall|x: S| xs.contains(x) ==> m.uset(inter, y).contains(x),
        (m.nset)(inter, xs, u),
    ensures m.uset(inter, y).contains(u),
{
    lemma_uset_basic(m, inter, y);
    lemma_yv(m, inter, y);
    lemma_uset_sops(m, inter, y, xs);
    lemma_tclosure(m, inter, y);
    let yv = m.yv(inter, y);
    let c = m.tclosure(inter, y);
    assert forall|x: S| xs.contains(x) implies m.st(x) by {}
    assert(m.nset_ok());
    assert(m.nset_shape(inter, xs, u));
    if !m.is_const(u) {
        assert forall|o: S| #[trigger] m.sops(inter, u).contains(o) implies yv.contains(o) by {
            if !m.in_sops_of(inter, xs, o) {
                let ts = choose|ts: Set<S>| #[trigger] m.combo_from(inter, xs, ts, o);
                assert(m.combo_from(inter, xs, ts, o));
                assert forall|t: S| ts.contains(t) implies c.contains(t) by {
                    assert(m.is_test(t) && m.in_sops_of(inter, xs, t));
                    assert(m.yv(inter, y).contains(t));
                }
                assert(c.contains(o));
            }
        }
        if m.is_set(inter, u) {
            assert(m.ops_in(u, yv)) by {
                assert forall|o: S| #[trigger] (m.ops)(u).contains(o) implies yv.contains(o) by {
                    assert(m.sops(inter, u).contains(o));
                }
            }
        } else {
            assert(m.sops(inter, u).contains(u));
        }
    }
}

pub proof fn lemma_uset_nset_closed<S>(m: Model<S>, inter: bool, y: ISet<S>)
    requires m.contract(), m.y_ok(inter, y),
    ensures m.nset_closed(inter, m.uset(inter, y)), m.has_consts(m.uset(inter, y)),
{
    lemma_uset_basic(m, inter, y);
    assert forall|xs: Set<S>, u: S| (forall|x: S| xs.contains(x) ==> m.uset(inter, y).contains(x))
        && #[trigger] (m.nset)(inter, xs, u) implies m.uset(inter, y).contains(u) by {
        lemma_uset_nset(m, inter, y, xs, u);
    }
}

/// (S1): constants and tests have constant successors, literals, and products.
pub proof fn lemma_base_vals<S>(m: Model<S>, p: S)
    requires m.contract(), m.st(p), m.base_kind(p),
    ensures
        forall|v: S| #[trigger] (m.succ)(p, v) ==> m.is_const(v),
        forall|v: S| #[trigger] (m.lit)(p, v) ==> m.is_const(v),
        forall|v: S| #[trigger] (m.prod)(p, v) ==> m.is_const(v),
{
    assert forall|v: S| #[trigger] (m.succ)(p, v) implies m.is_const(v) by { assert(m.succ_shape(p, v)); }
    assert forall|v: S| #[trigger] (m.lit)(p, v) implies m.is_const(v) by { assert(m.lit_shape(p, v)); }
    assert forall|v: S| #[trigger] (m.prod)(p, v) implies m.is_const(v) by { assert(m.prod_shape(p, v)); }
}

/// Members of `Y^∨` outside `Y` are constants or tests.
pub proof fn lemma_yv_base<S>(m: Model<S>, inter: bool, y: ISet<S>, p: S)
    requires m.contract(), m.y_ok(inter, y), m.yv(inter, y).contains(p), !y.contains(p),
    ensures m.st(p), m.base_kind(p),
{
    lemma_yv(m, inter, y);
    if m.is_const(p) {
        assert(m.constants_ok());
    } else {
        assert(m.is_test(p));
    }
}

/// Successor closure: (C2) for `U(Y)` from (C2) for `Y`.
pub proof fn lemma_uset_closed<S>(m: Model<S>, y: ISet<S>)
    requires m.contract(), m.y_ok(false, y), m.vals_into(y, m.uset(false, y)),
    ensures m.vals_into(m.uset(false, y), m.uset(false, y)),
{
    lemma_uset_basic(m, false, y);
    lemma_yv(m, false, y);
    lemma_uset_nset_closed(m, false, y);
    let us = m.uset(false, y);
    let yv = m.yv(false, y);
    // Members of Y^∨.
    assert(m.vals_into(yv, us)) by {
        assert forall|p: S, v: S| yv.contains(p) && #[trigger] (m.succ)(p, v) implies us.contains(v) by {
            if !y.contains(p) { lemma_yv_base(m, false, y, p); lemma_base_vals(m, p); }
        }
        assert forall|p: S, v: S| yv.contains(p) && #[trigger] (m.lit)(p, v) implies us.contains(v) by {
            if !y.contains(p) { lemma_yv_base(m, false, y, p); lemma_base_vals(m, p); }
        }
        assert forall|p: S, v: S| yv.contains(p) && #[trigger] (m.prod)(p, v) implies us.contains(v) by {
            if !y.contains(p) { lemma_yv_base(m, false, y, p); lemma_base_vals(m, p); }
        }
    }
    // Union states with operands in Y^∨.
    assert forall|p: S, v: S| us.contains(p) && #[trigger] (m.lit)(p, v) implies us.contains(v) by {
        if !yv.contains(p) {
            assert(m.st(p) && m.is_set(false, p) && m.ops_in(p, yv));
            assert(m.lit_shape(p, v));
            assert forall|w: S| m.ops_lit(p, w) implies us.contains(w) by {
                let o = choose|o: S| (m.ops)(p).contains(o) && #[trigger] (m.lit)(o, w);
                assert(yv.contains(o));
            }
            assert(m.built(false, |w: S| m.ops_lit(p, w), v));
            assert(us.contains(v));
        }
    }
    assert forall|p: S, v: S| us.contains(p) && #[trigger] (m.prod)(p, v) implies us.contains(v) by {
        if !yv.contains(p) {
            assert(m.st(p) && m.is_set(false, p) && m.ops_in(p, yv));
            assert(m.prod_shape(p, v));
            if !(m.lit)(p, v) {
                let o = choose|o: S| (m.ops)(p).contains(o) && #[trigger] (m.prod)(o, v);
                assert(yv.contains(o));
            }
        }
    }
    assert forall|p: S, v: S| us.contains(p) && #[trigger] (m.succ)(p, v) implies us.contains(v) by {
        if !yv.contains(p) {
            assert(m.st(p) && m.is_set(false, p));
            assert(m.succ_shape(p, v));
            assert forall|w: S| (m.prod)(p, w) implies us.contains(w) by {}
            assert(m.built(false, |w: S| (m.prod)(p, w), v));
            assert(us.contains(v));
        }
    }
}

/// (C3) for `U(Y)` from (C3) for `Y`.
pub proof fn lemma_uset_ops<S>(m: Model<S>, inter: bool, y: ISet<S>)
    requires m.contract(), m.y_ok(inter, y), m.r_ops(y),
    ensures m.r_ops(m.uset(inter, y)),
{
    lemma_uset_basic(m, inter, y);
    lemma_yv(m, inter, y);
    let us = m.uset(inter, y);
    let yv = m.yv(inter, y);
    assert forall|p: S, o: S| us.contains(p) && (m.k(p) == Kind::Union || m.k(p) == Kind::Intersect)
        && #[trigger] (m.ops)(p).contains(o) implies us.contains(o) by {
        if y.contains(p) {
        } else if yv.contains(p) {
            if !m.is_const(p) { assert(m.is_test(p)); }
        } else {
            assert(m.ops_in(p, yv));
        }
    }
    assert forall|p: S| us.contains(p) && m.k(p) == Kind::Not implies us.contains(#[trigger] (m.body)(p)) by {
        if !y.contains(p) && yv.contains(p) && !m.is_const(p) { assert(m.is_test(p)); }
    }
}

/// The lists of `U(Y)` belong to `Y`, so (C4) carries over.
pub proof fn lemma_uset_lists<S>(m: Model<S>, inter: bool, y: ISet<S>, u: ISet<S>)
    requires m.contract(), m.y_ok(inter, y), m.r_lists_in(y, u),
    ensures m.r_lists_in(m.uset(inter, y), u),
{
    lemma_uset_basic(m, inter, y);
    lemma_yv(m, inter, y);
    let us = m.uset(inter, y);
    let yv = m.yv(inter, y);
    assert forall|p: S| us.contains(p) && m.k(p) == Kind::List implies #[trigger] m.list_in(p, u) by {
        assert(yv.contains(p));
        if !y.contains(p) && !m.is_const(p) { assert(m.is_test(p)); }
    }
}

/// `U_&(Y)` contains the union operands of its members, and `U(U_&(Y))` is finite.
pub proof fn lemma_dnf_basic<S>(m: Model<S>, y: ISet<S>)
    requires m.contract(), m.y_ok(true, y), m.y_ok(false, y),
    ensures
        m.y_ok(false, m.uset(true, y)),
        y.subset_of(m.uset(true, y)),
        m.uset(true, y).subset_of(m.dnf(y)),
        m.dnf(y).finite(), m.r_states(m.dnf(y)), m.has_consts(m.dnf(y)),
        m.nset_closed(true, m.uset(true, y)), m.has_consts(m.uset(true, y)),
        m.nset_closed(false, m.dnf(y)),
{
    lemma_uset_basic(m, true, y);
    lemma_yv(m, true, y);
    lemma_uset_nset_closed(m, true, y);
    let ua = m.uset(true, y);
    assert forall|p: S, o: S| ua.contains(p) && m.is_set(false, p) && #[trigger] (m.ops)(p).contains(o)
        implies ua.contains(o) by {
        assert(m.yv(true, y).contains(p));
        if !y.contains(p) && !m.is_const(p) { assert(m.is_test(p)); }
    }
    lemma_uset_basic(m, false, ua);
    lemma_uset_nset_closed(m, false, ua);
}

/// Successor closure for `U(U_&(Y))`: if the successors of members of `Y` lie in `U(U_&(Y))` and their
/// literals and products in `U_&(Y)`, then `U(U_&(Y))` satisfies (C2).
pub proof fn lemma_dnf_closed<S>(m: Model<S>, y: ISet<S>)
    requires
        m.contract(), m.y_ok(true, y), m.y_ok(false, y),
        forall|p: S, v: S| y.contains(p) && #[trigger] (m.succ)(p, v) ==> m.dnf(y).contains(v),
        forall|p: S, v: S| y.contains(p) && #[trigger] (m.lit)(p, v) ==> m.uset(true, y).contains(v),
        forall|p: S, v: S| y.contains(p) && #[trigger] (m.prod)(p, v) ==> m.uset(true, y).contains(v),
    ensures m.vals_into(m.dnf(y), m.dnf(y)),
{
    lemma_dnf_basic(m, y);
    lemma_yv(m, true, y);
    let ua = m.uset(true, y);
    let d = m.dnf(y);
    let yv = m.yv(true, y);
    // Literals and products of members of U_&(Y) lie in U_&(Y).
    assert forall|p: S, v: S| ua.contains(p) && #[trigger] (m.lit)(p, v) implies ua.contains(v) by {
        if y.contains(p) {
        } else if yv.contains(p) {
            lemma_yv_base(m, true, y, p);
            lemma_base_vals(m, p);
        } else {
            assert(m.st(p) && m.is_set(true, p) && m.ops_in(p, yv));
            assert(m.lit_shape(p, v));
            assert forall|w: S| m.ops_lit(p, w) implies ua.contains(w) by {
                let o = choose|o: S| (m.ops)(p).contains(o) && #[trigger] (m.lit)(o, w);
                assert(yv.contains(o));
                if !y.contains(o) { lemma_yv_base(m, true, y, o); lemma_base_vals(m, o); }
            }
            assert(m.built(true, |w: S| m.ops_lit(p, w), v));
            assert(ua.contains(v));
        }
    }
    assert forall|p: S, v: S| ua.contains(p) && #[trigger] (m.prod)(p, v) implies ua.contains(v) by {
        if y.contains(p) {
        } else if yv.contains(p) {
            lemma_yv_base(m, true, y, p);
            lemma_base_vals(m, p);
        } else {
            assert(m.st(p) && m.is_set(true, p));
            assert(m.prod_shape(p, v));
            assert forall|w: S| (m.lit)(p, w) implies ua.contains(w) by {}
            assert(m.built(true, |w: S| (m.lit)(p, w), v));
            assert(ua.contains(v));
        }
    }
    assert forall|p: S, v: S| ua.contains(p) && #[trigger] (m.succ)(p, v) implies d.contains(v) by {
        if y.contains(p) {
        } else if yv.contains(p) {
            lemma_yv_base(m, true, y, p);
            lemma_base_vals(m, p);
        } else {
            assert(m.st(p) && m.is_set(true, p));
            assert(m.succ_shape(p, v));
            assert forall|w: S| (m.prod)(p, w) implies d.contains(w) by { assert(ua.contains(w)); }
            assert(m.built(false, |w: S| (m.prod)(p, w), v));
            assert(d.contains(v));
        }
    }
    lemma_uset_closed(m, ua);
}

// ===== concatenation =====

pub proof fn lemma_flat_append<S>(m: Model<S>, xs: Seq<S>, ys: Seq<S>)
    ensures m.flat(xs + ys) == m.flat(xs) + m.flat(ys),
    decreases ys.len(),
{
    if ys.len() == 0 {
        assert(xs + ys =~= xs);
        assert(m.flat(xs) + m.flat(ys) =~= m.flat(xs));
    } else {
        assert((xs + ys).drop_last() =~= xs + ys.drop_last());
        assert((xs + ys).last() == ys.last());
        lemma_flat_append(m, xs, ys.drop_last());
        assert(m.flat(xs + ys) =~= m.flat(xs) + m.flat(ys));
    }
}

pub proof fn lemma_flat_single<S>(m: Model<S>, x: S)
    ensures m.flat(seq![x]) == m.piece(x),
{
    assert(seq![x].drop_last() =~= Seq::<S>::empty());
    assert(m.flat(Seq::<S>::empty()) + m.piece(x) =~= m.piece(x));
}

pub proof fn lemma_flat_atoms<S>(m: Model<S>, xs: Seq<S>)
    requires m.atoms(xs),
    ensures m.flat(xs) == xs,
    decreases xs.len(),
{
    if xs.len() > 0 {
        assert(m.atoms(xs.drop_last()));
        lemma_flat_atoms(m, xs.drop_last());
        assert(m.atom(xs.last()));
        assert(xs.drop_last() + seq![xs.last()] =~= xs);
    }
}

/// Without `∅`, the flattening of states consists of atoms.
pub proof fn lemma_flat_atoms_of<S>(m: Model<S>, xs: Seq<S>)
    requires m.contract(), m.states(xs), !m.has_empty(xs),
    ensures m.atoms(m.flat(xs)),
    decreases xs.len(),
{
    if xs.len() > 0 {
        let init = xs.drop_last();
        let x = xs.last();
        assert(!m.has_empty(init)) by {
            if m.has_empty(init) {
                let i = choose|i: int| 0 <= i < init.len() && init[i] == m.empty;
                assert(xs[i] == m.empty);
            }
        }
        lemma_flat_atoms_of(m, init);
        assert(m.st(x));
        assert(x != m.empty) by { assert(xs[xs.len() - 1] == x); }
        assert(m.atoms(m.piece(x))) by {
            if m.k(x) == Kind::List {
                let es = (m.elems)(x);
                assert forall|i: int| 0 <= i < es.len() implies m.atom(#[trigger] es[i]) by {}
            }
        }
        let f = m.flat(xs);
        assert(f == m.flat(init) + m.piece(x));
        assert forall|i: int| 0 <= i < f.len() implies m.atom(#[trigger] f[i]) by {
            if i < m.flat(init).len() {
                assert(f[i] == m.flat(init)[i]);
            } else {
                assert(f[i] == m.piece(x)[i - m.flat(init).len()]);
            }
        }
    }
}

pub proof fn lemma_list_unique<S>(m: Model<S>, a: S, b: S)
    requires m.contract(), m.st(a), m.st(b), m.k(a) == Kind::List, m.k(b) == Kind::List,
        (m.elems)(a) == (m.elems)(b),
    ensures a == b,
{
    assert((m.ncat)((m.elems)(a)) == a);
    assert((m.ncat)((m.elems)(b)) == b);
}

/// Without `∅`, `N(xs)` is not `∅` and contributes exactly the flattening of `xs`.
pub proof fn lemma_cat_piece<S>(m: Model<S>, xs: Seq<S>)
    requires m.contract(), m.states(xs), !m.has_empty(xs),
    ensures
        (m.ncat)(xs) != m.empty,
        m.st((m.ncat)(xs)),
        m.piece((m.ncat)(xs)) == m.flat(xs),
{
    assert(m.cat_shape(xs));
    lemma_flat_atoms_of(m, xs);
    let f = m.flat(xs);
    let r = (m.ncat)(xs);
    if f.len() == 0 {
        assert(m.piece(r) =~= f);
    } else if f.len() == 1 {
        assert(m.atom(f[0]));
        assert(m.piece(r) =~= f);
    } else {
        assert(m.k(r) == Kind::List);
    }
}

/// `N` depends only on the flattening, once `∅` is excluded.
pub proof fn lemma_cat_flat_eq<S>(m: Model<S>, xs: Seq<S>, ys: Seq<S>)
    requires m.contract(), m.states(xs), m.states(ys), !m.has_empty(xs), !m.has_empty(ys),
        m.flat(xs) == m.flat(ys),
    ensures (m.ncat)(xs) == (m.ncat)(ys),
{
    assert(m.cat_shape(xs));
    assert(m.cat_shape(ys));
    if m.flat(xs).len() >= 2 {
        lemma_list_unique(m, (m.ncat)(xs), (m.ncat)(ys));
    }
}

pub proof fn lemma_no_empty_pair<S>(m: Model<S>, x: S, y: S)
    requires x != m.empty, y != m.empty,
    ensures !m.has_empty(seq![x, y]),
{
    if m.has_empty(seq![x, y]) {
        let i = choose|i: int| 0 <= i < 2 && seq![x, y][i] == m.empty;
        assert(i == 0 || i == 1);
    }
}

pub proof fn lemma_no_empty_atoms<S>(m: Model<S>, xs: Seq<S>)
    requires m.atoms(xs),
    ensures !m.has_empty(xs), m.states(xs),
{
    if m.has_empty(xs) {
        let i = choose|i: int| 0 <= i < xs.len() && xs[i] == m.empty;
        assert(m.atom(xs[i]));
    }
    assert forall|i: int| 0 <= i < xs.len() implies m.st(#[trigger] xs[i]) by { assert(m.atom(xs[i])); }
}

pub proof fn lemma_cat_single<S>(m: Model<S>, x: S)
    requires m.contract(), m.st(x),
    ensures (m.ncat)(seq![x]) == x,
{
    let xs = seq![x];
    assert(m.states(xs));
    assert(m.cat_shape(xs));
    lemma_flat_single(m, x);
    if x == m.empty {
        assert(xs[0] == m.empty);
    } else {
        assert(!m.has_empty(xs)) by {
            if m.has_empty(xs) { let i = choose|i: int| 0 <= i < xs.len() && xs[i] == m.empty; }
        }
        if m.k(x) == Kind::List {
            assert((m.elems)(x).len() >= 2);
            lemma_list_unique(m, (m.ncat)(xs), x);
        }
    }
}

/// A sequence of atoms normalizes to its single element or to the list of its elements.
pub proof fn lemma_cat_atoms<S>(m: Model<S>, zs: Seq<S>)
    requires m.contract(), m.atoms(zs), zs.len() >= 1,
    ensures
        zs.len() == 1 ==> (m.ncat)(zs) == zs[0],
        zs.len() >= 2 ==> m.k((m.ncat)(zs)) == Kind::List && (m.elems)((m.ncat)(zs)) == zs,
        m.st((m.ncat)(zs)), (m.ncat)(zs) != m.empty,
{
    lemma_no_empty_atoms(m, zs);
    lemma_flat_atoms(m, zs);
    assert(m.cat_shape(zs));
    assert(m.atom(zs[0]));
}

/// `N(a z w) = N(N(a z) N(w))` for a state `a` and sequences of atoms `z`, `w`.
pub proof fn lemma_cat_assoc<S>(m: Model<S>, a: S, z: Seq<S>, w: Seq<S>)
    requires m.contract(), m.st(a), m.atoms(z), m.atoms(w),
    ensures (m.ncat)(seq![a] + z + w) == m.cat2((m.ncat)(seq![a] + z), (m.ncat)(w)),
{
    lemma_no_empty_atoms(m, z);
    lemma_no_empty_atoms(m, w);
    let az = seq![a] + z;
    let azw = seq![a] + z + w;
    assert(m.states(az)) by {
        assert forall|i: int| 0 <= i < az.len() implies m.st(#[trigger] az[i]) by {
            if i > 0 { assert(az[i] == z[i - 1]); }
        }
    }
    assert(m.states(azw)) by {
        assert forall|i: int| 0 <= i < azw.len() implies m.st(#[trigger] azw[i]) by {
            if i > 0 && i <= z.len() { assert(azw[i] == z[i - 1]); }
            if i > z.len() { assert(azw[i] == w[i - 1 - z.len()]); }
        }
    }
    assert(m.cat_shape(az));
    assert(m.cat_shape(w));
    assert(m.cat_shape(azw));
    let l = (m.ncat)(az);
    let r = (m.ncat)(w);
    let outer = seq![l, r];
    assert(m.states(outer)) by {
        assert forall|i: int| 0 <= i < outer.len() implies m.st(#[trigger] outer[i]) by {}
    }
    assert(m.cat_shape(outer));
    if a == m.empty {
        assert(azw[0] == m.empty);
        assert(az[0] == m.empty);
        assert(outer[0] == m.empty);
    } else {
        assert(!m.has_empty(az)) by {
            if m.has_empty(az) {
                let i = choose|i: int| 0 <= i < az.len() && az[i] == m.empty;
                if i > 0 { assert(az[i] == z[i - 1]); }
            }
        }
        assert(!m.has_empty(azw)) by {
            if m.has_empty(azw) {
                let i = choose|i: int| 0 <= i < azw.len() && azw[i] == m.empty;
                if i > 0 && i <= z.len() { assert(azw[i] == z[i - 1]); }
                if i > z.len() { assert(azw[i] == w[i - 1 - z.len()]); }
            }
        }
        lemma_cat_piece(m, az);
        lemma_cat_piece(m, w);
        lemma_no_empty_pair(m, l, r);
        lemma_flat_append(m, seq![l], seq![r]);
        assert(seq![l] + seq![r] =~= outer);
        lemma_flat_single(m, l);
        lemma_flat_single(m, r);
        lemma_flat_append(m, az, w);
        assert(az + w =~= azw);
        lemma_cat_flat_eq(m, azw, outer);
    }
}

/// Shape of `N(x s)` for a state `x` and an atom sequence whose normal form is `s`.
pub proof fn lemma_cat_pair<S>(m: Model<S>, x: S, w: Seq<S>)
    requires m.contract(), m.st(x), m.atoms(w),
    ensures
        m.st(m.cat2(x, (m.ncat)(w))),
        x == m.empty ==> m.cat2(x, (m.ncat)(w)) == m.empty,
        x == m.epsilon ==> m.cat2(x, (m.ncat)(w)) == (m.ncat)(w),
        x != m.empty ==> m.cat2(x, (m.ncat)(w)) == (m.ncat)(m.piece(x) + w),
        x != m.empty && x != m.epsilon ==> m.atoms(m.piece(x)) && m.piece(x).len() >= 1,
        m.k(x) != Kind::List && x != m.empty && x != m.epsilon ==> m.piece(x) == seq![x],
{
    lemma_no_empty_atoms(m, w);
    let r = (m.ncat)(w);
    assert(m.cat_shape(w));
    let xs = seq![x, r];
    lemma_cat_piece(m, w);
    assert(m.states(xs)) by {
        assert forall|i: int| 0 <= i < xs.len() implies m.st(#[trigger] xs[i]) by {}
    }
    assert(m.cat_shape(xs));
    if x == m.empty {
        assert(xs[0] == m.empty);
    } else {
        lemma_no_empty_pair(m, x, r);
        assert(m.states(seq![x]));
        assert(!m.has_empty(seq![x])) by {
            if m.has_empty(seq![x]) { let i = choose|i: int| 0 <= i < 1 && seq![x][i] == m.empty; }
        }
        lemma_flat_atoms_of(m, seq![x]);
        lemma_flat_single(m, x);
        lemma_flat_append(m, seq![x], seq![r]);
        assert(seq![x] + seq![r] =~= xs);
        lemma_flat_single(m, r);
        lemma_flat_atoms(m, w);
        let pw = m.piece(x) + w;
        assert(m.atoms(m.piece(x)));
        assert(m.atoms(pw)) by {
            assert forall|i: int| 0 <= i < pw.len() implies m.atom(#[trigger] pw[i]) by {
                if i < m.piece(x).len() { assert(pw[i] == m.piece(x)[i]); } else { assert(pw[i] == w[i - m.piece(x).len()]); }
            }
        }
        lemma_no_empty_atoms(m, pw);
        lemma_flat_atoms(m, pw);
        lemma_cat_flat_eq(m, xs, pw);
        if x == m.epsilon {
            assert(pw =~= w);
        } else {
            if m.k(x) == Kind::List {
                assert((m.elems)(x).len() >= 2);
            }
        }
    }
}

// ===== C(q) =====

pub proof fn lemma_vals_mono<S>(m: Model<S>, y: ISet<S>, u1: ISet<S>, u2: ISet<S>)
    requires m.vals_into(y, u1), u1.subset_of(u2),
    ensures m.vals_into(y, u2),
{
    assert forall|p: S, v: S| y.contains(p) && #[trigger] (m.succ)(p, v) implies u2.contains(v) by { assert(u1.contains(v)); }
    assert forall|p: S, v: S| y.contains(p) && #[trigger] (m.lit)(p, v) implies u2.contains(v) by { assert(u1.contains(v)); }
    assert forall|p: S, v: S| y.contains(p) && #[trigger] (m.prod)(p, v) implies u2.contains(v) by { assert(u1.contains(v)); }
}

pub proof fn lemma_list_in_mono<S>(m: Model<S>, p: S, u1: ISet<S>, u2: ISet<S>)
    requires m.list_in(p, u1), u1.subset_of(u2),
    ensures m.list_in(p, u2),
{
    assert forall|i: int, a: S| 0 <= i < (m.elems)(p).len() && #[trigger] (m.prod)((m.elems)(p)[i], a)
        implies u2.contains((m.ncat)(seq![a] + (m.elems)(p).skip(i + 1))) by {
        assert(u1.contains((m.ncat)(seq![a] + (m.elems)(p).skip(i + 1))));
    }
}

pub proof fn lemma_lists_mono<S>(m: Model<S>, r: ISet<S>, u1: ISet<S>, u2: ISet<S>)
    requires m.r_lists_in(r, u1), u1.subset_of(u2),
    ensures m.r_lists_in(r, u2),
{
    assert forall|p: S| r.contains(p) && m.k(p) == Kind::List implies #[trigger] m.list_in(p, u2) by {
        assert(m.list_in(p, u1));
        lemma_list_in_mono(m, p, u1, u2);
    }
}

pub proof fn lemma_good_base<S>(m: Model<S>, q: S)
    requires m.contract(), m.st(q), m.base_kind(q),
    ensures m.good(m.rset(q), q),
{
    let r = ISet::empty().insert(q).insert(m.empty).insert(m.epsilon).insert(m.universal);
    assert(m.constants_ok());
    assert forall|p: S| r.contains(p) implies m.st(p) && #[trigger] m.base_kind(p) by {}
    assert(m.vals_into(r, r)) by {
        assert forall|p: S, v: S| r.contains(p) && #[trigger] (m.succ)(p, v) implies r.contains(v) by {
            assert(m.base_kind(p));
            lemma_base_vals(m, p);
        }
        assert forall|p: S, v: S| r.contains(p) && #[trigger] (m.lit)(p, v) implies r.contains(v) by {
            assert(m.base_kind(p));
            lemma_base_vals(m, p);
        }
        assert forall|p: S, v: S| r.contains(p) && #[trigger] (m.prod)(p, v) implies r.contains(v) by {
            assert(m.base_kind(p));
            lemma_base_vals(m, p);
        }
    }
    assert forall|p: S| r.contains(p) && m.k(p) == Kind::List implies #[trigger] m.list_in(p, r) by {
        assert(m.base_kind(p));
    }
    assert(m.good(r, q));
}

/// `Y = ⋃ᵢ C(oᵢ)` inherits (C1)–(C4) from the `C(oᵢ)`.
pub proof fn lemma_ops_union<S>(m: Model<S>, q: S)
    requires m.contract(), m.st(q), m.k(q) == Kind::Union || m.k(q) == Kind::Intersect,
        forall|o: S| #[trigger] (m.ops)(q).contains(o) ==> m.good(m.rset(o), o),
    ensures ({
        let y = m.ops_union(q);
        &&& m.y_ok(false, y) && m.y_ok(true, y) && m.r_ops(y)
        &&& m.vals_into(y, y) && m.r_lists_in(y, y)
        &&& forall|o: S| #[trigger] (m.ops)(q).contains(o) ==> y.contains(o)
    }),
{
    let os = (m.ops)(q);
    let f = |o: S| m.rset(o);
    lemma_big_union_finite(os, f);
    let y = m.ops_union(q);
    assert(y =~= ISet::new(|x: S| exists|o: S| os.contains(o) && #[trigger] f(o).contains(x))) by {
        assert forall|x: S| y.contains(x) implies exists|o: S| os.contains(o) && #[trigger] f(o).contains(x) by {
            let o = choose|o: S| os.contains(o) && #[trigger] m.rset(o).contains(x);
            assert(f(o).contains(x));
        }
        assert forall|x: S| (exists|o: S| os.contains(o) && #[trigger] f(o).contains(x)) implies y.contains(x) by {
            let o = choose|o: S| os.contains(o) && #[trigger] f(o).contains(x);
            assert(m.rset(o).contains(x));
        }
    }
    assert(m.r_states(y)) by {
        assert forall|p: S| y.contains(p) implies m.st(p) by {
            let o = choose|o: S| os.contains(o) && #[trigger] m.rset(o).contains(p);
            assert(m.good(m.rset(o), o));
        }
    }
    assert(m.r_ops(y)) by {
        assert forall|p: S, o2: S| y.contains(p) && (m.k(p) == Kind::Union || m.k(p) == Kind::Intersect)
            && #[trigger] (m.ops)(p).contains(o2) implies y.contains(o2) by {
            let o = choose|o: S| os.contains(o) && #[trigger] m.rset(o).contains(p);
            assert(m.good(m.rset(o), o));
            assert(m.rset(o).contains(o2));
        }
        assert forall|p: S| y.contains(p) && m.k(p) == Kind::Not implies y.contains(#[trigger] (m.body)(p)) by {
            let o = choose|o: S| os.contains(o) && #[trigger] m.rset(o).contains(p);
            assert(m.good(m.rset(o), o));
            assert(m.rset(o).contains((m.body)(p)));
        }
    }
    assert(m.vals_into(y, y)) by {
        assert forall|p: S, v: S| y.contains(p) && #[trigger] (m.succ)(p, v) implies y.contains(v) by {
            let o = choose|o: S| os.contains(o) && #[trigger] m.rset(o).contains(p);
            assert(m.good(m.rset(o), o));
            assert(m.rset(o).contains(v));
        }
        assert forall|p: S, v: S| y.contains(p) && #[trigger] (m.lit)(p, v) implies y.contains(v) by {
            let o = choose|o: S| os.contains(o) && #[trigger] m.rset(o).contains(p);
            assert(m.good(m.rset(o), o));
            assert(m.rset(o).contains(v));
        }
        assert forall|p: S, v: S| y.contains(p) && #[trigger] (m.prod)(p, v) implies y.contains(v) by {
            let o = choose|o: S| os.contains(o) && #[trigger] m.rset(o).contains(p);
            assert(m.good(m.rset(o), o));
            assert(m.rset(o).contains(v));
        }
    }
    assert(m.r_lists_in(y, y)) by {
        assert forall|p: S| y.contains(p) && m.k(p) == Kind::List implies #[trigger] m.list_in(p, y) by {
            let o = choose|o: S| os.contains(o) && #[trigger] m.rset(o).contains(p);
            assert(m.good(m.rset(o), o));
            assert(m.list_in(p, m.rset(o)));
            lemma_list_in_mono(m, p, m.rset(o), y);
        }
    }
    assert forall|o: S| #[trigger] (m.ops)(q).contains(o) implies y.contains(o) by {
        assert(m.good(m.rset(o), o));
        assert(m.rset(o).contains(o));
    }
}

pub proof fn lemma_good_union<S>(m: Model<S>, q: S)
    requires m.contract(), m.st(q), m.k(q) == Kind::Union,
        forall|o: S| #[trigger] (m.ops)(q).contains(o) ==> m.good(m.rset(o), o),
    ensures m.good(m.rset(q), q),
{
    lemma_ops_union(m, q);
    let y = m.ops_union(q);
    lemma_uset_basic(m, false, y);
    lemma_yv(m, false, y);
    let us = m.uset(false, y);
    lemma_vals_mono(m, y, y, us);
    lemma_uset_closed(m, y);
    lemma_uset_ops(m, false, y);
    lemma_lists_mono(m, y, y, us);
    lemma_uset_lists(m, false, y, us);
    assert(us.contains(q)) by {
        assert(m.ops_in(q, m.yv(false, y))) by {
            assert forall|o: S| #[trigger] (m.ops)(q).contains(o) implies m.yv(false, y).contains(o) by {}
        }
    }
    assert(m.good(us, q));
}

pub proof fn lemma_good_inter<S>(m: Model<S>, q: S)
    requires m.contract(), m.st(q), m.k(q) == Kind::Intersect,
        forall|o: S| #[trigger] (m.ops)(q).contains(o) ==> m.good(m.rset(o), o),
    ensures m.good(m.rset(q), q),
{
    lemma_ops_union(m, q);
    let y = m.ops_union(q);
    lemma_dnf_basic(m, y);
    lemma_yv(m, true, y);
    let ua = m.uset(true, y);
    let d = m.dnf(y);
    assert forall|p: S, v: S| y.contains(p) && #[trigger] (m.succ)(p, v) implies d.contains(v) by { assert(y.contains(v)); }
    assert forall|p: S, v: S| y.contains(p) && #[trigger] (m.lit)(p, v) implies ua.contains(v) by { assert(y.contains(v)); }
    assert forall|p: S, v: S| y.contains(p) && #[trigger] (m.prod)(p, v) implies ua.contains(v) by { assert(y.contains(v)); }
    lemma_dnf_closed(m, y);
    lemma_uset_ops(m, true, y);
    lemma_uset_ops(m, false, ua);
    lemma_lists_mono(m, y, y, d);
    lemma_uset_lists(m, true, y, d);
    lemma_uset_lists(m, false, ua, d);
    assert(ua.contains(q)) by {
        assert(m.ops_in(q, m.yv(true, y))) by {
            assert forall|o: S| #[trigger] (m.ops)(q).contains(o) implies m.yv(true, y).contains(o) by {}
        }
    }
    assert(m.good(d, q));
}

pub proof fn lemma_good_not<S>(m: Model<S>, q: S)
    requires m.contract(), m.st(q), m.k(q) == Kind::Not, m.good(m.rset((m.body)(q)), (m.body)(q)),
    ensures m.good(m.rset(q), q),
{
    let p = (m.body)(q);
    let rp = m.rset(p);
    let nn = |s: S| (m.nnot)(s);
    rp.lemma_map_finite(nn);
    let lam = rp.union(rp.map(nn));
    assert(m.constants_ok());
    // Members of Λ outside C(p) are constants or complements of members of C(p).
    assert forall|x: S| lam.contains(x) && !rp.contains(x) implies m.st(x)
        && (m.is_const(x) || (m.k(x) == Kind::Not && rp.contains((m.body)(x)))) by {
        let s = choose|s: S| rp.contains(s) && nn(s) == x;
        assert(m.not_shape(s));
        if !m.is_const(x) && !(m.k(x) == Kind::Not && (m.body)(x) == s) {
            assert(m.k(s) == Kind::Not && x == (m.body)(s));
        }
    }
    assert(m.r_states(lam));
    assert forall|x: S, o: S| lam.contains(x) && (m.k(x) == Kind::Union || m.k(x) == Kind::Intersect)
        && #[trigger] (m.ops)(x).contains(o) implies lam.contains(o) by {
        assert(rp.contains(x));
    }
    assert forall|x: S| lam.contains(x) && m.k(x) == Kind::Not implies lam.contains(#[trigger] (m.body)(x)) by {}
    assert(m.y_ok(true, lam) && m.y_ok(false, lam) && m.r_ops(lam));
    lemma_dnf_basic(m, lam);
    let ua = m.uset(true, lam);
    let d = m.dnf(lam);
    // Literals of a complement ¬s are normalized intersections of complements of literals of s.
    assert forall|x: S, v: S| lam.contains(x) && #[trigger] (m.lit)(x, v) implies ua.contains(v) by {
        if rp.contains(x) {
            assert(rp.contains(v));
        } else if m.is_const(x) {
            lemma_base_vals(m, x);
        } else {
            assert(m.lit_shape(x, v));
            assert forall|w: S| m.not_lit(x, w) implies ua.contains(w) by {
                let l = choose|l: S| #[trigger] (m.lit)((m.body)(x), l) && w == (m.nnot)(l);
                assert(rp.contains(l));
                assert(rp.map(nn).contains(nn(l)));
            }
            assert(m.built(true, |w: S| m.not_lit(x, w), v));
            assert(ua.contains(v));
        }
    }
    assert forall|x: S, v: S| lam.contains(x) && #[trigger] (m.prod)(x, v) implies ua.contains(v) by {
        if rp.contains(x) {
            assert(rp.contains(v));
        } else if m.is_const(x) {
            lemma_base_vals(m, x);
        } else {
            assert(m.prod_shape(x, v));
            assert forall|w: S| (m.lit)(x, w) implies ua.contains(w) by {}
            assert(m.built(true, |w: S| (m.lit)(x, w), v));
            assert(ua.contains(v));
        }
    }
    assert forall|x: S, v: S| lam.contains(x) && #[trigger] (m.succ)(x, v) implies d.contains(v) by {
        if rp.contains(x) {
            assert(rp.contains(v));
        } else if m.is_const(x) {
            lemma_base_vals(m, x);
        } else {
            assert(m.succ_shape(x, v));
            assert forall|w: S| (m.prod)(x, w) implies d.contains(w) by { assert(ua.contains(w)); }
            assert(m.built(false, |w: S| (m.prod)(x, w), v));
            assert(d.contains(v));
        }
    }
    lemma_dnf_closed(m, lam);
    lemma_uset_ops(m, true, lam);
    lemma_uset_ops(m, false, ua);
    assert(m.r_lists_in(lam, d)) by {
        assert forall|x: S| lam.contains(x) && m.k(x) == Kind::List implies #[trigger] m.list_in(x, d) by {
            assert(rp.contains(x));
            assert(m.list_in(x, rp));
            lemma_list_in_mono(m, x, rp, d);
        }
    }
    lemma_uset_lists(m, true, lam, d);
    lemma_uset_lists(m, false, ua, d);
    assert(lam.contains(q)) by {
        assert((m.nnot)(p) == q);
        assert(rp.map(nn).contains(nn(p)));
    }
    assert(m.good(d, q));
}

/// The element sequence of a member `x ∉ {∅, ε}` of `C(·)` satisfies (C4) relative to `C(·)`.
pub proof fn lemma_piece_tails<S>(m: Model<S>, r: ISet<S>, q0: S, x: S)
    requires m.contract(), m.good(r, q0), r.contains(x), x != m.empty, x != m.epsilon,
    ensures
        m.atoms(m.piece(x)), m.piece(x).len() >= 1,
        forall|i: int, a: S| 0 <= i < m.piece(x).len() && #[trigger] (m.prod)(m.piece(x)[i], a)
            ==> r.contains((m.ncat)(seq![a] + m.piece(x).skip(i + 1))),
{
    assert(m.st(x));
    let z = m.piece(x);
    if m.k(x) == Kind::List {
        assert(m.list_in(x, r));
        let es = (m.elems)(x);
        assert(es.len() >= 2);
        assert forall|i: int| 0 <= i < z.len() implies m.atom(#[trigger] z[i]) by { assert(z[i] == es[i]); }
    } else {
        assert(z == seq![x]);
        assert(m.atom(x));
        assert(m.atoms(z)) by {
            assert forall|i: int| 0 <= i < z.len() implies m.atom(#[trigger] z[i]) by { assert(i == 0); }
        }
        assert forall|i: int, a: S| 0 <= i < z.len() && #[trigger] (m.prod)(z[i], a)
            implies r.contains((m.ncat)(seq![a] + z.skip(i + 1))) by {
            assert(i == 0 && z[i] == x);
            assert(r.contains(a));
            assert(m.st(a));
            assert(seq![a] + z.skip(1) =~= seq![a]);
            lemma_cat_single(m, a);
        }
    }
}

/// A list whose partial successors (C4) and final-element literals and products lie in a set `u`
/// closed under normalized unions has its successors, literals, and products in `u`, by (S6).
pub proof fn lemma_list_vals<S>(m: Model<S>, t: S, u: ISet<S>)
    requires
        m.contract(), m.st(t), m.k(t) == Kind::List,
        m.has_consts(u), m.nset_closed(false, u), m.list_in(t, u),
        forall|w: S| #[trigger] (m.lit)((m.elems)(t).last(), w) ==> u.contains(w),
        forall|w: S| #[trigger] (m.prod)((m.elems)(t).last(), w) ==> u.contains(w),
    ensures
        forall|v: S| #[trigger] (m.lit)(t, v) ==> u.contains(v),
        forall|v: S| #[trigger] (m.prod)(t, v) ==> u.contains(v),
        forall|v: S| #[trigger] (m.succ)(t, v) ==> u.contains(v),
{
    let es = (m.elems)(t);
    assert forall|v: S| #[trigger] (m.lit)(t, v) implies u.contains(v) by {
        assert(m.lit_shape(t, v));
        assert forall|w: S| m.list_lit(t, w) implies u.contains(w) by {
            if !(m.lit)(es.last(), w) {
                let (i, a) = choose|i: int, a: S| 0 <= i < es.len() - 1 && #[trigger] (m.prod)(es[i], a)
                    && w == (m.ncat)(seq![a] + es.skip(i + 1));
            }
        }
        assert(m.built(false, |w: S| m.list_lit(t, w), v));
        assert(u.contains(v));
    }
    assert forall|v: S| #[trigger] (m.prod)(t, v) implies u.contains(v) by {
        assert(m.prod_shape(t, v));
    }
    assert forall|v: S| #[trigger] (m.succ)(t, v) implies u.contains(v) by {
        assert(m.succ_shape(t, v));
        assert forall|w: S| (m.prod)(t, w) implies u.contains(w) by {}
        assert(m.built(false, |w: S| (m.prod)(t, w), v));
        assert(u.contains(v));
    }
}

pub proof fn lemma_good_star<S>(m: Model<S>, q: S)
    requires m.contract(), m.st(q), m.k(q) == Kind::Star, m.good(m.rset((m.body)(q)), (m.body)(q)),
    ensures m.good(m.rset(q), q),
{
    let p = (m.body)(q);
    let rp = m.rset(p);
    let cq = |x: S| m.cat2(x, q);
    rp.lemma_map_finite(cq);
    let t = m.star_terms(q);
    let w = seq![q];
    assert(m.constants_ok());
    assert(m.atom(q));
    assert(m.atoms(w));
    lemma_cat_single(m, q);
    assert((m.ncat)(w) == q);
    // Members of T: ∅, q, or lists `z q`.
    assert forall|x: S| rp.contains(x) implies m.st(#[trigger] m.cat2(x, q)) && (
        m.cat2(x, q) == m.empty && x == m.empty
        || m.cat2(x, q) == q && x == m.epsilon
        || (x != m.empty && x != m.epsilon && m.k(m.cat2(x, q)) == Kind::List
            && (m.elems)(m.cat2(x, q)) == m.piece(x) + w)) by {
        assert(m.st(x));
        lemma_cat_pair(m, x, w);
        if x != m.empty && x != m.epsilon {
            let z = m.piece(x);
            let zw = z + w;
            assert(m.atoms(zw)) by {
                assert forall|h: int| 0 <= h < zw.len() implies m.atom(#[trigger] zw[h]) by {
                    if h < z.len() { assert(zw[h] == z[h]); } else { assert(zw[h] == w[h - z.len()]); }
                }
            }
            lemma_cat_atoms(m, zw);
        }
    }
    assert(t.contains(q)) by {
        assert(cq(m.epsilon) == q);
    }
    assert forall|v: S| t.contains(v) implies exists|x: S| rp.contains(x) && v == #[trigger] m.cat2(x, q) by {}
    assert(m.r_states(t)) by {
        assert forall|v: S| t.contains(v) implies m.st(v) by {
            let x = choose|x: S| rp.contains(x) && v == #[trigger] m.cat2(x, q);
        }
    }
    // No unions, intersections, or complements in T.
    assert forall|v: S| t.contains(v) implies m.k(v) != Kind::Union && m.k(v) != Kind::Intersect && m.k(v) != Kind::Not by {
        let x = choose|x: S| rp.contains(x) && v == #[trigger] m.cat2(x, q);
    }
    assert(m.y_ok(false, t));
    assert(m.r_ops(t));
    lemma_uset_basic(m, false, t);
    lemma_uset_nset_closed(m, false, t);
    let us = m.uset(false, t);
    // Literals, products, and successors of q: (S5).
    assert forall|v: S| #[trigger] (m.lit)(q, v) implies us.contains(v) by {
        assert(m.lit_shape(q, v));
        assert forall|wv: S| m.star_lit(q, wv) implies us.contains(wv) by {
            let a = choose|a: S| #[trigger] (m.prod)((m.body)(q), a) && wv == m.cat2(a, q);
            assert(rp.contains(a));
            assert(t.contains(cq(a)));
        }
        assert(m.built(false, |wv: S| m.star_lit(q, wv), v));
        assert(us.contains(v));
    }
    assert forall|v: S| #[trigger] (m.prod)(q, v) implies us.contains(v) by { assert(m.prod_shape(q, v)); }
    assert forall|v: S| #[trigger] (m.succ)(q, v) implies us.contains(v) by {
        assert(m.succ_shape(q, v));
        assert forall|wv: S| (m.prod)(q, wv) implies us.contains(wv) by {}
        assert(m.built(false, |wv: S| (m.prod)(q, wv), v));
        assert(us.contains(v));
    }
    // (C4) for the lists of T, relative to U(T).
    assert forall|y: S| t.contains(y) && m.k(y) == Kind::List implies #[trigger] m.list_in(y, us) by {
        let x = choose|x: S| rp.contains(x) && y == #[trigger] m.cat2(x, q);
        assert(x != m.empty && x != m.epsilon);
        let z = m.piece(x);
        lemma_piece_tails(m, rp, p, x);
        let es = (m.elems)(y);
        assert(es == z + w);
        assert forall|i: int, a: S| 0 <= i < es.len() && #[trigger] (m.prod)(es[i], a)
            implies us.contains((m.ncat)(seq![a] + es.skip(i + 1))) by {
            if i < z.len() {
                assert(es[i] == z[i]);
                assert(m.st(z[i]));
                assert(m.st(a));
                let zr = z.skip(i + 1);
                assert(m.atoms(zr)) by {
                    assert forall|h: int| 0 <= h < zr.len() implies m.atom(#[trigger] zr[h]) by { assert(zr[h] == z[i + 1 + h]); }
                }
                lemma_cat_assoc(m, a, zr, w);
                assert(seq![a] + es.skip(i + 1) =~= seq![a] + zr + w);
                assert(rp.contains((m.ncat)(seq![a] + zr)));
                assert(t.contains(cq((m.ncat)(seq![a] + zr))));
            } else {
                assert(es[i] == q);
                assert(m.st(a));
                assert(seq![a] + es.skip(i + 1) =~= seq![a]);
                lemma_cat_single(m, a);
            }
        }
    }
    // (C2) for T.
    assert forall|y: S| t.contains(y) implies {
        &&& forall|v: S| #[trigger] (m.succ)(y, v) ==> us.contains(v)
        &&& forall|v: S| #[trigger] (m.lit)(y, v) ==> us.contains(v)
        &&& forall|v: S| #[trigger] (m.prod)(y, v) ==> us.contains(v)
    } by {
        let x = choose|x: S| rp.contains(x) && y == #[trigger] m.cat2(x, q);
        if x == m.empty {
            lemma_base_vals(m, y);
        } else if x == m.epsilon {
        } else {
            assert(m.list_in(y, us));
            assert((m.elems)(y).last() == q);
            lemma_list_vals(m, y, us);
        }
    }
    assert(m.vals_into(t, us));
    lemma_uset_closed(m, t);
    lemma_uset_ops(m, false, t);
    lemma_uset_lists(m, false, t, us);
    assert(m.good(us, q));
}

/// Facts shared by the list-case lemmas.
pub open spec fn list_ctx<S>(m: Model<S>, q: S) -> bool {
    let c = (m.elems)(q);
    &&& m.contract() && m.st(q) && m.k(q) == Kind::List && m.atoms(c) && c.len() >= 2
    &&& forall|j: int| 0 <= j < c.len() ==> m.good(m.rset(#[trigger] c[j]), c[j])
    &&& forall|j: int| 0 <= j < c.len() ==> #[trigger] m.atoms(c.skip(j + 1))
}

/// `T` contains `N(x s_j)` for `x ∈ C(c_j)`.
pub proof fn lemma_list_term<S>(m: Model<S>, c: Seq<S>, j: int, x: S)
    requires 0 <= j < c.len(), m.rset(c[j]).contains(x),
    ensures m.list_terms(c).contains(m.cat2(x, m.suffix(c, j))),
{}

/// Shape of a member `N(x s_j)` of `T` with `j < m`.
pub proof fn lemma_list_term_shape<S>(m: Model<S>, q: S, j: int, x: S)
    requires list_ctx(m, q), 0 <= j < (m.elems)(q).len() - 1, m.rset((m.elems)(q)[j]).contains(x),
    ensures ({
        let c = (m.elems)(q);
        let y = m.cat2(x, m.suffix(c, j));
        &&& m.st(y)
        &&& (x == m.empty && y == m.empty)
            || (x == m.epsilon && j == c.len() - 2 && y == c[c.len() - 1])
            || (x != m.empty && m.k(y) == Kind::List && (m.elems)(y) == m.piece(x) + c.skip(j + 1)
                && (m.elems)(y).last() == c[c.len() - 1])
    }),
{
    let c = (m.elems)(q);
    let n = c.len() as int;
    let w = c.skip(j + 1);
    assert(m.good(m.rset(c[j]), c[j]));
    assert(m.st(x));
    assert(m.atoms(w));
    lemma_cat_pair(m, x, w);
    if x != m.empty {
        let z = m.piece(x);
        let es = z + w;
        assert(m.atoms(z)) by {
            if x == m.epsilon { assert(z =~= Seq::<S>::empty()); }
        }
        assert(m.atoms(es)) by {
            assert forall|h: int| 0 <= h < es.len() implies m.atom(#[trigger] es[h]) by {
                if h < z.len() { assert(es[h] == z[h]); } else { assert(es[h] == w[h - z.len()]); }
            }
        }
        lemma_cat_atoms(m, es);
        assert(es.last() == c[n - 1]);
        if es.len() == 1 {
            assert(z.len() == 0);
            assert(x == m.epsilon) by {
                if x != m.epsilon { assert(m.piece(x).len() >= 1); }
            }
            assert(w.len() == 1);
            assert(es[0] == c[n - 1]);
        }
    }
}

/// (C4) for a list `N(x s_j)` of `T` with `j < m`, relative to `T`.
pub proof fn lemma_list_member<S>(m: Model<S>, q: S, j: int, x: S)
    requires list_ctx(m, q), 0 <= j < (m.elems)(q).len() - 1, m.rset((m.elems)(q)[j]).contains(x),
        x != m.empty, m.k(m.cat2(x, m.suffix((m.elems)(q), j))) == Kind::List,
    ensures m.list_in(m.cat2(x, m.suffix((m.elems)(q), j)), m.list_terms((m.elems)(q))),
{
    let c = (m.elems)(q);
    let n = c.len() as int;
    let w = c.skip(j + 1);
    let rx = m.rset(c[j]);
    let tt = m.list_terms(c);
    let y = m.cat2(x, m.suffix(c, j));
    lemma_list_term_shape(m, q, j, x);
    assert(m.good(rx, c[j]));
    let z = m.piece(x);
    let es = (m.elems)(y);
    assert(es == z + w);
    if x != m.epsilon {
        lemma_piece_tails(m, rx, c[j], x);
    } else {
        assert(z =~= Seq::<S>::empty());
    }
    assert(m.atoms(w));
    assert forall|i: int, a: S| 0 <= i < es.len() && #[trigger] (m.prod)(es[i], a)
        implies tt.contains((m.ncat)(seq![a] + es.skip(i + 1))) by {
        if i < z.len() {
            assert(es[i] == z[i]);
            assert(m.atoms(z));
            assert(m.st(z[i]));
            assert(m.st(a));
            let zr = z.skip(i + 1);
            assert(m.atoms(zr)) by {
                assert forall|h: int| 0 <= h < zr.len() implies m.atom(#[trigger] zr[h]) by { assert(zr[h] == z[i + 1 + h]); }
            }
            lemma_cat_assoc(m, a, zr, w);
            assert(seq![a] + es.skip(i + 1) =~= seq![a] + zr + w);
            assert(rx.contains((m.ncat)(seq![a] + zr)));
            lemma_list_term(m, c, j, (m.ncat)(seq![a] + zr));
        } else {
            let k = j + 1 + (i - z.len());
            assert(es[i] == c[k]);
            assert(m.good(m.rset(c[k]), c[k]));
            assert(m.rset(c[k]).contains(c[k]));
            assert(m.rset(c[k]).contains(a));
            assert(m.st(a));
            let w2 = c.skip(k + 1);
            assert(m.atoms(w2));
            assert(es.skip(i + 1) =~= w2);
            lemma_cat_assoc(m, a, Seq::<S>::empty(), w2);
            assert(seq![a] + Seq::<S>::empty() + w2 =~= seq![a] + w2);
            assert(seq![a] + Seq::<S>::empty() =~= seq![a]);
            lemma_cat_single(m, a);
            lemma_list_term(m, c, k, a);
        }
    }
}

pub proof fn lemma_good_list<S>(m: Model<S>, q: S)
    requires m.contract(), m.st(q), m.k(q) == Kind::List,
        forall|j: int| 0 <= j < (m.elems)(q).len() ==> m.good(m.rset(#[trigger] (m.elems)(q)[j]), (m.elems)(q)[j]),
    ensures m.good(m.rset(q), q),
{
    let c = (m.elems)(q);
    let n = c.len() as int;
    assert(n >= 2);
    assert(m.atoms(c));
    let t = m.list_terms(c);
    // T is finite.
    lemma_int_range(0, n);
    let f = |j: int| m.rset(c[j]).map(|x: S| m.cat2(x, m.suffix(c, j)));
    assert forall|j: int| set_int_range(0, n).contains(j) implies #[trigger] f(j).finite() by {
        m.rset(c[j]).lemma_map_finite(|x: S| m.cat2(x, m.suffix(c, j)));
    }
    lemma_big_union_finite(set_int_range(0, n), f);
    assert(t =~= ISet::new(|x: S| exists|j: int| set_int_range(0, n).contains(j) && #[trigger] f(j).contains(x))) by {
        assert forall|y: S| t.contains(y) implies exists|j: int| set_int_range(0, n).contains(j) && #[trigger] f(j).contains(y) by {
            let (j, x) = choose|j: int, x: S| 0 <= j < c.len() && m.rset(c[j]).contains(x)
                && y == #[trigger] m.cat2(x, m.suffix(c, j));
            assert(f(j).contains(y));
        }
        assert forall|y: S| (exists|j: int| set_int_range(0, n).contains(j) && #[trigger] f(j).contains(y)) implies t.contains(y) by {
            let j = choose|j: int| set_int_range(0, n).contains(j) && #[trigger] f(j).contains(y);
            let x = choose|x: S| m.rset(c[j]).contains(x) && y == m.cat2(x, m.suffix(c, j));
            assert(y == m.cat2(x, m.suffix(c, j)));
        }
    }
    // Suffix facts.
    assert forall|j: int| 0 <= j < n implies #[trigger] m.atoms(c.skip(j + 1)) by {
        assert forall|h: int| 0 <= h < c.skip(j + 1).len() implies m.atom(#[trigger] c.skip(j + 1)[h]) by {
            assert(c.skip(j + 1)[h] == c[j + 1 + h]);
        }
    }
    assert(list_ctx(m, q));
    assert(m.suffix(c, n - 1) == m.epsilon) by {
        assert(c.skip(n) =~= Seq::<S>::empty());
        assert(m.states(c.skip(n)));
        assert(m.cat_shape(c.skip(n)));
        assert(!m.has_empty(c.skip(n)));
    }
    // q ∈ T.
    assert(t.contains(q)) by {
        assert(m.good(m.rset(c[0]), c[0]));
        assert(m.rset(c[0]).contains(c[0]));
        assert(m.atoms(c.skip(0int + 1)));
        assert(m.atom(c[0]));
        lemma_cat_pair(m, c[0], c.skip(1));
        assert(m.piece(c[0]) + c.skip(1) =~= c);
        assert(m.fixpoints_ok());
        assert((m.ncat)(c) == q);
        assert(m.cat2(c[0], m.suffix(c, 0)) == q);
        lemma_list_term(m, c, 0, c[0]);
    }
    // Level-(m-1) members are C(c_m).
    let rl = m.rset(c[n - 1]);
    assert(m.good(rl, c[n - 1]));
    assert forall|x: S| rl.contains(x) implies #[trigger] m.cat2(x, m.suffix(c, n - 1)) == x by {
        assert(m.st(x));
        assert(c.skip(n) =~= Seq::<S>::empty());
        lemma_cat_pair(m, x, c.skip(n));
        if x != m.empty && x != m.epsilon {
            assert(m.piece(x) + c.skip(n) =~= m.piece(x));
            lemma_cat_pair(m, x, seq![]);
            if m.k(x) == Kind::List {
                lemma_cat_atoms(m, m.piece(x));
                lemma_list_unique(m, (m.ncat)(m.piece(x)), x);
            } else {
                lemma_cat_atoms(m, m.piece(x));
            }
        }
    }
    assert forall|x: S| rl.contains(x) implies t.contains(x) by {
        assert(m.cat2(x, m.suffix(c, n - 1)) == x);
        lemma_list_term(m, c, n - 1, x);
    }
    // Classification of members of T.
    assert forall|y: S| t.contains(y) implies m.st(y) && (rl.contains(y) || y == m.empty || (m.k(y) == Kind::List
        && m.list_in(y, t) && (m.elems)(y).last() == c[n - 1])) by {
        let (j, x) = choose|j: int, x: S| 0 <= j < c.len() && m.rset(c[j]).contains(x)
            && y == #[trigger] m.cat2(x, m.suffix(c, j));
        if j == n - 1 {
            assert(m.cat2(x, m.suffix(c, n - 1)) == x);
            assert(m.good(m.rset(c[j]), c[j]));
        } else {
            lemma_list_term_shape(m, q, j, x);
            if x != m.empty && !(x == m.epsilon && j == n - 2) {
                lemma_list_member(m, q, j, x);
            }
        }
    }
    assert(m.r_states(t));
    assert(m.r_ops(t)) by {
        assert forall|y: S, o: S| t.contains(y) && (m.k(y) == Kind::Union || m.k(y) == Kind::Intersect)
            && #[trigger] (m.ops)(y).contains(o) implies t.contains(o) by {
            assert(rl.contains(y));
        }
        assert forall|y: S| t.contains(y) && m.k(y) == Kind::Not implies t.contains(#[trigger] (m.body)(y)) by {
            assert(rl.contains(y));
        }
    }
    assert(m.y_ok(false, t));
    lemma_uset_basic(m, false, t);
    lemma_uset_nset_closed(m, false, t);
    let us = m.uset(false, t);
    assert(m.r_lists_in(t, t)) by {
        assert forall|y: S| t.contains(y) && m.k(y) == Kind::List implies #[trigger] m.list_in(y, t) by {
            if rl.contains(y) {
                assert(m.list_in(y, rl));
                lemma_list_in_mono(m, y, rl, t);
            }
        }
    }
    // (C2) for T.
    assert forall|y: S| t.contains(y) implies {
        &&& forall|v: S| #[trigger] (m.succ)(y, v) ==> us.contains(v)
        &&& forall|v: S| #[trigger] (m.lit)(y, v) ==> us.contains(v)
        &&& forall|v: S| #[trigger] (m.prod)(y, v) ==> us.contains(v)
    } by {
        if rl.contains(y) {
            assert forall|v: S| #[trigger] (m.succ)(y, v) implies us.contains(v) by { assert(rl.contains(v)); }
            assert forall|v: S| #[trigger] (m.lit)(y, v) implies us.contains(v) by { assert(rl.contains(v)); }
            assert forall|v: S| #[trigger] (m.prod)(y, v) implies us.contains(v) by { assert(rl.contains(v)); }
        } else if y == m.empty {
            assert(m.constants_ok());
            lemma_base_vals(m, y);
        } else {
            lemma_list_in_mono(m, y, t, us);
            assert forall|v: S| #[trigger] (m.lit)((m.elems)(y).last(), v) implies us.contains(v) by { assert(rl.contains(v)); }
            assert forall|v: S| #[trigger] (m.prod)((m.elems)(y).last(), v) implies us.contains(v) by { assert(rl.contains(v)); }
            lemma_list_vals(m, y, us);
        }
    }
    assert(m.vals_into(t, us));
    lemma_uset_closed(m, t);
    lemma_uset_ops(m, false, t);
    lemma_lists_mono(m, t, t, us);
    lemma_uset_lists(m, false, t, us);
    assert(m.good(us, q));
}

pub proof fn lemma_finite_states<S>(m: Model<S>, q: S)
    requires m.contract(), m.st(q),
    ensures m.good(m.rset(q), q),
    decreases (m.size)(q),
{
    let kq = m.k(q);
    if m.base_kind(q) {
        lemma_good_base(m, q);
    } else if kq == Kind::Union || kq == Kind::Intersect {
        assert forall|o: S| #[trigger] (m.ops)(q).contains(o) implies m.good(m.rset(o), o) by {
            lemma_finite_states(m, o);
        }
        if kq == Kind::Union { lemma_good_union(m, q); } else { lemma_good_inter(m, q); }
    } else if kq == Kind::Not {
        lemma_finite_states(m, (m.body)(q));
        lemma_good_not(m, q);
    } else if kq == Kind::Star {
        lemma_finite_states(m, (m.body)(q));
        lemma_good_star(m, q);
    } else {
        let c = (m.elems)(q);
        assert forall|j: int| 0 <= j < c.len() implies m.good(m.rset(#[trigger] c[j]), c[j]) by {
            assert(m.atom(c[j]));
            lemma_finite_states(m, c[j]);
        }
        lemma_good_list(m, q);
    }
}

/// Paper Lemma `lem:finite-states`: for every state `q` there is a finite set, independent of
/// valuations and events, containing `q`, closed under all successors, and containing every state
/// reachable from `q`.
pub proof fn theorem_finite_reachable<S>(m: Model<S>, q: S) -> (r: Set<S>)
    requires m.contract(), m.st(q),
    ensures
        r.contains(q),
        forall|p: S| r.contains(p) ==> m.st(p),
        forall|p: S, v: S| r.contains(p) && #[trigger] (m.succ)(p, v) ==> r.contains(v),
        forall|n: nat, p: S| #[trigger] reachable(m, q, n, p) ==> r.contains(p),
{
    lemma_finite_states(m, q);
    let ri = m.rset(q);
    let r = Set::new_from_iset(ri).unwrap();
    assert(r.to_iset() == ri);
    assert(m.r_closed(ri));
    assert forall|n: nat, p: S| #[trigger] reachable(m, q, n, p) implies r.contains(p) by {
        lemma_reachable_in(m, q, ri, n, p);
    }
    r
}

pub proof fn lemma_reachable_in<S>(m: Model<S>, q: S, r: ISet<S>, n: nat, p: S)
    requires r.contains(q), m.r_closed(r), reachable(m, q, n, p),
    ensures r.contains(p),
    decreases n,
{
    if n > 0 {
        let p0 = choose|p0: S| reachable(m, q, (n - 1) as nat, p0) && #[trigger] (m.succ)(p0, p);
        lemma_reachable_in(m, q, r, (n - 1) as nat, p0);
    }
}

// ===== non-vacuity: a model satisfying the contract =====

/// States of a small model: the constants and lists of `Univ`.
pub enum Toy { Emp, Eps, Univ, Lst(Seq<Toy>) }

pub open spec fn toy_univs(s: Seq<Toy>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> #[trigger] s[i] == Toy::Univ
}

pub open spec fn toy_state(x: Toy) -> bool {
    match x { Toy::Lst(s) => s.len() >= 2 && toy_univs(s), _ => true }
}

pub open spec fn toy_kind(x: Toy) -> Kind {
    match x { Toy::Emp => Kind::Empty, Toy::Eps => Kind::Epsilon, Toy::Univ => Kind::Universal, Toy::Lst(_) => Kind::List }
}

pub open spec fn toy_elems(x: Toy) -> Seq<Toy> {
    match x { Toy::Lst(s) => s, _ => seq![] }
}

/// Successors, literals, and products of the small model coincide: `Univ` for `Univ`, else `∅`.
pub open spec fn toy_succ(p: Toy, v: Toy) -> bool {
    (p == Toy::Emp || p == Toy::Eps || p is Lst) && v == Toy::Emp || p == Toy::Univ && v == Toy::Univ
}

pub open spec fn toy_base() -> Model<Toy> {
    Model {
        state: |x: Toy| toy_state(x),
        kind: |x: Toy| toy_kind(x),
        ops: |x: Toy| Set::<Toy>::empty(),
        body: |x: Toy| Toy::Emp,
        elems: |x: Toy| toy_elems(x),
        size: |x: Toy| if x is Lst { 1nat } else { 0nat },
        empty: Toy::Emp,
        epsilon: Toy::Eps,
        universal: Toy::Univ,
        nset: |inter: bool, xs: Set<Toy>, u: Toy| u == Toy::Emp,
        nnot: |x: Toy| Toy::Emp,
        ncat: |xs: Seq<Toy>| Toy::Emp,
        combo: |inter: bool, ts: Set<Toy>, t: Toy| false,
        succ: |p: Toy, v: Toy| toy_succ(p, v),
        lit: |p: Toy, v: Toy| toy_succ(p, v),
        prod: |p: Toy, v: Toy| toy_succ(p, v),
    }
}

/// `N(x₁⋯xₖ)` of the small model, defined by (N4).
pub open spec fn toy_cat(xs: Seq<Toy>) -> Toy {
    let f = toy_base().flat(xs);
    if toy_base().has_empty(xs) { Toy::Emp } else if f.len() == 0 { Toy::Eps } else if f.len() == 1 { f[0] } else { Toy::Lst(f) }
}

pub open spec fn toy() -> Model<Toy> {
    Model { ncat: |xs: Seq<Toy>| toy_cat(xs), ..toy_base() }
}

pub proof fn lemma_toy_flat(xs: Seq<Toy>)
    requires forall|i: int| 0 <= i < xs.len() ==> toy_state(#[trigger] xs[i]),
    ensures
        !toy_base().has_empty(xs) ==> toy_univs(toy_base().flat(xs)),
        toy().flat(xs) == toy_base().flat(xs),
    decreases xs.len(),
{
    if xs.len() > 0 {
        let init = xs.drop_last();
        assert forall|i: int| 0 <= i < init.len() implies toy_state(#[trigger] init[i]) by { assert(init[i] == xs[i]); }
        lemma_toy_flat(init);
        if !toy_base().has_empty(xs) {
            assert(!toy_base().has_empty(init)) by {
                if toy_base().has_empty(init) {
                    let i = choose|i: int| 0 <= i < init.len() && init[i] == Toy::Emp;
                    assert(xs[i] == Toy::Emp);
                }
            }
            let f0 = toy_base().flat(init);
            let p = toy_base().piece(xs.last());
            assert(toy_state(xs[xs.len() - 1]));
            assert(xs[xs.len() - 1] != Toy::Emp);
            assert(toy_univs(p));
            assert forall|i: int| 0 <= i < (f0 + p).len() implies #[trigger] (f0 + p)[i] == Toy::Univ by {
                if i < f0.len() { assert((f0 + p)[i] == f0[i]); } else { assert((f0 + p)[i] == p[i - f0.len()]); }
            }
        }
    }
}

/// The contract is satisfiable, so `theorem_finite_reachable` is not vacuous.
pub proof fn lemma_contract_satisfiable()
    ensures toy().contract(),
{
    let m = toy();
    assert(m.constants_ok());
    assert(m.substates_ok());
    assert forall|xs: Seq<Toy>| m.states(xs) implies #[trigger] m.cat_shape(xs) by {
        lemma_toy_flat(xs);
    }
    assert(m.fixpoints_ok()) by {
        assert forall|x: Toy| m.st(x) && m.k(x) == Kind::List implies (m.ncat)(#[trigger] (m.elems)(x)) == x by {
            let s = toy_elems(x);
            assert forall|i: int| 0 <= i < s.len() implies toy_state(#[trigger] s[i]) by {}
            lemma_toy_flat(s);
            assert(m.flat(s) == s) by {
                assert forall|i: int| 0 <= i < s.len() implies m.atom(#[trigger] s[i]) by {}
                lemma_flat_atoms(m, s);
            }
            assert(!m.has_empty(s));
        }
    }
    assert(m.nset_ok()) by {
        assert forall|inter: bool, f: Set<Toy>| #[trigger] m.has_set_bound(inter, f) by {
            assert(m.set_states_within(inter, f, Set::empty()));
        }
    }
    assert(m.not_ok());
    assert(m.cat_ok());
    assert(m.tests_ok()) by {
        assert forall|inter: bool, ts: ISet<Toy>| ts.finite() && (forall|t: Toy| ts.contains(t) ==> m.is_test(t))
            implies #[trigger] m.has_closure(inter, ts) by {
            assert(m.closure_for(inter, ts, ts));
        }
    }
    assert(m.succ_ok()) by {
        assert forall|p: Toy, v: Toy| m.st(p) && #[trigger] (m.succ)(p, v) implies m.st(v) && m.succ_shape(p, v) by {
            if p is Lst { assert(m.built(false, |w: Toy| (m.prod)(p, w), v)); }
        }
        assert forall|p: Toy, v: Toy| m.st(p) && #[trigger] (m.lit)(p, v) implies m.st(v) && m.lit_shape(p, v) by {
            if p is Lst { assert(m.built(false, |w: Toy| m.list_lit(p, w), v)); }
        }
        assert forall|p: Toy, v: Toy| m.st(p) && #[trigger] (m.prod)(p, v) implies m.st(v) && m.prod_shape(p, v) by {}
    }
}

} // verus!
