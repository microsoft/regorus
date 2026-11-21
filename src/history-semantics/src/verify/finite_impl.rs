//! The finiteness model instantiated with the implementation's states (see `finiteness::instantiation_ok`).
//!
//! States are lifted trees `Regex<model::Test>` in *hereditary normal form* ([`regex_nf`]): set
//! operands are duplicate-free and not sets of the same kind, lists have at least two atoms,
//! complements wrap neither constants nor complements, and connective tests are flat and
//! duplicate-free. The constructors are the tree-level counterparts of the implemented ones:
//! `N(¬·)` is [`r_not`] (`normalize::verify::regex_not_result`), `N(x₁⋯xₖ)` is [`r_cat`]
//! (`regex_concat_result`), and since the implementation orders set operands by interning order,
//! `N(ΣX)`/`N(&X)` is the relation of all outputs allowed by (N1)/(N2) (`regex_set_shape`), and the
//! test combinations are all outputs allowed by `test_connective_result`. Literals, products, and
//! successors are the *largest* relations allowed by (S0)–(S6): `lit`/`prod` are the greatest
//! fixpoint of the successor equations ([`g_lit`], [`g_prod`]), characterized by
//! [`lemma_lit_fold`]/[`lemma_prod_fold`], and `succ` is every state allowed by (S0)/(S1).
//! [`theorem_impl_contract`] proves the contract.
use crate::verify::finite_states::*;
use alloc::boxed::Box;
use junco_core::kernel::verify as model;
use junco_core::verify::history_specs::Regex;
use vstd::iset_lib::lemma_iset_subset_finite;
use vstd::prelude::*;

verus! {

pub type R = Regex<model::Test>;

// ===== hereditary normal forms =====

/// `phi` is in the piece contributed by `psi` to a flattened `∧` (`inter`) or `∨`.
pub open spec fn test_piece(inter: bool, psi: model::Test, phi: model::Test) -> bool {
    match psi {
        model::Test::And(cs) => if inter { cs.contains(phi) } else { phi == psi },
        model::Test::Or(cs) => if !inter { cs.contains(phi) } else { phi == psi },
        _ => phi == psi,
    }
}

pub open spec fn is_conn(inter: bool, t: model::Test) -> bool {
    if inter { t is And } else { t is Or }
}

pub open spec fn test_kids(t: model::Test) -> Seq<model::Test> {
    match t { model::Test::And(cs) => cs, model::Test::Or(cs) => cs, _ => seq![] }
}

pub open spec fn test_nf(t: model::Test) -> bool
    decreases t,
{
    match t {
        model::Test::And(cs) => cs.no_duplicates()
            && forall|i: int| 0 <= i < cs.len() ==> test_nf(#[trigger] cs[i]) && !(cs[i] is And),
        model::Test::Or(cs) => cs.no_duplicates()
            && forall|i: int| 0 <= i < cs.len() ==> test_nf(#[trigger] cs[i]) && !(cs[i] is Or),
        _ => true,
    }
}

pub open spec fn regex_nf(r: R) -> bool
    decreases r,
{
    match r {
        Regex::Test(t) => test_nf(t),
        Regex::Union(cs) => cs.no_duplicates()
            && forall|i: int| 0 <= i < cs.len() ==> regex_nf(#[trigger] cs[i]) && !(cs[i] is Union),
        Regex::Intersect(cs) => cs.no_duplicates()
            && forall|i: int| 0 <= i < cs.len() ==> regex_nf(#[trigger] cs[i]) && !(cs[i] is Intersect),
        Regex::Concat(cs) => cs.len() >= 2
            && forall|i: int| 0 <= i < cs.len() ==> regex_nf(#[trigger] cs[i])
                && !(cs[i] is Concat || cs[i] is Epsilon || cs[i] is Empty),
        Regex::Star(b) => regex_nf(*b),
        Regex::Not(b) => regex_nf(*b) && !(*b is Empty || *b is All || *b is Not),
        _ => true,
    }
}

pub open spec fn r_kind(r: R) -> Kind {
    match r {
        Regex::Empty => Kind::Empty, Regex::Epsilon => Kind::Epsilon, Regex::All => Kind::Universal,
        Regex::Test(_) => Kind::Test, Regex::Union(_) => Kind::Union, Regex::Intersect(_) => Kind::Intersect,
        Regex::Not(_) => Kind::Not, Regex::Star(_) => Kind::Star, Regex::Concat(_) => Kind::List,
    }
}

pub open spec fn r_ops(r: R) -> Set<R> {
    match r { Regex::Union(cs) => cs.to_set(), Regex::Intersect(cs) => cs.to_set(), _ => Set::empty() }
}

pub open spec fn r_body(r: R) -> R {
    match r { Regex::Star(b) => *b, Regex::Not(b) => *b, _ => Regex::Empty }
}

pub open spec fn r_elems(r: R) -> Seq<R> {
    match r { Regex::Concat(cs) => cs, _ => seq![] }
}

pub open spec fn r_size(r: R) -> nat
    decreases r, 1nat, 0nat,
{
    match r {
        Regex::Union(cs) => 1 + r_sum(r, cs.len()),
        Regex::Intersect(cs) => 1 + r_sum(r, cs.len()),
        Regex::Concat(cs) => 1 + r_sum(r, cs.len()),
        Regex::Star(b) => 1 + r_size(*b),
        Regex::Not(b) => 1 + r_size(*b),
        _ => 1,
    }
}

/// Sum of the sizes of the first `n` children of a set or list.
pub open spec fn r_sum(r: R, n: nat) -> nat
    decreases r, 0nat, n,
{
    match r {
        Regex::Union(cs) => if 0 < n <= cs.len() { r_sum(r, (n - 1) as nat) + r_size(cs[n - 1]) } else { 0 },
        Regex::Intersect(cs) => if 0 < n <= cs.len() { r_sum(r, (n - 1) as nat) + r_size(cs[n - 1]) } else { 0 },
        Regex::Concat(cs) => if 0 < n <= cs.len() { r_sum(r, (n - 1) as nat) + r_size(cs[n - 1]) } else { 0 },
        _ => 0,
    }
}

/// `N(¬x)` (`regex_not_result`).
pub open spec fn r_not(x: R) -> R {
    match x { Regex::Empty => Regex::All, Regex::All => Regex::Empty, Regex::Not(b) => *b, _ => Regex::Not(Box::new(x)) }
}

/// `phi` is a piece of the test of some member of `us`.
pub open spec fn piece_of(inter: bool, us: Set<R>, phi: model::Test) -> bool {
    exists|psi: model::Test| us.contains(Regex::Test(psi)) && #[trigger] test_piece(inter, psi, phi)
}

/// Test combinations allowed by `test_connective_result`: `⊤`, `⊥`, a piece of an input, or a
/// connective over pieces of the inputs.
pub open spec fn test_combo(inter: bool, us: Set<R>, phi: model::Test) -> bool {
    ||| phi == model::Test::True
    ||| phi == model::Test::False
    ||| piece_of(inter, us, phi)
    ||| is_conn(inter, phi) && forall|k: int| 0 <= k < test_kids(phi).len() ==> piece_of(inter, us, #[trigger] test_kids(phi)[k])
}

pub open spec fn r_combo(inter: bool, us: Set<R>, t: R) -> bool {
    regex_nf(t) && match t { Regex::Test(phi) => test_combo(inter, us, phi), _ => false }
}

/// The model without its relations (placeholders), used to define them.
pub open spec fn pre() -> Model<R> {
    Model {
        state: |x: R| regex_nf(x),
        kind: |x: R| r_kind(x),
        ops: |x: R| r_ops(x),
        body: |x: R| r_body(x),
        elems: |x: R| r_elems(x),
        size: |x: R| r_size(x),
        empty: Regex::Empty,
        epsilon: Regex::Epsilon,
        universal: Regex::All,
        nset: |inter: bool, xs: Set<R>, u: R| false,
        nnot: |x: R| r_not(x),
        ncat: |xs: Seq<R>| Regex::Empty,
        combo: |inter: bool, us: Set<R>, t: R| r_combo(inter, us, t),
        succ: |p: R, v: R| false,
        lit: |p: R, v: R| false,
        prod: |p: R, v: R| false,
    }
}

/// `N(x₁⋯xₖ)` (`regex_concat_result`), defined by (N4).
pub open spec fn r_cat(xs: Seq<R>) -> R {
    let f = pre().flat(xs);
    if pre().has_empty(xs) { Regex::Empty } else if f.len() == 0 { Regex::Epsilon } else if f.len() == 1 { f[0] } else { Regex::Concat(f) }
}

/// Normal forms and constructors; the set constructor relates `X` to every output allowed by (N1)/(N2).
pub open spec fn core() -> Model<R> {
    Model {
        nset: |inter: bool, xs: Set<R>, u: R| pre().nset_shape(inter, xs, u),
        ncat: |xs: Seq<R>| r_cat(xs),
        ..pre()
    }
}

pub open spec fn with_rel(l: spec_fn(R, R) -> bool, p: spec_fn(R, R) -> bool) -> Model<R> {
    Model { lit: l, prod: p, ..core() }
}

/// `(l, p)` satisfies the successor equations (S1)–(S6): a post-fixpoint.
pub open spec fn consistent(l: spec_fn(R, R) -> bool, p: spec_fn(R, R) -> bool) -> bool {
    &&& forall|a: R, v: R| regex_nf(a) && #[trigger] l(a, v) ==> regex_nf(v) && with_rel(l, p).lit_shape(a, v)
    &&& forall|a: R, v: R| regex_nf(a) && #[trigger] p(a, v) ==> regex_nf(v) && with_rel(l, p).prod_shape(a, v)
}

/// The largest literal relation allowed by (S1)–(S6).
pub open spec fn g_lit(a: R, v: R) -> bool {
    exists|l: spec_fn(R, R) -> bool, p: spec_fn(R, R) -> bool| #[trigger] consistent(l, p) && l(a, v)
}

/// The largest product relation allowed by (S1)–(S6).
pub open spec fn g_prod(a: R, v: R) -> bool {
    exists|l: spec_fn(R, R) -> bool, p: spec_fn(R, R) -> bool| #[trigger] consistent(l, p) && p(a, v)
}

pub open spec fn m_gfp() -> Model<R> {
    with_rel(|a: R, v: R| g_lit(a, v), |a: R, v: R| g_prod(a, v))
}

/// The largest successor relation allowed by (S0)/(S1).
pub open spec fn g_succ(a: R, v: R) -> bool {
    regex_nf(v) && m_gfp().succ_shape(a, v)
}

/// The implementation's model.
pub open spec fn m_impl() -> Model<R> {
    Model { succ: |a: R, v: R| g_succ(a, v), ..m_gfp() }
}

// ===== sizes =====

pub proof fn lemma_sum_ge(r: R, n: nat, i: int)
    requires 0 <= i < n, n <= r_elems_or_ops(r).len(),
    ensures r_size(r_elems_or_ops(r)[i]) <= r_sum(r, n),
    decreases n,
{
    if i < n - 1 { lemma_sum_ge(r, (n - 1) as nat, i); }
}

pub open spec fn r_elems_or_ops(r: R) -> Seq<R> {
    match r { Regex::Union(cs) => cs, Regex::Intersect(cs) => cs, Regex::Concat(cs) => cs, _ => seq![] }
}

pub proof fn lemma_child_smaller(r: R, i: int)
    requires 0 <= i < r_elems_or_ops(r).len(),
    ensures r_size(r_elems_or_ops(r)[i]) < r_size(r),
{
    lemma_sum_ge(r, r_elems_or_ops(r).len(), i);
}

// ===== sequences over a finite set =====

pub open spec fn seqs_over<A>(d: Set<A>, n: nat) -> ISet<Seq<A>> {
    ISet::new(|s: Seq<A>| s.len() <= n && forall|i: int| 0 <= i < s.len() ==> d.contains(#[trigger] s[i]))
}

pub open spec fn pusher<A>(base: ISet<Seq<A>>) -> spec_fn(A) -> ISet<Seq<A>> {
    |x: A| base.map(|s: Seq<A>| s.push(x))
}

pub proof fn lemma_seqs_over_finite<A>(d: Set<A>, n: nat)
    ensures seqs_over(d, n).finite(),
    decreases n,
{
    broadcast use vstd::iset::lemma_iset_union_finite, vstd::iset::lemma_iset_empty_finite, vstd::iset::lemma_iset_insert_finite;
    if n == 0 {
        assert(seqs_over(d, 0) =~= ISet::empty().insert(Seq::<A>::empty())) by {
            assert forall|s: Seq<A>| seqs_over(d, 0).contains(s) implies s == Seq::<A>::empty() by {
                assert(s =~= Seq::<A>::empty());
            }
        }
    } else {
        let base = seqs_over(d, (n - 1) as nat);
        lemma_seqs_over_finite(d, (n - 1) as nat);
        let mk = pusher(base);
        assert forall|x: A| d.contains(x) implies #[trigger] mk(x).finite() by {
            base.lemma_map_finite(|s: Seq<A>| s.push(x));
        }
        lemma_big_union_finite(d, mk);
        let big = ISet::new(|s: Seq<A>| exists|x: A| d.contains(x) && #[trigger] mk(x).contains(s));
        assert forall|s: Seq<A>| seqs_over(d, n).contains(s) implies base.union(big).contains(s) by {
            if s.len() > 0 {
                let init = s.drop_last();
                let x = s.last();
                assert(base.contains(init)) by {
                    assert forall|i: int| 0 <= i < init.len() implies d.contains(#[trigger] init[i]) by { assert(init[i] == s[i]); }
                }
                assert(init.push(x) =~= s);
                assert(d.contains(s[s.len() - 1]));
                assert(mk(x).contains(s));
            } else {
                assert(base.contains(s));
            }
        }
        lemma_iset_subset_finite(base.union(big), seqs_over(d, n));
    }
}

/// A duplicate-free sequence over `d` is no longer than `d`.
pub proof fn lemma_nodup_len<A>(s: Seq<A>, d: Set<A>)
    requires s.no_duplicates(), forall|i: int| 0 <= i < s.len() ==> d.contains(#[trigger] s[i]),
    ensures s.len() <= d.len(),
{
    broadcast use vstd::prelude::Seq::to_set_ensures;
    s.unique_seq_to_set();
    assert(s.to_set().subset_of(d)) by {
        assert forall|a: A| s.to_set().contains(a) implies d.contains(a) by {
            let i = choose|i: int| 0 <= i < s.len() && s[i] == a;
        }
    }
    vstd::set_lib::lemma_len_subset(s.to_set(), d);
}

// ===== the contract =====

pub proof fn lemma_models_agree()
    ensures
        m_impl().state == pre().state, m_impl().kind == pre().kind, m_impl().ops == pre().ops,
        m_impl().body == pre().body, m_impl().elems == pre().elems, m_impl().size == pre().size,
        m_impl().empty == pre().empty, m_impl().epsilon == pre().epsilon, m_impl().universal == pre().universal,
        m_impl().nnot == pre().nnot, m_impl().combo == pre().combo,
        m_impl().nset == core().nset, m_impl().ncat == core().ncat,
        m_impl().lit == m_gfp().lit, m_impl().prod == m_gfp().prod,
{}

/// `flat` reads only kinds, list elements, and `ε`.
pub proof fn lemma_flat_agree(m1: Model<R>, m2: Model<R>, xs: Seq<R>)
    requires m1.kind == m2.kind, m1.elems == m2.elems, m1.epsilon == m2.epsilon,
    ensures m1.flat(xs) == m2.flat(xs),
    decreases xs.len(),
{
    if xs.len() > 0 { lemma_flat_agree(m1, m2, xs.drop_last()); }
}

/// Without `∅`, the flattening of states consists of atoms.
pub proof fn lemma_pre_flat_atoms(xs: Seq<R>)
    requires forall|i: int| 0 <= i < xs.len() ==> regex_nf(#[trigger] xs[i]), !pre().has_empty(xs),
    ensures pre().atoms(pre().flat(xs)),
    decreases xs.len(),
{
    let m = pre();
    if xs.len() > 0 {
        let init = xs.drop_last();
        let x = xs.last();
        assert(!m.has_empty(init)) by {
            if m.has_empty(init) {
                let i = choose|i: int| 0 <= i < init.len() && init[i] == m.empty;
                assert(xs[i] == m.empty);
            }
        }
        assert forall|i: int| 0 <= i < init.len() implies regex_nf(#[trigger] init[i]) by { assert(init[i] == xs[i]); }
        lemma_pre_flat_atoms(init);
        assert(regex_nf(xs[xs.len() - 1]));
        assert(x != m.empty) by { assert(xs[xs.len() - 1] == x); }
        assert(m.atoms(m.piece(x))) by {
            if m.k(x) == Kind::List {
                let es = r_elems(x);
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

pub proof fn lemma_impl_substates()
    ensures m_impl().substates_ok(),
{
    let m = m_impl();
    lemma_models_agree();
    broadcast use vstd::prelude::Seq::to_set_ensures;
    assert forall|x: R, o: R| m.st(x) && (m.k(x) == Kind::Union || m.k(x) == Kind::Intersect)
        && #[trigger] (m.ops)(x).contains(o) implies m.st(o) && (m.size)(o) < (m.size)(x) by {
        let cs = r_elems_or_ops(x);
        assert(cs.contains(o));
        let i = choose|i: int| 0 <= i < cs.len() && cs[i] == o;
        lemma_child_smaller(x, i);
    }
    assert forall|x: R| m.st(x) && (m.k(x) == Kind::Not || m.k(x) == Kind::Star)
        implies m.st(#[trigger] (m.body)(x)) && (m.size)((m.body)(x)) < (m.size)(x) by {}
    assert forall|x: R| m.st(x) && m.k(x) == Kind::List implies {
        let es = #[trigger] (m.elems)(x);
        es.len() >= 2 && forall|i: int| 0 <= i < es.len() ==> m.atom(#[trigger] es[i]) && (m.size)(es[i]) < (m.size)(x)
    } by {
        let es = r_elems(x);
        assert forall|i: int| 0 <= i < es.len() implies m.atom(#[trigger] es[i]) && (m.size)(es[i]) < (m.size)(x) by {
            lemma_child_smaller(x, i);
        }
    }
}

pub proof fn lemma_impl_fixpoints()
    ensures m_impl().fixpoints_ok(),
{
    let m = m_impl();
    lemma_models_agree();
    assert forall|x: R| m.st(x) && m.k(x) == Kind::List implies (m.ncat)(#[trigger] (m.elems)(x)) == x by {
        let es = r_elems(x);
        assert(pre().atoms(es)) by {
            assert forall|i: int| 0 <= i < es.len() implies pre().atom(#[trigger] es[i]) by {}
        }
        lemma_flat_atoms(pre(), es);
        assert(!pre().has_empty(es)) by {
            if pre().has_empty(es) {
                let i = choose|i: int| 0 <= i < es.len() && es[i] == pre().empty;
                assert(pre().atom(es[i]));
            }
        }
    }
    assert forall|x: R| m.st(x) && m.k(x) == Kind::Not implies (m.nnot)(#[trigger] (m.body)(x)) == x by {}
}

pub proof fn lemma_impl_not()
    ensures m_impl().not_ok(),
{
    let m = m_impl();
    lemma_models_agree();
    assert forall|x: R| m.st(x) implies #[trigger] m.not_shape(x) by {}
}

pub proof fn lemma_impl_cat()
    ensures m_impl().cat_ok(),
{
    let m = m_impl();
    lemma_models_agree();
    assert forall|xs: Seq<R>| m.states(xs) implies #[trigger] m.cat_shape(xs) by {
        lemma_flat_agree(m, pre(), xs);
        assert(m.has_empty(xs) == pre().has_empty(xs));
        if !pre().has_empty(xs) {
            assert forall|i: int| 0 <= i < xs.len() implies regex_nf(#[trigger] xs[i]) by { assert(m.st(xs[i])); }
            lemma_pre_flat_atoms(xs);
            let f = pre().flat(xs);
            if f.len() == 1 {
                assert(pre().atom(f[0]));
            } else if f.len() >= 2 {
                assert forall|i: int| 0 <= i < f.len() implies regex_nf(#[trigger] f[i])
                    && !(f[i] is Concat || f[i] is Epsilon || f[i] is Empty) by {
                    assert(pre().atom(f[i]));
                }
                assert(regex_nf(Regex::Concat(f)));
            }
        }
    }
}

pub proof fn lemma_impl_nset()
    ensures m_impl().nset_ok(),
{
    let m = m_impl();
    lemma_models_agree();
    assert forall|inter: bool, xs: Set<R>, u: R| (forall|x: R| xs.contains(x) ==> m.st(x))
        && #[trigger] (m.nset)(inter, xs, u) implies m.nset_shape(inter, xs, u) by {
        assert(pre().nset_shape(inter, xs, u));
        lemma_nset_shape_agree(pre(), m, inter, xs, u);
    }
    assert forall|inter: bool, f: Set<R>| #[trigger] m.has_set_bound(inter, f) by {
        lemma_set_bound(inter, f);
    }
}

pub open spec fn set_node(inter: bool, cs: Seq<R>) -> R {
    if inter { Regex::Intersect(cs) } else { Regex::Union(cs) }
}

pub proof fn lemma_set_bound(inter: bool, f: Set<R>)
    ensures m_impl().has_set_bound(inter, f),
{
    broadcast use vstd::prelude::Seq::to_set_ensures, vstd::set::lemma_set_new_from_iset;
    let m = m_impl();
    lemma_models_agree();
    let sq = seqs_over(f, f.len());
    lemma_seqs_over_finite(f, f.len());
    let img = sq.map(|cs: Seq<R>| set_node(inter, cs));
    sq.lemma_map_finite(|cs: Seq<R>| set_node(inter, cs));
    let g = Set::new_from_iset(img).unwrap();
    assert(g.to_iset() == img);
    assert forall|x: R| m.st(x) && m.is_set(inter, x) && (m.ops)(x).subset_of(f) implies #[trigger] g.contains(x) by {
        let cs = r_elems_or_ops(x);
        assert forall|i: int| 0 <= i < cs.len() implies f.contains(#[trigger] cs[i]) by {
            assert(cs.to_set().contains(cs[i]));
        }
        lemma_nodup_len(cs, f);
        assert(sq.contains(cs));
        assert(set_node(inter, cs) == x);
        assert(img.contains(x));
    }
    assert(m.set_states_within(inter, f, g));
}

// ----- (N5) -----

/// Pieces of the tests of `ts`, with `⊤` and `⊥`.
pub open spec fn piece_set(inter: bool, ts: ISet<R>) -> ISet<model::Test> {
    ISet::new(|phi: model::Test| phi == model::Test::True || phi == model::Test::False
        || exists|psi: model::Test| ts.contains(Regex::Test(psi)) && #[trigger] test_piece(inter, psi, phi))
}

pub open spec fn test_closure(inter: bool, ts: ISet<R>) -> ISet<R> {
    ISet::new(|t: R| regex_nf(t) && match t {
        Regex::Test(phi) => ts.contains(t) || piece_set(inter, ts).contains(phi)
            || (is_conn(inter, phi) && forall|k: int| 0 <= k < test_kids(phi).len()
                ==> piece_set(inter, ts).contains(#[trigger] test_kids(phi)[k])),
        _ => false,
    })
}

pub open spec fn test_pieces_of(inter: bool, psi: model::Test) -> ISet<model::Test> {
    ISet::new(|phi: model::Test| test_piece(inter, psi, phi))
}

pub proof fn lemma_test_pieces_finite(inter: bool, psi: model::Test)
    ensures test_pieces_of(inter, psi).finite(),
{
    broadcast use vstd::prelude::Seq::to_set_ensures, vstd::set::lemma_to_iset_finite,
        vstd::iset::lemma_iset_insert_finite, vstd::iset::lemma_iset_empty_finite;
    let k = test_kids(psi).to_set().to_iset();
    let one = ISet::<model::Test>::empty().insert(psi);
    assert forall|phi: model::Test| test_pieces_of(inter, psi).contains(phi) implies k.union(one).contains(phi) by {
        match psi {
            model::Test::And(cs) => { if inter { assert(test_kids(psi).contains(phi)); } },
            model::Test::Or(cs) => { if !inter { assert(test_kids(psi).contains(phi)); } },
            _ => {},
        }
    }
    vstd::iset::lemma_iset_union_finite(k, one);
    lemma_iset_subset_finite(k.union(one), test_pieces_of(inter, psi));
}

pub open spec fn regex_test_of(t: R) -> model::Test {
    match t { Regex::Test(phi) => phi, _ => model::Test::False }
}

pub proof fn lemma_piece_set_finite(inter: bool, ts: ISet<R>)
    requires ts.finite(),
    ensures piece_set(inter, ts).finite(),
{
    broadcast use vstd::set::lemma_set_new_from_iset, vstd::iset::lemma_iset_union_finite,
        vstd::iset::lemma_iset_insert_finite, vstd::iset::lemma_iset_empty_finite;
    let tset = Set::new_from_iset(ts).unwrap();
    assert(tset.to_iset() == ts);
    let mk = |t: R| test_pieces_of(inter, regex_test_of(t));
    assert forall|t: R| tset.contains(t) implies #[trigger] mk(t).finite() by {
        lemma_test_pieces_finite(inter, regex_test_of(t));
    }
    lemma_big_union_finite(tset, mk);
    let big = ISet::new(|phi: model::Test| exists|t: R| tset.contains(t) && #[trigger] mk(t).contains(phi));
    let consts = ISet::<model::Test>::empty().insert(model::Test::True).insert(model::Test::False);
    assert forall|phi: model::Test| piece_set(inter, ts).contains(phi) implies big.union(consts).contains(phi) by {
        if phi != model::Test::True && phi != model::Test::False {
            let psi = choose|psi: model::Test| ts.contains(Regex::Test(psi)) && #[trigger] test_piece(inter, psi, phi);
            let t = Regex::Test(psi);
            assert(tset.contains(t));
            assert(mk(t).contains(phi));
        }
    }
    lemma_iset_subset_finite(big.union(consts), piece_set(inter, ts));
}

pub open spec fn conn_node(inter: bool, ks: Seq<model::Test>) -> R {
    Regex::Test(if inter { model::Test::And(ks) } else { model::Test::Or(ks) })
}

pub proof fn lemma_test_closure_finite(inter: bool, ts: ISet<R>)
    requires ts.finite(),
    ensures test_closure(inter, ts).finite(),
{
    broadcast use vstd::set::lemma_set_new_from_iset, vstd::iset::lemma_iset_union_finite;
    lemma_piece_set_finite(inter, ts);
    let ps = piece_set(inter, ts);
    let pset = Set::new_from_iset(ps).unwrap();
    assert(pset.to_iset() == ps);
    let singles = ps.map(|phi: model::Test| Regex::Test(phi));
    ps.lemma_map_finite(|phi: model::Test| Regex::Test(phi));
    lemma_seqs_over_finite(pset, pset.len());
    let sq = seqs_over(pset, pset.len());
    let conns = sq.map(|ks: Seq<model::Test>| conn_node(inter, ks));
    sq.lemma_map_finite(|ks: Seq<model::Test>| conn_node(inter, ks));
    let all = ts.union(singles).union(conns);
    assert forall|t: R| test_closure(inter, ts).contains(t) implies all.contains(t) by {
        let phi = regex_test_of(t);
        assert(t == Regex::Test(phi));
        if ts.contains(t) {
        } else if ps.contains(phi) {
            assert(singles.contains(t));
        } else {
            let ks = test_kids(phi);
            assert forall|i: int| 0 <= i < ks.len() implies pset.contains(#[trigger] ks[i]) by {}
            assert(test_nf(phi));
            assert(ks.no_duplicates());
            lemma_nodup_len(ks, pset);
            assert(sq.contains(ks));
            assert(conn_node(inter, ks) == t);
            assert(conns.contains(t));
        }
    }
    lemma_iset_subset_finite(all, test_closure(inter, ts));
}

/// A piece of a member of the closure is in the piece set.
pub proof fn lemma_closure_pieces(inter: bool, ts: ISet<R>, psi: model::Test, phi: model::Test)
    requires
        forall|t: R| ts.contains(t) ==> m_impl().is_test(t),
        test_closure(inter, ts).contains(Regex::Test(psi)),
        test_piece(inter, psi, phi),
    ensures piece_set(inter, ts).contains(phi),
{
    lemma_models_agree();
    let ps = piece_set(inter, ts);
    let t = Regex::Test(psi);
    if ts.contains(t) {
    } else if ps.contains(psi) {
        // `psi` is ⊤, ⊥, or a piece of a test of `ts`; its own pieces are itself.
        if psi != model::Test::True && psi != model::Test::False {
            let psi0 = choose|psi0: model::Test| ts.contains(Regex::Test(psi0)) && #[trigger] test_piece(inter, psi0, psi);
            assert(m_impl().is_test(Regex::Test(psi0)));
            assert(regex_nf(Regex::Test(psi0)));
            assert(test_nf(psi0));
            match psi0 {
                model::Test::And(cs) => {
                    if inter {
                        let i = choose|i: int| 0 <= i < cs.len() && cs[i] == psi;
                        assert(!(cs[i] is And));
                    }
                },
                model::Test::Or(cs) => {
                    if !inter {
                        let i = choose|i: int| 0 <= i < cs.len() && cs[i] == psi;
                        assert(!(cs[i] is Or));
                    }
                },
                _ => {},
            }
            assert(phi == psi);
        }
    } else {
        assert(is_conn(inter, psi));
        let ks = test_kids(psi);
        assert(ks.contains(phi));
        let k = choose|k: int| 0 <= k < ks.len() && ks[k] == phi;
        assert(ps.contains(ks[k]));
    }
}

pub proof fn lemma_impl_tests()
    ensures m_impl().tests_ok(),
{
    let m = m_impl();
    lemma_models_agree();
    assert forall|inter: bool, ts: ISet<R>| ts.finite() && (forall|t: R| ts.contains(t) ==> m.is_test(t))
        implies #[trigger] m.has_closure(inter, ts) by {
        let c = test_closure(inter, ts);
        lemma_test_closure_finite(inter, ts);
        let ps = piece_set(inter, ts);
        assert(ts.subset_of(c)) by {
            assert forall|t: R| ts.contains(t) implies c.contains(t) by { assert(m.is_test(t)); }
        }
        assert forall|t: R| c.contains(t) implies m.is_test(t) by {}
        assert forall|us: Set<R>, t: R| (forall|u: R| us.contains(u) ==> c.contains(u))
            && #[trigger] (m.combo)(inter, us, t) implies c.contains(t) by {
            assert(r_combo(inter, us, t));
            let phi = regex_test_of(t);
            assert(t == Regex::Test(phi));
            assert(test_combo(inter, us, phi));
            if phi == model::Test::True || phi == model::Test::False {
                assert(ps.contains(phi));
            } else if exists|psi: model::Test| us.contains(Regex::Test(psi)) && #[trigger] test_piece(inter, psi, phi) {
                let psi = choose|psi: model::Test| us.contains(Regex::Test(psi)) && #[trigger] test_piece(inter, psi, phi);
                lemma_closure_pieces(inter, ts, psi, phi);
            } else {
                let ks = test_kids(phi);
                assert forall|k: int| 0 <= k < ks.len() implies ps.contains(#[trigger] ks[k]) by {
                    let psi = choose|psi: model::Test| us.contains(Regex::Test(psi)) && #[trigger] test_piece(inter, psi, test_kids(phi)[k]);
                    lemma_closure_pieces(inter, ts, psi, ks[k]);
                }
            }
        }
        assert(m.closure_for(inter, ts, c));
    }
}

// ----- the greatest fixpoint -----

pub proof fn lemma_built_mono(m1: Model<R>, m2: Model<R>, inter: bool, b1: spec_fn(R) -> bool, b2: spec_fn(R) -> bool, v: R)
    requires
        m1.nset == m2.nset, m1.empty == m2.empty, m1.epsilon == m2.epsilon, m1.universal == m2.universal,
        forall|w: R| #[trigger] b1(w) ==> b2(w),
        m1.built(inter, b1, v),
    ensures m2.built(inter, b2, v),
{
    assert forall|u: ISet<R>| m2.has_consts(u) && (forall|w: R| #[trigger] b2(w) ==> u.contains(w))
        && m2.nset_closed(inter, u) implies #[trigger] u.contains(v) by {
        assert(m1.has_consts(u));
        assert(m1.nset_closed(inter, u));
        assert forall|w: R| #[trigger] b1(w) implies u.contains(w) by { assert(b2(w)); }
    }
}

/// Two models with the same states and constructors.
pub open spec fn core_same(m1: Model<R>, m2: Model<R>) -> bool {
    &&& m1.state == m2.state && m1.kind == m2.kind && m1.ops == m2.ops && m1.body == m2.body
    &&& m1.elems == m2.elems && m1.size == m2.size
    &&& m1.empty == m2.empty && m1.epsilon == m2.epsilon && m1.universal == m2.universal
    &&& m1.nset == m2.nset && m1.nnot == m2.nnot && m1.ncat == m2.ncat && m1.combo == m2.combo
}

/// The shapes are monotone in the literal and product relations.
pub proof fn lemma_shapes_mono_m(m1: Model<R>, m2: Model<R>, a: R, v: R)
    requires core_same(m1, m2),
        forall|x: R, y: R| #[trigger] (m1.lit)(x, y) ==> (m2.lit)(x, y),
        forall|x: R, y: R| #[trigger] (m1.prod)(x, y) ==> (m2.prod)(x, y),
    ensures
        m1.lit_shape(a, v) ==> m2.lit_shape(a, v),
        m1.prod_shape(a, v) ==> m2.prod_shape(a, v),
        m1.succ_shape(a, v) ==> m2.succ_shape(a, v),
{
    assert(m1.k(a) == m2.k(a) && m1.base_kind(a) == m2.base_kind(a) && m1.is_const(v) == m2.is_const(v));
    if m1.lit_shape(a, v) && !m1.base_kind(a) {
        if m1.k(a) == Kind::Union || m1.k(a) == Kind::Intersect {
            assert forall|w: R| #[trigger] m1.ops_lit(a, w) implies m2.ops_lit(a, w) by {
                let o = choose|o: R| (m1.ops)(a).contains(o) && #[trigger] (m1.lit)(o, w);
                assert((m2.lit)(o, w));
            }
            if m1.k(a) == Kind::Union {
                lemma_built_mono(m1, m2, false, |w: R| m1.ops_lit(a, w), |w: R| m2.ops_lit(a, w), v);
            } else {
                lemma_built_mono(m1, m2, true, |w: R| m1.ops_lit(a, w), |w: R| m2.ops_lit(a, w), v);
            }
        } else if m1.k(a) == Kind::Not {
            assert forall|w: R| #[trigger] m1.not_lit(a, w) implies m2.not_lit(a, w) by {
                let l = choose|l: R| #[trigger] (m1.lit)((m1.body)(a), l) && w == (m1.nnot)(l);
                assert((m2.lit)((m2.body)(a), l));
            }
            lemma_built_mono(m1, m2, true, |w: R| m1.not_lit(a, w), |w: R| m2.not_lit(a, w), v);
        } else if m1.k(a) == Kind::Star {
            assert forall|w: R| #[trigger] m1.star_lit(a, w) implies m2.star_lit(a, w) by {
                let b = choose|b: R| #[trigger] (m1.prod)((m1.body)(a), b) && w == m1.cat2(b, a);
                assert((m2.prod)((m2.body)(a), b));
                assert(m1.cat2(b, a) == m2.cat2(b, a));
            }
            lemma_built_mono(m1, m2, false, |w: R| m1.star_lit(a, w), |w: R| m2.star_lit(a, w), v);
        } else {
            assert forall|w: R| #[trigger] m1.list_lit(a, w) implies m2.list_lit(a, w) by {
                let es = (m1.elems)(a);
                assert(es == (m2.elems)(a));
                if exists|i: int, b: R| 0 <= i < es.len() - 1 && #[trigger] (m1.prod)(es[i], b)
                    && w == (m1.ncat)(seq![b] + es.skip(i + 1)) {
                    let (i, b) = choose|i: int, b: R| 0 <= i < es.len() - 1 && #[trigger] (m1.prod)(es[i], b)
                        && w == (m1.ncat)(seq![b] + es.skip(i + 1));
                    assert((m2.prod)(es[i], b));
                } else {
                    assert((m1.lit)(es.last(), w));
                    assert((m2.lit)(es.last(), w));
                }
            }
            lemma_built_mono(m1, m2, false, |w: R| m1.list_lit(a, w), |w: R| m2.list_lit(a, w), v);
        }
    }
    if m1.prod_shape(a, v) && !m1.base_kind(a) {
        if m1.k(a) == Kind::Intersect || m1.k(a) == Kind::Not {
            lemma_built_mono(m1, m2, true, |w: R| (m1.lit)(a, w), |w: R| (m2.lit)(a, w), v);
        } else if m1.k(a) == Kind::Union {
            if exists|o: R| (m1.ops)(a).contains(o) && #[trigger] (m1.prod)(o, v) {
                let o = choose|o: R| (m1.ops)(a).contains(o) && #[trigger] (m1.prod)(o, v);
                assert((m2.prod)(o, v));
            } else {
                assert((m1.lit)(a, v));
            }
        } else if m1.k(a) == Kind::Star {
            assert((m1.lit)(a, v));
        } else {
            if (m1.lit)(a, v) {
            } else {
                assert((m1.prod)((m1.elems)(a).last(), v));
                assert((m2.prod)((m2.elems)(a).last(), v));
            }
        }
    }
    if m1.succ_shape(a, v) && !m1.base_kind(a) {
        lemma_built_mono(m1, m2, false, |w: R| (m1.prod)(a, w), |w: R| (m2.prod)(a, w), v);
    }
}

pub proof fn lemma_shapes_mono(l1: spec_fn(R, R) -> bool, p1: spec_fn(R, R) -> bool,
    l2: spec_fn(R, R) -> bool, p2: spec_fn(R, R) -> bool, a: R, v: R)
    requires forall|x: R, y: R| #[trigger] l1(x, y) ==> l2(x, y), forall|x: R, y: R| #[trigger] p1(x, y) ==> p2(x, y),
    ensures
        with_rel(l1, p1).lit_shape(a, v) ==> with_rel(l2, p2).lit_shape(a, v),
        with_rel(l1, p1).prod_shape(a, v) ==> with_rel(l2, p2).prod_shape(a, v),
{
    lemma_shapes_mono_m(with_rel(l1, p1), with_rel(l2, p2), a, v);
}

/// `m_impl` and `m_gfp` have the same shapes.
pub proof fn lemma_impl_gfp_shapes(a: R, v: R)
    ensures
        m_impl().lit_shape(a, v) == m_gfp().lit_shape(a, v),
        m_impl().prod_shape(a, v) == m_gfp().prod_shape(a, v),
        m_impl().succ_shape(a, v) == m_gfp().succ_shape(a, v),
{
    lemma_models_agree();
    lemma_shapes_mono_m(m_impl(), m_gfp(), a, v);
    lemma_shapes_mono_m(m_gfp(), m_impl(), a, v);
}

/// `nset_shape` reads only states, kinds, operands, constants, and test combinations.
pub proof fn lemma_nset_shape_agree(m1: Model<R>, m2: Model<R>, inter: bool, xs: Set<R>, u: R)
    requires m1.state == m2.state, m1.kind == m2.kind, m1.ops == m2.ops, m1.combo == m2.combo,
        m1.empty == m2.empty, m1.epsilon == m2.epsilon, m1.universal == m2.universal,
    ensures m1.nset_shape(inter, xs, u) == m2.nset_shape(inter, xs, u),
{
    assert forall|x: R| m1.sops(inter, x) == m2.sops(inter, x) by {}
    assert forall|o: R| m1.in_sops_of(inter, xs, o) == m2.in_sops_of(inter, xs, o) by {
        if m1.in_sops_of(inter, xs, o) {
            let x = choose|x: R| xs.contains(x) && #[trigger] m1.sops(inter, x).contains(o);
            assert(m2.sops(inter, x).contains(o));
        }
        if m2.in_sops_of(inter, xs, o) {
            let x = choose|x: R| xs.contains(x) && #[trigger] m2.sops(inter, x).contains(o);
            assert(m1.sops(inter, x).contains(o));
        }
    }
    assert forall|ts: Set<R>, o: R| #[trigger] m1.combo_from(inter, xs, ts, o) == m2.combo_from(inter, xs, ts, o) by {
        if m1.combo_from(inter, xs, ts, o) { lemma_combo_from_transfer(m1, m2, inter, xs, ts, o); }
        if m2.combo_from(inter, xs, ts, o) { lemma_combo_from_transfer(m2, m1, inter, xs, ts, o); }
    }
    assert(m1.is_const(u) == m2.is_const(u));
    assert forall|o: R| (m1.is_test(o) && exists|ts: Set<R>| #[trigger] m1.combo_from(inter, xs, ts, o))
        == (m2.is_test(o) && exists|ts: Set<R>| #[trigger] m2.combo_from(inter, xs, ts, o)) by {
        if exists|ts: Set<R>| #[trigger] m1.combo_from(inter, xs, ts, o) {
            let ts = choose|ts: Set<R>| #[trigger] m1.combo_from(inter, xs, ts, o);
            assert(m2.combo_from(inter, xs, ts, o));
        }
        if exists|ts: Set<R>| #[trigger] m2.combo_from(inter, xs, ts, o) {
            let ts = choose|ts: Set<R>| #[trigger] m2.combo_from(inter, xs, ts, o);
            assert(m1.combo_from(inter, xs, ts, o));
        }
    }
}

pub proof fn lemma_combo_from_transfer(m1: Model<R>, m2: Model<R>, inter: bool, xs: Set<R>, ts: Set<R>, o: R)
    requires m1.state == m2.state, m1.kind == m2.kind, m1.ops == m2.ops, m1.combo == m2.combo,
        m1.combo_from(inter, xs, ts, o),
    ensures m2.combo_from(inter, xs, ts, o),
{
    assert forall|t: R| ts.contains(t) implies #[trigger] m1.is_test(t) by {
        assert(m1.combo_from(inter, xs, ts, o));
    }
    assert forall|t: R| ts.contains(t) implies m2.is_test(t) && m2.in_sops_of(inter, xs, t) by {
        assert(m1.is_test(t));
        assert(m1.in_sops_of(inter, xs, t));
        let x = choose|x: R| xs.contains(x) && #[trigger] m1.sops(inter, x).contains(t);
        assert(m2.sops(inter, x) == m1.sops(inter, x));
    }
}

pub proof fn lemma_gfp_consistent()
    ensures consistent(|a: R, v: R| g_lit(a, v), |a: R, v: R| g_prod(a, v)),
{
    let gl = |a: R, v: R| g_lit(a, v);
    let gp = |a: R, v: R| g_prod(a, v);
    assert forall|a: R, v: R| regex_nf(a) && #[trigger] gl(a, v) implies regex_nf(v) && with_rel(gl, gp).lit_shape(a, v) by {
        let (l, p) = choose|l: spec_fn(R, R) -> bool, p: spec_fn(R, R) -> bool| #[trigger] consistent(l, p) && l(a, v);
        lemma_rel_in_gfp(l, p);
        lemma_shapes_mono(l, p, gl, gp, a, v);
    }
    assert forall|a: R, v: R| regex_nf(a) && #[trigger] gp(a, v) implies regex_nf(v) && with_rel(gl, gp).prod_shape(a, v) by {
        let (l, p) = choose|l: spec_fn(R, R) -> bool, p: spec_fn(R, R) -> bool| #[trigger] consistent(l, p) && p(a, v);
        lemma_rel_in_gfp(l, p);
        lemma_shapes_mono(l, p, gl, gp, a, v);
    }
}

pub proof fn lemma_rel_in_gfp(l: spec_fn(R, R) -> bool, p: spec_fn(R, R) -> bool)
    requires consistent(l, p),
    ensures
        forall|x: R, y: R| #[trigger] l(x, y) ==> g_lit(x, y),
        forall|x: R, y: R| #[trigger] p(x, y) ==> g_prod(x, y),
{}

/// Folding: a literal allowed by (S1)–(S6) with respect to `lit`/`prod` is a literal.
pub proof fn lemma_lit_fold(a: R, v: R)
    requires regex_nf(a), regex_nf(v), m_impl().lit_shape(a, v),
    ensures (m_impl().lit)(a, v),
{
    lemma_models_agree();
    let gl = |x: R, y: R| g_lit(x, y);
    let gp = |x: R, y: R| g_prod(x, y);
    let l2 = |x: R, y: R| g_lit(x, y) || (x == a && y == v);
    lemma_impl_gfp_shapes(a, v);
    lemma_gfp_consistent();
    assert forall|x: R, y: R| #[trigger] gl(x, y) implies l2(x, y) by {}
    assert forall|x: R, y: R| #[trigger] gp(x, y) implies gp(x, y) by {}
    assert(consistent(l2, gp)) by {
        assert forall|x: R, y: R| regex_nf(x) && #[trigger] l2(x, y) implies regex_nf(y) && with_rel(l2, gp).lit_shape(x, y) by {
            if g_lit(x, y) {
                assert(gl(x, y));
            }
            lemma_shapes_mono(gl, gp, l2, gp, x, y);
        }
        assert forall|x: R, y: R| regex_nf(x) && #[trigger] gp(x, y) implies regex_nf(y) && with_rel(l2, gp).prod_shape(x, y) by {
            lemma_shapes_mono(gl, gp, l2, gp, x, y);
        }
    }
    assert(l2(a, v));
}

/// Folding for products.
pub proof fn lemma_prod_fold(a: R, v: R)
    requires regex_nf(a), regex_nf(v), m_impl().prod_shape(a, v),
    ensures (m_impl().prod)(a, v),
{
    lemma_models_agree();
    let gl = |x: R, y: R| g_lit(x, y);
    let gp = |x: R, y: R| g_prod(x, y);
    let p2 = |x: R, y: R| g_prod(x, y) || (x == a && y == v);
    lemma_impl_gfp_shapes(a, v);
    lemma_gfp_consistent();
    assert forall|x: R, y: R| #[trigger] gl(x, y) implies gl(x, y) by {}
    assert forall|x: R, y: R| #[trigger] gp(x, y) implies p2(x, y) by {}
    assert(consistent(gl, p2)) by {
        assert forall|x: R, y: R| regex_nf(x) && #[trigger] gl(x, y) implies regex_nf(y) && with_rel(gl, p2).lit_shape(x, y) by {
            lemma_shapes_mono(gl, gp, gl, p2, x, y);
        }
        assert forall|x: R, y: R| regex_nf(x) && #[trigger] p2(x, y) implies regex_nf(y) && with_rel(gl, p2).prod_shape(x, y) by {
            if g_prod(x, y) {
                assert(gp(x, y));
            }
            lemma_shapes_mono(gl, gp, gl, p2, x, y);
        }
    }
    assert(p2(a, v));
}

pub proof fn lemma_impl_succ()
    ensures m_impl().succ_ok(),
{
    let m = m_impl();
    lemma_models_agree();
    lemma_gfp_consistent();
    let gl = |x: R, y: R| g_lit(x, y);
    let gp = |x: R, y: R| g_prod(x, y);
    assert forall|p: R, v: R| m.st(p) && #[trigger] (m.succ)(p, v) implies m.st(v) && m.succ_shape(p, v) by {
        lemma_impl_gfp_shapes(p, v);
    }
    assert forall|p: R, v: R| m.st(p) && #[trigger] (m.lit)(p, v) implies m.st(v) && m.lit_shape(p, v) by {
        assert(gl(p, v));
        assert(with_rel(gl, gp).lit_shape(p, v));
        lemma_impl_gfp_shapes(p, v);
    }
    assert forall|p: R, v: R| m.st(p) && #[trigger] (m.prod)(p, v) implies m.st(v) && m.prod_shape(p, v) by {
        assert(gp(p, v));
        assert(with_rel(gl, gp).prod_shape(p, v));
        lemma_impl_gfp_shapes(p, v);
    }
}

/// The implementation's model satisfies the contract (N0)–(N5), (S0)–(S6).
pub proof fn theorem_impl_contract()
    ensures m_impl().contract(),
{
    lemma_models_agree();
    assert(m_impl().constants_ok());
    lemma_impl_substates();
    lemma_impl_fixpoints();
    lemma_impl_nset();
    lemma_impl_not();
    lemma_impl_cat();
    lemma_impl_tests();
    lemma_impl_succ();
}

} // verus!
