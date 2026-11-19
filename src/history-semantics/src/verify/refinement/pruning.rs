//! Layer 4: pruning (appendix `app:pruning`, Definition Pruning checks `def:pruning`, Lemma
//! `lem:prune`; simulation, appendix `app:simulation`).
//!
//! The search may discard an item at insertion when `search::may_discard` holds. This layer
//! states that the implemented checks (dead items, domination up to a sound simulation) imply it.
//! The simulation rules are those of `history-analysis/src/simulation.rs`. They differ from Figure
//! `fig:simulation`: the code reads `SumL`, `SumR`, `AndL` and `AndR` on lifted tests only when both
//! sides are lifted tests (`test_step`), so its relation is smaller than the Figure's. The side
//! conditions `k ≥ 2` and `a + b ≥ 1` are dropped. Soundness is proved; that the recursion decides
//! the Figure's relation is not.
use super::encoding::*;
use super::inclusion::*;
use super::search::*;
use alloc::boxed::Box;
use junco_core::kernel::verify as model;
use junco_core::verify::history_specs as language;
use junco_core::verify::history_specs::{EventView, Regex, Subst};
use vstd::prelude::*;

verus! {

/// `L_θ(x) ⊆ L_θ(y)` for every admissible `θ`.
pub open spec fn lang_le(x: Regex<model::Test>, y: Regex<model::Test>) -> bool {
    forall|theta: Subst, w: Seq<EventView>| language::event_wf(theta, theta.len()) && #[trigger] n_lang(theta, x, w) ==> n_lang(theta, y, w)
}

pub open spec fn test_le_sem(x: model::Test, y: model::Test) -> bool {
    forall|theta: Subst, e: EventView| language::event_wf(theta, theta.len()) && #[trigger] model::test_holds(theta, x, e) ==> model::test_holds(theta, y, e)
}

/// `≤` is sound (Lemma Simulation soundness and decidability, `lem:simulation`).
pub open spec fn sim_sound(le: spec_fn(Regex<model::Test>, Regex<model::Test>) -> bool) -> bool {
    forall|x: Regex<model::Test>, y: Regex<model::Test>| #[trigger] le(x, y) ==> lang_le(x, y)
}

pub open spec fn test_sim_sound(tle: spec_fn(model::Test, model::Test) -> bool) -> bool {
    forall|x: model::Test, y: model::Test| #[trigger] tle(x, y) ==> test_le_sem(x, y)
}

/// Operands of `q` for `&` (`+`): its operands if it is an intersection (union), else `{q}`.
pub open spec fn inter_ops(q: Regex<model::Test>) -> Seq<Regex<model::Test>> {
    match q { Regex::Intersect(cs) => cs, _ => seq![q] }
}

pub open spec fn union_ops(q: Regex<model::Test>) -> Seq<Regex<model::Test>> {
    match q { Regex::Union(cs) => cs, _ => seq![q] }
}

/// `dec(q) = (P, N)` (Definition Decomposition, `def:decomposition`).
pub open spec fn required(q: Regex<model::Test>, p: Regex<model::Test>) -> bool {
    inter_ops(q).contains(p) && !(p is Not)
}

pub open spec fn excluded(q: Regex<model::Test>, n: Regex<model::Test>) -> bool {
    exists|v: Regex<model::Test>| #[trigger] inter_ops(q).contains(Regex::Not(Box::new(v))) && union_ops(v).contains(n)
}

/// Equation `eq:decomposition`: `L_θ(q) = ⋂_{p∈P} L_θ(p) \ ⋃_{n∈N} L_θ(n)`.
pub open spec fn stmt_decomposition() -> bool {
    forall|q: Regex<model::Test>, theta: Subst, w: Seq<EventView>| #[trigger] n_lang(theta, q, w) == (
        (forall|p: Regex<model::Test>| #[trigger] required(q, p) ==> n_lang(theta, p, w))
        && (forall|n: Regex<model::Test>| #[trigger] excluded(q, n) ==> !n_lang(theta, n, w)))
}

/// Dead test (Definition Pruning checks, `def:pruning`).
pub open spec fn dead(le: spec_fn(Regex<model::Test>, Regex<model::Test>) -> bool, q: Regex<model::Test>) -> bool {
    exists|p: Regex<model::Test>| #[trigger] required(q, p) && forall|v: Regex<model::Test>| #[trigger] union_ops(p).contains(v)
        ==> exists|n: Regex<model::Test>| #[trigger] excluded(q, n) && le(v, n)
}

/// Domination `J ⊑ I` (Definition Pruning checks, `def:pruning`).
pub open spec fn dominated(d: NDomains, le: spec_fn(Regex<model::Test>, Regex<model::Test>) -> bool, j: Item, i: Item) -> bool {
    &&& entails(d, j.constraint, i.constraint)
    &&& forall|p: Regex<model::Test>| #[trigger] required(i.state, p) ==> required(j.state, p)
    &&& forall|n: Regex<model::Test>| #[trigger] excluded(i.state, n) ==> exists|n2: Regex<model::Test>| #[trigger] excluded(j.state, n2) && le(n, n2)
}

/// Lemma Pruning soundness (`lem:prune`): a dead item has no witnesses, and `J ⊑ I` gives `W(J) ⊆ W(I)`.
pub open spec fn stmt_prune_sound() -> bool {
    forall|d: NDomains, le: spec_fn(Regex<model::Test>, Regex<model::Test>) -> bool, j: Item, i: Item|
        #[trigger] sim_sound(le) ==> {
            &&& (dead(le, j.state) ==> no_witness(d, j))
            &&& (#[trigger] dominated(d, le, j, i) ==> witnesses_within(d, j, i))
        }
}

/// One rule of the code's term simulation, with premises read from `le` and `tle`.
pub open spec fn sim_step(le: spec_fn(Regex<model::Test>, Regex<model::Test>) -> bool,
    tle: spec_fn(model::Test, model::Test) -> bool, x: Regex<model::Test>, y: Regex<model::Test>) -> bool {
    ||| x == y                                                     // Refl
    ||| x is Empty                                                 // Zero
    ||| y is All                                                   // One
    ||| x is Epsilon && language::nullable(y)                      // Eps
    ||| (x matches Regex::Union(cs) && forall|i: int| 0 <= i < cs.len() ==> #[trigger] le(cs[i], y))        // SumL
    ||| (y matches Regex::Union(cs) && exists|i: int| 0 <= i < cs.len() && #[trigger] le(x, cs[i]))         // SumR
    ||| (x matches Regex::Intersect(cs) && exists|i: int| 0 <= i < cs.len() && #[trigger] le(cs[i], y))     // AndL
    ||| (y matches Regex::Intersect(cs) && forall|i: int| 0 <= i < cs.len() ==> #[trigger] le(x, cs[i]))    // AndR
    ||| (x matches Regex::Not(a) && y matches Regex::Not(b) && le(*b, *a))                                   // Not
    ||| (x matches Regex::Test(f) && y matches Regex::Test(g) && tle(f, g))                                  // tests
    ||| (x matches Regex::Star(a) && y matches Regex::Star(b) && le(*a, *b))                                 // Star
    ||| (y matches Regex::Star(b) && le(x, *b))                                                              // StarI
    ||| (y matches Regex::Concat(ys) && cat_padded(le, x, ys))                                               // Cat, PadL, PadR
}

/// `x`'s factors (its list, or `x` itself) match `ys` pointwise after dropping `a` leading and
/// `b` trailing `Univ` factors of `ys`.
pub open spec fn cat_padded(le: spec_fn(Regex<model::Test>, Regex<model::Test>) -> bool,
    x: Regex<model::Test>, ys: Seq<Regex<model::Test>>) -> bool {
    let xs = match x { Regex::Concat(cs) => cs, _ => seq![x] };
    exists|a: nat, b: nat| #![trigger padding_trigger(ys, a, b)] padding_ok(ys, a, b, xs.len())
        && forall|i: int| #![trigger ys[a + i]] 0 <= i < xs.len() ==> le(xs[i], ys[a + i])
}

pub open spec fn padding_ok(ys: Seq<Regex<model::Test>>, a: nat, b: nat, len: nat) -> bool {
    a + b + len == ys.len()
        && forall|i: int| (0 <= i < a || ys.len() - b <= i < ys.len()) ==> #[trigger] ys[i] is All
}

/// One rule of the code's test simulation (`Simulation::test_le` in `history-analysis/src/simulation.rs`).
pub open spec fn test_step(tle: spec_fn(model::Test, model::Test) -> bool, x: model::Test, y: model::Test) -> bool {
    ||| x == y
    ||| y is True
    ||| x is False
    ||| (x matches model::Test::Or(cs) && forall|i: int| 0 <= i < cs.len() ==> #[trigger] tle(cs[i], y))
    ||| (y matches model::Test::And(cs) && forall|i: int| 0 <= i < cs.len() ==> #[trigger] tle(x, cs[i]))
    ||| (x matches model::Test::And(cs) && exists|i: int| 0 <= i < cs.len() && #[trigger] tle(cs[i], y))
    ||| (y matches model::Test::Or(cs) && exists|i: int| 0 <= i < cs.len() && #[trigger] tle(x, cs[i]))
}

/// Lemma Simulation soundness (`lem:simulation`), rule by rule: each rule applied to sound premises gives a
/// sound conclusion; by induction on derivations the least relation closed under the rules,
/// and any relation the memoized recursion computes inside it, is sound.
pub open spec fn stmt_sim_rules_sound() -> bool {
    forall|le: spec_fn(Regex<model::Test>, Regex<model::Test>) -> bool, tle: spec_fn(model::Test, model::Test) -> bool,
        x: Regex<model::Test>, y: Regex<model::Test>|
        sim_sound(le) && test_sim_sound(tle) && #[trigger] sim_step(le, tle, x, y) ==> lang_le(x, y)
}

pub open spec fn stmt_test_rules_sound() -> bool {
    forall|tle: spec_fn(model::Test, model::Test) -> bool, x: model::Test, y: model::Test|
        test_sim_sound(tle) && #[trigger] test_step(tle, x, y) ==> test_le_sem(x, y)
}

/// The implemented insertion checks discharge `search::may_discard`: the dead check gives no
/// witnesses, and domination by an earlier node gives `W(J) ⊆ W(K)`.
pub open spec fn stmt_checks_discard() -> bool {
    forall|d: NDomains, le: spec_fn(Regex<model::Test>, Regex<model::Test>) -> bool, nodes: Seq<Node>, j: Item, depth: nat|
        #[trigger] sim_sound(le) && (dead(le, j.state) || exists|k: int| 0 <= k < nodes.len() && nodes[k].depth <= depth
            && #[trigger] dominated(d, le, j, nodes[k].item))
            ==> #[trigger] may_discard(d, nodes, j, depth)
}

// ----- proofs -----

/// `L_θ(v)` is the union of the languages of `v`'s union operands.
pub proof fn lemma_union_ops_lang(theta: Subst, v: Regex<model::Test>, w: Seq<EventView>)
    ensures n_lang(theta, v, w) == exists|n: Regex<model::Test>| #[trigger] union_ops(v).contains(n) && n_lang(theta, n, w),
{
    let sem = model::gsem(theta);
    match v {
        Regex::Union(cs) => {
            language::lemma_lang_union(sem, cs, w);
            if n_lang(theta, v, w) {
                let i = choose|i: int| 0 <= i < cs.len() && language::numeric_lang(sem, cs[i], w);
                assert(union_ops(v).contains(cs[i]));
                assert(n_lang(theta, cs[i], w));
            }
            if exists|n: Regex<model::Test>| #[trigger] union_ops(v).contains(n) && n_lang(theta, n, w) {
                let n = choose|n: Regex<model::Test>| #[trigger] union_ops(v).contains(n) && n_lang(theta, n, w);
                let i = choose|i: int| 0 <= i < cs.len() && cs[i] == n;
                assert(language::numeric_lang(sem, cs[i], w));
            }
        },
        _ => {
            assert(union_ops(v)[0] == v);
            assert(union_ops(v).contains(v));
            if exists|n: Regex<model::Test>| #[trigger] union_ops(v).contains(n) && n_lang(theta, n, w) {
                let n = choose|n: Regex<model::Test>| #[trigger] union_ops(v).contains(n) && n_lang(theta, n, w);
                let i = choose|i: int| 0 <= i < union_ops(v).len() && union_ops(v)[i] == n;
                assert(i == 0);
            }
        },
    }
}

/// `L_θ(q)` is the intersection of the languages of `q`'s intersection operands.
pub proof fn lemma_inter_ops_lang(theta: Subst, q: Regex<model::Test>, w: Seq<EventView>)
    ensures n_lang(theta, q, w) == (forall|i: int|
        0 <= i < inter_ops(q).len() ==> #[trigger] n_lang(theta, inter_ops(q)[i], w)),
{
    match q {
        Regex::Intersect(cs) => {
            language::lemma_lang_intersect(model::gsem(theta), cs, w);
            assert forall|i: int| 0 <= i < cs.len() implies
                n_lang(theta, q, w) ==> #[trigger] n_lang(theta, cs[i], w) by {}
            if forall|i: int| 0 <= i < cs.len() ==> #[trigger] n_lang(theta, cs[i], w) {
                assert forall|i: int| 0 <= i < cs.len() implies
                    language::numeric_lang(model::gsem(theta), cs[i], w) by {
                    assert(n_lang(theta, cs[i], w));
                }
            }
        },
        _ => {
            assert(inter_ops(q).len() == 1 && inter_ops(q)[0] == q);
            if forall|i: int| 0 <= i < inter_ops(q).len() ==> #[trigger] n_lang(theta, inter_ops(q)[i], w) {
                assert(n_lang(theta, inter_ops(q)[0], w));
            }
        },
    }
}

pub proof fn lemma_decomposition(q: Regex<model::Test>, theta: Subst, w: Seq<EventView>)
    ensures n_lang(theta, q, w) == (
        (forall|p: Regex<model::Test>| #[trigger] required(q, p) ==> n_lang(theta, p, w))
        && (forall|n: Regex<model::Test>| #[trigger] excluded(q, n) ==> !n_lang(theta, n, w))),
{
    let ops = inter_ops(q);
    lemma_inter_ops_lang(theta, q, w);
    if n_lang(theta, q, w) {
        assert forall|p: Regex<model::Test>| #[trigger] required(q, p) implies n_lang(theta, p, w) by {
            let i = choose|i: int| 0 <= i < ops.len() && ops[i] == p;
            assert(n_lang(theta, ops[i], w));
        }
        assert forall|n: Regex<model::Test>| #[trigger] excluded(q, n) implies !n_lang(theta, n, w) by {
            let v = choose|v: Regex<model::Test>| #[trigger] inter_ops(q).contains(Regex::Not(Box::new(v))) && union_ops(v).contains(n);
            let i = choose|i: int| 0 <= i < ops.len() && ops[i] == Regex::Not(Box::new(v));
            assert(n_lang(theta, ops[i], w));
            assert(!n_lang(theta, v, w));
            lemma_union_ops_lang(theta, v, w);
        }
    }
    if (forall|p: Regex<model::Test>| #[trigger] required(q, p) ==> n_lang(theta, p, w))
        && (forall|n: Regex<model::Test>| #[trigger] excluded(q, n) ==> !n_lang(theta, n, w)) {
        assert forall|i: int| 0 <= i < ops.len() implies #[trigger] n_lang(theta, ops[i], w) by {
            assert(ops.contains(ops[i]));
            match ops[i] {
                Regex::Not(b) => {
                    let v = *b;
                    assert(ops[i] == Regex::Not(Box::new(v)));
                    lemma_union_ops_lang(theta, v, w);
                    assert forall|n: Regex<model::Test>| #[trigger] union_ops(v).contains(n) implies !n_lang(theta, n, w) by {
                        assert(inter_ops(q).contains(Regex::Not(Box::new(v))) && union_ops(v).contains(n));
                        assert(excluded(q, n));
                    }
                },
                _ => { assert(required(q, ops[i])); },
            }
        }
    }
}

pub proof fn theorem_decomposition()
    ensures stmt_decomposition(),
{
    assert forall|q: Regex<model::Test>, theta: Subst, w: Seq<EventView>| #[trigger] n_lang(theta, q, w) == (
        (forall|p: Regex<model::Test>| #[trigger] required(q, p) ==> n_lang(theta, p, w))
        && (forall|n: Regex<model::Test>| #[trigger] excluded(q, n) ==> !n_lang(theta, n, w))) by {
        lemma_decomposition(q, theta, w);
    }
}

/// Lemma `lem:prune` for one pair of items.
pub proof fn lemma_prune_sound(d: NDomains, le: spec_fn(Regex<model::Test>, Regex<model::Test>) -> bool, j: Item, i: Item)
    requires sim_sound(le),
    ensures
        dead(le, j.state) ==> no_witness(d, j),
        dominated(d, le, j, i) ==> witnesses_within(d, j, i),
{
    if dead(le, j.state) {
        assert forall|theta: Subst, w: Seq<EventView>| !#[trigger] witness(d, j, theta, w) by {
            if witness(d, j, theta, w) {
                let p = choose|p: Regex<model::Test>| #[trigger] required(j.state, p) && forall|v: Regex<model::Test>| #[trigger] union_ops(p).contains(v)
                    ==> exists|n: Regex<model::Test>| #[trigger] excluded(j.state, n) && le(v, n);
                lemma_decomposition(j.state, theta, w);
                assert(n_lang(theta, p, w));
                lemma_union_ops_lang(theta, p, w);
                let v = choose|v: Regex<model::Test>| #[trigger] union_ops(p).contains(v) && n_lang(theta, v, w);
                let n = choose|n: Regex<model::Test>| #[trigger] excluded(j.state, n) && le(v, n);
                assert(lang_le(v, n));
                assert(n_lang(theta, n, w));
            }
        }
    }
    if dominated(d, le, j, i) {
        assert forall|theta: Subst, w: Seq<EventView>| #[trigger] witness(d, j, theta, w) implies witness(d, i, theta, w) by {
            lemma_decomposition(j.state, theta, w);
            lemma_decomposition(i.state, theta, w);
            assert(sat_by(theta, i.constraint));
            assert forall|p: Regex<model::Test>| #[trigger] required(i.state, p) implies n_lang(theta, p, w) by {
                assert(required(j.state, p));
            }
            assert forall|n: Regex<model::Test>| #[trigger] excluded(i.state, n) implies !n_lang(theta, n, w) by {
                let n2 = choose|n2: Regex<model::Test>| #[trigger] excluded(j.state, n2) && le(n, n2);
                assert(lang_le(n, n2));
                assert(!n_lang(theta, n2, w));
            }
        }
    }
}

pub proof fn theorem_prune_sound()
    ensures stmt_prune_sound(),
{
    assert forall|d: NDomains, le: spec_fn(Regex<model::Test>, Regex<model::Test>) -> bool,
        j: Item, theta: Subst, w: Seq<EventView>|
        #[trigger] sim_sound(le) && #[trigger] dead(le, j.state)
            implies !#[trigger] witness(d, j, theta, w) by {
        lemma_prune_sound(d, le, j, j);
    }
    assert forall|d: NDomains, le: spec_fn(Regex<model::Test>, Regex<model::Test>) -> bool,
        j: Item, i: Item|
        #[trigger] sim_sound(le) && #[trigger] dominated(d, le, j, i)
            implies witnesses_within(d, j, i) by {
        lemma_prune_sound(d, le, j, i);
    }
}

/// Cat/PadL/PadR, with the factors' parts given.
proof fn lemma_cat_parts(le: spec_fn(Regex<model::Test>, Regex<model::Test>) -> bool, xs: Seq<Regex<model::Test>>,
    ys: Seq<Regex<model::Test>>, a: nat, b: nat, parts: Seq<Seq<EventView>>, theta: Subst, w: Seq<EventView>)
    requires
        sim_sound(le), language::event_wf(theta, theta.len()),
        padding_ok(ys, a, b, xs.len()),
        forall|i: int| 0 <= i < xs.len() ==> #[trigger] le(xs[i], ys[a + i]),
        parts.len() == xs.len(), parts.flatten() == w,
        forall|i: int| 0 <= i < xs.len() ==> #[trigger] n_lang(theta, xs[i], parts[i]),
    ensures n_lang(theta, Regex::Concat(ys), w),
{
    let pre = Seq::new(a, |k: int| Seq::<EventView>::empty());
    let post = Seq::new(b, |k: int| Seq::<EventView>::empty());
    let all = pre + parts + post;
    vstd::seq_lib::lemma_flatten_concat(pre + parts, post);
    vstd::seq_lib::lemma_flatten_concat(pre, parts);
    language::lemma_flatten_empty(pre);
    language::lemma_flatten_empty(post);
    assert(pre.flatten() =~= Seq::<EventView>::empty());
    assert(post.flatten() =~= Seq::<EventView>::empty());
    assert(all.flatten() =~= w);
    assert(all.len() == ys.len());
    assert forall|i: int| 0 <= i < ys.len() implies language::numeric_lang(model::gsem(theta), ys[i], all[i]) by {
        if i < a {
            assert(ys[i] is All);
        } else if i < a + xs.len() {
            let k = i - a;
            assert(all[i] == parts[k]);
            assert(ys[a + k] == ys[i]);
            assert(le(xs[k], ys[a + k]));
            assert(lang_le(xs[k], ys[a + k]));
            assert(n_lang(theta, xs[k], parts[k]));
            assert(n_lang(theta, ys[i], all[i]));
        } else {
            assert(ys.len() - b <= i);
            assert(ys[i] is All);
        }
    }
}

proof fn lemma_cat_padded_sound(le: spec_fn(Regex<model::Test>, Regex<model::Test>) -> bool, x: Regex<model::Test>,
    ys: Seq<Regex<model::Test>>, theta: Subst, w: Seq<EventView>)
    requires sim_sound(le), language::event_wf(theta, theta.len()), cat_padded(le, x, ys), n_lang(theta, x, w),
    ensures n_lang(theta, Regex::Concat(ys), w),
{
    let sem = model::gsem(theta);
    reveal(cat_padded);
    let xs = match x { Regex::Concat(cs) => cs, _ => seq![x] };
    let (a, b) = choose|a: nat, b: nat| #[trigger] padding_ok(ys, a, b, xs.len())
        && forall|i: int| 0 <= i < xs.len() ==> #[trigger] le(xs[i], ys[a + i]);
    match x {
        Regex::Concat(cs) => {
            let parts = choose|parts: Seq<Seq<EventView>>| parts.len() == cs.len() && w == parts.flatten()
                && forall|i: int| 0 <= i < cs.len() ==> language::numeric_lang(sem, cs[i], parts[i]);
            assert forall|i: int| 0 <= i < xs.len() implies #[trigger] n_lang(theta, xs[i], parts[i]) by {}
            lemma_cat_parts(le, xs, ys, a, b, parts, theta, w);
        },
        _ => {
            let parts = seq![w];
            parts.lemma_flatten_one_element();
            assert forall|i: int| 0 <= i < xs.len() implies #[trigger] n_lang(theta, xs[i], parts[i]) by {
                assert(i == 0);
            }
            lemma_cat_parts(le, xs, ys, a, b, parts, theta, w);
        },
    }
}

/// One rule of the term simulation is sound.
pub proof fn lemma_sim_step_sound(le: spec_fn(Regex<model::Test>, Regex<model::Test>) -> bool,
    tle: spec_fn(model::Test, model::Test) -> bool, x: Regex<model::Test>, y: Regex<model::Test>)
    requires sim_sound(le), test_sim_sound(tle), sim_step(le, tle, x, y),
    ensures lang_le(x, y),
{
    assert forall|theta: Subst, w: Seq<EventView>| language::event_wf(theta, theta.len()) && #[trigger] n_lang(theta, x, w)
        implies n_lang(theta, y, w) by {
        let sem = model::gsem(theta);
        if x is Epsilon && language::nullable(y) {
            language::lemma_nullable_iff_nil(sem, y);
            assert(w =~= Seq::<EventView>::empty());
        }
        if x matches Regex::Union(cs) && forall|i: int| 0 <= i < cs.len() ==> #[trigger] le(cs[i], y) {
            let cs = x->Union_0;
            let i = choose|i: int| 0 <= i < cs.len() && language::numeric_lang(sem, cs[i], w);
            assert(le(cs[i], y));
            assert(lang_le(cs[i], y));
            assert(n_lang(theta, cs[i], w));
        }
        if y matches Regex::Union(cs) && exists|i: int| 0 <= i < cs.len() && #[trigger] le(x, cs[i]) {
            let cs = y->Union_0;
            let i = choose|i: int| 0 <= i < cs.len() && #[trigger] le(x, cs[i]);
            assert(lang_le(x, cs[i]));
            assert(n_lang(theta, cs[i], w));
            language::lemma_lang_union(sem, cs, w);
        }
        if x matches Regex::Intersect(cs) && exists|i: int| 0 <= i < cs.len() && #[trigger] le(cs[i], y) {
            let cs = x->Intersect_0;
            let i = choose|i: int| 0 <= i < cs.len() && #[trigger] le(cs[i], y);
            assert(lang_le(cs[i], y));
            assert(language::numeric_lang(sem, cs[i], w));
            assert(n_lang(theta, cs[i], w));
        }
        if y matches Regex::Intersect(cs) && forall|i: int| 0 <= i < cs.len() ==> #[trigger] le(x, cs[i]) {
            let cs = y->Intersect_0;
            assert forall|i: int| 0 <= i < cs.len() implies language::numeric_lang(sem, cs[i], w) by {
                assert(le(x, cs[i]));
                assert(lang_le(x, cs[i]));
                assert(n_lang(theta, cs[i], w));
            }
            language::lemma_lang_intersect(sem, cs, w);
        }
        if x matches Regex::Not(a) && y matches Regex::Not(b) && le(*b, *a) {
            let a = *(x->Not_0);
            let b = *(y->Not_0);
            assert(lang_le(b, a));
            if n_lang(theta, b, w) { assert(n_lang(theta, a, w)); }
        }
        if x matches Regex::Test(f) && y matches Regex::Test(g) && tle(f, g) {
            let f = x->Test_0;
            let g = y->Test_0;
            assert(test_le_sem(f, g));
            assert(model::test_holds(theta, f, w[0]));
            assert(model::test_holds(theta, g, w[0]));
        }
        if x matches Regex::Star(a) && y matches Regex::Star(b) && le(*a, *b) {
            let a = *(x->Star_0);
            let b = *(y->Star_0);
            assert(lang_le(a, b));
            let parts = choose|parts: Seq<Seq<EventView>>| w == parts.flatten()
                && forall|i: int| 0 <= i < parts.len() ==> language::numeric_lang(sem, a, parts[i]);
            assert forall|i: int| 0 <= i < parts.len() implies language::numeric_lang(sem, b, parts[i]) by {
                assert(n_lang(theta, a, parts[i]));
            }
        }
        if y matches Regex::Star(b) && le(x, *b) {
            let b = *(y->Star_0);
            assert(lang_le(x, b));
            assert(n_lang(theta, b, w));
            crate::verify::history_algebra::lemma_parts_star_single(sem, b, w);
        }
        if y matches Regex::Concat(ys) && cat_padded(le, x, ys) {
            lemma_cat_padded_sound(le, x, y->Concat_0, theta, w);
        }
    }
}

pub proof fn theorem_sim_rules_sound()
    ensures stmt_sim_rules_sound(),
{
    assert forall|le: spec_fn(Regex<model::Test>, Regex<model::Test>) -> bool, tle: spec_fn(model::Test, model::Test) -> bool,
        x: Regex<model::Test>, y: Regex<model::Test>|
        sim_sound(le) && test_sim_sound(tle) && #[trigger] sim_step(le, tle, x, y) implies lang_le(x, y) by {
        lemma_sim_step_sound(le, tle, x, y);
    }
}

/// One rule of the test simulation is sound.
pub proof fn lemma_test_step_sound(tle: spec_fn(model::Test, model::Test) -> bool, x: model::Test, y: model::Test)
    requires test_sim_sound(tle), test_step(tle, x, y),
    ensures test_le_sem(x, y),
{
    assert forall|theta: Subst, e: EventView| language::event_wf(theta, theta.len()) && #[trigger] model::test_holds(theta, x, e)
        implies model::test_holds(theta, y, e) by {
        if x matches model::Test::Or(cs) && forall|i: int| 0 <= i < cs.len() ==> #[trigger] tle(cs[i], y) {
            let cs = x->Or_0;
            let i = choose|i: int| 0 <= i < cs.len() && model::test_holds(theta, cs[i], e);
            assert(tle(cs[i], y));
            assert(test_le_sem(cs[i], y));
        }
        if y matches model::Test::And(cs) && forall|i: int| 0 <= i < cs.len() ==> #[trigger] tle(x, cs[i]) {
            let cs = y->And_0;
            assert forall|i: int| 0 <= i < cs.len() implies model::test_holds(theta, cs[i], e) by {
                assert(tle(x, cs[i]));
                assert(test_le_sem(x, cs[i]));
            }
        }
        if x matches model::Test::And(cs) && exists|i: int| 0 <= i < cs.len() && #[trigger] tle(cs[i], y) {
            let cs = x->And_0;
            let i = choose|i: int| 0 <= i < cs.len() && #[trigger] tle(cs[i], y);
            assert(test_le_sem(cs[i], y));
            assert(model::test_holds(theta, cs[i], e));
        }
        if y matches model::Test::Or(cs) && exists|i: int| 0 <= i < cs.len() && #[trigger] tle(x, cs[i]) {
            let cs = y->Or_0;
            let i = choose|i: int| 0 <= i < cs.len() && #[trigger] tle(x, cs[i]);
            assert(test_le_sem(x, cs[i]));
            assert(model::test_holds(theta, cs[i], e));
        }
    }
}

pub proof fn theorem_test_rules_sound()
    ensures stmt_test_rules_sound(),
{
    assert forall|tle: spec_fn(model::Test, model::Test) -> bool, x: model::Test, y: model::Test|
        test_sim_sound(tle) && #[trigger] test_step(tle, x, y) implies test_le_sem(x, y) by {
        lemma_test_step_sound(tle, x, y);
    }
}

pub proof fn theorem_checks_discard()
    ensures stmt_checks_discard(),
{
    assert forall|d: NDomains, le: spec_fn(Regex<model::Test>, Regex<model::Test>) -> bool, nodes: Seq<Node>, j: Item, depth: nat|
        #[trigger] sim_sound(le) && (dead(le, j.state) || exists|k: int| 0 <= k < nodes.len() && nodes[k].depth <= depth
            && #[trigger] dominated(d, le, j, nodes[k].item))
            implies #[trigger] may_discard(d, nodes, j, depth) by {
        if dead(le, j.state) {
            lemma_prune_sound(d, le, j, j);
        } else {
            let k = choose|k: int| 0 <= k < nodes.len() && nodes[k].depth <= depth && #[trigger] dominated(d, le, j, nodes[k].item);
            lemma_prune_sound(d, le, j, nodes[k].item);
            assert(witnesses_within(d, j, nodes[k].item));
        }
    }
}

// The trigger must not capture the conditional operand list inside `cat_padded`.
pub closed spec fn padding_trigger(ys: Seq<Regex<model::Test>>, a: nat, b: nat) -> (nat, nat) {
    (a, b)
}

pub proof fn lemma_padding_trigger(ys: Seq<Regex<model::Test>>, a: nat, b: nat)
    ensures padding_trigger(ys, a, b) == (a, b),
{
    reveal(padding_trigger);
}
} // verus!
