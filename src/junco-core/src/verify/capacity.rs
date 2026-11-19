//! Real instances of symbolic counterexamples (`junco_core::spec::questions`): fresh-value capacity gives an
//! admissible choice of fresh values, `views_surjective` turns the chosen tuples into events,
//! and integer coordinates have capacity whenever the type is large enough.

use crate::spec::hypotheses::{eq_equivalence, event_obligations};
use crate::spec::questions::*;
use crate::spec::semantics::history_view;
use history_syntax::Event;
use history_syntax::event::specs::EventSpec;
use history_syntax::spec::events::{arity, event_view, well_tagged};
use vstd::prelude::*;
use vstd::std_specs::cmp::PartialEqSpec;

verus! {

broadcast use {vstd::seq::group_seq_lemmas, vstd::iset::group_iset_lemmas};

/// Every constant of the counterexample at coordinate `i` is tagged `i` (the reconstruction
/// bridge establishes it from the analyzer's constant book).
pub open spec fn cex_constants_tagged<E: Event>(cex: CexView<E::Component>) -> bool {
    &&& forall|i: int| 0 <= i < cex.candidate.len() ==> match #[trigger] cex.candidate[i] {
        ValueView::Constant(c) => E::coordinate_spec(c) == i,
        ValueView::Fresh(_) => true,
    }
    &&& forall|j: int, i: int| 0 <= j < cex.history.len() && 0 <= i < cex.history[j].len()
        ==> match #[trigger] cex.history[j][i] {
            ValueView::Constant(c) => E::coordinate_spec(c) == i,
            ValueView::Fresh(_) => true,
        }
}

/// A finite candidate and history contain finitely many fresh numbers per coordinate.
pub proof fn lemma_fresh_used_finite<C>(cex: CexView<C>, coordinate: int)
    ensures fresh_used(cex, coordinate).finite(),
{
    broadcast use vstd::set::lemma_to_iset_finite, vstd::prelude::Seq::to_set_ensures;
    let events = cex.history.to_set().insert(cex.candidate).to_iset();
    let number = |c: ComponentsView<C>| if 0 <= coordinate < c.len() {
        match c[coordinate] { ValueView::Fresh(n) => n, ValueView::Constant(_) => 0nat }
    } else { 0nat };
    events.lemma_map_finite(number);
    assert forall|n: nat| fresh_used(cex, coordinate).contains(n)
        implies events.map(number).contains(n) by {
        let c = if 0 <= coordinate < cex.candidate.len()
            && cex.candidate[coordinate] == ValueView::Fresh(n) {
            cex.candidate
        } else {
            let i = choose|i: int| 0 <= i < cex.history.len() && 0 <= coordinate < cex.history[i].len()
                && #[trigger] cex.history[i][coordinate] == ValueView::Fresh(n);
            assert(cex.history.to_set().contains(cex.history[i]));
            cex.history[i]
        };
        assert(events.contains(c));
        assert(number(c) == n);
        assert(events.map(number).contains(n));
    }
    vstd::iset_lib::lemma_iset_subset_finite(events.map(number), fresh_used(cex, coordinate));
}

/// An injection of a finite set of numbers into `0..len`.
proof fn lemma_enumerate(used: ISet<nat>) -> (g: spec_fn(nat) -> nat)
    requires used.finite(),
    ensures
        forall|n: nat| used.contains(n) ==> #[trigger] g(n) < used.len(),
        forall|m: nat, n: nat| used.contains(m) && used.contains(n) && m != n ==> #[trigger] g(m) != #[trigger] g(n),
    decreases used.len(),
{
    if used.len() == 0 {
        used.lemma_len0_is_empty();
        |n: nat| 0nat
    } else {
        let a = used.choose();
        assert(used.contains(a));
        let rest = used.remove(a);
        let g0 = lemma_enumerate(rest);
        let g = |n: nat| if n == a { rest.len() } else { g0(n) };
        assert forall|m: nat, n: nat| used.contains(m) && used.contains(n) && m != n
            implies #[trigger] g(m) != #[trigger] g(n) by {
            if m == a { assert(rest.contains(n)); }
            else if n == a { assert(rest.contains(m)); }
            else { assert(rest.contains(m) && rest.contains(n)); }
        }
        g
    }
}

/// Capacity at one coordinate yields an admissible choice for the fresh numbers used there.
proof fn lemma_choice_from_capacity<E: Event>(
    domains: DomainsView<E::Component>, known: Seq<Set<E::Component>>, cex: CexView<E::Component>, i: int,
) -> (f: spec_fn(nat) -> E::Component)
    requires
        eq_equivalence::<E::Component>(),
        fresh_capacity::<E>(domains, known, i, fresh_used(cex, i).len()),
    ensures choice_ok::<E>(f, fresh_used(cex, i), known[i], domains[i], i),
{
    let used = fresh_used(cex, i);
    lemma_fresh_used_finite(cex, i);
    let vs = choose|vs: Seq<E::Component>| #[trigger] vs.len() == used.len()
        && (forall|a: int, b: int| 0 <= a < b < vs.len() ==> !vs[a].eq_spec(&vs[b]))
        && forall|a: int| 0 <= a < vs.len() ==> E::coordinate_spec(#[trigger] vs[a]) == i
            && in_domain(domains[i], vs[a]) && misses(known[i], vs[a]);
    let g = lemma_enumerate(used);
    let f = |n: nat| vs[g(n) as int];
    assert forall|m: nat, n: nat| #![trigger used.contains(m), used.contains(n)]
        used.contains(m) && used.contains(n) && m != n implies !f(m).eq_spec(&f(n)) by {
        let a = g(m) as int;
        let b = g(n) as int;
        if a < b { assert(!vs[a].eq_spec(&vs[b])); }
        else { assert(!vs[b].eq_spec(&vs[a])); assert(vs[a].eq_spec(&vs[b]) == vs[b].eq_spec(&vs[a])); }
    }
    assert forall|n: nat, k: E::Component| #![trigger used.contains(n), known[i].contains(k)]
        used.contains(n) && known[i].contains(k) implies !f(n).eq_spec(&k) by {
        assert(misses(known[i], vs[g(n) as int]));
    }
    f
}

/// Capacity for the counterexample's own fresh values yields an admissible choice.
pub proof fn lemma_admissible_from_capacity<E: Event>(
    domains: DomainsView<E::Component>, known: Seq<Set<E::Component>>, cex: CexView<E::Component>,
) -> (f: FreshChoice<E::Component>)
    requires
        eq_equivalence::<E::Component>(),
        domains.len() == arity::<E>(), known.len() == arity::<E>(), cex_arity(cex, arity::<E>()),
        capacity_for::<E>(domains, known, cex),
    ensures admissible::<E>(domains, known, cex, f),
{
    assert forall|i: int| 0 <= i < arity::<E>() implies
        exists|f: spec_fn(nat) -> E::Component| choice_ok::<E>(f, #[trigger] fresh_used(cex, i), known[i], domains[i], i) by {
        let f = lemma_choice_from_capacity::<E>(domains, known, cex, i);
    }
    let f = Seq::new(arity::<E>(), |i: int| choose|f: spec_fn(nat) -> E::Component|
        choice_ok::<E>(f, fresh_used(cex, i), known[i], domains[i], i));
    assert forall|i: int| 0 <= i < arity::<E>() implies
        choice_ok::<E>(#[trigger] f[i], fresh_used(cex, i), known[i], domains[i], i) by {}
    f
}

/// Under an admissible choice every tuple the counterexample denotes is well tagged.
proof fn lemma_event_of_well_tagged<E: Event>(
    domains: DomainsView<E::Component>, known: Seq<Set<E::Component>>, cex: CexView<E::Component>,
    f: FreshChoice<E::Component>, c: ComponentsView<E::Component>,
)
    requires
        admissible::<E>(domains, known, cex, f),
        c.len() == arity::<E>(),
        forall|i: int| 0 <= i < c.len() ==> match #[trigger] c[i] {
            ValueView::Constant(k) => E::coordinate_spec(k) == i,
            ValueView::Fresh(n) => fresh_used(cex, i).contains(n),
        },
    ensures well_tagged::<E>(event_of(c, f)),
{
    assert forall|i: int| 0 <= i < c.len() implies E::coordinate_spec(#[trigger] event_of(c, f)[i]) == i by {
        match c[i] {
            ValueView::Constant(k) => {},
            ValueView::Fresh(n) => {
                assert(choice_ok::<E>(f[i], fresh_used(cex, i), known[i], domains[i], i));
                assert(fresh_used(cex, i).contains(n));
            },
        }
    }
}

/// An admissible choice denotes a real pair of events (`views_surjective` in `history_syntax::spec::events`).
pub proof fn lemma_instance_from_choice<E: Event>(
    domains: DomainsView<E::Component>, known: Seq<Set<E::Component>>, cex: CexView<E::Component>,
    f: FreshChoice<E::Component>,
)
    requires
        event_obligations::<E>(),
        cex_constants_tagged::<E>(cex),
        admissible::<E>(domains, known, cex, f),
    ensures exists|c: E, h: Seq<E>| #[trigger] instantiates::<E>(cex, f, c, h),
{
    assert forall|i: int| 0 <= i < cex.candidate.len() implies match #[trigger] cex.candidate[i] {
        ValueView::Constant(k) => E::coordinate_spec(k) == i,
        ValueView::Fresh(n) => fresh_used(cex, i).contains(n),
    } by {
        if let ValueView::Fresh(n) = cex.candidate[i] { assert(fresh_used(cex, i).contains(n)); }
    }
    lemma_event_of_well_tagged::<E>(domains, known, cex, f, cex.candidate);
    let c = choose|c: E| event_view(c) == event_of(cex.candidate, f);
    assert forall|j: int| 0 <= j < cex.history.len() implies
        exists|e: E| event_view(e) == event_of(#[trigger] cex.history[j], f) by {
        assert forall|i: int| 0 <= i < cex.history[j].len() implies match #[trigger] cex.history[j][i] {
            ValueView::Constant(k) => E::coordinate_spec(k) == i,
            ValueView::Fresh(n) => fresh_used(cex, i).contains(n),
        } by {
            if let ValueView::Fresh(n) = cex.history[j][i] { assert(fresh_used(cex, i).contains(n)); }
        }
        lemma_event_of_well_tagged::<E>(domains, known, cex, f, cex.history[j]);
    }
    let h = Seq::new(cex.history.len(), |j: int| choose|e: E| event_view(e) == event_of(cex.history[j], f));
    assert(history_view(h) =~= history_of(cex, f));
    assert(instantiates::<E>(cex, f, c, h));
}

/// Decision 2: capacity for the counterexample's own fresh values gives a real instance.
pub proof fn lemma_capacity_gives_instance<E: Event>(
    domains: DomainsView<E::Component>, known: Seq<Set<E::Component>>, cex: CexView<E::Component>,
)
    requires
        event_obligations::<E>(),
        domains.len() == arity::<E>(), known.len() == arity::<E>(), cex_arity(cex, arity::<E>()),
        cex_constants_tagged::<E>(cex),
        capacity_for::<E>(domains, known, cex),
    ensures cex_has_instance::<E>(domains, known, cex),
{
    let f = lemma_admissible_from_capacity::<E>(domains, known, cex);
    lemma_instance_from_choice::<E>(domains, known, cex, f);
    let (c, h) = choose|c: E, h: Seq<E>| #[trigger] instantiates::<E>(cex, f, c, h);
    assert(admissible::<E>(domains, known, cex, f) && instantiates::<E>(cex, f, c, h));
}

// ----- capacity of integer coordinates -----

/// `size` values `embed(0), …, embed(size-1)`, pairwise distinct up to `eq_spec` and tagged `i`,
/// give capacity `k` at an undeclared coordinate whenever `known[i].len() + k <= size`: each
/// known constant blocks at most one of them.
pub proof fn lemma_fresh_capacity_range<E: Event>(
    domains: DomainsView<E::Component>, known: Seq<Set<E::Component>>, i: int, k: nat,
    embed: spec_fn(int) -> E::Component, size: nat,
)
    requires
        eq_equivalence::<E::Component>(),
        0 <= i < domains.len(), 0 <= i < known.len(), domains[i] is None,
        known[i].len() + k <= size,
        forall|a: int, b: int| 0 <= a < size && 0 <= b < size ==> (#[trigger] embed(a).eq_spec(&embed(b)) <==> a == b),
        forall|a: int| 0 <= a < size ==> E::coordinate_spec(#[trigger] embed(a)) == i,
    ensures fresh_capacity::<E>(domains, known, i, k),
{
    broadcast use {vstd::set::lemma_to_iset_len, vstd::set::lemma_to_iset_finite,
        vstd::iset_lib::group_iset_properties, vstd::prelude::Seq::to_set_ensures};
    let fixed = known[i];
    let codes = vstd::iset_lib::set_int_range(0, size as int);
    vstd::iset_lib::lemma_int_range(0, size as int);
    let blocked = codes.filter(|n: int| !misses(fixed, embed(n)));
    codes.lemma_len_filter(|n: int| !misses(fixed, embed(n)));
    let pick = |n: int| choose|w: E::Component| fixed.contains(w) && embed(n).eq_spec(&w);
    assert forall|m: int, n: int| blocked.contains(m) && blocked.contains(n) && #[trigger] pick(m) == #[trigger] pick(n)
        implies m == n by {
        let w = pick(m);
        assert(fixed.contains(w) && embed(m).eq_spec(&w));
        assert(embed(n).eq_spec(&w));
        assert(w.eq_spec(&embed(n)));
        assert(embed(m).eq_spec(&embed(n)));
    }
    assert(blocked.injective_on(pick));
    vstd::iset_lib::lemma_map_size(blocked, blocked.map(pick), pick);
    assert forall|w: E::Component| blocked.map(pick).contains(w) implies fixed.to_iset().contains(w) by {
        let n = choose|n: int| blocked.contains(n) && pick(n) == w;
        assert(fixed.contains(pick(n)));
    }
    vstd::iset_lib::lemma_len_subset(blocked.map(pick), fixed.to_iset());
    assert(blocked.len() <= fixed.len());
    let free = codes.difference(blocked);
    assert(codes.intersect(blocked) =~= blocked);
    assert(free.len() == size - blocked.len());
    assert(free.len() >= k);
    let all = free.to_seq();
    free.lemma_to_seq_len();
    free.lemma_to_seq_no_duplicates();
    free.lemma_to_seq_to_set_id();
    let picked = all.take(k as int);
    let vs = picked.map(|j: int, n: int| embed(n));
    assert(vs.len() == k);
    assert forall|a: int| 0 <= a < k implies free.contains(#[trigger] picked[a]) by {
        assert(all.to_set().contains(all[a]));
        assert(all.to_set().to_iset().contains(all[a]));
    }
    assert forall|a: int, b: int| 0 <= a < b < vs.len() implies !vs[a].eq_spec(&vs[b]) by {
        assert(picked[a] != picked[b]);
        assert(codes.contains(picked[a]) && codes.contains(picked[b]));
    }
    assert forall|a: int| 0 <= a < vs.len() implies E::coordinate_spec(#[trigger] vs[a]) == i
        && in_domain(domains[i], vs[a]) && misses(fixed, vs[a]) by {
        assert(codes.contains(picked[a]));
        assert(!blocked.contains(picked[a]));
    }
    assert(exists|vs: Seq<E::Component>| #[trigger] vs.len() == k
        && (forall|a: int, b: int| 0 <= a < b < vs.len() ==> !vs[a].eq_spec(&vs[b]))
        && forall|a: int| 0 <= a < vs.len() ==> E::coordinate_spec(#[trigger] vs[a]) == i
            && in_domain(domains[i], vs[a]) && misses(known[i], vs[a]));
}

/// Capacity `k` at an undeclared `u8` coordinate `i`, embedded by `embed` (injective up to
/// `eq_spec`, tagged `i`), whenever `known[i].len() + k <= 256`.
pub proof fn lemma_fresh_capacity_u8<E: Event>(
    domains: DomainsView<E::Component>, known: Seq<Set<E::Component>>, i: int, k: nat,
    embed: spec_fn(u8) -> E::Component,
)
    requires
        eq_equivalence::<E::Component>(),
        0 <= i < domains.len(), 0 <= i < known.len(), domains[i] is None,
        known[i].len() + k <= 0x100,
        forall|a: u8, b: u8| #[trigger] embed(a).eq_spec(&embed(b)) <==> a == b,
        forall|a: u8| E::coordinate_spec(#[trigger] embed(a)) == i,
    ensures fresh_capacity::<E>(domains, known, i, k),
{
    lemma_fresh_capacity_range::<E>(domains, known, i, k, |n: int| embed(n as u8), 0x100);
}

pub proof fn lemma_fresh_capacity_u16<E: Event>(
    domains: DomainsView<E::Component>, known: Seq<Set<E::Component>>, i: int, k: nat,
    embed: spec_fn(u16) -> E::Component,
)
    requires
        eq_equivalence::<E::Component>(),
        0 <= i < domains.len(), 0 <= i < known.len(), domains[i] is None,
        known[i].len() + k <= 0x1_0000,
        forall|a: u16, b: u16| #[trigger] embed(a).eq_spec(&embed(b)) <==> a == b,
        forall|a: u16| E::coordinate_spec(#[trigger] embed(a)) == i,
    ensures fresh_capacity::<E>(domains, known, i, k),
{
    lemma_fresh_capacity_range::<E>(domains, known, i, k, |n: int| embed(n as u16), 0x1_0000);
}

pub proof fn lemma_fresh_capacity_u32<E: Event>(
    domains: DomainsView<E::Component>, known: Seq<Set<E::Component>>, i: int, k: nat,
    embed: spec_fn(u32) -> E::Component,
)
    requires
        eq_equivalence::<E::Component>(),
        0 <= i < domains.len(), 0 <= i < known.len(), domains[i] is None,
        known[i].len() + k <= 0x1_0000_0000,
        forall|a: u32, b: u32| #[trigger] embed(a).eq_spec(&embed(b)) <==> a == b,
        forall|a: u32| E::coordinate_spec(#[trigger] embed(a)) == i,
    ensures fresh_capacity::<E>(domains, known, i, k),
{
    lemma_fresh_capacity_range::<E>(domains, known, i, k, |n: int| embed(n as u32), 0x1_0000_0000);
}

pub proof fn lemma_fresh_capacity_u64<E: Event>(
    domains: DomainsView<E::Component>, known: Seq<Set<E::Component>>, i: int, k: nat,
    embed: spec_fn(u64) -> E::Component,
)
    requires
        eq_equivalence::<E::Component>(),
        0 <= i < domains.len(), 0 <= i < known.len(), domains[i] is None,
        known[i].len() + k <= 0x1_0000_0000_0000_0000,
        forall|a: u64, b: u64| #[trigger] embed(a).eq_spec(&embed(b)) <==> a == b,
        forall|a: u64| E::coordinate_spec(#[trigger] embed(a)) == i,
    ensures fresh_capacity::<E>(domains, known, i, k),
{
    lemma_fresh_capacity_range::<E>(domains, known, i, k, |n: int| embed(n as u64), 0x1_0000_0000_0000_0000);
}

} // verus!
