// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Independent pair-language semantics: request is the head, followed by history
//! in oldest-to-newest order. Runtime errors carry no Boolean interpretation.

use crate::rvm::program::HistoryField;
use alloc::boxed::Box;
use vstd::prelude::*;

verus! {

/// Fixed-width semantic event; zero is reserved for an unbound binding coordinate.
pub struct EventView {
    pub principal: nat,
    pub action: nat,
    pub resource: nat,
}

pub type Subst = EventView;

pub open spec fn event_wf(event: EventView) -> bool {
    event.principal <= u64::MAX && event.action <= u64::MAX && event.resource <= u64::MAX
}

pub open spec fn field_value(event: EventView, field: HistoryField) -> nat {
    match field {
        HistoryField::Principal => event.principal,
        HistoryField::Action => event.action,
        HistoryField::Resource => event.resource,
    }
}

pub enum Regex<L> {
    Empty, All, Epsilon, Test(L), Union(Seq<Regex<L>>), Concat(Seq<Regex<L>>),
    Star(Box<Regex<L>>), Intersect(Seq<Regex<L>>), Not(Box<Regex<L>>),
}

pub enum Transition<L> {
    Const(Regex<L>), If(L, Box<Transition<L>>, Box<Transition<L>>),
    Union(Seq<Transition<L>>), Intersect(Seq<Transition<L>>),
    Not(Box<Transition<L>>), Append(Box<Transition<L>>, Seq<Regex<L>>),
}

pub open spec fn nullable<L>(r: Regex<L>) -> bool decreases r {
    match r {
        Regex::Empty | Regex::Test(_) => false,
        Regex::All | Regex::Epsilon | Regex::Star(_) => true,
        Regex::Union(cs) => exists|i: int| 0 <= i < cs.len() && nullable(cs[i]),
        Regex::Concat(cs) => forall|i: int| 0 <= i < cs.len() ==> nullable(cs[i]),
        Regex::Intersect(cs) => forall|i: int| 0 <= i < cs.len() ==> nullable(cs[i]),
        Regex::Not(c) => !nullable(*c),
    }
}

pub open spec fn lang<L>(sem: spec_fn(L, EventView) -> bool, r: Regex<L>, w: Seq<EventView>) -> bool decreases r {
    match r {
        Regex::Empty => false,
        Regex::All => true,
        Regex::Epsilon => w.len() == 0,
        Regex::Test(l) => w.len() == 1 && sem(l, w[0]),
        Regex::Union(cs) => exists|i: int| 0 <= i < cs.len() && lang(sem, cs[i], w),
        Regex::Intersect(cs) => forall|i: int| 0 <= i < cs.len() ==> lang(sem, cs[i], w),
        Regex::Not(c) => !lang(sem, *c, w),
        Regex::Concat(cs) => exists|parts: Seq<Seq<EventView>>| parts.len() == cs.len() && w == parts.flatten()
            && forall|i: int| 0 <= i < cs.len() ==> lang(sem, cs[i], parts[i]),
        Regex::Star(c) => exists|parts: Seq<Seq<EventView>>| w == parts.flatten()
            && forall|i: int| 0 <= i < parts.len() ==> lang(sem, *c, parts[i]),
    }
}

pub open spec fn derivative<L>(sem: spec_fn(L, EventView) -> bool, e: EventView, r: Regex<L>) -> Regex<L>
    decreases r, 1nat, 0nat,
{
    match r {
        Regex::Empty | Regex::Epsilon => Regex::Empty,
        Regex::All => Regex::All,
        Regex::Test(l) => if sem(l, e) { Regex::Epsilon } else { Regex::Empty },
        Regex::Union(cs) => Regex::Union(Seq::new(cs.len(), |i: int| if 0 <= i < cs.len() { derivative(sem, e, cs[i]) } else { Regex::Empty })),
        Regex::Intersect(cs) => Regex::Intersect(Seq::new(cs.len(), |i: int| if 0 <= i < cs.len() { derivative(sem, e, cs[i]) } else { Regex::Empty })),
        Regex::Not(c) => Regex::Not(Box::new(derivative(sem, e, *c))),
        Regex::Star(c) => Regex::Concat(seq![derivative(sem, e, *c), Regex::Star(c)]),
        Regex::Concat(cs) => derivative_concat(sem, e, r, cs),
    }
}

pub open spec fn derivative_concat<L>(sem: spec_fn(L, EventView) -> bool, e: EventView, bound: Regex<L>, cs: Seq<Regex<L>>) -> Regex<L>
    decreases bound, 0nat, cs.len(),
    when forall|i: int| 0 <= i < cs.len() ==> is_smaller_than(cs[i], bound)
{
    if cs.len() == 0 { Regex::Empty }
    else {
        Regex::Union(seq![Regex::Concat(seq![derivative(sem, e, cs[0])] + cs.drop_first())]
            + if nullable(cs[0]) { seq![derivative_concat(sem, e, bound, cs.drop_first())] } else { Seq::empty() })
    }
}

pub open spec fn derive_word<L>(sem: spec_fn(L, EventView) -> bool, w: Seq<EventView>, r: Regex<L>) -> Regex<L>
    decreases w.len(),
{
    if w.len() == 0 { r }
    else { derive_word(sem, w.drop_first(), derivative(sem, w[0], r)) }
}

pub open spec fn interp_transition<L>(sem: spec_fn(L, EventView) -> bool, e: EventView, t: Transition<L>) -> Regex<L>
    decreases t,
{
    match t {
        Transition::Const(r) => r,
        Transition::If(l, a, b) => if sem(l, e) { interp_transition(sem, e, *a) } else { interp_transition(sem, e, *b) },
        Transition::Union(cs) => Regex::Union(Seq::new(cs.len(), |i: int| if 0 <= i < cs.len() { interp_transition(sem, e, cs[i]) } else { Regex::Empty })),
        Transition::Intersect(cs) => Regex::Intersect(Seq::new(cs.len(), |i: int| if 0 <= i < cs.len() { interp_transition(sem, e, cs[i]) } else { Regex::Empty })),
        Transition::Not(c) => Regex::Not(Box::new(interp_transition(sem, e, *c))),
        Transition::Append(c, suffix) => Regex::Concat(seq![interp_transition(sem, e, *c)] + suffix),
    }
}

pub proof fn lemma_flatten_empty(parts: Seq<Seq<EventView>>)
    ensures parts.flatten().len() == 0 <==> forall|i: int| 0 <= i < parts.len() ==> parts[i].len() == 0,
    decreases parts.len(),
{
    if parts.len() > 0 {
        lemma_flatten_empty(parts.drop_first());
        if parts.flatten().len() == 0 {
            assert forall|i: int| 0 <= i < parts.len() implies parts[i].len() == 0 by {
                if i > 0 { assert(parts[i] == parts.drop_first()[i - 1]); }
            }
        }
        if forall|i: int| 0 <= i < parts.len() ==> parts[i].len() == 0 {
            assert forall|i: int| 0 <= i < parts.drop_first().len() implies parts.drop_first()[i].len() == 0 by {
                assert(parts.drop_first()[i] == parts[i + 1]);
            }
        }
    }
}

pub proof fn lemma_concat_uncons<L>(sem: spec_fn(L, EventView) -> bool, cs: Seq<Regex<L>>, w: Seq<EventView>)
    requires cs.len() > 0,
    ensures lang(sem, Regex::Concat(cs), w) <==> exists|a: Seq<EventView>, b: Seq<EventView>|
        w == a + b && lang(sem, cs[0], a) && lang(sem, Regex::Concat(cs.drop_first()), b),
{
    if lang(sem, Regex::Concat(cs), w) {
        let parts = choose|parts: Seq<Seq<EventView>>| parts.len() == cs.len() && w == parts.flatten()
            && forall|i: int| 0 <= i < cs.len() ==> lang(sem, cs[i], parts[i]);
        let a = parts[0];
        let tail = parts.drop_first();
        let b = tail.flatten();
        assert forall|i: int| 0 <= i < cs.drop_first().len() implies lang(sem, cs.drop_first()[i], tail[i]) by {
            assert(cs.drop_first()[i] == cs[i + 1]);
            assert(tail[i] == parts[i + 1]);
        }
        assert(lang(sem, Regex::Concat(cs.drop_first()), b));
        assert(w == a + b);
    }
    if exists|a: Seq<EventView>, b: Seq<EventView>| w == a + b && lang(sem, cs[0], a) && lang(sem, Regex::Concat(cs.drop_first()), b) {
        let (a, b) = choose|a: Seq<EventView>, b: Seq<EventView>| w == a + b && lang(sem, cs[0], a) && lang(sem, Regex::Concat(cs.drop_first()), b);
        let tail = choose|tail: Seq<Seq<EventView>>| tail.len() == cs.drop_first().len() && b == tail.flatten()
            && forall|i: int| 0 <= i < cs.drop_first().len() ==> lang(sem, cs.drop_first()[i], tail[i]);
        let parts = seq![a] + tail;
        assert(parts.drop_first() =~= tail);
        assert(parts.flatten() == w);
        assert forall|i: int| 0 <= i < cs.len() implies lang(sem, cs[i], parts[i]) by {
            if i > 0 { assert(cs[i] == cs.drop_first()[i - 1]); assert(parts[i] == tail[i - 1]); }
        }
        assert(lang(sem, Regex::Concat(cs), w));
    }
}

pub proof fn lemma_nullable_iff_nil<L>(sem: spec_fn(L, EventView) -> bool, r: Regex<L>)
    ensures nullable(r) <==> lang(sem, r, Seq::empty()),
    decreases r,
{
    match r {
        Regex::Union(cs) => {
            assert forall|i: int| 0 <= i < cs.len() implies nullable(cs[i]) == lang(sem, cs[i], Seq::empty()) by {
                lemma_nullable_iff_nil(sem, cs[i]);
            }
        },
        Regex::Intersect(cs) => {
            assert forall|i: int| 0 <= i < cs.len() implies nullable(cs[i]) == lang(sem, cs[i], Seq::empty()) by {
                lemma_nullable_iff_nil(sem, cs[i]);
            }
        },
        Regex::Not(c) => lemma_nullable_iff_nil(sem, *c),
        Regex::Concat(cs) => {
            assert forall|i: int| 0 <= i < cs.len() implies nullable(cs[i]) == lang(sem, cs[i], Seq::empty()) by {
                lemma_nullable_iff_nil(sem, cs[i]);
            }
            if lang(sem, r, Seq::empty()) {
                let parts = choose|parts: Seq<Seq<EventView>>| parts.len() == cs.len() && Seq::<EventView>::empty() == parts.flatten()
                    && forall|i: int| 0 <= i < cs.len() ==> lang(sem, cs[i], parts[i]);
                lemma_flatten_empty(parts);
                assert forall|i: int| 0 <= i < cs.len() implies nullable(cs[i]) by {
                    assert(parts[i] =~= Seq::<EventView>::empty());
                }
            }
            if nullable(r) {
                let parts = Seq::new(cs.len(), |i: int| Seq::<EventView>::empty());
                lemma_flatten_empty(parts);
                assert(parts.flatten() =~= Seq::<EventView>::empty());
                assert forall|i: int| 0 <= i < cs.len() implies lang(sem, cs[i], parts[i]) by {
                    lemma_nullable_iff_nil(sem, cs[i]);
                    assert(nullable(cs[i]));
                    assert(parts[i] == Seq::<EventView>::empty());
                }
                assert(lang(sem, r, Seq::empty()));
            }
        },
        Regex::Star(c) => {
            let parts = Seq::<Seq<EventView>>::empty();
            assert(lang(sem, r, parts.flatten()));
        },
        _ => {},
    }
}


pub proof fn lemma_concat_prepend<L>(sem: spec_fn(L, EventView) -> bool, c: Regex<L>, cs: Seq<Regex<L>>, w: Seq<EventView>)
    ensures lang(sem, Regex::Concat(seq![c] + cs), w) <==> exists|a: Seq<EventView>, b: Seq<EventView>|
        w == a + b && lang(sem, c, a) && lang(sem, Regex::Concat(cs), b),
{
    lemma_concat_uncons(sem, seq![c] + cs, w);
    assert((seq![c] + cs).drop_first() =~= cs);
}

pub proof fn lemma_cons_split(e: EventView, w: Seq<EventView>, a: Seq<EventView>, b: Seq<EventView>)
    requires seq![e] + w == a + b, a.len() > 0,
    ensures a == seq![e] + a.drop_first(), w == a.drop_first() + b,
{
    broadcast use vstd::seq::group_seq_lemmas;
    assert((seq![e] + w).len() == 1 + w.len());
    assert((a + b).len() == a.len() + b.len());
    assert(seq![e] + w == a + b);
    assert(1 + w.len() == a.len() + b.len());
    assert((seq![e] + w)[0] == e);
    assert((a + b)[0] == a[0]);
    assert(a[0] == e);
    assert(a =~= seq![e] + a.drop_first());
    assert forall|i: int| 0 <= i < w.len() implies w[i] == (a.drop_first() + b)[i] by {
        assert((seq![e] + w)[i + 1] == w[i]);
        assert((a + b)[i + 1] == if i + 1 < a.len() { a[i + 1] } else { b[i + 1 - a.len()] });
    }
    assert(w =~= a.drop_first() + b);
}

pub proof fn lemma_star_parts_cons<L>(sem: spec_fn(L, EventView) -> bool, c: Regex<L>, parts: Seq<Seq<EventView>>, e: EventView, w: Seq<EventView>)
    requires parts.flatten() == seq![e] + w,
        forall|i: int| 0 <= i < parts.len() ==> lang(sem, c, parts[i]),
    ensures exists|a: Seq<EventView>, b: Seq<EventView>| w == a + b && lang(sem, c, seq![e] + a)
        && lang(sem, Regex::Star(Box::new(c)), b),
    decreases parts.len(),
{
    assert(parts.len() > 0);
    let tail = parts.drop_first();
    assert forall|i: int| 0 <= i < tail.len() implies lang(sem, c, tail[i]) by {
        assert(tail[i] == parts[i + 1]);
    }
    if parts[0].len() == 0 {
        assert(parts[0] =~= Seq::<EventView>::empty());
        lemma_star_parts_cons(sem, c, tail, e, w);
    } else {
        let a = parts[0].drop_first();
        let b = tail.flatten();
        lemma_cons_split(e, w, parts[0], b);
        assert(lang(sem, Regex::Star(Box::new(c)), b));
        assert(w == a + b && lang(sem, c, seq![e] + a) && lang(sem, Regex::Star(Box::new(c)), b));
    }
}

pub proof fn lemma_star_cons<L>(sem: spec_fn(L, EventView) -> bool, c: Regex<L>, e: EventView, w: Seq<EventView>)
    ensures lang(sem, Regex::Star(Box::new(c)), seq![e] + w) <==> exists|a: Seq<EventView>, b: Seq<EventView>|
        w == a + b && lang(sem, c, seq![e] + a) && lang(sem, Regex::Star(Box::new(c)), b),
{
    if lang(sem, Regex::Star(Box::new(c)), seq![e] + w) {
        let parts = choose|parts: Seq<Seq<EventView>>| seq![e] + w == parts.flatten()
            && forall|i: int| 0 <= i < parts.len() ==> lang(sem, c, parts[i]);
        lemma_star_parts_cons(sem, c, parts, e, w);
    }
    if exists|a: Seq<EventView>, b: Seq<EventView>| w == a + b && lang(sem, c, seq![e] + a) && lang(sem, Regex::Star(Box::new(c)), b) {
        let (a, b) = choose|a: Seq<EventView>, b: Seq<EventView>| w == a + b && lang(sem, c, seq![e] + a) && lang(sem, Regex::Star(Box::new(c)), b);
        let tail = choose|tail: Seq<Seq<EventView>>| b == tail.flatten()
            && forall|i: int| 0 <= i < tail.len() ==> lang(sem, c, tail[i]);
        let parts = seq![seq![e] + a] + tail;
        assert(parts.drop_first() =~= tail);
        assert(parts.flatten() =~= seq![e] + w);
        assert forall|i: int| 0 <= i < parts.len() implies lang(sem, c, parts[i]) by {
            if i > 0 { assert(parts[i] == tail[i - 1]); }
        }
        assert(lang(sem, Regex::Star(Box::new(c)), seq![e] + w));
    }
}

pub proof fn lemma_lang_union<L>(sem: spec_fn(L, EventView) -> bool, cs: Seq<Regex<L>>, w: Seq<EventView>)
    ensures lang(sem, Regex::Union(cs), w) == (exists|i: int| 0 <= i < cs.len() && lang(sem, cs[i], w)),
{
    reveal_with_fuel(lang, 2);
    assert(Regex::Union(cs)->Union_0 == cs);
}

pub proof fn lemma_union_optional<L>(sem: spec_fn(L, EventView) -> bool, a: Regex<L>, b: Regex<L>, flag: bool, w: Seq<EventView>)
    ensures lang(sem, Regex::Union(seq![a] + if flag { seq![b] } else { Seq::empty() }), w)
        == (lang(sem, a, w) || (flag && lang(sem, b, w))),
{
    broadcast use vstd::seq::group_seq_lemmas;
    reveal_with_fuel(lang, 2);
    let cs = seq![a] + if flag { seq![b] } else { Seq::empty() };
    lemma_lang_union(sem, cs, w);
    if lang(sem, Regex::Union(cs), w) {
        let i = choose|i: int| 0 <= i < cs.len() && lang(sem, cs[i], w);
        assert(i == 0 || (flag && i == 1));
        if i == 0 { assert(cs[i] == a); } else { assert(cs[i] == b); }
    }
    if lang(sem, a, w) {
        assert(cs.len() >= 1);
        assert(cs[0] == a);
        assert(0 <= 0int < cs.len() && lang(sem, cs[0], w));
        assert(exists|i: int| 0 <= i < cs.len() && lang(sem, cs[i], w));
        assert(lang(sem, Regex::Union(cs), w));
    }
    if flag && lang(sem, b, w) {
        assert(cs.len() == 2);
        assert(cs[1] == b);
        assert(exists|i: int| 0 <= i < cs.len() && lang(sem, cs[i], w));
        assert(lang(sem, Regex::Union(cs), w));
    }
}

pub proof fn lemma_lang_intersect<L>(sem: spec_fn(L, EventView) -> bool, cs: Seq<Regex<L>>, w: Seq<EventView>)
    ensures lang(sem, Regex::Intersect(cs), w) == (forall|i: int| 0 <= i < cs.len() ==> lang(sem, cs[i], w)),
{
    reveal_with_fuel(lang, 2);
    assert(Regex::Intersect(cs)->Intersect_0 == cs);
    if lang(sem, Regex::Intersect(cs), w) {
        assert forall|i: int| 0 <= i < cs.len() implies lang(sem, cs[i], w) by {
            assert(lang(sem, Regex::Intersect(cs), w));
        }
    }
}

pub proof fn lemma_derivative_concat<L>(sem: spec_fn(L, EventView) -> bool, e: EventView, bound: Regex<L>, cs: Seq<Regex<L>>, w: Seq<EventView>)
    requires
        forall|i: int| 0 <= i < cs.len() ==> is_smaller_than(cs[i], bound),
        forall|i: int, v: Seq<EventView>| 0 <= i < cs.len() ==> lang(sem, derivative(sem, e, cs[i]), v) == lang(sem, cs[i], seq![e] + v),
    ensures lang(sem, derivative_concat(sem, e, bound, cs), w) == lang(sem, Regex::Concat(cs), seq![e] + w),
    decreases cs.len(),
{
    if cs.len() == 0 {
        if lang(sem, Regex::Concat(cs), seq![e] + w) {
            let parts = choose|parts: Seq<Seq<EventView>>| parts.len() == cs.len() && seq![e] + w == parts.flatten()
                && forall|i: int| 0 <= i < cs.len() ==> lang(sem, cs[i], parts[i]);
            assert(parts =~= Seq::<Seq<EventView>>::empty());
        }
    } else {
        let c = cs[0];
        let rest = cs.drop_first();
        assert forall|i: int| 0 <= i < rest.len() implies is_smaller_than(rest[i], bound) by {
            assert(rest[i] == cs[i + 1]);
        }
        assert forall|i: int, v: Seq<EventView>| 0 <= i < rest.len() implies lang(sem, derivative(sem, e, rest[i]), v) == lang(sem, rest[i], seq![e] + v) by {
            assert(rest[i] == cs[i + 1]);
        }
        lemma_derivative_concat(sem, e, bound, rest, w);
        lemma_nullable_iff_nil(sem, c);
        let dc = derivative(sem, e, c);
        let dr = derivative_concat(sem, e, bound, rest);
        let left = Regex::Concat(seq![dc] + rest);
        lemma_union_optional(sem, left, dr, nullable(c), w);
        lemma_concat_prepend(sem, dc, rest, w);
        lemma_concat_uncons(sem, cs, seq![e] + w);
        if lang(sem, derivative_concat(sem, e, bound, cs), w) {
            if lang(sem, left, w) {
                let (a, b) = choose|a: Seq<EventView>, b: Seq<EventView>| w == a + b && lang(sem, dc, a) && lang(sem, Regex::Concat(rest), b);
                assert(lang(sem, c, seq![e] + a));
                assert(seq![e] + w =~= (seq![e] + a) + b);
                assert(exists|a0: Seq<EventView>, b0: Seq<EventView>| seq![e] + w == a0 + b0 && lang(sem, c, a0) && lang(sem, Regex::Concat(rest), b0));
            } else {
                assert(nullable(c) && lang(sem, dr, w));
                let a = Seq::<EventView>::empty();
                let b = seq![e] + w;
                assert(a + b =~= b);
                assert(lang(sem, c, a) && lang(sem, Regex::Concat(rest), b));
                assert(exists|a0: Seq<EventView>, b0: Seq<EventView>| seq![e] + w == a0 + b0 && lang(sem, c, a0) && lang(sem, Regex::Concat(rest), b0));
            }
            assert(lang(sem, Regex::Concat(cs), seq![e] + w));
        }
        if lang(sem, Regex::Concat(cs), seq![e] + w) {
            let (a, b) = choose|a: Seq<EventView>, b: Seq<EventView>| seq![e] + w == a + b && lang(sem, c, a) && lang(sem, Regex::Concat(rest), b);
            if a.len() == 0 {
                assert(a =~= Seq::<EventView>::empty());
                assert(b =~= seq![e] + w);
                assert(nullable(c));
                assert(lang(sem, dr, w));
            } else {
                lemma_cons_split(e, w, a, b);
                let v = a.drop_first();
                assert(lang(sem, dc, v));
                assert(exists|a0: Seq<EventView>, b0: Seq<EventView>| w == a0 + b0 && lang(sem, dc, a0) && lang(sem, Regex::Concat(rest), b0));
                assert(lang(sem, left, w));
            }
            assert(lang(sem, derivative_concat(sem, e, bound, cs), w));
        }
    }
}

pub proof fn lemma_concat_singleton<L>(sem: spec_fn(L, EventView) -> bool, r: Regex<L>, w: Seq<EventView>)
    ensures lang(sem, Regex::Concat(seq![r]), w) == lang(sem, r, w),
{
    if lang(sem, Regex::Concat(seq![r]), w) {
        let parts = choose|parts: Seq<Seq<EventView>>| parts.len() == 1 && w == parts.flatten()
            && forall|i: int| 0 <= i < 1 ==> lang(sem, seq![r][i], parts[i]);
        parts.lemma_flatten_one_element();
        assert(lang(sem, r, w));
    }
    if lang(sem, r, w) {
        let parts = seq![w];
        parts.lemma_flatten_one_element();
        assert forall|i: int| 0 <= i < 1 implies lang(sem, seq![r][i], parts[i]) by { assert(i == 0); }
        assert(lang(sem, Regex::Concat(seq![r]), w));
    }
}

pub proof fn lemma_concat_pair<L>(sem: spec_fn(L, EventView) -> bool, a: Regex<L>, b: Regex<L>, w: Seq<EventView>)
    ensures lang(sem, Regex::Concat(seq![a, b]), w) <==> exists|u: Seq<EventView>, v: Seq<EventView>|
        w == u + v && lang(sem, a, u) && lang(sem, b, v),
{
    assert(seq![a, b] =~= seq![a] + seq![b]);
    lemma_concat_prepend(sem, a, seq![b], w);
    assert forall|v: Seq<EventView>| lang(sem, Regex::Concat(seq![b]), v) == lang(sem, b, v) by {
        lemma_concat_singleton(sem, b, v);
    }
}

pub proof fn lemma_derivative_correct<L>(sem: spec_fn(L, EventView) -> bool, e: EventView, r: Regex<L>, w: Seq<EventView>)
    ensures lang(sem, derivative(sem, e, r), w) <==> lang(sem, r, seq![e] + w),
    decreases r,
{
    match r {
        Regex::Union(cs) => {
            let ds = Seq::new(cs.len(), |i: int| if 0 <= i < cs.len() { derivative(sem, e, cs[i]) } else { Regex::Empty });
            assert(ds.len() == cs.len());
            assert(derivative(sem, e, r)->Union_0 =~= ds);
            assert(derivative(sem, e, r) == Regex::Union(ds));
            lemma_lang_union(sem, ds, w);
            lemma_lang_union(sem, cs, seq![e] + w);
            assert forall|i: int| 0 <= i < cs.len() implies lang(sem, ds[i], w) == lang(sem, cs[i], seq![e] + w) by {
                lemma_derivative_correct(sem, e, cs[i], w);
            }
            assert(lang(sem, derivative(sem, e, r), w) == lang(sem, r, seq![e] + w));
        },
        Regex::Intersect(cs) => {
            let ds = Seq::new(cs.len(), |i: int| if 0 <= i < cs.len() { derivative(sem, e, cs[i]) } else { Regex::Empty });
            assert(ds.len() == cs.len());
            assert(derivative(sem, e, r)->Intersect_0 =~= ds);
            assert(derivative(sem, e, r) == Regex::Intersect(ds));
            lemma_lang_intersect(sem, ds, w);
            lemma_lang_intersect(sem, cs, seq![e] + w);
            assert forall|i: int| 0 <= i < cs.len() implies lang(sem, ds[i], w) == lang(sem, cs[i], seq![e] + w) by {
                lemma_derivative_correct(sem, e, cs[i], w);
            }
            assert(lang(sem, derivative(sem, e, r), w) == lang(sem, r, seq![e] + w));
        },
        Regex::Not(c) => lemma_derivative_correct(sem, e, *c, w),
        Regex::Star(c) => {
            lemma_star_cons(sem, *c, e, w);
            lemma_concat_pair(sem, derivative(sem, e, *c), Regex::Star(c), w);
            assert forall|a: Seq<EventView>| lang(sem, derivative(sem, e, *c), a) == lang(sem, *c, seq![e] + a) by {
                lemma_derivative_correct(sem, e, *c, a);
            }
            assert(lang(sem, derivative(sem, e, r), w) == lang(sem, r, seq![e] + w));
        },
        Regex::Concat(cs) => {
            assert forall|i: int| 0 <= i < cs.len() implies is_smaller_than(cs[i], r) by { }
            assert forall|i: int, v: Seq<EventView>| 0 <= i < cs.len() implies lang(sem, derivative(sem, e, cs[i]), v) == lang(sem, cs[i], seq![e] + v) by {
                lemma_derivative_correct(sem, e, cs[i], v);
            }
            lemma_derivative_concat(sem, e, r, cs, w);
        },
        Regex::Test(_) => { assert((seq![e] + w)[0] == e); },
        _ => {},
    }
}

pub proof fn lemma_derive_word_correct<L>(sem: spec_fn(L, EventView) -> bool, prefix: Seq<EventView>, r: Regex<L>, suffix: Seq<EventView>)
    ensures lang(sem, derive_word(sem, prefix, r), suffix) == lang(sem, r, prefix + suffix),
    decreases prefix.len(),
{
    if prefix.len() == 0 { assert(prefix + suffix =~= suffix); }
    else {
        lemma_derive_word_correct(sem, prefix.drop_first(), derivative(sem, prefix[0], r), suffix);
        lemma_derivative_correct(sem, prefix[0], r, prefix.drop_first() + suffix);
        assert(seq![prefix[0]] + (prefix.drop_first() + suffix) =~= prefix + suffix);
    }
}

pub proof fn lemma_derive_word_nullable<L>(sem: spec_fn(L, EventView) -> bool, w: Seq<EventView>, r: Regex<L>)
    ensures nullable(derive_word(sem, w, r)) == lang(sem, r, w),
{
    lemma_nullable_iff_nil(sem, derive_word(sem, w, r));
    lemma_derive_word_correct(sem, w, r, Seq::empty());
    assert(w + Seq::<EventView>::empty() =~= w);
}

pub proof fn lemma_interp_const<L>(sem: spec_fn(L, EventView) -> bool, e: EventView, r: Regex<L>)
    ensures interp_transition(sem, e, Transition::Const(r)) == r,
{ }

pub proof fn lemma_interp_if<L>(sem: spec_fn(L, EventView) -> bool, e: EventView, l: L, a: Transition<L>, b: Transition<L>)
    ensures interp_transition(sem, e, Transition::If(l, Box::new(a), Box::new(b)))
        == if sem(l, e) { interp_transition(sem, e, a) } else { interp_transition(sem, e, b) },
{ }

pub proof fn lemma_interp_union<L>(sem: spec_fn(L, EventView) -> bool, e: EventView, cs: Seq<Transition<L>>, w: Seq<EventView>)
    ensures lang(sem, interp_transition(sem, e, Transition::Union(cs)), w)
        == (exists|i: int| 0 <= i < cs.len() && lang(sem, interp_transition(sem, e, cs[i]), w)),
{
    let r = interp_transition(sem, e, Transition::Union(cs));
    assert(r is Union);
    assert((r->Union_0).len() == cs.len());
    lemma_lang_union(sem, r->Union_0, w);
    assert forall|i: int| 0 <= i < cs.len() implies (r->Union_0)[i] == interp_transition(sem, e, cs[i]) by { }
    assert forall|i: int| 0 <= i < cs.len() implies lang(sem, (r->Union_0)[i], w) == lang(sem, interp_transition(sem, e, cs[i]), w) by {
        assert((r->Union_0)[i] == interp_transition(sem, e, cs[i]));
    }
    if lang(sem, r, w) {
        let i = choose|i: int| 0 <= i < (r->Union_0).len() && lang(sem, (r->Union_0)[i], w);
        assert(lang(sem, interp_transition(sem, e, cs[i]), w));
        assert(exists|j: int| 0 <= j < cs.len() && lang(sem, interp_transition(sem, e, cs[j]), w));
    }
    if exists|i: int| 0 <= i < cs.len() && lang(sem, interp_transition(sem, e, cs[i]), w) {
        let i = choose|i: int| 0 <= i < cs.len() && lang(sem, interp_transition(sem, e, cs[i]), w);
        assert(lang(sem, (r->Union_0)[i], w));
        assert(exists|j: int| 0 <= j < (r->Union_0).len() && lang(sem, (r->Union_0)[j], w));
        assert(lang(sem, r, w));
    }
}

pub proof fn lemma_interp_intersect<L>(sem: spec_fn(L, EventView) -> bool, e: EventView, cs: Seq<Transition<L>>, w: Seq<EventView>)
    ensures lang(sem, interp_transition(sem, e, Transition::Intersect(cs)), w)
        == (forall|i: int| 0 <= i < cs.len() ==> lang(sem, interp_transition(sem, e, cs[i]), w)),
{
    let r = interp_transition(sem, e, Transition::Intersect(cs));
    assert(r is Intersect);
    assert((r->Intersect_0).len() == cs.len());
    lemma_lang_intersect(sem, r->Intersect_0, w);
    assert forall|i: int| 0 <= i < cs.len() implies (r->Intersect_0)[i] == interp_transition(sem, e, cs[i]) by { }
    assert forall|i: int| 0 <= i < cs.len() implies lang(sem, (r->Intersect_0)[i], w) == lang(sem, interp_transition(sem, e, cs[i]), w) by {
        assert((r->Intersect_0)[i] == interp_transition(sem, e, cs[i]));
    }
    if lang(sem, r, w) {
        assert forall|i: int| 0 <= i < cs.len() implies lang(sem, interp_transition(sem, e, cs[i]), w) by {
            assert(lang(sem, (r->Intersect_0)[i], w));
        }
    }
    if forall|i: int| 0 <= i < cs.len() ==> lang(sem, interp_transition(sem, e, cs[i]), w) {
        assert forall|i: int| 0 <= i < (r->Intersect_0).len() implies lang(sem, (r->Intersect_0)[i], w) by {
            assert(lang(sem, interp_transition(sem, e, cs[i]), w));
        }
        assert(lang(sem, r, w));
    }
}

pub proof fn lemma_interp_not<L>(sem: spec_fn(L, EventView) -> bool, e: EventView, t: Transition<L>)
    ensures interp_transition(sem, e, Transition::Not(Box::new(t))) == Regex::Not(Box::new(interp_transition(sem, e, t))),
{ }

pub proof fn lemma_interp_append<L>(sem: spec_fn(L, EventView) -> bool, e: EventView, t: Transition<L>, suffix: Seq<Regex<L>>)
    ensures interp_transition(sem, e, Transition::Append(Box::new(t), suffix)) == Regex::Concat(seq![interp_transition(sem, e, t)] + suffix),
{ }

pub enum Term {
    Constant(nat),
    Variable(HistoryField),
}

pub enum SrcTest {
    Bool(bool),
    And(Seq<SrcTest>),
    Or(Seq<SrcTest>),
    Eq(HistoryField, Term),
    Neq(HistoryField, Term),
}

pub enum HeadField { Any, Constant(nat), Bind }

pub struct Head {
    pub principal: HeadField,
    pub action: HeadField,
    pub resource: HeadField,
}

pub open spec fn head_field(head: Head, field: HistoryField) -> HeadField {
    match field {
        HistoryField::Principal => head.principal,
        HistoryField::Action => head.action,
        HistoryField::Resource => head.resource,
    }
}

pub open spec fn head_field_match(head: HeadField, request: nat, binding: nat) -> bool {
    match head {
        HeadField::Any => binding == 0,
        HeadField::Constant(value) => request == value && binding == 0,
        HeadField::Bind => binding == request,
    }
}

pub open spec fn head_match(head: Head, request: EventView, theta: Subst) -> bool {
    head_field_match(head.principal, request.principal, theta.principal)
        && head_field_match(head.action, request.action, theta.action)
        && head_field_match(head.resource, request.resource, theta.resource)
}

pub open spec fn head_bindings(head: Head, request: EventView) -> Subst {
    EventView {
        principal: if head.principal is Bind { request.principal } else { 0 },
        action: if head.action is Bind { request.action } else { 0 },
        resource: if head.resource is Bind { request.resource } else { 0 },
    }
}

pub open spec fn term_value(theta: Subst, term: Term) -> nat {
    match term {
        Term::Constant(value) => value,
        Term::Variable(field) => field_value(theta, field),
    }
}

pub open spec fn src_test_holds(theta: Subst, test: SrcTest, event: EventView) -> bool
    decreases test,
{
    match test {
        SrcTest::Bool(value) => value,
        SrcTest::And(children) => forall|i: int| 0 <= i < children.len()
            ==> src_test_holds(theta, children[i], event),
        SrcTest::Or(children) => exists|i: int| 0 <= i < children.len()
            && src_test_holds(theta, children[i], event),
        SrcTest::Eq(field, term) => field_value(event, field) == term_value(theta, term),
        SrcTest::Neq(field, term) => field_value(event, field) != term_value(theta, term),
    }
}

pub open spec fn term_wf(field: HistoryField, term: Term, head: Head) -> bool {
    match term {
        Term::Constant(value) => 0 < value <= u64::MAX,
        Term::Variable(variable) => variable == field && head_field(head, field) is Bind,
    }
}

pub open spec fn head_wf(head: Head) -> bool {
    (match head.principal {
        HeadField::Constant(value) => 0 < value <= u64::MAX,
        _ => true,
    }) && (match head.action {
        HeadField::Constant(value) => 0 < value <= u64::MAX,
        _ => true,
    }) && (match head.resource {
        HeadField::Constant(value) => 0 < value <= u64::MAX,
        _ => true,
    })
}

pub open spec fn test_wf(test: SrcTest, head: Head) -> bool
    decreases test,
{
    match test {
        SrcTest::Bool(_) => true,
        SrcTest::And(children) | SrcTest::Or(children) => forall|i: int|
            0 <= i < children.len() ==> test_wf(children[i], head),
        SrcTest::Eq(field, term) | SrcTest::Neq(field, term) => term_wf(field, term, head),
    }
}

pub open spec fn tail_wf(tail: Regex<SrcTest>, head: Head) -> bool
    decreases tail,
{
    match tail {
        Regex::Test(test) => test_wf(test, head),
        Regex::Union(children) | Regex::Concat(children) | Regex::Intersect(children) =>
            forall|i: int| 0 <= i < children.len() ==> tail_wf(children[i], head),
        Regex::Star(child) | Regex::Not(child) => tail_wf(*child, head),
        _ => true,
    }
}

pub open spec fn pair_lang(head: Head, tail: Regex<SrcTest>, request: EventView, history: Seq<EventView>) -> bool {
    exists|theta: Subst| head_match(head, request, theta)
        && lang(|test: SrcTest, event: EventView| src_test_holds(theta, test, event), tail, history)
}

pub proof fn lemma_head_match_unique_subst(head: Head, request: EventView, left: Subst, right: Subst)
    requires head_match(head, request, left), head_match(head, request, right),
    ensures left == right,
{
    match head.principal { HeadField::Any => {}, HeadField::Constant(_) => {}, HeadField::Bind => {} }
    match head.action { HeadField::Any => {}, HeadField::Constant(_) => {}, HeadField::Bind => {} }
    match head.resource { HeadField::Any => {}, HeadField::Constant(_) => {}, HeadField::Bind => {} }
}

pub proof fn lemma_pair_lang_substitutions(head: Head, tail: Regex<SrcTest>, request: EventView,
    history: Seq<EventView>, theta: Subst)
    requires head_match(head, request, theta),
    ensures pair_lang(head, tail, request, history)
        == lang(|test: SrcTest, event: EventView| src_test_holds(theta, test, event), tail, history),
{
    if pair_lang(head, tail, request, history) {
        let other = choose|other: Subst| head_match(head, request, other)
            && lang(|test: SrcTest, event: EventView| src_test_holds(other, test, event), tail, history);
        lemma_head_match_unique_subst(head, request, theta, other);
    }
    if lang(|test: SrcTest, event: EventView| src_test_holds(theta, test, event), tail, history) {
        assert(exists|other: Subst| head_match(head, request, other)
            && lang(|test: SrcTest, event: EventView| src_test_holds(other, test, event), tail, history));
    }
}

/// The selected batch is compositional; nullable is used only at the fixed target.
pub proof fn lemma_derive_word_append<L>(sem: spec_fn(L, EventView) -> bool,
    xs: Seq<EventView>, ys: Seq<EventView>, root: Regex<L>)
    ensures derive_word(sem, xs + ys, root) == derive_word(sem, ys, derive_word(sem, xs, root)),
    decreases xs.len(),
{
    if xs.len() == 0 {
        assert(xs + ys =~= ys);
    } else {
        assert((xs + ys)[0] == xs[0]);
        assert((xs + ys).drop_first() =~= xs.drop_first() + ys);
        lemma_derive_word_append(sem, xs.drop_first(), ys, derivative(sem, xs[0], root));
    }
}

pub open spec fn selected_end(consumed: nat, target: nat, batch_size: nat) -> nat {
    consumed + if batch_size < target - consumed { batch_size } else { (target - consumed) as nat }
}

pub proof fn lemma_selected_end(consumed: nat, target: nat, batch_size: nat)
    requires consumed <= target, batch_size > 0,
    ensures consumed <= selected_end(consumed, target, batch_size) <= target,
        consumed < target ==> consumed < selected_end(consumed, target, batch_size),
        selected_end(consumed, target, batch_size) - consumed <= batch_size,
        target - consumed <= batch_size ==> selected_end(consumed, target, batch_size) == target,
{ }

pub proof fn lemma_batch_prefix_composition<L>(sem: spec_fn(L, EventView) -> bool,
    history: Seq<EventView>, root: Regex<L>, consumed: nat, end: nat)
    requires consumed <= end <= history.len(),
    ensures derive_word(sem, history.subrange(consumed as int, end as int),
        derive_word(sem, history.take(consumed as int), root))
        == derive_word(sem, history.take(end as int), root),
{
    assert(history.take(consumed as int) + history.subrange(consumed as int, end as int)
        =~= history.take(end as int));
    lemma_derive_word_append(sem, history.take(consumed as int),
        history.subrange(consumed as int, end as int), root);
}

pub proof fn lemma_full_target_answer<L>(sem: spec_fn(L, EventView) -> bool,
    history: Seq<EventView>, root: Regex<L>, target: nat)
    requires target <= history.len(),
    ensures nullable(derive_word(sem, history.take(target as int), root))
        == lang(sem, root, history.take(target as int)),
{
    lemma_derive_word_nullable(sem, history.take(target as int), root);
}

pub struct HistoryStateView {
    pub events: Seq<EventView>,
    pub revision: nat,
}

/// Successful locked mutations either append, do nothing, or truncate with a checked revision.
pub open spec fn history_mutation(before: HistoryStateView, after: HistoryStateView) -> bool {
    before.revision <= u64::MAX && after.revision <= u64::MAX && (
        (before.revision == after.revision && before.events.is_prefix_of(after.events))
        || (before.revision < u64::MAX && after.revision == before.revision + 1
            && after.events.len() < before.events.len()
            && after.events == before.events.take(after.events.len() as int)))
}

pub proof fn lemma_revision_chain_preserves_prefix(states: Seq<HistoryStateView>)
    requires states.len() > 0,
        forall|i: int| 0 < i < states.len() ==> #[trigger] history_mutation(states[i - 1], states[i]),
    ensures states.first().revision <= states.last().revision,
        states.first().revision == states.last().revision
            ==> states.first().events.is_prefix_of(states.last().events),
    decreases states.len(),
{
    if states.len() > 1 {
        let prior = states.drop_last();
        assert forall|i: int| 0 < i < prior.len() implies #[trigger] history_mutation(prior[i - 1], prior[i]) by {
            assert(prior[i - 1] == states[i - 1]);
            assert(prior[i] == states[i]);
        }
        lemma_revision_chain_preserves_prefix(prior);
        assert(history_mutation(prior.last(), states.last()));
        if states.first().revision == states.last().revision {
            assert(prior.first().revision == prior.last().revision);
            assert(prior.last().events.is_prefix_of(states.last().events));
            assert(states.last().events.take(states.first().events.len() as int)
                =~= states.first().events);
        }
    }
}

/// Same-revision snapshots refer to an immutable prefix, not to the current length.
pub open spec fn snapshot_valid(captured: Seq<EventView>, revision: nat,
    current: Seq<EventView>, current_revision: nat) -> bool {
    revision == current_revision && captured.is_prefix_of(current)
}

pub proof fn lemma_append_preserves_snapshot(captured: Seq<EventView>, revision: nat,
    current: Seq<EventView>, suffix: Seq<EventView>)
    requires snapshot_valid(captured, revision, current, revision),
    ensures snapshot_valid(captured, revision, current + suffix, revision),
{
    assert(captured.len() <= current.len());
    assert((current + suffix).take(captured.len() as int) =~= captured);
}

pub proof fn lemma_truncate_invalidates_snapshot(captured: Seq<EventView>, revision: nat,
    current: Seq<EventView>, keep: nat)
    requires keep < current.len(), revision < u64::MAX,
    ensures !snapshot_valid(captured, revision, current.take(keep as int), revision + 1),
{ }

pub proof fn lemma_exact_utf8_equality(left: Seq<char>, right: Seq<char>)
    ensures (vstd::utf8::encode_utf8(left) == vstd::utf8::encode_utf8(right)) == (left == right),
{
    vstd::utf8::encode_utf8_decode_utf8(left);
    vstd::utf8::encode_utf8_decode_utf8(right);
}

/// Mutex linearization composes the checked executable allocator's consecutive states.
pub proof fn lemma_allocator_nonreuse(first: nat, after_first: nat, before_later: nat, later: nat)
    requires after_first == first + 1, after_first <= before_later, later == before_later,
    ensures first < later,
{ }

/// Exact UTF-8 bytes are keys; no normalization or ancestry relation is modeled.
pub open spec fn interner_wf(paths: Map<Seq<u8>, nat>, next: nat) -> bool {
    0 < next <= u64::MAX
        && (forall|path: Seq<u8>| paths.contains_key(path) ==> 0 < paths[path] < next)
        && (forall|left: Seq<u8>, right: Seq<u8>| paths.contains_key(left)
            && paths.contains_key(right) && paths[left] == paths[right] ==> left == right)
}

pub proof fn lemma_interner_raise_frontier(paths: Map<Seq<u8>, nat>, before: nat, after: nat)
    requires interner_wf(paths, before), before <= after <= u64::MAX,
    ensures interner_wf(paths, after),
{ }

pub proof fn lemma_interner_exact_equality(paths: Map<Seq<u8>, nat>, next: nat,
    left: Seq<u8>, right: Seq<u8>)
    requires interner_wf(paths, next), paths.contains_key(left), paths.contains_key(right),
    ensures (paths[left] == paths[right]) == (left == right),
{ }

pub proof fn lemma_interner_fresh_nonreuse(paths: Map<Seq<u8>, nat>, next: nat,
    path: Seq<u8>, allocated: nat)
    requires interner_wf(paths, next), !paths.contains_key(path),
        next <= allocated < u64::MAX,
    ensures interner_wf(paths.insert(path, allocated), allocated + 1),
        forall|old_path: Seq<u8>| paths.contains_key(old_path)
            ==> paths.insert(path, allocated)[old_path] == paths[old_path]
                && paths[old_path] != allocated,
{
    assert forall|left: Seq<u8>, right: Seq<u8>| paths.insert(path, allocated).contains_key(left)
        && paths.insert(path, allocated).contains_key(right)
        && paths.insert(path, allocated)[left] == paths.insert(path, allocated)[right]
        implies left == right by {
        if left != path && right != path { assert(paths[left] == paths[right]); }
    }
}

}
