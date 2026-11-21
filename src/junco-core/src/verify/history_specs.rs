// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Independent pair-language semantics: request is the head, followed by history
//! in oldest-to-newest order. Runtime errors carry no Boolean interpretation.

use alloc::boxed::Box;
use alloc::vec::Vec;
use history_syntax::{MAX_ARITY, syntax::Component};
use vstd::prelude::*;
use vstd::std_specs::iter::IteratorSpec;

verus! {

/// Resource failures and policy rejection remain distinct from impossible internal failures.
pub open spec fn no_invariant_failure<T>(result: Result<T, crate::errors::HistoryError>) -> bool {
    !(result matches Err(crate::errors::HistoryError::Invariant { .. }))
}

pub open spec fn no_invariant_compile_failure<T>(result: Result<T, crate::errors::CompileError>) -> bool {
    !(result matches Err(crate::errors::CompileError::Runtime(crate::errors::HistoryError::Invariant { .. })))
}


/// Exact yielded items for conversions whose result obeys the prophetic iterator laws.
#[verifier::prophetic]
pub open spec fn into_iter_yields<I: IntoIterator>(input: I, items: Seq<I::Item>) -> bool {
    forall|iter: I::IntoIter|
        #[trigger] call_ensures(I::into_iter, (input,), iter)
        ==> iter.obeys_prophetic_iter_laws() && iter.remaining() == items
}

/// Owned vectors convert without changing their exact item sequence.
pub proof fn lemma_vec_into_iter_yields<T>(input: Vec<T>)
    ensures into_iter_yields(input, input@),
{
    assert forall|iter: alloc::vec::IntoIter<T>|
        #[trigger] call_ensures(Vec::<T>::into_iter, (input,), iter)
        implies iter.obeys_prophetic_iter_laws() && iter.remaining() == input@ by {
        assert(iter.remaining() == input@);
    }
}

/// Iterator identity conversion preserves the caller's established prophetic laws.
pub proof fn lemma_iterator_into_iter_yields<I: Iterator>(input: I)
    requires input.obeys_prophetic_iter_laws(),
    ensures into_iter_yields(input, input.remaining()),
{
    assert forall|iter: I|
        #[trigger] call_ensures(I::into_iter, (input,), iter)
        implies iter.obeys_prophetic_iter_laws() && iter.remaining() == input.remaining() by {
        assert(iter == input);
    }
}

/// Numeric event coordinates; zero is reserved for an unbound binding coordinate.
pub type EventView = Seq<nat>;

pub type Subst = EventView;

pub open spec fn event_wf(event: EventView, arity: nat) -> bool {
    event.len() == arity && forall|i: int| 0 <= i < event.len() ==> event[i] <= u64::MAX
}

pub open spec fn field_value(event: EventView, field: Component) -> nat {
    event[field.0 as int]
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

pub open spec fn numeric_lang<L>(sem: spec_fn(L, EventView) -> bool, r: Regex<L>, w: Seq<EventView>) -> bool decreases r {
    match r {
        Regex::Empty => false,
        Regex::All => true,
        Regex::Epsilon => w.len() == 0,
        Regex::Test(l) => w.len() == 1 && sem(l, w[0]),
        Regex::Union(cs) => exists|i: int| 0 <= i < cs.len() && numeric_lang(sem, cs[i], w),
        Regex::Intersect(cs) => forall|i: int| 0 <= i < cs.len() ==> numeric_lang(sem, cs[i], w),
        Regex::Not(c) => !numeric_lang(sem, *c, w),
        Regex::Concat(cs) => exists|parts: Seq<Seq<EventView>>| parts.len() == cs.len() && w == parts.flatten()
            && forall|i: int| 0 <= i < cs.len() ==> numeric_lang(sem, cs[i], parts[i]),
        Regex::Star(c) => exists|parts: Seq<Seq<EventView>>| w == parts.flatten()
            && forall|i: int| 0 <= i < parts.len() ==> numeric_lang(sem, *c, parts[i]),
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
    ensures numeric_lang(sem, Regex::Concat(cs), w) <==> exists|a: Seq<EventView>, b: Seq<EventView>|
        w == a + b && numeric_lang(sem, cs[0], a) && numeric_lang(sem, Regex::Concat(cs.drop_first()), b),
{
    if numeric_lang(sem, Regex::Concat(cs), w) {
        let parts = choose|parts: Seq<Seq<EventView>>| parts.len() == cs.len() && w == parts.flatten()
            && forall|i: int| 0 <= i < cs.len() ==> numeric_lang(sem, cs[i], parts[i]);
        let a = parts[0];
        let tail = parts.drop_first();
        let b = tail.flatten();
        assert forall|i: int| 0 <= i < cs.drop_first().len() implies numeric_lang(sem, cs.drop_first()[i], tail[i]) by {
            assert(cs.drop_first()[i] == cs[i + 1]);
            assert(tail[i] == parts[i + 1]);
        }
        assert(numeric_lang(sem, Regex::Concat(cs.drop_first()), b));
        assert(w == a + b);
    }
    if exists|a: Seq<EventView>, b: Seq<EventView>| w == a + b && numeric_lang(sem, cs[0], a) && numeric_lang(sem, Regex::Concat(cs.drop_first()), b) {
        let (a, b) = choose|a: Seq<EventView>, b: Seq<EventView>| w == a + b && numeric_lang(sem, cs[0], a) && numeric_lang(sem, Regex::Concat(cs.drop_first()), b);
        let tail = choose|tail: Seq<Seq<EventView>>| tail.len() == cs.drop_first().len() && b == tail.flatten()
            && forall|i: int| 0 <= i < cs.drop_first().len() ==> numeric_lang(sem, cs.drop_first()[i], tail[i]);
        let parts = seq![a] + tail;
        assert(parts.drop_first() =~= tail);
        assert(parts.flatten() == w);
        assert forall|i: int| 0 <= i < cs.len() implies numeric_lang(sem, cs[i], parts[i]) by {
            if i > 0 { assert(cs[i] == cs.drop_first()[i - 1]); assert(parts[i] == tail[i - 1]); }
        }
        assert(numeric_lang(sem, Regex::Concat(cs), w));
    }
}

pub proof fn lemma_nullable_iff_nil<L>(sem: spec_fn(L, EventView) -> bool, r: Regex<L>)
    ensures nullable(r) <==> numeric_lang(sem, r, Seq::empty()),
    decreases r,
{
    match r {
        Regex::Union(cs) => {
            assert forall|i: int| 0 <= i < cs.len() implies nullable(cs[i]) == numeric_lang(sem, cs[i], Seq::empty()) by {
                lemma_nullable_iff_nil(sem, cs[i]);
            }
        },
        Regex::Intersect(cs) => {
            assert forall|i: int| 0 <= i < cs.len() implies nullable(cs[i]) == numeric_lang(sem, cs[i], Seq::empty()) by {
                lemma_nullable_iff_nil(sem, cs[i]);
            }
        },
        Regex::Not(c) => lemma_nullable_iff_nil(sem, *c),
        Regex::Concat(cs) => {
            assert forall|i: int| 0 <= i < cs.len() implies nullable(cs[i]) == numeric_lang(sem, cs[i], Seq::empty()) by {
                lemma_nullable_iff_nil(sem, cs[i]);
            }
            if numeric_lang(sem, r, Seq::empty()) {
                let parts = choose|parts: Seq<Seq<EventView>>| parts.len() == cs.len() && Seq::<EventView>::empty() == parts.flatten()
                    && forall|i: int| 0 <= i < cs.len() ==> numeric_lang(sem, cs[i], parts[i]);
                lemma_flatten_empty(parts);
                assert forall|i: int| 0 <= i < cs.len() implies nullable(cs[i]) by {
                    assert(parts[i] =~= Seq::<EventView>::empty());
                }
            }
            if nullable(r) {
                let parts = Seq::new(cs.len(), |i: int| Seq::<EventView>::empty());
                lemma_flatten_empty(parts);
                assert(parts.flatten() =~= Seq::<EventView>::empty());
                assert forall|i: int| 0 <= i < cs.len() implies numeric_lang(sem, cs[i], parts[i]) by {
                    lemma_nullable_iff_nil(sem, cs[i]);
                    assert(nullable(cs[i]));
                    assert(parts[i] == Seq::<EventView>::empty());
                }
                assert(numeric_lang(sem, r, Seq::empty()));
            }
        },
        Regex::Star(c) => {
            let parts = Seq::<Seq<EventView>>::empty();
            assert(numeric_lang(sem, r, parts.flatten()));
        },
        _ => {},
    }
}


pub proof fn lemma_concat_prepend<L>(sem: spec_fn(L, EventView) -> bool, c: Regex<L>, cs: Seq<Regex<L>>, w: Seq<EventView>)
    ensures numeric_lang(sem, Regex::Concat(seq![c] + cs), w) <==> exists|a: Seq<EventView>, b: Seq<EventView>|
        w == a + b && numeric_lang(sem, c, a) && numeric_lang(sem, Regex::Concat(cs), b),
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
        forall|i: int| 0 <= i < parts.len() ==> numeric_lang(sem, c, parts[i]),
    ensures exists|a: Seq<EventView>, b: Seq<EventView>| w == a + b && numeric_lang(sem, c, seq![e] + a)
        && numeric_lang(sem, Regex::Star(Box::new(c)), b),
    decreases parts.len(),
{
    assert(parts.len() > 0);
    let tail = parts.drop_first();
    assert forall|i: int| 0 <= i < tail.len() implies numeric_lang(sem, c, tail[i]) by {
        assert(tail[i] == parts[i + 1]);
    }
    if parts[0].len() == 0 {
        assert(parts[0] =~= Seq::<EventView>::empty());
        lemma_star_parts_cons(sem, c, tail, e, w);
    } else {
        let a = parts[0].drop_first();
        let b = tail.flatten();
        lemma_cons_split(e, w, parts[0], b);
        assert(numeric_lang(sem, Regex::Star(Box::new(c)), b));
        assert(w == a + b && numeric_lang(sem, c, seq![e] + a) && numeric_lang(sem, Regex::Star(Box::new(c)), b));
    }
}

pub proof fn lemma_star_cons<L>(sem: spec_fn(L, EventView) -> bool, c: Regex<L>, e: EventView, w: Seq<EventView>)
    ensures numeric_lang(sem, Regex::Star(Box::new(c)), seq![e] + w) <==> exists|a: Seq<EventView>, b: Seq<EventView>|
        w == a + b && numeric_lang(sem, c, seq![e] + a) && numeric_lang(sem, Regex::Star(Box::new(c)), b),
{
    if numeric_lang(sem, Regex::Star(Box::new(c)), seq![e] + w) {
        let parts = choose|parts: Seq<Seq<EventView>>| seq![e] + w == parts.flatten()
            && forall|i: int| 0 <= i < parts.len() ==> numeric_lang(sem, c, parts[i]);
        lemma_star_parts_cons(sem, c, parts, e, w);
    }
    if exists|a: Seq<EventView>, b: Seq<EventView>| w == a + b && numeric_lang(sem, c, seq![e] + a) && numeric_lang(sem, Regex::Star(Box::new(c)), b) {
        let (a, b) = choose|a: Seq<EventView>, b: Seq<EventView>| w == a + b && numeric_lang(sem, c, seq![e] + a) && numeric_lang(sem, Regex::Star(Box::new(c)), b);
        let tail = choose|tail: Seq<Seq<EventView>>| b == tail.flatten()
            && forall|i: int| 0 <= i < tail.len() ==> numeric_lang(sem, c, tail[i]);
        let parts = seq![seq![e] + a] + tail;
        assert(parts.drop_first() =~= tail);
        assert(parts.flatten() =~= seq![e] + w);
        assert forall|i: int| 0 <= i < parts.len() implies numeric_lang(sem, c, parts[i]) by {
            if i > 0 { assert(parts[i] == tail[i - 1]); }
        }
        assert(numeric_lang(sem, Regex::Star(Box::new(c)), seq![e] + w));
    }
}

pub proof fn lemma_lang_union<L>(sem: spec_fn(L, EventView) -> bool, cs: Seq<Regex<L>>, w: Seq<EventView>)
    ensures numeric_lang(sem, Regex::Union(cs), w) == (exists|i: int| 0 <= i < cs.len() && numeric_lang(sem, cs[i], w)),
{
    reveal_with_fuel(numeric_lang, 2);
    assert(Regex::Union(cs)->Union_0 == cs);
}

pub proof fn lemma_union_optional<L>(sem: spec_fn(L, EventView) -> bool, a: Regex<L>, b: Regex<L>, flag: bool, w: Seq<EventView>)
    ensures numeric_lang(sem, Regex::Union(seq![a] + if flag { seq![b] } else { Seq::empty() }), w)
        == (numeric_lang(sem, a, w) || (flag && numeric_lang(sem, b, w))),
{
    broadcast use vstd::seq::group_seq_lemmas;
    reveal_with_fuel(numeric_lang, 2);
    let cs = seq![a] + if flag { seq![b] } else { Seq::empty() };
    lemma_lang_union(sem, cs, w);
    if numeric_lang(sem, Regex::Union(cs), w) {
        let i = choose|i: int| 0 <= i < cs.len() && numeric_lang(sem, cs[i], w);
        assert(i == 0 || (flag && i == 1));
        if i == 0 { assert(cs[i] == a); } else { assert(cs[i] == b); }
    }
    if numeric_lang(sem, a, w) {
        assert(cs.len() >= 1);
        assert(cs[0] == a);
        assert(0 <= 0int < cs.len() && numeric_lang(sem, cs[0], w));
        assert(exists|i: int| 0 <= i < cs.len() && numeric_lang(sem, cs[i], w));
        assert(numeric_lang(sem, Regex::Union(cs), w));
    }
    if flag && numeric_lang(sem, b, w) {
        assert(cs.len() == 2);
        assert(cs[1] == b);
        assert(exists|i: int| 0 <= i < cs.len() && numeric_lang(sem, cs[i], w));
        assert(numeric_lang(sem, Regex::Union(cs), w));
    }
}

pub proof fn lemma_lang_intersect<L>(sem: spec_fn(L, EventView) -> bool, cs: Seq<Regex<L>>, w: Seq<EventView>)
    ensures numeric_lang(sem, Regex::Intersect(cs), w) == (forall|i: int| 0 <= i < cs.len() ==> numeric_lang(sem, cs[i], w)),
{
    reveal_with_fuel(numeric_lang, 2);
    assert(Regex::Intersect(cs)->Intersect_0 == cs);
    if numeric_lang(sem, Regex::Intersect(cs), w) {
        assert forall|i: int| 0 <= i < cs.len() implies numeric_lang(sem, cs[i], w) by {
            assert(numeric_lang(sem, Regex::Intersect(cs), w));
        }
    }
}

pub proof fn lemma_derivative_concat<L>(sem: spec_fn(L, EventView) -> bool, e: EventView, bound: Regex<L>, cs: Seq<Regex<L>>, w: Seq<EventView>)
    requires
        forall|i: int| 0 <= i < cs.len() ==> is_smaller_than(cs[i], bound),
        forall|i: int, v: Seq<EventView>| 0 <= i < cs.len() ==> numeric_lang(sem, derivative(sem, e, cs[i]), v) == numeric_lang(sem, cs[i], seq![e] + v),
    ensures numeric_lang(sem, derivative_concat(sem, e, bound, cs), w) == numeric_lang(sem, Regex::Concat(cs), seq![e] + w),
    decreases cs.len(),
{
    if cs.len() == 0 {
        if numeric_lang(sem, Regex::Concat(cs), seq![e] + w) {
            let parts = choose|parts: Seq<Seq<EventView>>| parts.len() == cs.len() && seq![e] + w == parts.flatten()
                && forall|i: int| 0 <= i < cs.len() ==> numeric_lang(sem, cs[i], parts[i]);
            assert(parts =~= Seq::<Seq<EventView>>::empty());
        }
    } else {
        let c = cs[0];
        let rest = cs.drop_first();
        assert forall|i: int| 0 <= i < rest.len() implies is_smaller_than(rest[i], bound) by {
            assert(rest[i] == cs[i + 1]);
        }
        assert forall|i: int, v: Seq<EventView>| 0 <= i < rest.len() implies numeric_lang(sem, derivative(sem, e, rest[i]), v) == numeric_lang(sem, rest[i], seq![e] + v) by {
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
        if numeric_lang(sem, derivative_concat(sem, e, bound, cs), w) {
            if numeric_lang(sem, left, w) {
                let (a, b) = choose|a: Seq<EventView>, b: Seq<EventView>| w == a + b && numeric_lang(sem, dc, a) && numeric_lang(sem, Regex::Concat(rest), b);
                assert(numeric_lang(sem, c, seq![e] + a));
                assert(seq![e] + w =~= (seq![e] + a) + b);
                assert(exists|a0: Seq<EventView>, b0: Seq<EventView>| seq![e] + w == a0 + b0 && numeric_lang(sem, c, a0) && numeric_lang(sem, Regex::Concat(rest), b0));
            } else {
                assert(nullable(c) && numeric_lang(sem, dr, w));
                let a = Seq::<EventView>::empty();
                let b = seq![e] + w;
                assert(a + b =~= b);
                assert(numeric_lang(sem, c, a) && numeric_lang(sem, Regex::Concat(rest), b));
                assert(exists|a0: Seq<EventView>, b0: Seq<EventView>| seq![e] + w == a0 + b0 && numeric_lang(sem, c, a0) && numeric_lang(sem, Regex::Concat(rest), b0));
            }
            assert(numeric_lang(sem, Regex::Concat(cs), seq![e] + w));
        }
        if numeric_lang(sem, Regex::Concat(cs), seq![e] + w) {
            let (a, b) = choose|a: Seq<EventView>, b: Seq<EventView>| seq![e] + w == a + b && numeric_lang(sem, c, a) && numeric_lang(sem, Regex::Concat(rest), b);
            if a.len() == 0 {
                assert(a =~= Seq::<EventView>::empty());
                assert(b =~= seq![e] + w);
                assert(nullable(c));
                assert(numeric_lang(sem, dr, w));
            } else {
                lemma_cons_split(e, w, a, b);
                let v = a.drop_first();
                assert(numeric_lang(sem, dc, v));
                assert(exists|a0: Seq<EventView>, b0: Seq<EventView>| w == a0 + b0 && numeric_lang(sem, dc, a0) && numeric_lang(sem, Regex::Concat(rest), b0));
                assert(numeric_lang(sem, left, w));
            }
            assert(numeric_lang(sem, derivative_concat(sem, e, bound, cs), w));
        }
    }
}

pub proof fn lemma_concat_singleton<L>(sem: spec_fn(L, EventView) -> bool, r: Regex<L>, w: Seq<EventView>)
    ensures numeric_lang(sem, Regex::Concat(seq![r]), w) == numeric_lang(sem, r, w),
{
    if numeric_lang(sem, Regex::Concat(seq![r]), w) {
        let parts = choose|parts: Seq<Seq<EventView>>| parts.len() == 1 && w == parts.flatten()
            && forall|i: int| 0 <= i < 1 ==> numeric_lang(sem, seq![r][i], parts[i]);
        parts.lemma_flatten_one_element();
        assert(numeric_lang(sem, r, w));
    }
    if numeric_lang(sem, r, w) {
        let parts = seq![w];
        parts.lemma_flatten_one_element();
        assert forall|i: int| 0 <= i < 1 implies numeric_lang(sem, seq![r][i], parts[i]) by { assert(i == 0); }
        assert(numeric_lang(sem, Regex::Concat(seq![r]), w));
    }
}

pub proof fn lemma_concat_pair<L>(sem: spec_fn(L, EventView) -> bool, a: Regex<L>, b: Regex<L>, w: Seq<EventView>)
    ensures numeric_lang(sem, Regex::Concat(seq![a, b]), w) <==> exists|u: Seq<EventView>, v: Seq<EventView>|
        w == u + v && numeric_lang(sem, a, u) && numeric_lang(sem, b, v),
{
    assert(seq![a, b] =~= seq![a] + seq![b]);
    lemma_concat_prepend(sem, a, seq![b], w);
    assert forall|v: Seq<EventView>| numeric_lang(sem, Regex::Concat(seq![b]), v) == numeric_lang(sem, b, v) by {
        lemma_concat_singleton(sem, b, v);
    }
}

pub proof fn lemma_derivative_correct<L>(sem: spec_fn(L, EventView) -> bool, e: EventView, r: Regex<L>, w: Seq<EventView>)
    ensures numeric_lang(sem, derivative(sem, e, r), w) <==> numeric_lang(sem, r, seq![e] + w),
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
            assert forall|i: int| 0 <= i < cs.len() implies numeric_lang(sem, ds[i], w) == numeric_lang(sem, cs[i], seq![e] + w) by {
                lemma_derivative_correct(sem, e, cs[i], w);
            }
            assert(numeric_lang(sem, derivative(sem, e, r), w) == numeric_lang(sem, r, seq![e] + w));
        },
        Regex::Intersect(cs) => {
            let ds = Seq::new(cs.len(), |i: int| if 0 <= i < cs.len() { derivative(sem, e, cs[i]) } else { Regex::Empty });
            assert(ds.len() == cs.len());
            assert(derivative(sem, e, r)->Intersect_0 =~= ds);
            assert(derivative(sem, e, r) == Regex::Intersect(ds));
            lemma_lang_intersect(sem, ds, w);
            lemma_lang_intersect(sem, cs, seq![e] + w);
            assert forall|i: int| 0 <= i < cs.len() implies numeric_lang(sem, ds[i], w) == numeric_lang(sem, cs[i], seq![e] + w) by {
                lemma_derivative_correct(sem, e, cs[i], w);
            }
            assert(numeric_lang(sem, derivative(sem, e, r), w) == numeric_lang(sem, r, seq![e] + w));
        },
        Regex::Not(c) => lemma_derivative_correct(sem, e, *c, w),
        Regex::Star(c) => {
            lemma_star_cons(sem, *c, e, w);
            lemma_concat_pair(sem, derivative(sem, e, *c), Regex::Star(c), w);
            assert forall|a: Seq<EventView>| numeric_lang(sem, derivative(sem, e, *c), a) == numeric_lang(sem, *c, seq![e] + a) by {
                lemma_derivative_correct(sem, e, *c, a);
            }
            assert(numeric_lang(sem, derivative(sem, e, r), w) == numeric_lang(sem, r, seq![e] + w));
        },
        Regex::Concat(cs) => {
            assert forall|i: int| 0 <= i < cs.len() implies is_smaller_than(cs[i], r) by { }
            assert forall|i: int, v: Seq<EventView>| 0 <= i < cs.len() implies numeric_lang(sem, derivative(sem, e, cs[i]), v) == numeric_lang(sem, cs[i], seq![e] + v) by {
                lemma_derivative_correct(sem, e, cs[i], v);
            }
            lemma_derivative_concat(sem, e, r, cs, w);
        },
        Regex::Test(_) => { assert((seq![e] + w)[0] == e); },
        _ => {},
    }
}

pub proof fn lemma_derive_word_correct<L>(sem: spec_fn(L, EventView) -> bool, prefix: Seq<EventView>, r: Regex<L>, suffix: Seq<EventView>)
    ensures numeric_lang(sem, derive_word(sem, prefix, r), suffix) == numeric_lang(sem, r, prefix + suffix),
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
    ensures nullable(derive_word(sem, w, r)) == numeric_lang(sem, r, w),
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
    ensures numeric_lang(sem, interp_transition(sem, e, Transition::Union(cs)), w)
        == (exists|i: int| 0 <= i < cs.len() && numeric_lang(sem, interp_transition(sem, e, cs[i]), w)),
{
    let r = interp_transition(sem, e, Transition::Union(cs));
    assert(r is Union);
    assert((r->Union_0).len() == cs.len());
    lemma_lang_union(sem, r->Union_0, w);
    assert forall|i: int| 0 <= i < cs.len() implies (r->Union_0)[i] == interp_transition(sem, e, cs[i]) by { }
    assert forall|i: int| 0 <= i < cs.len() implies numeric_lang(sem, (r->Union_0)[i], w) == numeric_lang(sem, interp_transition(sem, e, cs[i]), w) by {
        assert((r->Union_0)[i] == interp_transition(sem, e, cs[i]));
    }
    if numeric_lang(sem, r, w) {
        let i = choose|i: int| 0 <= i < (r->Union_0).len() && numeric_lang(sem, (r->Union_0)[i], w);
        assert(numeric_lang(sem, interp_transition(sem, e, cs[i]), w));
        assert(exists|j: int| 0 <= j < cs.len() && numeric_lang(sem, interp_transition(sem, e, cs[j]), w));
    }
    if exists|i: int| 0 <= i < cs.len() && numeric_lang(sem, interp_transition(sem, e, cs[i]), w) {
        let i = choose|i: int| 0 <= i < cs.len() && numeric_lang(sem, interp_transition(sem, e, cs[i]), w);
        assert(numeric_lang(sem, (r->Union_0)[i], w));
        assert(exists|j: int| 0 <= j < (r->Union_0).len() && numeric_lang(sem, (r->Union_0)[j], w));
        assert(numeric_lang(sem, r, w));
    }
}

pub proof fn lemma_interp_intersect<L>(sem: spec_fn(L, EventView) -> bool, e: EventView, cs: Seq<Transition<L>>, w: Seq<EventView>)
    ensures numeric_lang(sem, interp_transition(sem, e, Transition::Intersect(cs)), w)
        == (forall|i: int| 0 <= i < cs.len() ==> numeric_lang(sem, interp_transition(sem, e, cs[i]), w)),
{
    let r = interp_transition(sem, e, Transition::Intersect(cs));
    assert(r is Intersect);
    assert((r->Intersect_0).len() == cs.len());
    lemma_lang_intersect(sem, r->Intersect_0, w);
    assert forall|i: int| 0 <= i < cs.len() implies (r->Intersect_0)[i] == interp_transition(sem, e, cs[i]) by { }
    assert forall|i: int| 0 <= i < cs.len() implies numeric_lang(sem, (r->Intersect_0)[i], w) == numeric_lang(sem, interp_transition(sem, e, cs[i]), w) by {
        assert((r->Intersect_0)[i] == interp_transition(sem, e, cs[i]));
    }
    if numeric_lang(sem, r, w) {
        assert forall|i: int| 0 <= i < cs.len() implies numeric_lang(sem, interp_transition(sem, e, cs[i]), w) by {
            assert(numeric_lang(sem, (r->Intersect_0)[i], w));
        }
    }
    if forall|i: int| 0 <= i < cs.len() ==> numeric_lang(sem, interp_transition(sem, e, cs[i]), w) {
        assert forall|i: int| 0 <= i < (r->Intersect_0).len() implies numeric_lang(sem, (r->Intersect_0)[i], w) by {
            assert(numeric_lang(sem, interp_transition(sem, e, cs[i]), w));
        }
        assert(numeric_lang(sem, r, w));
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
    Variable(Component),
}

pub enum SrcTest {
    Bool(bool),
    And(Seq<SrcTest>),
    Or(Seq<SrcTest>),
    Eq(Component, Term),
    Neq(Component, Term),
}

pub enum HeadField { Any, Constant(nat), Bind }

pub type Head = Seq<HeadField>;

pub open spec fn head_field(head: Head, field: Component) -> HeadField {
    head[field.0 as int]
}

pub open spec fn head_field_match(head: HeadField, request: nat, binding: nat) -> bool {
    match head {
        HeadField::Any => binding == 0,
        HeadField::Constant(value) => request == value && binding == 0,
        HeadField::Bind => binding == request,
    }
}

pub open spec fn head_match(head: Head, request: EventView, theta: Subst) -> bool {
    head.len() == request.len() && head.len() == theta.len()
        && forall|i: int| 0 <= i < head.len() ==> head_field_match(head[i], request[i], theta[i])
}

pub open spec fn head_bindings(head: Head, request: EventView) -> Subst {
    Seq::new(head.len(), |i: int| if head[i] is Bind { request[i] } else { 0 })
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

pub open spec fn term_wf(field: Component, term: Term, head: Head) -> bool {
    field.0 < head.len() && match term {
        Term::Constant(value) => 0 < value <= u64::MAX,
        Term::Variable(variable) => variable == field && head_field(head, field) is Bind,
    }
}

pub open spec fn head_wf(head: Head) -> bool {
    1 <= head.len() <= MAX_ARITY && forall|i: int| 0 <= i < head.len() ==> match #[trigger] head[i] {
        HeadField::Constant(value) => 0 < value <= u64::MAX,
        _ => true,
    }
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
        && numeric_lang(|test: SrcTest, event: EventView| src_test_holds(theta, test, event), tail, history)
}

pub proof fn lemma_head_match_unique_subst(head: Head, request: EventView, left: Subst, right: Subst)
    requires head_match(head, request, left), head_match(head, request, right),
    ensures left == right,
{
    assert forall|i: int| 0 <= i < head.len() implies left[i] == right[i] by {
        match head[i] { HeadField::Any => {}, HeadField::Constant(_) => {}, HeadField::Bind => {} }
    }
    assert(left =~= right);
}

pub proof fn lemma_pair_lang_substitutions(head: Head, tail: Regex<SrcTest>, request: EventView,
    history: Seq<EventView>, theta: Subst)
    requires head_match(head, request, theta),
    ensures pair_lang(head, tail, request, history)
        == numeric_lang(|test: SrcTest, event: EventView| src_test_holds(theta, test, event), tail, history),
{
    if pair_lang(head, tail, request, history) {
        let other = choose|other: Subst| head_match(head, request, other)
            && numeric_lang(|test: SrcTest, event: EventView| src_test_holds(other, test, event), tail, history);
        lemma_head_match_unique_subst(head, request, theta, other);
    }
    if numeric_lang(|test: SrcTest, event: EventView| src_test_holds(theta, test, event), tail, history) {
        assert(exists|other: Subst| head_match(head, request, other)
            && numeric_lang(|test: SrcTest, event: EventView| src_test_holds(other, test, event), tail, history));
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
        == numeric_lang(sem, root, history.take(target as int)),
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
