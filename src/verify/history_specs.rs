// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Independent pair-language semantics: request is the head, followed by history
//! in oldest-to-newest order. Runtime errors carry no Boolean interpretation.

use super::value_numeric::Numeric;
use super::value_specs::Data;
use alloc::boxed::Box;
use vstd::prelude::*;

verus! {

broadcast use vstd::string::group_string_axioms;

pub proof fn lemma_source_literals()
    ensures
        "value"@ == seq!['v', 'a', 'l', 'u', 'e'],
        "var"@ == seq!['v', 'a', 'r'],
        "any"@ == seq!['a', 'n', 'y'],
        "array"@ == seq!['a', 'r', 'r', 'a', 'y'],
        "object"@ == seq!['o', 'b', 'j', 'e', 'c', 't'],
        "and"@ == seq!['a', 'n', 'd'],
        "or"@ == seq!['o', 'r'],
        "eq"@ == seq!['e', 'q'],
        "neq"@ == seq!['n', 'e', 'q'],
        "empty"@ == seq!['e', 'm', 'p', 't', 'y'],
        "all"@ == seq!['a', 'l', 'l'],
        "epsilon"@ == seq!['e', 'p', 's', 'i', 'l', 'o', 'n'],
        "test"@ == seq!['t', 'e', 's', 't'],
        "union"@ == seq!['u', 'n', 'i', 'o', 'n'],
        "concat"@ == seq!['c', 'o', 'n', 'c', 'a', 't'],
        "star"@ == seq!['s', 't', 'a', 'r'],
        "intersect"@ == seq!['i', 'n', 't', 'e', 'r', 's', 'e', 'c', 't'],
        "not"@ == seq!['n', 'o', 't'],
        "path"@ == seq!['p', 'a', 't', 'h'],
        "term"@ == seq!['t', 'e', 'r', 'm'],
        "request"@ == seq!['r', 'e', 'q', 'u', 'e', 's', 't'],
        "history"@ == seq!['h', 'i', 's', 't', 'o', 'r', 'y'],
        "bool"@ == seq!['b', 'o', 'o', 'l'],
{
    reveal_strlit("value");
    assert("value"@ =~= seq!['v', 'a', 'l', 'u', 'e']);
    reveal_strlit("var");
    assert("var"@ =~= seq!['v', 'a', 'r']);
    reveal_strlit("any");
    assert("any"@ =~= seq!['a', 'n', 'y']);
    reveal_strlit("array");
    assert("array"@ =~= seq!['a', 'r', 'r', 'a', 'y']);
    reveal_strlit("object");
    assert("object"@ =~= seq!['o', 'b', 'j', 'e', 'c', 't']);
    reveal_strlit("and");
    assert("and"@ =~= seq!['a', 'n', 'd']);
    reveal_strlit("or");
    assert("or"@ =~= seq!['o', 'r']);
    reveal_strlit("eq");
    assert("eq"@ =~= seq!['e', 'q']);
    reveal_strlit("neq");
    assert("neq"@ =~= seq!['n', 'e', 'q']);
    reveal_strlit("empty");
    assert("empty"@ =~= seq!['e', 'm', 'p', 't', 'y']);
    reveal_strlit("all");
    assert("all"@ =~= seq!['a', 'l', 'l']);
    reveal_strlit("epsilon");
    assert("epsilon"@ =~= seq!['e', 'p', 's', 'i', 'l', 'o', 'n']);
    reveal_strlit("test");
    assert("test"@ =~= seq!['t', 'e', 's', 't']);
    reveal_strlit("union");
    assert("union"@ =~= seq!['u', 'n', 'i', 'o', 'n']);
    reveal_strlit("concat");
    assert("concat"@ =~= seq!['c', 'o', 'n', 'c', 'a', 't']);
    reveal_strlit("star");
    assert("star"@ =~= seq!['s', 't', 'a', 'r']);
    reveal_strlit("intersect");
    assert("intersect"@ =~= seq!['i', 'n', 't', 'e', 'r', 's', 'e', 'c', 't']);
    reveal_strlit("not");
    assert("not"@ =~= seq!['n', 'o', 't']);
    reveal_strlit("path");
    assert("path"@ =~= seq!['p', 'a', 't', 'h']);
    reveal_strlit("term");
    assert("term"@ =~= seq!['t', 'e', 'r', 'm']);
    reveal_strlit("request");
    assert("request"@ =~= seq!['r', 'e', 'q', 'u', 'e', 's', 't']);
    reveal_strlit("history");
    assert("history"@ =~= seq!['h', 'i', 's', 't', 'o', 'r', 'y']);
    reveal_strlit("bool");
    assert("bool"@ =~= seq!['b', 'o', 'o', 'l']);
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

pub open spec fn lang<L>(sem: spec_fn(L, Data) -> bool, r: Regex<L>, w: Seq<Data>) -> bool decreases r {
    match r {
        Regex::Empty => false,
        Regex::All => true,
        Regex::Epsilon => w.len() == 0,
        Regex::Test(l) => w.len() == 1 && sem(l, w[0]),
        Regex::Union(cs) => exists|i: int| 0 <= i < cs.len() && lang(sem, cs[i], w),
        Regex::Intersect(cs) => forall|i: int| 0 <= i < cs.len() ==> lang(sem, cs[i], w),
        Regex::Not(c) => !lang(sem, *c, w),
        Regex::Concat(cs) => exists|parts: Seq<Seq<Data>>| parts.len() == cs.len() && w == parts.flatten()
            && forall|i: int| 0 <= i < cs.len() ==> lang(sem, cs[i], parts[i]),
        Regex::Star(c) => exists|parts: Seq<Seq<Data>>| w == parts.flatten()
            && forall|i: int| 0 <= i < parts.len() ==> lang(sem, *c, parts[i]),
    }
}

pub open spec fn derivative<L>(sem: spec_fn(L, Data) -> bool, e: Data, r: Regex<L>) -> Regex<L>
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

pub open spec fn derivative_concat<L>(sem: spec_fn(L, Data) -> bool, e: Data, bound: Regex<L>, cs: Seq<Regex<L>>) -> Regex<L>
    decreases bound, 0nat, cs.len(),
    when forall|i: int| 0 <= i < cs.len() ==> is_smaller_than(cs[i], bound)
{
    if cs.len() == 0 { Regex::Empty }
    else {
        Regex::Union(seq![Regex::Concat(seq![derivative(sem, e, cs[0])] + cs.drop_first())]
            + if nullable(cs[0]) { seq![derivative_concat(sem, e, bound, cs.drop_first())] } else { Seq::empty() })
    }
}

pub open spec fn derive_word<L>(sem: spec_fn(L, Data) -> bool, w: Seq<Data>, r: Regex<L>) -> Regex<L>
    decreases w.len(),
{
    if w.len() == 0 { r }
    else { derive_word(sem, w.drop_first(), derivative(sem, w[0], r)) }
}

pub open spec fn interp_transition<L>(sem: spec_fn(L, Data) -> bool, e: Data, t: Transition<L>) -> Regex<L>
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

pub proof fn lemma_flatten_empty(parts: Seq<Seq<Data>>)
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

pub proof fn lemma_concat_uncons<L>(sem: spec_fn(L, Data) -> bool, cs: Seq<Regex<L>>, w: Seq<Data>)
    requires cs.len() > 0,
    ensures lang(sem, Regex::Concat(cs), w) <==> exists|a: Seq<Data>, b: Seq<Data>|
        w == a + b && lang(sem, cs[0], a) && lang(sem, Regex::Concat(cs.drop_first()), b),
{
    if lang(sem, Regex::Concat(cs), w) {
        let parts = choose|parts: Seq<Seq<Data>>| parts.len() == cs.len() && w == parts.flatten()
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
    if exists|a: Seq<Data>, b: Seq<Data>| w == a + b && lang(sem, cs[0], a) && lang(sem, Regex::Concat(cs.drop_first()), b) {
        let (a, b) = choose|a: Seq<Data>, b: Seq<Data>| w == a + b && lang(sem, cs[0], a) && lang(sem, Regex::Concat(cs.drop_first()), b);
        let tail = choose|tail: Seq<Seq<Data>>| tail.len() == cs.drop_first().len() && b == tail.flatten()
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

pub proof fn lemma_nullable_iff_nil<L>(sem: spec_fn(L, Data) -> bool, r: Regex<L>)
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
                let parts = choose|parts: Seq<Seq<Data>>| parts.len() == cs.len() && Seq::<Data>::empty() == parts.flatten()
                    && forall|i: int| 0 <= i < cs.len() ==> lang(sem, cs[i], parts[i]);
                lemma_flatten_empty(parts);
                assert forall|i: int| 0 <= i < cs.len() implies nullable(cs[i]) by {
                    assert(parts[i] =~= Seq::<Data>::empty());
                }
            }
            if nullable(r) {
                let parts = Seq::new(cs.len(), |i: int| Seq::<Data>::empty());
                lemma_flatten_empty(parts);
                assert(parts.flatten() =~= Seq::<Data>::empty());
                assert forall|i: int| 0 <= i < cs.len() implies lang(sem, cs[i], parts[i]) by {
                    lemma_nullable_iff_nil(sem, cs[i]);
                    assert(nullable(cs[i]));
                    assert(parts[i] == Seq::<Data>::empty());
                }
                assert(lang(sem, r, Seq::empty()));
            }
        },
        Regex::Star(c) => {
            let parts = Seq::<Seq<Data>>::empty();
            assert(lang(sem, r, parts.flatten()));
        },
        _ => {},
    }
}


pub proof fn lemma_concat_prepend<L>(sem: spec_fn(L, Data) -> bool, c: Regex<L>, cs: Seq<Regex<L>>, w: Seq<Data>)
    ensures lang(sem, Regex::Concat(seq![c] + cs), w) <==> exists|a: Seq<Data>, b: Seq<Data>|
        w == a + b && lang(sem, c, a) && lang(sem, Regex::Concat(cs), b),
{
    lemma_concat_uncons(sem, seq![c] + cs, w);
    assert((seq![c] + cs).drop_first() =~= cs);
}

pub proof fn lemma_cons_split(e: Data, w: Seq<Data>, a: Seq<Data>, b: Seq<Data>)
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

pub proof fn lemma_star_parts_cons<L>(sem: spec_fn(L, Data) -> bool, c: Regex<L>, parts: Seq<Seq<Data>>, e: Data, w: Seq<Data>)
    requires parts.flatten() == seq![e] + w,
        forall|i: int| 0 <= i < parts.len() ==> lang(sem, c, parts[i]),
    ensures exists|a: Seq<Data>, b: Seq<Data>| w == a + b && lang(sem, c, seq![e] + a)
        && lang(sem, Regex::Star(Box::new(c)), b),
    decreases parts.len(),
{
    assert(parts.len() > 0);
    let tail = parts.drop_first();
    assert forall|i: int| 0 <= i < tail.len() implies lang(sem, c, tail[i]) by {
        assert(tail[i] == parts[i + 1]);
    }
    if parts[0].len() == 0 {
        assert(parts[0] =~= Seq::<Data>::empty());
        lemma_star_parts_cons(sem, c, tail, e, w);
    } else {
        let a = parts[0].drop_first();
        let b = tail.flatten();
        lemma_cons_split(e, w, parts[0], b);
        assert(lang(sem, Regex::Star(Box::new(c)), b));
        assert(w == a + b && lang(sem, c, seq![e] + a) && lang(sem, Regex::Star(Box::new(c)), b));
    }
}

pub proof fn lemma_star_cons<L>(sem: spec_fn(L, Data) -> bool, c: Regex<L>, e: Data, w: Seq<Data>)
    ensures lang(sem, Regex::Star(Box::new(c)), seq![e] + w) <==> exists|a: Seq<Data>, b: Seq<Data>|
        w == a + b && lang(sem, c, seq![e] + a) && lang(sem, Regex::Star(Box::new(c)), b),
{
    if lang(sem, Regex::Star(Box::new(c)), seq![e] + w) {
        let parts = choose|parts: Seq<Seq<Data>>| seq![e] + w == parts.flatten()
            && forall|i: int| 0 <= i < parts.len() ==> lang(sem, c, parts[i]);
        lemma_star_parts_cons(sem, c, parts, e, w);
    }
    if exists|a: Seq<Data>, b: Seq<Data>| w == a + b && lang(sem, c, seq![e] + a) && lang(sem, Regex::Star(Box::new(c)), b) {
        let (a, b) = choose|a: Seq<Data>, b: Seq<Data>| w == a + b && lang(sem, c, seq![e] + a) && lang(sem, Regex::Star(Box::new(c)), b);
        let tail = choose|tail: Seq<Seq<Data>>| b == tail.flatten()
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

pub proof fn lemma_lang_union<L>(sem: spec_fn(L, Data) -> bool, cs: Seq<Regex<L>>, w: Seq<Data>)
    ensures lang(sem, Regex::Union(cs), w) == (exists|i: int| 0 <= i < cs.len() && lang(sem, cs[i], w)),
{ }

pub proof fn lemma_union_optional<L>(sem: spec_fn(L, Data) -> bool, a: Regex<L>, b: Regex<L>, flag: bool, w: Seq<Data>)
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

pub proof fn lemma_lang_intersect<L>(sem: spec_fn(L, Data) -> bool, cs: Seq<Regex<L>>, w: Seq<Data>)
    ensures lang(sem, Regex::Intersect(cs), w) == (forall|i: int| 0 <= i < cs.len() ==> lang(sem, cs[i], w)),
{
    if lang(sem, Regex::Intersect(cs), w) {
        assert forall|i: int| 0 <= i < cs.len() implies lang(sem, cs[i], w) by {
            assert(lang(sem, Regex::Intersect(cs), w));
        }
    }
}

pub proof fn lemma_derivative_concat<L>(sem: spec_fn(L, Data) -> bool, e: Data, bound: Regex<L>, cs: Seq<Regex<L>>, w: Seq<Data>)
    requires
        forall|i: int| 0 <= i < cs.len() ==> is_smaller_than(cs[i], bound),
        forall|i: int, v: Seq<Data>| 0 <= i < cs.len() ==> lang(sem, derivative(sem, e, cs[i]), v) == lang(sem, cs[i], seq![e] + v),
    ensures lang(sem, derivative_concat(sem, e, bound, cs), w) == lang(sem, Regex::Concat(cs), seq![e] + w),
    decreases cs.len(),
{
    if cs.len() == 0 {
        if lang(sem, Regex::Concat(cs), seq![e] + w) {
            let parts = choose|parts: Seq<Seq<Data>>| parts.len() == cs.len() && seq![e] + w == parts.flatten()
                && forall|i: int| 0 <= i < cs.len() ==> lang(sem, cs[i], parts[i]);
            assert(parts =~= Seq::<Seq<Data>>::empty());
        }
    } else {
        let c = cs[0];
        let rest = cs.drop_first();
        assert forall|i: int| 0 <= i < rest.len() implies is_smaller_than(rest[i], bound) by {
            assert(rest[i] == cs[i + 1]);
        }
        assert forall|i: int, v: Seq<Data>| 0 <= i < rest.len() implies lang(sem, derivative(sem, e, rest[i]), v) == lang(sem, rest[i], seq![e] + v) by {
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
                let (a, b) = choose|a: Seq<Data>, b: Seq<Data>| w == a + b && lang(sem, dc, a) && lang(sem, Regex::Concat(rest), b);
                assert(lang(sem, c, seq![e] + a));
                assert(seq![e] + w =~= (seq![e] + a) + b);
                assert(exists|a0: Seq<Data>, b0: Seq<Data>| seq![e] + w == a0 + b0 && lang(sem, c, a0) && lang(sem, Regex::Concat(rest), b0));
            } else {
                assert(nullable(c) && lang(sem, dr, w));
                let a = Seq::<Data>::empty();
                let b = seq![e] + w;
                assert(a + b =~= b);
                assert(lang(sem, c, a) && lang(sem, Regex::Concat(rest), b));
                assert(exists|a0: Seq<Data>, b0: Seq<Data>| seq![e] + w == a0 + b0 && lang(sem, c, a0) && lang(sem, Regex::Concat(rest), b0));
            }
            assert(lang(sem, Regex::Concat(cs), seq![e] + w));
        }
        if lang(sem, Regex::Concat(cs), seq![e] + w) {
            let (a, b) = choose|a: Seq<Data>, b: Seq<Data>| seq![e] + w == a + b && lang(sem, c, a) && lang(sem, Regex::Concat(rest), b);
            if a.len() == 0 {
                assert(a =~= Seq::<Data>::empty());
                assert(b =~= seq![e] + w);
                assert(nullable(c));
                assert(lang(sem, dr, w));
            } else {
                lemma_cons_split(e, w, a, b);
                let v = a.drop_first();
                assert(lang(sem, dc, v));
                assert(exists|a0: Seq<Data>, b0: Seq<Data>| w == a0 + b0 && lang(sem, dc, a0) && lang(sem, Regex::Concat(rest), b0));
                assert(lang(sem, left, w));
            }
            assert(lang(sem, derivative_concat(sem, e, bound, cs), w));
        }
    }
}

pub proof fn lemma_concat_singleton<L>(sem: spec_fn(L, Data) -> bool, r: Regex<L>, w: Seq<Data>)
    ensures lang(sem, Regex::Concat(seq![r]), w) == lang(sem, r, w),
{
    if lang(sem, Regex::Concat(seq![r]), w) {
        let parts = choose|parts: Seq<Seq<Data>>| parts.len() == 1 && w == parts.flatten()
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

pub proof fn lemma_concat_pair<L>(sem: spec_fn(L, Data) -> bool, a: Regex<L>, b: Regex<L>, w: Seq<Data>)
    ensures lang(sem, Regex::Concat(seq![a, b]), w) <==> exists|u: Seq<Data>, v: Seq<Data>|
        w == u + v && lang(sem, a, u) && lang(sem, b, v),
{
    assert(seq![a, b] =~= seq![a] + seq![b]);
    lemma_concat_prepend(sem, a, seq![b], w);
    assert forall|v: Seq<Data>| lang(sem, Regex::Concat(seq![b]), v) == lang(sem, b, v) by {
        lemma_concat_singleton(sem, b, v);
    }
}

pub proof fn lemma_derivative_correct<L>(sem: spec_fn(L, Data) -> bool, e: Data, r: Regex<L>, w: Seq<Data>)
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
            assert forall|a: Seq<Data>| lang(sem, derivative(sem, e, *c), a) == lang(sem, *c, seq![e] + a) by {
                lemma_derivative_correct(sem, e, *c, a);
            }
            assert(lang(sem, derivative(sem, e, r), w) == lang(sem, r, seq![e] + w));
        },
        Regex::Concat(cs) => {
            assert forall|i: int| 0 <= i < cs.len() implies is_smaller_than(cs[i], r) by { }
            assert forall|i: int, v: Seq<Data>| 0 <= i < cs.len() implies lang(sem, derivative(sem, e, cs[i]), v) == lang(sem, cs[i], seq![e] + v) by {
                lemma_derivative_correct(sem, e, cs[i], v);
            }
            lemma_derivative_concat(sem, e, r, cs, w);
        },
        Regex::Test(_) => { assert((seq![e] + w)[0] == e); },
        _ => {},
    }
}

pub proof fn lemma_derive_word_correct<L>(sem: spec_fn(L, Data) -> bool, prefix: Seq<Data>, r: Regex<L>, suffix: Seq<Data>)
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

pub proof fn lemma_derive_word_nullable<L>(sem: spec_fn(L, Data) -> bool, w: Seq<Data>, r: Regex<L>)
    ensures nullable(derive_word(sem, w, r)) == lang(sem, r, w),
{
    lemma_nullable_iff_nil(sem, derive_word(sem, w, r));
    lemma_derive_word_correct(sem, w, r, Seq::empty());
    assert(w + Seq::<Data>::empty() =~= w);
}

pub proof fn lemma_derivative_concat_bound<L>(sem: spec_fn(L, Data) -> bool, e: Data, b1: Regex<L>, b2: Regex<L>, cs: Seq<Regex<L>>)
    requires
        forall|i: int| 0 <= i < cs.len() ==> is_smaller_than(cs[i], b1),
        forall|i: int| 0 <= i < cs.len() ==> is_smaller_than(cs[i], b2),
    ensures derivative_concat(sem, e, b1, cs) == derivative_concat(sem, e, b2, cs),
    decreases cs.len(),
{
    if cs.len() > 0 {
        assert forall|i: int| 0 <= i < cs.drop_first().len() implies is_smaller_than(cs.drop_first()[i], b1) && is_smaller_than(cs.drop_first()[i], b2) by {
            assert(cs.drop_first()[i] == cs[i + 1]);
        }
        lemma_derivative_concat_bound(sem, e, b1, b2, cs.drop_first());
    }
}

pub proof fn lemma_derivative_concat_unfold<L>(sem: spec_fn(L, Data) -> bool, e: Data, cs: Seq<Regex<L>>)
    ensures derivative(sem, e, Regex::Concat(cs)) == if cs.len() == 0 { Regex::Empty } else {
        Regex::Union(seq![Regex::Concat(seq![derivative(sem, e, cs[0])] + cs.drop_first())]
            + if nullable(cs[0]) { seq![derivative(sem, e, Regex::Concat(cs.drop_first()))] } else { Seq::empty() })
    },
{
    reveal_with_fuel(derivative, 2);
    reveal_with_fuel(derivative_concat, 2);
    assert forall|i: int| 0 <= i < cs.len() implies is_smaller_than(cs[i], Regex::Concat(cs)) by { }
    if cs.len() > 0 {
        let rest = cs.drop_first();
        assert(rest.len() == cs.len() - 1);
        assert forall|i: int| 0 <= i < rest.len() implies is_smaller_than(rest[i], Regex::Concat(cs)) by {
            assert(rest[i] == cs[i + 1]);
        }
        assert forall|i: int| 0 <= i < rest.len() implies is_smaller_than(rest[i], Regex::Concat(rest)) by { }
        lemma_derivative_concat_bound(sem, e, Regex::Concat(cs), Regex::Concat(rest), rest);
        assert(derivative(sem, e, Regex::Concat(rest)) == derivative_concat(sem, e, Regex::Concat(rest), rest));
        let expected = seq![Regex::Concat(seq![derivative(sem, e, cs[0])] + rest)]
            + if nullable(cs[0]) { seq![derivative(sem, e, Regex::Concat(rest))] } else { Seq::empty() };
        assert(derivative(sem, e, Regex::Concat(cs))->Union_0 =~= expected);
    }
}

pub proof fn lemma_interp_const<L>(sem: spec_fn(L, Data) -> bool, e: Data, r: Regex<L>)
    ensures interp_transition(sem, e, Transition::Const(r)) == r,
{ }

pub proof fn lemma_interp_if<L>(sem: spec_fn(L, Data) -> bool, e: Data, l: L, a: Transition<L>, b: Transition<L>)
    ensures interp_transition(sem, e, Transition::If(l, Box::new(a), Box::new(b)))
        == if sem(l, e) { interp_transition(sem, e, a) } else { interp_transition(sem, e, b) },
{ }

pub proof fn lemma_interp_union<L>(sem: spec_fn(L, Data) -> bool, e: Data, cs: Seq<Transition<L>>, w: Seq<Data>)
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

pub proof fn lemma_interp_intersect<L>(sem: spec_fn(L, Data) -> bool, e: Data, cs: Seq<Transition<L>>, w: Seq<Data>)
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

pub proof fn lemma_interp_not<L>(sem: spec_fn(L, Data) -> bool, e: Data, t: Transition<L>)
    ensures interp_transition(sem, e, Transition::Not(Box::new(t))) == Regex::Not(Box::new(interp_transition(sem, e, t))),
{ }

pub proof fn lemma_interp_append<L>(sem: spec_fn(L, Data) -> bool, e: Data, t: Transition<L>, suffix: Seq<Regex<L>>)
    ensures interp_transition(sem, e, Transition::Append(Box::new(t), suffix)) == Regex::Concat(seq![interp_transition(sem, e, t)] + suffix),
{ }

pub enum Term {
    Constant(Data),
    Variable(Seq<char>),
}

pub enum SrcTest {
    Bool(bool),
    And(Seq<SrcTest>),
    Or(Seq<SrcTest>),
    Eq(Seq<Data>, Term),
    Neq(Seq<Data>, Term),
}

pub enum Head {
    Literal(Data),
    Variable(Seq<char>),
    Any,
    Array(Seq<Head>),
    Object(Map<Data, Head>),
}

pub type Subst = Map<Seq<char>, Data>;

pub open spec fn array_index(n: Numeric) -> Option<int> {
    let scale = vstd::arithmetic::power2::pow2(1074) as int;
    if n.rank == 0 && n.units >= 0 && n.units % scale == 0 { Some(n.units / scale) } else { None }
}

pub open spec fn select(event: Data, path: Seq<Data>) -> Option<Data>
    decreases path.len(),
{
    if event == Data::Undefined { None }
    else if path.len() == 0 { Some(event) }
    else {
        let next = match event {
            Data::Object(fields) => {
                if fields.contains_key(path[0]) { Some(fields[path[0]]) } else { None }
            },
            Data::Set(values) => {
                if values.contains(path[0]) { Some(path[0]) } else { None }
            },
            Data::Array(values) => match path[0] {
                Data::Number(n) => match array_index(n) {
                    Some(i) => if 0 <= i < values.len() { Some(values[i]) } else { None },
                    None => None,
                },
                _ => None,
            },
            _ => None,
        };
        match next {
            Some(value) => select(value, path.drop_first()),
            None => None,
        }
    }
}

pub open spec fn term_value(theta: Subst, t: Term) -> Data {
    match t {
        Term::Constant(value) => value,
        Term::Variable(name) => theta[name],
    }
}

pub open spec fn src_test_holds(theta: Subst, t: SrcTest, event: Data) -> bool
    decreases t,
{
    match t {
        SrcTest::Bool(value) => value,
        SrcTest::And(children) => forall|i: int| 0 <= i < children.len()
            ==> src_test_holds(theta, children[i], event),
        SrcTest::Or(children) => exists|i: int| 0 <= i < children.len()
            && src_test_holds(theta, children[i], event),
        SrcTest::Eq(path, term) => match select(event, path) {
            Some(value) => value == term_value(theta, term),
            None => false,
        },
        SrcTest::Neq(path, term) => match select(event, path) {
            Some(value) => value != term_value(theta, term),
            None => false,
        },
    }
}

pub open spec fn head_match(h: Head, req: Data, theta: Subst) -> bool
    decreases h,
{
    match h {
        Head::Literal(value) => req != Data::Undefined && req == value,
        Head::Variable(name) => req != Data::Undefined
            && theta.contains_key(name) && theta[name] == req,
        Head::Any => req != Data::Undefined,
        Head::Array(children) => match req {
            Data::Array(values) => children.len() == values.len()
                && forall|i: int| 0 <= i < children.len()
                    ==> head_match(children[i], values[i], theta),
            _ => false,
        },
        Head::Object(fields) => match req {
            Data::Object(values) => forall|key: Data| fields.contains_key(key)
                ==> values.contains_key(key) && head_match(fields[key], values[key], theta),
            _ => false,
        },
    }
}

pub open spec fn head_vars(h: Head) -> Set<Seq<char>>
    decreases h, 1nat, 0nat,
{
    match h {
        Head::Variable(name) => Set::empty().insert(name),
        Head::Array(children) => head_vars_array(h, children),
        Head::Object(fields) => head_vars_object(h, fields, fields.dom()),
        _ => Set::empty(),
    }
}

pub open spec fn head_vars_array(bound: Head, children: Seq<Head>) -> Set<Seq<char>>
    decreases bound, 0nat, children.len(),
    when forall|i: int| 0 <= i < children.len() ==> is_smaller_than(children[i], bound)
{
    if children.len() == 0 { Set::empty() }
    else { head_vars_array(bound, children.drop_last()).union(head_vars(children.last())) }
}

pub open spec fn head_vars_object(bound: Head, fields: Map<Data, Head>, keys: Set<Data>) -> Set<Seq<char>>
    decreases bound, 0nat, keys.len(),
    when keys.subset_of(fields.dom()) && forall|key: Data| fields.contains_key(key)
        ==> is_smaller_than(fields[key], bound)
{
    if keys.is_empty() { Set::empty() }
    else {
        let key = keys.choose();
        head_vars_object(bound, fields, keys.remove(key)).union(head_vars(fields[key]))
    }
}

pub proof fn lemma_head_vars_array_membership(bound: Head, children: Seq<Head>)
    requires forall|i: int| 0 <= i < children.len() ==> is_smaller_than(children[i], bound),
    ensures forall|name: Seq<char>| head_vars_array(bound, children).contains(name)
        <==> exists|i: int| 0 <= i < children.len() && head_vars(children[i]).contains(name),
    decreases children.len(),
{
    broadcast use vstd::set::group_set_lemmas;
    if children.len() > 0 {
        lemma_head_vars_array_membership(bound, children.drop_last());
        assert forall|name: Seq<char>| head_vars_array(bound, children).contains(name)
            <==> (exists|i: int| 0 <= i < children.len() && head_vars(children[i]).contains(name)) by {
            if head_vars_array(bound, children).contains(name) {
                if head_vars(children.last()).contains(name) {
                    assert(head_vars(children[children.len() - 1]).contains(name));
                } else {
                    assert(head_vars_array(bound, children.drop_last()).contains(name));
                    let i = choose|i: int| 0 <= i < children.drop_last().len()
                        && head_vars(children.drop_last()[i]).contains(name);
                    assert(children.drop_last()[i] == children[i]);
                }
            }
            if exists|i: int| 0 <= i < children.len() && head_vars(children[i]).contains(name) {
                let i = choose|i: int| 0 <= i < children.len() && head_vars(children[i]).contains(name);
                if i < children.len() - 1 {
                    assert(children.drop_last()[i] == children[i]);
                } else { assert(children[i] == children.last()); }
            }
        }
    }
}

pub proof fn lemma_head_vars_object_membership(bound: Head, fields: Map<Data, Head>, keys: Set<Data>)
    requires keys.subset_of(fields.dom()),
        forall|key: Data| fields.contains_key(key) ==> is_smaller_than(fields[key], bound),
    ensures forall|name: Seq<char>| head_vars_object(bound, fields, keys).contains(name)
        <==> exists|key: Data| keys.contains(key) && head_vars(fields[key]).contains(name),
    decreases keys.len(),
{
    broadcast use vstd::set::group_set_lemmas;
    if !keys.is_empty() {
        let key = keys.choose();
        lemma_head_vars_object_membership(bound, fields, keys.remove(key));
        assert forall|name: Seq<char>| head_vars_object(bound, fields, keys).contains(name)
            <==> (exists|k: Data| keys.contains(k) && head_vars(fields[k]).contains(name)) by {
            if head_vars_object(bound, fields, keys).contains(name) {
                if head_vars(fields[key]).contains(name) {
                    assert(keys.contains(key) && head_vars(fields[key]).contains(name));
                } else {
                    assert(head_vars_object(bound, fields, keys.remove(key)).contains(name));
                    let k = choose|k: Data| keys.remove(key).contains(k) && head_vars(fields[k]).contains(name);
                    assert(keys.contains(k));
                }
            }
            if exists|k: Data| keys.contains(k) && head_vars(fields[k]).contains(name) {
                let k = choose|k: Data| keys.contains(k) && head_vars(fields[k]).contains(name);
                if k != key { assert(keys.remove(key).contains(k)); }
            }
        }
    }
}

pub proof fn lemma_head_vars_array(children: Seq<Head>)
    ensures forall|name: Seq<char>| head_vars(Head::Array(children)).contains(name)
        <==> exists|i: int| 0 <= i < children.len() && head_vars(children[i]).contains(name),
{
    let bound = Head::Array(children);
    let field: Seq<Head> = get_variant_field(bound, "Array", "0");
    assert(is_smaller_than(field, bound));
    assert forall|i: int| 0 <= i < children.len()
        implies is_smaller_than(children[i], Head::Array(children)) by {
        assert(is_smaller_than(children[i], children));
    }
    lemma_head_vars_array_membership(Head::Array(children), children);
    assert(head_vars(Head::Array(children)) == head_vars_array(Head::Array(children), children));
}

pub proof fn lemma_head_vars_object(fields: Map<Data, Head>)
    ensures forall|name: Seq<char>| head_vars(Head::Object(fields)).contains(name)
        <==> exists|key: Data| fields.contains_key(key) && head_vars(fields[key]).contains(name),
{
    broadcast use vstd::map::group_map_lemmas;
    let bound = Head::Object(fields);
    let field: Map<Data, Head> = get_variant_field(bound, "Object", "0");
    assert(is_smaller_than(field, bound));
    assert forall|key: Data| fields.contains_key(key)
        implies is_smaller_than(fields[key], Head::Object(fields)) by {
        assert(is_smaller_than(fields[key], fields));
    }
    lemma_head_vars_object_membership(Head::Object(fields), fields, fields.dom());
    assert(head_vars(Head::Object(fields)) == head_vars_object(Head::Object(fields), fields, fields.dom()));
}

/// A tag is exactly one string-keyed member; no iteration order is specified.
pub open spec fn tagged_payload(d: Data, tag: Seq<char>) -> Option<Data> {
    match d {
        Data::Object(fields) => {
            let key = Data::String(tag);
            if fields.dom() == Set::empty().insert(key) { Some(fields[key]) } else { None }
        },
        _ => None,
    }
}

pub open spec fn decodes_term(d: Data, term: Term) -> bool {
    match term {
        Term::Constant(value) => tagged_payload(d, "value"@) == Some(value),
        Term::Variable(name) => name.len() > 0
            && tagged_payload(d, "var"@) == Some(Data::String(name)),
    }
}

pub open spec fn decodes_head(d: Data, h: Head) -> bool
    decreases h,
{
    match h {
        Head::Literal(value) => tagged_payload(d, "value"@) == Some(value),
        Head::Variable(name) => name.len() > 0
            && tagged_payload(d, "var"@) == Some(Data::String(name)),
        Head::Any => tagged_payload(d, "any"@) == Some(Data::Bool(true)),
        Head::Array(children) => match tagged_payload(d, "array"@) {
            Some(Data::Array(values)) => values.len() == children.len()
                && forall|i: int| 0 <= i < children.len()
                    ==> decodes_head(values[i], children[i]),
            _ => false,
        },
        Head::Object(fields) => match tagged_payload(d, "object"@) {
            Some(Data::Object(values)) => values.dom() == fields.dom()
                && forall|key: Data| fields.contains_key(key)
                    ==> decodes_head(values[key], fields[key]),
            _ => false,
        },
    }
}

pub open spec fn decodes_comparison(d: Data, tag: Seq<char>, path: Seq<Data>, term: Term) -> bool {
    match tagged_payload(d, tag) {
        Some(Data::Object(fields)) => {
            let pk = Data::String("path"@);
            let tk = Data::String("term"@);
            fields.dom() == Set::empty().insert(pk).insert(tk)
                && fields[pk] == Data::Array(path)
                && (forall|i: int| 0 <= i < path.len() ==> path[i] != Data::Undefined)
                && decodes_term(fields[tk], term)
        },
        _ => false,
    }
}

pub open spec fn decodes_test(d: Data, test: SrcTest) -> bool
    decreases test,
{
    match test {
        SrcTest::Bool(value) => d == Data::Bool(value),
        SrcTest::And(children) => match tagged_payload(d, "and"@) {
            Some(Data::Array(values)) => values.len() == children.len()
                && forall|i: int| 0 <= i < children.len()
                    ==> decodes_test(values[i], children[i]),
            _ => false,
        },
        SrcTest::Or(children) => match tagged_payload(d, "or"@) {
            Some(Data::Array(values)) => values.len() == children.len()
                && forall|i: int| 0 <= i < children.len()
                    ==> decodes_test(values[i], children[i]),
            _ => false,
        },
        SrcTest::Eq(path, term) => decodes_comparison(d, "eq"@, path, term),
        SrcTest::Neq(path, term) => decodes_comparison(d, "neq"@, path, term),
    }
}

pub open spec fn decodes_tail(d: Data, r: Regex<SrcTest>) -> bool
    decreases r,
{
    match r {
        Regex::Empty => tagged_payload(d, "empty"@) == Some(Data::Bool(true)),
        Regex::All => tagged_payload(d, "all"@) == Some(Data::Bool(true)),
        Regex::Epsilon => tagged_payload(d, "epsilon"@) == Some(Data::Bool(true)),
        Regex::Test(test) => match tagged_payload(d, "test"@) {
            Some(value) => decodes_test(value, test),
            None => false,
        },
        Regex::Union(children) => match tagged_payload(d, "union"@) {
            Some(Data::Array(values)) => values.len() == children.len()
                && forall|i: int| 0 <= i < children.len() ==> decodes_tail(values[i], children[i]),
            _ => false,
        },
        Regex::Concat(children) => match tagged_payload(d, "concat"@) {
            Some(Data::Array(values)) => values.len() == children.len()
                && forall|i: int| 0 <= i < children.len() ==> decodes_tail(values[i], children[i]),
            _ => false,
        },
        Regex::Star(child) => match tagged_payload(d, "star"@) {
            Some(value) => decodes_tail(value, *child),
            None => false,
        },
        Regex::Intersect(children) => match tagged_payload(d, "intersect"@) {
            Some(Data::Array(values)) => values.len() == children.len()
                && forall|i: int| 0 <= i < children.len() ==> decodes_tail(values[i], children[i]),
            _ => false,
        },
        Regex::Not(child) => match tagged_payload(d, "not"@) {
            Some(value) => decodes_tail(value, *child),
            None => false,
        },
    }
}

pub open spec fn decodes_policy(policy: Data, head: Head, tail: Regex<SrcTest>) -> bool {
    match policy {
        Data::Object(fields) => {
            let rk = Data::String("request"@);
            let hk = Data::String("history"@);
            fields.dom() == Set::empty().insert(rk).insert(hk)
                && decodes_head(fields[rk], head) && decodes_tail(fields[hk], tail)
        },
        _ => false,
    }
}

pub open spec fn pair_lang(head: Head, tail: Regex<SrcTest>, req: Data, history: Seq<Data>) -> bool {
    exists|theta: Subst| head_match(head, req, theta) && theta.dom() == head_vars(head)
        && lang(|test: SrcTest, event: Data| src_test_holds(theta, test, event), tail, history)
}

pub open spec fn policy_lang(policy: Data, req: Data, history: Seq<Data>) -> bool {
    exists|head: Head, tail: Regex<SrcTest>| decodes_policy(policy, head, tail)
        && pair_lang(head, tail, req, history)
}

pub proof fn lemma_tagged_payload_unique_tag(d: Data, left: Seq<char>, right: Seq<char>)
    requires tagged_payload(d, left) is Some, tagged_payload(d, right) is Some,
    ensures left == right,
{
    broadcast use vstd::set::group_set_lemmas;
    match d {
        Data::Object(fields) => {
            assert(fields.dom().contains(Data::String(left)));
            assert(Set::empty().insert(Data::String(right)).contains(Data::String(left)));
        },
        _ => {},
    }
}

pub open spec fn head_tag(head: Head) -> Seq<char> {
    match head {
        Head::Literal(_) => "value"@,
        Head::Variable(_) => "var"@,
        Head::Any => "any"@,
        Head::Array(_) => "array"@,
        Head::Object(_) => "object"@,
    }
}

pub proof fn lemma_decode_head_tag(d: Data, head: Head)
    requires decodes_head(d, head),
    ensures tagged_payload(d, head_tag(head)) is Some,
{
    match head {
        Head::Literal(_) => {},
        Head::Variable(_) => {},
        Head::Any => {},
        Head::Array(_) => {},
        Head::Object(_) => {},
    }
}

pub proof fn lemma_decode_head_deterministic(d: Data, left: Head, right: Head)
    requires decodes_head(d, left), decodes_head(d, right),
    ensures left == right,
    decreases left,
{
    lemma_source_literals();
    broadcast use vstd::map::group_map_lemmas;
    lemma_decode_head_tag(d, left);
    lemma_decode_head_tag(d, right);
    lemma_tagged_payload_unique_tag(d, head_tag(left), head_tag(right));
    match (left, right) {
        (Head::Array(a), Head::Array(b)) => {
            let values = tagged_payload(d, "array"@)->Some_0->Array_0;
            assert forall|i: int| 0 <= i < a.len() implies a[i] == b[i] by {
                lemma_decode_head_deterministic(values[i], a[i], b[i]);
            }
            assert(a =~= b);
        },
        (Head::Object(a), Head::Object(b)) => {
            let values = tagged_payload(d, "object"@)->Some_0->Object_0;
            assert forall|key: Data| a.contains_key(key) implies a[key] == b[key] by {
                lemma_decode_head_deterministic(values[key], a[key], b[key]);
            }
            assert(a =~= b);
        },
        _ => {},
    }
}

pub proof fn lemma_decode_term_deterministic(d: Data, left: Term, right: Term)
    requires decodes_term(d, left), decodes_term(d, right),
    ensures left == right,
{
    lemma_source_literals();
    match (left, right) {
        (Term::Constant(_), Term::Variable(_)) => {
            lemma_tagged_payload_unique_tag(d, "value"@, "var"@);
        },
        (Term::Variable(_), Term::Constant(_)) => {
            lemma_tagged_payload_unique_tag(d, "var"@, "value"@);
        },
        _ => {},
    }
}

pub open spec fn test_tag(test: SrcTest) -> Seq<char> {
    match test {
        SrcTest::Bool(_) => "bool"@,
        SrcTest::And(_) => "and"@,
        SrcTest::Or(_) => "or"@,
        SrcTest::Eq(_, _) => "eq"@,
        SrcTest::Neq(_, _) => "neq"@,
    }
}

pub proof fn lemma_decode_test_tag(d: Data, test: SrcTest)
    requires decodes_test(d, test),
    ensures test is Bool ==> d is Bool,
        !(test is Bool) ==> tagged_payload(d, test_tag(test)) is Some,
{
    match test {
        SrcTest::Bool(_) => {},
        SrcTest::And(_) => {},
        SrcTest::Or(_) => {},
        SrcTest::Eq(_, _) => {},
        SrcTest::Neq(_, _) => {},
    }
}

pub proof fn lemma_decode_comparison_deterministic(d: Data, tag: Seq<char>, p1: Seq<Data>, t1: Term, p2: Seq<Data>, t2: Term)
    requires decodes_comparison(d, tag, p1, t1), decodes_comparison(d, tag, p2, t2),
    ensures p1 == p2, t1 == t2,
{
    let fields = tagged_payload(d, tag)->Some_0->Object_0;
    lemma_decode_term_deterministic(fields[Data::String("term"@)], t1, t2);
}

pub proof fn lemma_decode_test_deterministic(d: Data, left: SrcTest, right: SrcTest)
    requires decodes_test(d, left), decodes_test(d, right),
    ensures left == right,
    decreases left,
{
    lemma_source_literals();
    lemma_decode_test_tag(d, left);
    lemma_decode_test_tag(d, right);
    if !(left is Bool) && !(right is Bool) {
        lemma_tagged_payload_unique_tag(d, test_tag(left), test_tag(right));
    }
    match (left, right) {
        (SrcTest::And(a), SrcTest::And(b)) => {
            let values = tagged_payload(d, "and"@)->Some_0->Array_0;
            assert forall|i: int| 0 <= i < a.len() implies a[i] == b[i] by {
                lemma_decode_test_deterministic(values[i], a[i], b[i]);
            }
            assert(a =~= b);
        },
        (SrcTest::Or(a), SrcTest::Or(b)) => {
            let values = tagged_payload(d, "or"@)->Some_0->Array_0;
            assert forall|i: int| 0 <= i < a.len() implies a[i] == b[i] by {
                lemma_decode_test_deterministic(values[i], a[i], b[i]);
            }
            assert(a =~= b);
        },
        (SrcTest::Eq(p1, t1), SrcTest::Eq(p2, t2)) => {
            lemma_decode_comparison_deterministic(d, "eq"@, p1, t1, p2, t2);
        },
        (SrcTest::Neq(p1, t1), SrcTest::Neq(p2, t2)) => {
            lemma_decode_comparison_deterministic(d, "neq"@, p1, t1, p2, t2);
        },
        _ => {},
    }
}

pub open spec fn tail_tag(tail: Regex<SrcTest>) -> Seq<char> {
    match tail {
        Regex::Empty => "empty"@,
        Regex::All => "all"@,
        Regex::Epsilon => "epsilon"@,
        Regex::Test(_) => "test"@,
        Regex::Union(_) => "union"@,
        Regex::Concat(_) => "concat"@,
        Regex::Star(_) => "star"@,
        Regex::Intersect(_) => "intersect"@,
        Regex::Not(_) => "not"@,
    }
}

pub proof fn lemma_decode_tail_tag(d: Data, tail: Regex<SrcTest>)
    requires decodes_tail(d, tail),
    ensures tagged_payload(d, tail_tag(tail)) is Some,
{
    match tail {
        Regex::Empty => {},
        Regex::All => {},
        Regex::Epsilon => {},
        Regex::Test(_) => {},
        Regex::Union(_) => {},
        Regex::Concat(_) => {},
        Regex::Star(_) => {},
        Regex::Intersect(_) => {},
        Regex::Not(_) => {},
    }
}

pub proof fn lemma_decode_tail_deterministic(d: Data, left: Regex<SrcTest>, right: Regex<SrcTest>)
    requires decodes_tail(d, left), decodes_tail(d, right),
    ensures left == right,
    decreases left,
{
    lemma_source_literals();
    lemma_decode_tail_tag(d, left);
    lemma_decode_tail_tag(d, right);
    lemma_tagged_payload_unique_tag(d, tail_tag(left), tail_tag(right));
    match (left, right) {
        (Regex::Test(a), Regex::Test(b)) => {
            lemma_decode_test_deterministic(tagged_payload(d, "test"@)->Some_0, a, b);
        },
        (Regex::Union(a), Regex::Union(b)) => {
            let values = tagged_payload(d, "union"@)->Some_0->Array_0;
            assert forall|i: int| 0 <= i < a.len() implies a[i] == b[i] by {
                lemma_decode_tail_deterministic(values[i], a[i], b[i]);
            }
            assert(a =~= b);
        },
        (Regex::Concat(a), Regex::Concat(b)) => {
            let values = tagged_payload(d, "concat"@)->Some_0->Array_0;
            assert forall|i: int| 0 <= i < a.len() implies a[i] == b[i] by {
                lemma_decode_tail_deterministic(values[i], a[i], b[i]);
            }
            assert(a =~= b);
        },
        (Regex::Star(a), Regex::Star(b)) => {
            lemma_decode_tail_deterministic(tagged_payload(d, "star"@)->Some_0, *a, *b);
        },
        (Regex::Intersect(a), Regex::Intersect(b)) => {
            let values = tagged_payload(d, "intersect"@)->Some_0->Array_0;
            assert forall|i: int| 0 <= i < a.len() implies a[i] == b[i] by {
                lemma_decode_tail_deterministic(values[i], a[i], b[i]);
            }
            assert(a =~= b);
        },
        (Regex::Not(a), Regex::Not(b)) => {
            lemma_decode_tail_deterministic(tagged_payload(d, "not"@)->Some_0, *a, *b);
        },
        _ => {},
    }
}

pub proof fn lemma_decode_deterministic(policy: Data, h1: Head, r1: Regex<SrcTest>, h2: Head, r2: Regex<SrcTest>)
    requires decodes_policy(policy, h1, r1), decodes_policy(policy, h2, r2),
    ensures h1 == h2, r1 == r2,
{
    match policy {
        Data::Object(fields) => {
            lemma_decode_head_deterministic(fields[Data::String("request"@)], h1, h2);
            lemma_decode_tail_deterministic(fields[Data::String("history"@)], r1, r2);
        },
        _ => {},
    }
}

pub proof fn lemma_head_match_agrees(
    h: Head, request: Data, left: Subst, right: Subst, name: Seq<char>,
)
    requires
        head_match(h, request, left), head_match(h, request, right),
        head_vars(h).contains(name),
    ensures left.contains_key(name) && right.contains_key(name) && left[name] == right[name],
    decreases h,
{
    match h {
        Head::Literal(_) => {},
        Head::Any => {},
        Head::Variable(_) => {},
        Head::Array(children) => {
            lemma_head_vars_array(children);
            let i = choose|i: int| 0 <= i < children.len()
                && head_vars(children[i]).contains(name);
            match request {
                Data::Array(values) => {
                    lemma_head_match_agrees(children[i], values[i], left, right, name);
                },
                _ => {},
            }
        },
        Head::Object(fields) => {
            lemma_head_vars_object(fields);
            let key = choose|key: Data| fields.contains_key(key)
                && head_vars(fields[key]).contains(name);
            vstd::map::axiom_map_index_decreases(fields, key);
            match request {
                Data::Object(values) => {
                    lemma_head_match_agrees(fields[key], values[key], left, right, name);
                },
                _ => {},
            }
        },
    }
}

pub proof fn lemma_head_match_unique_subst(
    h: Head, request: Data, left: Subst, right: Subst,
)
    requires
        head_match(h, request, left),
        head_match(h, request, right),
        left.dom() == head_vars(h),
        right.dom() == head_vars(h),
    ensures left == right,
{
    assert forall|name: Seq<char>| head_vars(h).contains(name)
        implies left[name] == right[name] by {
        lemma_head_match_agrees(h, request, left, right, name);
    }
    assert(left =~= right);
}

/// A complete matching substitution is the unique binding used by the tail.
pub proof fn lemma_pair_lang_substitutions(
    head: Head, tail: Regex<SrcTest>, request: Data, history: Seq<Data>, theta: Subst,
)
    requires head_match(head, request, theta), theta.dom() == head_vars(head),
    ensures pair_lang(head, tail, request, history)
        == lang(|test: SrcTest, event: Data| src_test_holds(theta, test, event), tail, history),
{
    if pair_lang(head, tail, request, history) {
        let other = choose|other: Subst| head_match(head, request, other)
            && other.dom() == head_vars(head)
            && lang(|test: SrcTest, event: Data| src_test_holds(other, test, event), tail, history);
        lemma_head_match_unique_subst(head, request, theta, other);
    }
    if lang(|test: SrcTest, event: Data| src_test_holds(theta, test, event), tail, history) {
        assert(exists|other: Subst| head_match(head, request, other)
            && other.dom() == head_vars(head)
            && lang(|test: SrcTest, event: Data| src_test_holds(other, test, event), tail, history));
    }
}

pub proof fn lemma_policy_lang_decoded(
    policy: Data, head: Head, tail: Regex<SrcTest>, request: Data, history: Seq<Data>,
)
    requires decodes_policy(policy, head, tail),
    ensures policy_lang(policy, request, history) == pair_lang(head, tail, request, history),
{
    if policy_lang(policy, request, history) {
        let (other_head, other_tail) = choose|other_head: Head, other_tail: Regex<SrcTest>|
            decodes_policy(policy, other_head, other_tail)
                && pair_lang(other_head, other_tail, request, history);
        lemma_decode_deterministic(policy, head, tail, other_head, other_tail);
    }
    if pair_lang(head, tail, request, history) {
        assert(exists|h: Head, r: Regex<SrcTest>| decodes_policy(policy, h, r)
            && pair_lang(h, r, request, history));
    }
}

}
