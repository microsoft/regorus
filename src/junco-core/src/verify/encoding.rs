//! Finite component codebooks and the constant-encoding bridge.
//!
//! Representatives are concrete values. Equality, domain membership, and native
//! lookup correspondence are obligations of an opted-in encoder, not Rust identity.

use crate::flat::verify::field_index;
use crate::flat::{FlatHead, FlatPair, FlatRegex, FlatTerm, FlatTest};
use crate::verify::history_specs::EventView;
use history_syntax::MAX_ARITY;
use history_syntax::syntax::Component;
use vstd::prelude::*;

verus! {

broadcast use {vstd::std_specs::vec::group_vec_axioms, vstd::seq::group_seq_lemmas};

/// Pointwise numeric representation preserves the policy's coordinate count.
pub open spec fn event_representation(event: Seq<u64>, numeric: EventView) -> bool {
    event.len() == numeric.len()
        && forall|i: int| 0 <= i < event.len() ==> numeric[i] == event[i] as nat
}

pub open spec fn event_relation() -> spec_fn(Seq<u64>, EventView) -> bool {
    |event: Seq<u64>, numeric: EventView| event_representation(event, numeric)
}

pub open spec fn word_representation(word: Seq<Seq<u64>>, numeric: Seq<EventView>) -> bool {
    pointwise(word, numeric, event_relation())
}

pub type Equality<C> = spec_fn(Component, C, C) -> bool;
pub type Domain<C> = spec_fn(Component, C) -> bool;
/// One finite sequence of representatives per policy coordinate.
pub type Codebook<C> = Seq<Seq<(C, u64)>>;

pub open spec fn field_at(index: int) -> Component {
    Component(index as u8)
}

pub open spec fn equality_laws<C>(eq: Equality<C>, domain: Domain<C>) -> bool {
    (forall|f: Component, a: C| #[trigger] domain(f, a) ==> eq(f, a, a))
    && (forall|f: Component, a: C, b: C| domain(f, a) && domain(f, b)
        ==> #[trigger] eq(f, a, b) == eq(f, b, a))
    && (forall|f: Component, a: C, b: C, c: C|
        domain(f, a) && domain(f, b) && domain(f, c)
            && #[trigger] eq(f, a, b) && #[trigger] eq(f, b, c)
        ==> eq(f, a, c))
}

pub open spec fn encoded<C>(maps: Codebook<C>, eq: Equality<C>, field: Component, value: C, id: u64) -> bool {
    1 <= maps.len() <= MAX_ARITY && 0 <= field_index(field) < maps.len()
        && id > 0 && exists|i: int|
            0 <= i < maps[field_index(field)].len()
            && maps[field_index(field)][i].1 == id
            && eq(field, value, maps[field_index(field)][i].0)
}

pub open spec fn maps_wf<C>(maps: Codebook<C>, eq: Equality<C>, domain: Domain<C>) -> bool {
    1 <= maps.len() <= MAX_ARITY && equality_laws(eq, domain)
    && (forall|f: int, i: int| 0 <= f < maps.len() && 0 <= i < maps[f].len()
        ==> domain(field_at(f), maps[f][i].0) && maps[f][i].1 > 0)
    && (forall|f: int, i: int, j: int|
        0 <= f < maps.len() && 0 <= i < maps[f].len() && 0 <= j < maps[f].len()
        ==> (eq(field_at(f), maps[f][i].0, maps[f][j].0)
            == (maps[f][i].1 == maps[f][j].1)))
}

/// Even an unsuccessful insertion preserves every previously published association.
pub open spec fn extends<C>(before: Codebook<C>, after: Codebook<C>, eq: Equality<C>) -> bool {
    forall|f: Component, value: C, id: u64| encoded(before, eq, f, value, id)
        ==> encoded(after, eq, f, value, id)
}

pub proof fn lemma_extends_transitive<C>(a: Codebook<C>, b: Codebook<C>, c: Codebook<C>, eq: Equality<C>)
    requires extends(a, b, eq), extends(b, c, eq),
    ensures extends(a, c, eq),
{}

/// Every value in `after`'s books is a value `before` held at the same coordinate or one that
/// `added` admits there: an encoding interns nothing but what it was asked to encode.
pub open spec fn grows_by<C>(before: Codebook<C>, after: Codebook<C>, added: spec_fn(Component, C) -> bool) -> bool {
    after.len() == before.len() && forall|f: int, i: int| #![trigger after[f][i]] 0 <= f < after.len() && 0 <= i < after[f].len()
        ==> (exists|j: int| 0 <= j < before[f].len() && (#[trigger] before[f][j]).0 == after[f][i].0)
            || added(field_at(f), after[f][i].0)
}

/// The one value an `encode` call may intern.
pub open spec fn only_value<C>(field: Component, value: C) -> spec_fn(Component, C) -> bool {
    |f: Component, v: C| f == field && v == value
}

/// The constant a head slot at `field` may intern.
pub open spec fn head_constant_of<C>(head: FlatHead<C>, field: Component) -> spec_fn(Component, C) -> bool {
    |f: Component, v: C| f == field && head == FlatHead::Constant(v)
}

/// The constant a test atom may intern.
pub open spec fn test_constant_of<C>(test: FlatTest<C>) -> spec_fn(Component, C) -> bool {
    |f: Component, v: C| match test {
        FlatTest::Atom { field, term: FlatTerm::Constant(value), .. } => f == field && v == value,
        _ => false,
    }
}

/// `value` is a constant of `source` at coordinate `field` (a head slot or a test atom).
pub open spec fn source_constant<C>(source: FlatPair<C>, field: Component, value: C) -> bool {
    (exists|i: int| 0 <= i < source.head@.len() && field_at(i) == field
        && (#[trigger] source.head@[i]) == FlatHead::Constant(value))
    || (exists|i: int| 0 <= i < source.tests@.len() && match #[trigger] source.tests@[i] {
        FlatTest::Atom { field: f, term: FlatTerm::Constant(v), .. } => f == field && v == value,
        _ => false,
    })
}

pub open spec fn source_constants<C>(source: FlatPair<C>) -> spec_fn(Component, C) -> bool {
    |f: Component, v: C| source_constant(source, f, v)
}

pub proof fn lemma_head_source_constant<C>(source: FlatPair<C>, i: int)
    requires 0 <= i < source.head@.len(),
    ensures forall|f: Component, v: C| #[trigger] head_constant_of(source.head@[i], field_at(i))(f, v)
        ==> source_constants(source)(f, v),
{
    assert forall|f: Component, v: C| #[trigger] head_constant_of(source.head@[i], field_at(i))(f, v)
        implies source_constants(source)(f, v) by {
        assert(source.head@[i] == FlatHead::Constant(v));
    }
}

pub proof fn lemma_test_source_constant<C>(source: FlatPair<C>, i: int)
    requires 0 <= i < source.tests@.len(),
    ensures forall|f: Component, v: C| #[trigger] test_constant_of(source.tests@[i])(f, v)
        ==> source_constants(source)(f, v),
{
    assert forall|f: Component, v: C| #[trigger] test_constant_of(source.tests@[i])(f, v)
        implies source_constants(source)(f, v) by {
        assert(match source.tests@[i] {
            FlatTest::Atom { field: f2, term: FlatTerm::Constant(v2), .. } => f2 == f && v2 == v,
            _ => false,
        });
    }
}

pub proof fn lemma_grows_by_refl<C>(book: Codebook<C>, added: spec_fn(Component, C) -> bool)
    ensures grows_by(book, book, added),
{
    assert forall|f: int, i: int| #![trigger book[f][i]] 0 <= f < book.len() && 0 <= i < book[f].len()
        implies exists|j: int| 0 <= j < book[f].len() && (#[trigger] book[f][j]).0 == book[f][i].0 by {
        let j = i;
        assert(0 <= j < book[f].len() && book[f][j].0 == book[f][i].0);
    }
}

/// Two growths compose, and either bound may be weakened to a common one.
pub proof fn lemma_grows_by_transitive<C>(a: Codebook<C>, b: Codebook<C>, c: Codebook<C>,
    p: spec_fn(Component, C) -> bool, q: spec_fn(Component, C) -> bool, r: spec_fn(Component, C) -> bool)
    requires grows_by(a, b, p), grows_by(b, c, q),
        forall|f: Component, v: C| #[trigger] p(f, v) ==> r(f, v),
        forall|f: Component, v: C| #[trigger] q(f, v) ==> r(f, v),
    ensures grows_by(a, c, r),
{
    assert forall|f: int, i: int| #![trigger c[f][i]] 0 <= f < c.len() && 0 <= i < c[f].len()
        implies (exists|j: int| 0 <= j < a[f].len() && (#[trigger] a[f][j]).0 == c[f][i].0)
            || r(field_at(f), c[f][i].0) by {
        if exists|j: int| 0 <= j < b[f].len() && (#[trigger] b[f][j]).0 == c[f][i].0 {
            let j = choose|j: int| 0 <= j < b[f].len() && (#[trigger] b[f][j]).0 == c[f][i].0;
            assert(0 <= f < b.len() && 0 <= j < b[f].len());
        }
    }
}

pub proof fn lemma_grows_by_weaken<C>(a: Codebook<C>, b: Codebook<C>,
    p: spec_fn(Component, C) -> bool, q: spec_fn(Component, C) -> bool)
    requires grows_by(a, b, p), forall|f: Component, v: C| #[trigger] p(f, v) ==> q(f, v),
    ensures grows_by(a, b, q),
{
    lemma_grows_by_refl(a, p);
    lemma_grows_by_transitive(a, a, b, p, p, q);
}

pub proof fn lemma_encoded_equality<C>(
    maps: Codebook<C>, eq: Equality<C>, domain: Domain<C>, field: Component,
    left: C, right: C, left_id: u64, right_id: u64,
)
    requires maps_wf(maps, eq, domain), domain(field, left), domain(field, right),
        encoded(maps, eq, field, left, left_id), encoded(maps, eq, field, right, right_id),
    ensures eq(field, left, right) == (left_id == right_id),
{
    let f = field_index(field);
    assert(field_at(f) == field);
    let i = choose|i: int| 0 <= i < maps[f].len() && maps[f][i].1 == left_id
        && eq(field, left, maps[f][i].0);
    let j = choose|j: int| 0 <= j < maps[f].len() && maps[f][j].1 == right_id
        && eq(field, right, maps[f][j].0);
    let a = maps[f][i].0;
    let b = maps[f][j].0;
    assert(domain(field, a) && domain(field, b));
    assert(eq(field, a, left));
    assert(eq(field, b, right));
    if eq(field, left, right) {
        assert(eq(field, a, right));
        assert(eq(field, a, b));
    }
    if left_id == right_id {
        assert(eq(field, a, b));
        assert(eq(field, left, b));
        assert(eq(field, left, right));
    }
}

pub open spec fn head_shape<C>(source: FlatHead<C>, target: FlatHead<u64>) -> bool {
    match (source, target) {
        (FlatHead::Any, FlatHead::Any) | (FlatHead::Bind, FlatHead::Bind)
        | (FlatHead::Constant(_), FlatHead::Constant(_)) => true,
        _ => false,
    }
}

pub open spec fn head_encoded<C>(source: FlatHead<C>, target: FlatHead<u64>, field: Component,
    maps: Codebook<C>, eq: Equality<C>) -> bool {
    match (source, target) {
        (FlatHead::Any, FlatHead::Any) | (FlatHead::Bind, FlatHead::Bind) => true,
        (FlatHead::Constant(value), FlatHead::Constant(id)) => encoded(maps, eq, field, value, id),
        _ => false,
    }
}

pub open spec fn test_shape<C>(source: FlatTest<C>, target: FlatTest<u64>) -> bool {
    match (source, target) {
        (FlatTest::Bool(a), FlatTest::Bool(b)) => a == b,
        (FlatTest::Atom { field: a, term: x, positive: p },
         FlatTest::Atom { field: b, term: y, positive: q }) => a == b && p == q && match (x, y) {
            (FlatTerm::Constant(_), FlatTerm::Constant(_)) => true,
            (FlatTerm::Variable(i), FlatTerm::Variable(j)) => i == j,
            _ => false,
        },
        (FlatTest::And(a), FlatTest::And(b)) | (FlatTest::Or(a), FlatTest::Or(b)) => a@ == b@,
        _ => false,
    }
}

pub open spec fn test_encoded<C>(source: FlatTest<C>, target: FlatTest<u64>, maps: Codebook<C>, eq: Equality<C>) -> bool {
    test_shape(source, target) && match (source, target) {
        (FlatTest::Atom { field, term: FlatTerm::Constant(value), .. },
         FlatTest::Atom { term: FlatTerm::Constant(id), .. }) => encoded(maps, eq, field, value, id),
        _ => true,
    }
}

pub open spec fn regex_same(source: FlatRegex, target: FlatRegex) -> bool {
    match (source, target) {
        (FlatRegex::Empty, FlatRegex::Empty) | (FlatRegex::All, FlatRegex::All)
        | (FlatRegex::Epsilon, FlatRegex::Epsilon) => true,
        (FlatRegex::Test(a), FlatRegex::Test(b)) | (FlatRegex::Star(a), FlatRegex::Star(b))
        | (FlatRegex::Complement(a), FlatRegex::Complement(b)) => a == b,
        (FlatRegex::Concat(a), FlatRegex::Concat(b)) | (FlatRegex::Union(a), FlatRegex::Union(b))
        | (FlatRegex::Intersect(a), FlatRegex::Intersect(b)) => a@ == b@,
        _ => false,
    }
}

pub open spec fn regex_tables_same(source: Seq<FlatRegex>, target: Seq<FlatRegex>) -> bool {
    source.len() == target.len() && forall|i: int| 0 <= i < source.len()
        ==> regex_same(source[i], target[i])
}

pub open spec fn topology<C>(source: FlatPair<C>, target: FlatPair<u64>) -> bool {
    source.root == target.root && regex_tables_same(source.regexes@, target.regexes@)
    && source.tests@.len() == target.tests@.len()
    && source.head@.len() == target.head@.len()
    && (forall|i: int| 0 <= i < source.head@.len() ==> head_shape(source.head@[i], target.head@[i]))
    && (forall|i: int| 0 <= i < source.tests@.len() ==> test_shape(source.tests@[i], target.tests@[i]))
}

pub proof fn lemma_topology_wf<C>(source: FlatPair<C>, target: FlatPair<u64>)
    requires crate::flat::verify::structural_wf(source), topology(source, target),
    ensures crate::flat::verify::structural_wf(target),
{
    assert forall|i: int| 0 <= i < target.tests@.len() implies
        crate::flat::verify::test_wf(target.head@, target.tests@[i], i as nat) by {
        if let FlatTest::Atom { field, term: FlatTerm::Variable(_), .. } = target.tests@[i] {
            let f = field_index(field);
            assert(source.head@[f] is Bind);
            assert(target.head@[f] is Bind);
        }
    }
    assert forall|i: int| 0 <= i < target.regexes@.len() implies
        crate::flat::verify::regex_wf(target.regexes@[i], i as nat, target.tests@.len()) by {
    }
}

pub open spec fn lowering<C>(source: FlatPair<C>, target: FlatPair<u64>, maps: Codebook<C>, eq: Equality<C>) -> bool {
    topology(source, target)
    && (forall|i: int| 0 <= i < source.head@.len() ==> head_encoded(source.head@[i], target.head@[i], field_at(i), maps, eq))
    && (forall|i: int| 0 <= i < source.tests@.len() ==> test_encoded(source.tests@[i], target.tests@[i], maps, eq))
}

pub proof fn lemma_head_extends<C>(source: FlatHead<C>, target: FlatHead<u64>, field: Component,
    before: Codebook<C>, after: Codebook<C>, eq: Equality<C>)
    requires head_encoded(source, target, field, before, eq), extends(before, after, eq),
    ensures head_encoded(source, target, field, after, eq),
{}

pub proof fn lemma_test_extends<C>(source: FlatTest<C>, target: FlatTest<u64>,
    before: Codebook<C>, after: Codebook<C>, eq: Equality<C>)
    requires test_encoded(source, target, before, eq), extends(before, after, eq),
    ensures test_encoded(source, target, after, eq),
{}

pub proof fn lemma_lowering_extends<C>(source: FlatPair<C>, target: FlatPair<u64>,
    before: Codebook<C>, after: Codebook<C>, eq: Equality<C>)
    requires lowering(source, target, before, eq), extends(before, after, eq),
    ensures lowering(source, target, after, eq),
{
    assert forall|i: int| 0 <= i < source.head@.len() implies head_encoded(source.head@[i], target.head@[i], field_at(i), after, eq) by {
        lemma_head_extends(source.head@[i], target.head@[i], field_at(i), before, after, eq);
    }
    assert forall|i: int| 0 <= i < source.tests@.len() implies test_encoded(source.tests@[i], target.tests@[i], after, eq) by {
        lemma_test_extends(source.tests@[i], target.tests@[i], before, after, eq);
    }
}

pub open spec fn event_encoded<C>(maps: Codebook<C>, eq: Equality<C>, domain: Domain<C>,
    source: Seq<C>, target: Seq<u64>) -> bool {
    source.len() == maps.len() && target.len() == maps.len()
    && forall|i: int| 0 <= i < maps.len() ==> domain(field_at(i), source[i])
        && encoded(maps, eq, field_at(i), source[i], target[i])
}

pub open spec fn word_encoded<C>(maps: Codebook<C>, eq: Equality<C>, domain: Domain<C>,
    source: Seq<Seq<C>>, target: Seq<Seq<u64>>) -> bool {
    source.len() == target.len() && forall|i: int| 0 <= i < source.len()
        ==> event_encoded(maps, eq, domain, source[i], target[i])
}

pub open spec fn head_in_domain<C>(head: FlatHead<C>, field: Component, domain: Domain<C>) -> bool {
    match head { FlatHead::Constant(value) => domain(field, value), _ => true }
}

pub open spec fn test_in_domain<C>(test: FlatTest<C>, domain: Domain<C>) -> bool {
    match test {
        FlatTest::Atom { field, term: FlatTerm::Constant(value), .. } => domain(field, value), _ => true,
    }
}

pub open spec fn constants_in_domain<C>(source: FlatPair<C>, domain: Domain<C>) -> bool {
    (forall|i: int| 0 <= i < source.head@.len() ==> head_in_domain(source.head@[i], field_at(i), domain))
        && (forall|i: int| 0 <= i < source.tests@.len() ==> test_in_domain(source.tests@[i], domain))
}

pub open spec fn numeric_equality() -> Equality<u64> { |_: Component, a: u64, b: u64| a == b }

pub proof fn lemma_head_preservation<C>(source: FlatPair<C>, target: FlatPair<u64>,
    maps: Codebook<C>, eq: Equality<C>, domain: Domain<C>, request: Seq<C>, numeric: Seq<u64>)
    requires lowering(source, target, maps, eq), maps_wf(maps, eq, domain),
        constants_in_domain(source, domain), event_encoded(maps, eq, domain, request, numeric),
    ensures crate::flat::verify::head_matches(source.head@, request, eq)
        == crate::flat::verify::head_matches(target.head@, numeric, numeric_equality()),
{
    if source.head@.len() == request.len() {
        assert forall|i: int| 0 <= i < source.head@.len() implies (match (#[trigger] source.head@[i], target.head@[i]) {
            (FlatHead::Constant(value), FlatHead::Constant(id)) => eq(field_at(i), request[i], value) == (numeric[i] == id),
            _ => true,
        }) by {
            if let FlatHead::Constant(value) = source.head@[i] {
                if let FlatHead::Constant(id) = target.head@[i] {
                    lemma_encoded_equality(maps, eq, domain, field_at(i), request[i], value, numeric[i], id);
                }
            }
        }
    }
}

pub open spec fn pointwise<A, B>(source: Seq<A>, target: Seq<B>, relation: spec_fn(A, B) -> bool) -> bool {
    source.len() == target.len() && forall|i: int| 0 <= i < source.len() ==> relation(source[i], target[i])
}

/// Lift a partition by its lengths; no injectivity of the event representation is needed.
pub proof fn lemma_partition_lift<A, B>(source: Seq<A>, target: Seq<B>, parts: Seq<Seq<B>>,
    relation: spec_fn(A, B) -> bool)
    requires pointwise(source, target, relation), target == parts.flatten(),
    ensures exists|lifted: Seq<Seq<A>>| lifted.len() == parts.len() && source == lifted.flatten()
        && forall|i: int| 0 <= i < parts.len() ==> pointwise(lifted[i], parts[i], relation),
    decreases parts.len(),
{
    if parts.len() == 0 {
        assert(source == Seq::<A>::empty());
        assert(source == Seq::<Seq<A>>::empty().flatten());
    } else {
        let count = parts[0].len() as int;
        let prefix = source.take(count);
        let suffix = source.skip(count);
        assert(target.take(count) =~= parts[0]);
        assert(target.skip(count) =~= parts.drop_first().flatten());
        assert forall|i: int| 0 <= i < prefix.len() implies relation(prefix[i], parts[0][i]) by {
            assert(prefix[i] == source[i]);
            assert(parts[0][i] == target[i]);
        }
        assert forall|i: int| 0 <= i < suffix.len() implies relation(suffix[i], target.skip(count)[i]) by {
            assert(suffix[i] == source[i + count]);
            assert(target.skip(count)[i] == target[i + count]);
        }
        lemma_partition_lift(suffix, target.skip(count), parts.drop_first(), relation);
        let tail = choose|tail: Seq<Seq<A>>| tail.len() == parts.drop_first().len()
            && suffix == tail.flatten()
            && forall|i: int| 0 <= i < parts.drop_first().len() ==> pointwise(tail[i], parts.drop_first()[i], relation);
        let lifted = seq![prefix] + tail;
        assert(lifted.drop_first() =~= tail);
        assert(lifted.flatten() == source);
        assert forall|i: int| 0 <= i < parts.len() implies pointwise(lifted[i], parts[i], relation) by {
            if i > 0 { assert(lifted[i] == tail[i - 1]); assert(parts[i] == parts.drop_first()[i - 1]); }
        }
    }
}

pub proof fn lemma_test_preservation<C>(source: FlatPair<C>, target: FlatPair<u64>, id: nat,
    maps: Codebook<C>, eq: Equality<C>, domain: Domain<C>, request: Seq<C>, numeric_request: Seq<u64>,
    event: Seq<C>, numeric_event: Seq<u64>)
    requires crate::flat::verify::structural_wf(source), lowering(source, target, maps, eq),
        id < source.tests@.len(), maps_wf(maps, eq, domain), constants_in_domain(source, domain),
        event_encoded(maps, eq, domain, request, numeric_request),
        event_encoded(maps, eq, domain, event, numeric_event),
    ensures crate::flat::verify::test_sem(source.tests@, id, request, event, eq)
        == crate::flat::verify::test_sem(target.tests@, id, numeric_request, numeric_event, numeric_equality()),
    decreases id,
{
    match (source.tests@[id as int], target.tests@[id as int]) {
        (FlatTest::Atom { field, term: FlatTerm::Constant(value), .. },
         FlatTest::Atom { term: FlatTerm::Constant(value_id), .. }) => {
            let f = field_index(field);
            assert(field_at(f) == field);
            if f < event.len() {
                lemma_encoded_equality(maps, eq, domain, field, event[f], value, numeric_event[f], value_id);
            }
        },
        (FlatTest::Atom { field, term: FlatTerm::Variable(variable), .. }, _) => {
            assert(field == variable);
            let f = field_index(field);
            assert(field_at(f) == field);
            if f < event.len() {
                lemma_encoded_equality(maps, eq, domain, field, event[f], request[f], numeric_event[f], numeric_request[f]);
            }
        },
        (FlatTest::And(children), _) | (FlatTest::Or(children), _) => {
            assert forall|i: int| 0 <= i < children@.len() implies
                crate::flat::verify::test_sem(source.tests@, children@[i] as nat, request, event, eq)
                    == crate::flat::verify::test_sem(target.tests@, children@[i] as nat, numeric_request, numeric_event, numeric_equality()) by {
                lemma_test_preservation(source, target, children@[i] as nat, maps, eq, domain,
                    request, numeric_request, event, numeric_event);
            }
        },
        _ => {},
    }
}

pub proof fn lemma_lang_preservation<C>(source: FlatPair<C>, target: FlatPair<u64>, id: nat,
    maps: Codebook<C>, eq: Equality<C>, domain: Domain<C>, request: Seq<C>, numeric_request: Seq<u64>,
    word: Seq<Seq<C>>, numeric_word: Seq<Seq<u64>>)
    requires crate::flat::verify::structural_wf(source), lowering(source, target, maps, eq),
        id < source.regexes@.len(), maps_wf(maps, eq, domain), constants_in_domain(source, domain),
        event_encoded(maps, eq, domain, request, numeric_request),
        word_encoded(maps, eq, domain, word, numeric_word),
    ensures crate::flat::verify::flat_lang(source.tests@, source.regexes@, id, request, word, eq)
        == crate::flat::verify::flat_lang(target.tests@, target.regexes@, id, numeric_request, numeric_word, numeric_equality()),
    decreases id,
{
    lemma_topology_wf(source, target);
    assert(regex_same(source.regexes@[id as int], target.regexes@[id as int]));
    assert forall|i: int| 0 <= i < word.len() implies crate::flat::verify::event_wf(#[trigger] word[i], request.len()) by {
        assert(event_encoded(maps, eq, domain, word[i], numeric_word[i]));
    }
    assert forall|i: int| 0 <= i < numeric_word.len() implies crate::flat::verify::event_wf(#[trigger] numeric_word[i], numeric_request.len()) by {
        assert(event_encoded(maps, eq, domain, word[i], numeric_word[i]));
    }
    match source.regexes@[id as int] {
        FlatRegex::Test(test) => {
            if word.len() == 1 {
                lemma_test_preservation(source, target, test as nat, maps, eq, domain,
                    request, numeric_request, word[0], numeric_word[0]);
            }
            assert(crate::flat::verify::flat_lang(source.tests@, source.regexes@, id, request, word, eq)
                == crate::flat::verify::flat_lang(target.tests@, target.regexes@, id, numeric_request, numeric_word, numeric_equality()));
        },
        FlatRegex::Union(children) | FlatRegex::Intersect(children) => {
            assert forall|i: int| 0 <= i < children@.len() implies
                crate::flat::verify::flat_lang(source.tests@, source.regexes@, children@[i] as nat, request, word, eq)
                    == crate::flat::verify::flat_lang(target.tests@, target.regexes@, children@[i] as nat, numeric_request, numeric_word, numeric_equality()) by {
                lemma_lang_preservation(source, target, children@[i] as nat, maps, eq, domain,
                    request, numeric_request, word, numeric_word);
            }
            assert(crate::flat::verify::flat_lang(source.tests@, source.regexes@, id, request, word, eq)
                == crate::flat::verify::flat_lang(target.tests@, target.regexes@, id, numeric_request, numeric_word, numeric_equality()));
        },
        FlatRegex::Complement(child) => {
            lemma_lang_preservation(source, target, child as nat, maps, eq, domain,
                request, numeric_request, word, numeric_word);
            assert(crate::flat::verify::flat_lang(source.tests@, source.regexes@, id, request, word, eq)
                == crate::flat::verify::flat_lang(target.tests@, target.regexes@, id, numeric_request, numeric_word, numeric_equality()));
        },
        FlatRegex::Concat(children) => {
            if crate::flat::verify::flat_lang(source.tests@, source.regexes@, id, request, word, eq) {
                let parts = choose|parts: Seq<Seq<Seq<C>>>| parts.len() == children@.len()
                    && word == parts.flatten() && forall|i: int| 0 <= i < children@.len() ==>
                        crate::flat::verify::flat_lang(source.tests@, source.regexes@, children@[i] as nat, request, parts[i], eq);
                let relation = |n: Seq<u64>, r: Seq<C>| event_encoded(maps, eq, domain, r, n);
                assert(pointwise(numeric_word, word, relation));
                lemma_partition_lift(numeric_word, word, parts, relation);
                let lifted = choose|lifted: Seq<Seq<Seq<u64>>>| lifted.len() == parts.len()
                    && numeric_word == lifted.flatten()
                    && forall|i: int| 0 <= i < parts.len() ==> pointwise(lifted[i], parts[i], relation);
                assert forall|i: int| 0 <= i < children@.len() implies
                    crate::flat::verify::flat_lang(target.tests@, target.regexes@, children@[i] as nat, numeric_request, lifted[i], numeric_equality()) by {
                    assert(word_encoded(maps, eq, domain, parts[i], lifted[i]));
                    lemma_lang_preservation(source, target, children@[i] as nat, maps, eq, domain,
                        request, numeric_request, parts[i], lifted[i]);
                }
            }
            if crate::flat::verify::flat_lang(target.tests@, target.regexes@, id, numeric_request, numeric_word, numeric_equality()) {
                let parts = choose|parts: Seq<Seq<Seq<u64>>>| parts.len() == children@.len()
                    && numeric_word == parts.flatten() && forall|i: int| 0 <= i < children@.len() ==>
                        crate::flat::verify::flat_lang(target.tests@, target.regexes@, children@[i] as nat, numeric_request, parts[i], numeric_equality());
                let relation = |r: Seq<C>, n: Seq<u64>| event_encoded(maps, eq, domain, r, n);
                lemma_partition_lift(word, numeric_word, parts, relation);
                let lifted = choose|lifted: Seq<Seq<Seq<C>>>| lifted.len() == parts.len()
                    && word == lifted.flatten()
                    && forall|i: int| 0 <= i < parts.len() ==> pointwise(lifted[i], parts[i], relation);
                assert forall|i: int| 0 <= i < children@.len() implies
                    crate::flat::verify::flat_lang(source.tests@, source.regexes@, children@[i] as nat, request, lifted[i], eq) by {
                    assert(word_encoded(maps, eq, domain, lifted[i], parts[i]));
                    lemma_lang_preservation(source, target, children@[i] as nat, maps, eq, domain,
                        request, numeric_request, lifted[i], parts[i]);
                }
            }
            assert(crate::flat::verify::flat_lang(source.tests@, source.regexes@, id, request, word, eq)
                == crate::flat::verify::flat_lang(target.tests@, target.regexes@, id, numeric_request, numeric_word, numeric_equality()));
        },
        FlatRegex::Star(child) => {
            if crate::flat::verify::flat_lang(source.tests@, source.regexes@, id, request, word, eq) {
                let parts = choose|parts: Seq<Seq<Seq<C>>>| word == parts.flatten()
                    && forall|i: int| 0 <= i < parts.len() ==>
                        crate::flat::verify::flat_lang(source.tests@, source.regexes@, child as nat, request, parts[i], eq);
                let relation = |n: Seq<u64>, r: Seq<C>| event_encoded(maps, eq, domain, r, n);
                assert(pointwise(numeric_word, word, relation));
                lemma_partition_lift(numeric_word, word, parts, relation);
                let lifted = choose|lifted: Seq<Seq<Seq<u64>>>| lifted.len() == parts.len()
                    && numeric_word == lifted.flatten()
                    && forall|i: int| 0 <= i < parts.len() ==> pointwise(lifted[i], parts[i], relation);
                assert forall|i: int| 0 <= i < parts.len() implies
                    crate::flat::verify::flat_lang(target.tests@, target.regexes@, child as nat, numeric_request, lifted[i], numeric_equality()) by {
                    assert(word_encoded(maps, eq, domain, parts[i], lifted[i]));
                    lemma_lang_preservation(source, target, child as nat, maps, eq, domain,
                        request, numeric_request, parts[i], lifted[i]);
                }
            }
            if crate::flat::verify::flat_lang(target.tests@, target.regexes@, id, numeric_request, numeric_word, numeric_equality()) {
                let parts = choose|parts: Seq<Seq<Seq<u64>>>| numeric_word == parts.flatten()
                    && forall|i: int| 0 <= i < parts.len() ==>
                        crate::flat::verify::flat_lang(target.tests@, target.regexes@, child as nat, numeric_request, parts[i], numeric_equality());
                let relation = |r: Seq<C>, n: Seq<u64>| event_encoded(maps, eq, domain, r, n);
                lemma_partition_lift(word, numeric_word, parts, relation);
                let lifted = choose|lifted: Seq<Seq<Seq<C>>>| lifted.len() == parts.len()
                    && word == lifted.flatten()
                    && forall|i: int| 0 <= i < parts.len() ==> pointwise(lifted[i], parts[i], relation);
                assert forall|i: int| 0 <= i < parts.len() implies
                    crate::flat::verify::flat_lang(source.tests@, source.regexes@, child as nat, request, lifted[i], eq) by {
                    assert(word_encoded(maps, eq, domain, lifted[i], parts[i]));
                    lemma_lang_preservation(source, target, child as nat, maps, eq, domain,
                        request, numeric_request, lifted[i], parts[i]);
                }
            }
            assert(crate::flat::verify::flat_lang(source.tests@, source.regexes@, id, request, word, eq)
                == crate::flat::verify::flat_lang(target.tests@, target.regexes@, id, numeric_request, numeric_word, numeric_equality()));
        },
        _ => {
            assert(crate::flat::verify::flat_lang(source.tests@, source.regexes@, id, request, word, eq)
                == crate::flat::verify::flat_lang(target.tests@, target.regexes@, id, numeric_request, numeric_word, numeric_equality()));
        },
    }
}

/// The request/history may introduce values after compilation. Only extension and
/// coverage are required; semantic equivalence is the conclusion, never a premise.
pub proof fn lemma_later_maps_preservation<C>(source: FlatPair<C>, target: FlatPair<u64>,
    compiled_maps: Codebook<C>, later_maps: Codebook<C>, eq: Equality<C>, domain: Domain<C>,
    request: Seq<C>, numeric_request: Seq<u64>, word: Seq<Seq<C>>, numeric_word: Seq<Seq<u64>>)
    requires crate::flat::verify::structural_wf(source), lowering(source, target, compiled_maps, eq),
        extends(compiled_maps, later_maps, eq), maps_wf(later_maps, eq, domain),
        constants_in_domain(source, domain), event_encoded(later_maps, eq, domain, request, numeric_request),
        word_encoded(later_maps, eq, domain, word, numeric_word),
    ensures crate::flat::verify::head_matches(source.head@, request, eq)
            == crate::flat::verify::head_matches(target.head@, numeric_request, numeric_equality()),
        crate::flat::verify::flat_lang(source.tests@, source.regexes@, source.root as nat, request, word, eq)
            == crate::flat::verify::flat_lang(target.tests@, target.regexes@, target.root as nat, numeric_request, numeric_word, numeric_equality()),
{
    lemma_lowering_extends(source, target, compiled_maps, later_maps, eq);
    lemma_head_preservation(source, target, later_maps, eq, domain, request, numeric_request);
    lemma_lang_preservation(source, target, source.root as nat, later_maps, eq, domain,
        request, numeric_request, word, numeric_word);
}


/// Composition leaves only native component equality/projection and codebook
/// correspondence conditional; neither lowering's semantic equation is assumed.
pub proof fn lemma_dsl_later_maps_preservation<E: history_syntax::Event>(
    rule: history_syntax::syntax::Rule<E>,
    flattened_rule: crate::flat::FlatRule<E::Component>,
    numeric: FlatPair<u64>,
    compiled_maps: Codebook<E::Component>,
    later_maps: Codebook<E::Component>,
    domain: Domain<E::Component>,
    request: Seq<E::Component>,
    history: Seq<Seq<E::Component>>,
    numeric_request: Seq<u64>, numeric_history: Seq<Seq<u64>>,
)
    requires crate::verify::flatten::flattened::<E>(rule, flattened_rule),
        request.len() == rule.head@.len(),
        lowering(flattened_rule.source, numeric, compiled_maps, crate::verify::flatten::component_equality::<E>()),
        extends(compiled_maps, later_maps, crate::verify::flatten::component_equality::<E>()),
        maps_wf(later_maps, crate::verify::flatten::component_equality::<E>(), domain),
        constants_in_domain(flattened_rule.source, domain),
        event_encoded(later_maps, crate::verify::flatten::component_equality::<E>(), domain,
            request, numeric_request),
        word_encoded(later_maps, crate::verify::flatten::component_equality::<E>(), domain,
            history, numeric_history),
    ensures crate::spec::semantics::head_matches(rule.head@, request)
            == crate::flat::verify::head_matches(numeric.head@, numeric_request, numeric_equality()),
        crate::spec::semantics::lang(rule.tail@, rule.head@, request, history)
            == crate::flat::verify::flat_lang(numeric.tests@, numeric.regexes@, numeric.root as nat,
                numeric_request, numeric_history, numeric_equality()),
{
    assert forall|i: int| 0 <= i < history.len() implies history[i].len() == request.len() by {
        assert(event_encoded(later_maps, crate::verify::flatten::component_equality::<E>(), domain,
            history[i], numeric_history[i]));
    }
    crate::verify::flatten::flattening_preserves_semantics::<E>(rule, flattened_rule, request, history);
    lemma_later_maps_preservation(flattened_rule.source, numeric, compiled_maps, later_maps,
        crate::verify::flatten::component_equality::<E>(), domain,
        request, numeric_request, history, numeric_history);
}

}
