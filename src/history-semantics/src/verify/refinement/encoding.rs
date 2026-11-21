//! Layer 1: typed rules and pairs as numeric ones.
//!
//! The typed-to-numeric bridge is the existing verified front end, which the analyzer already
//! calls (`PolicyAnalyzer::add_rule` and `tail_included`): `flatten_rule_parts` (`junco_core::verify::flatten`,
//! `flattened`, `flattening_preserves_semantics`), `lower_flat` with the analyzer's encoder
//! (`junco_core::verify::encoding`, `lowering`, `lemma_dsl_later_maps_preservation`), and the
//! graph compiler (`crate::compile`, `lemma_flat_regex`, the `compile` contract). This layer only
//! adds what those do not state: the numeric rule with its mode, the whole-candidate valuation
//! the analyzer uses (the runtime uses head bindings, with 0 at unbound components), and
//! renaming invariance for fresh values.
use super::semantics::*;
use crate::compile::verify as numeric;
use history_syntax::Event;
use history_syntax::spec::events::RuleView;
use history_syntax::syntax::{Component, Rule, RuleMode};
use junco_core::spec::semantics::{rule_violated_view, violated_by};

use junco_core::flat::verify as portable;
use junco_core::flat::{FlatHead, FlatPair, FlatRule};
use junco_core::flat::{FlatRegex, FlatTerm, FlatTest};
use junco_core::kernel::verify as model;

use junco_core::verify::encoding as enc;
use junco_core::verify::flatten as fl;
use junco_core::verify::history_specs as language;
use junco_core::verify::history_specs::{EventView, Regex, Subst};
use vstd::prelude::*;

verus! {

broadcast use {vstd::std_specs::vec::group_vec_axioms, vstd::seq::group_seq_lemmas};

/// Kernel test semantics under the whole-candidate valuation `θ`.
pub open spec fn n_lang(theta: Subst, r: Regex<model::Test>, w: Seq<EventView>) -> bool {
    language::numeric_lang(model::gsem(theta), r, w)
}

/// A numeric head: a code per constant component, `None` for a variable.
pub type NHead = Seq<Option<nat>>;

/// A numeric rule. Tail atoms compare component `i` with a code or with `Variable(i)`, which reads
/// the candidate's component `i`.
pub struct NRule { pub mode: RuleMode, pub head: NHead, pub tail: Regex<model::Test> }

pub open spec fn n_head_field(h: NHead, c: Component) -> Option<nat> {
    if (c.0 as nat) < h.len() { h[c.0 as int] } else { None }
}

pub open spec fn n_head_matches(h: NHead, theta: Subst) -> bool {
    h.len() == theta.len() && forall|i: int| 0 <= i < h.len() ==>
        (#[trigger] h[i] matches Some(v) ==> theta[i] == v)
}

pub open spec fn n_rule_denies(rule: NRule, theta: Subst, w: Seq<EventView>) -> bool {
    n_head_matches(rule.head, theta) && violated_by(rule.mode, n_lang(theta, rule.tail, w))
}

pub open spec fn n_policy_denies(p: Seq<NRule>, theta: Subst, w: Seq<EventView>) -> bool {
    exists|i: int| 0 <= i < p.len() && #[trigger] n_rule_denies(p[i], theta, w)
}

/// Numeric domains: all of `nat` (`None`) or a finite set of codes (a declared finite domain).
pub type NDomains = Seq<Option<Set<nat>>>;

pub open spec fn n_domain(d: NDomains, c: Component) -> Option<Set<nat>> {
    if (c.0 as nat) < d.len() { d[c.0 as int] } else { None }
}

pub open spec fn n_event_in(d: NDomains, e: EventView) -> bool {
    1 <= d.len() <= history_syntax::MAX_ARITY && e.len() == d.len()
        && forall|i: int| 0 <= i < d.len() ==> (#[trigger] d[i] matches Some(values) ==> values.contains(e[i]))
}

pub open spec fn n_history_in(d: NDomains, w: Seq<EventView>) -> bool {
    forall|i: int| 0 <= i < w.len() ==> #[trigger] n_event_in(d, w[i])
}

/// Valuations range over the domain and, as the kernel contracts require, over `u64` values.
pub open spec fn n_theta_ok(d: NDomains, theta: Subst) -> bool {
    language::event_wf(theta, d.len()) && n_event_in(d, theta)
}

// ----- the verified front end -----

/// The view of an executable rule.
pub open spec fn rule_view<E: Event>(rule: Rule<E>) -> RuleView<E::Component> {
    RuleView { mode: rule.mode, head: rule.head@, tail: rule.tail@ }
}

/// What the analyzer's front end establishes for an added rule: the verified `flatten_rule`
/// (`flattening_client` gives `flattened`, hence `head_scoped` and `regex_scoped`) and
/// `lower_flat` (`lowering` and `constants_in_domain` for the encoder's books).
pub open spec fn front_end_ok<E: Event>(
    rule: Rule<E>, flat: FlatRule<E::Component>, template: FlatPair<u64>,
    maps: enc::Codebook<E::Component>, domain: enc::Domain<E::Component>,
) -> bool {
    &&& fl::flattened::<E>(rule, flat)
    &&& enc::lowering(flat.source, template, maps, fl::component_equality::<E>())
    &&& enc::constants_in_domain(flat.source, domain)
}

pub open spec fn head_code(h: FlatHead<u64>) -> Option<nat> {
    match h { FlatHead::Constant(v) => Some(v as nat), _ => None }
}

/// The numeric rule `n` searched by the analyzer stands for the lowered template: same mode and
/// head constants, and a tail with the template's language (`numeric::source_regex`) under every
/// valuation. The `compile` contract gives the tail clause for the compiled graph root.
pub open spec fn represents(n: NRule, mode: RuleMode, template: FlatPair<u64>) -> bool {
    &&& n.mode == mode
    &&& n.head == template.head@.map(|i: int, h: FlatHead<u64>| head_code(h))
    &&& forall|theta: Subst, w: Seq<EventView>| language::event_wf(theta, theta.len())
        ==> #[trigger] n_lang(theta, n.tail, w) == numeric::source_regex(template, template.root as nat, theta, w)
}

/// Agreement includes the valuation lengths formerly fixed by the tuple type.
pub open spec fn agrees_on_binds(template: FlatPair<u64>, a: Subst, b: Subst) -> bool {
    a.len() == template.head@.len() && b.len() == template.head@.len()
        && forall|i: int| 0 <= i < template.head@.len() && #[trigger] numeric::head_view(template)[i] is Bind
            ==> a[i] == b[i]
}

/// New: `source_regex` reads the valuation only at bound components, because tail variables
/// refer only to bound components (`structural_wf`). This moves the existing results, stated for
/// the runtime's head bindings, to the analyzer's whole-candidate valuation.
pub open spec fn stmt_source_regex_local() -> bool {
    forall|template: FlatPair<u64>, a: Subst, b: Subst, w: Seq<EventView>|
        junco_core::flat::verify::structural_wf(template) && agrees_on_binds(template, a, b)
            ==> (#[trigger] numeric::source_regex(template, template.root as nat, a, w)
                == #[trigger] numeric::source_regex(template, template.root as nat, b, w))
}

/// Typed denial is numeric denial for a rule passed through the front end. Proof plan, from
/// existing results: `enc::lemma_dsl_later_maps_preservation` (typed head and language equal the
/// numeric flat ones), `numeric::lemma_flat_head` and `numeric::lemma_flat_regex` (flat language
/// equals `source_regex` under the head bindings), `stmt_source_regex_local`, and `represents`.
/// Like the runtime's typed guarantees, it is conditional on the encoder's books (`maps_wf`, which
/// requires nonzero codes) and on the pair being encoded. Tails (`tail_included`) are the case
/// `mode = Forbid`.
pub open spec fn stmt_front_end_denies<E: Event>() -> bool {
    forall|rule: Rule<E>, flat: FlatRule<E::Component>, template: FlatPair<u64>,
        maps: enc::Codebook<E::Component>, later: enc::Codebook<E::Component>,
        domain: enc::Domain<E::Component>, n: NRule,
        candidate: Seq<E::Component>,
        history: Seq<Seq<E::Component>>,
        request: Seq<u64>, word: Seq<Seq<u64>>, theta: Subst, w: Seq<EventView>|
        #![trigger front_end_ok(rule, flat, template, maps, domain), represents(n, rule.mode, template),
            enc::extends(maps, later, fl::component_equality::<E>()),
            enc::event_encoded(later, fl::component_equality::<E>(), domain, candidate, request),
            enc::word_encoded(later, fl::component_equality::<E>(), domain, history, word),
            enc::event_representation(request, theta), enc::word_representation(word, w)]
        front_end_ok(rule, flat, template, maps, domain) && represents(n, rule.mode, template)
            && candidate.len() == rule.head@.len()
            && enc::extends(maps, later, fl::component_equality::<E>())
            && enc::maps_wf(later, fl::component_equality::<E>(), domain)
            && enc::event_encoded(later, fl::component_equality::<E>(), domain, candidate, request)
            && enc::word_encoded(later, fl::component_equality::<E>(), domain, history, word)
            && enc::event_representation(request, theta) && enc::word_representation(word, w)
            ==> (rule_violated_view(rule_view(rule), candidate, history) == n_rule_denies(n, theta, w))
}

// ----- fresh values -----

/// Numeric genericity: renaming the values of a pair injectively, fixing the codes of the
/// rules' constants, preserves denial. Together with `stmt_front_end_denies` this transfers a
/// numeric verdict to every typed pair and every typed instantiation of fresh values.
pub open spec fn n_renaming_ok(f: spec_fn(nat) -> nat, fixed: ISet<nat>, values: ISet<nat>) -> bool {
    &&& forall|x: nat, y: nat| values.contains(x) && values.contains(y) ==> (#[trigger] f(x) == #[trigger] f(y) <==> x == y)
    &&& forall|x: nat| #[trigger] fixed.contains(x) ==> f(x) == x
    &&& forall|x: nat, k: nat| #![trigger values.contains(x), fixed.contains(k)]
        values.contains(x) && fixed.contains(k) ==> (f(x) == k <==> x == k)
}

pub open spec fn n_rename_event(f: spec_fn(nat) -> nat, e: EventView) -> EventView {
    e.map(|i: int, value: nat| f(value))
}

pub open spec fn n_rename_history(f: spec_fn(nat) -> nat, w: Seq<EventView>) -> Seq<EventView> {
    w.map(|i: int, e: EventView| n_rename_event(f, e))
}

/// The rule's head or tail compares component `c` with the code `v`.
pub open spec fn rule_mentions(rule: NRule, c: Component, v: nat) -> bool {
    n_head_field(rule.head, c) == Some(v) || regex_mentions(rule.tail, c, v)
}

/// The codes occurring in a rule (head constants and tail atoms).
pub open spec fn n_rule_codes(rule: NRule) -> ISet<nat> {
    ISet::new(|v: nat| (exists|i: int| 0 <= i < rule.head.len() && #[trigger] rule.head[i] == Some(v))
        || exists|c: Component| #[trigger] regex_mentions(rule.tail, c, v))
}

/// Some atom of `r` compares component `c` with the code `v`.
pub open spec fn regex_mentions(r: Regex<model::Test>, c: Component, v: nat) -> bool
    decreases r,
{
    match r {
        Regex::Test(t) => test_mentions(t, c, v),
        Regex::Union(cs) | Regex::Concat(cs) | Regex::Intersect(cs) =>
            exists|i: int| #![trigger regex_mention_child(r, i)] 0 <= i < cs.len() && regex_mentions(cs[i], c, v),
        Regex::Star(b) | Regex::Not(b) => regex_mentions(*b, c, v),
        _ => false,
    }
}

pub open spec fn test_mentions(t: model::Test, c: Component, v: nat) -> bool
    decreases t,
{
    match t {
        model::Test::Atom(model::Primitive::Eq(field, model::GTerm::Constant(k)), _) => field == c && k == v,
        model::Test::And(cs) | model::Test::Or(cs) => exists|i: int| #![trigger test_mention_child(t, i)] 0 <= i < cs.len() && test_mentions(cs[i], c, v),
        _ => false,
    }
}

pub open spec fn stmt_numeric_genericity() -> bool {
    forall|rule: NRule, theta: Subst, w: Seq<EventView>, f: spec_fn(nat) -> nat|
        n_renaming_ok(f, n_rule_codes(rule), n_pair_values(theta, w))
            ==> (n_rule_denies(rule, theta, w) == #[trigger] n_rule_denies(rule, n_rename_event(f, theta), n_rename_history(f, w)))
}

/// Every component value of a numeric pair.
pub open spec fn n_pair_values(theta: Subst, w: Seq<EventView>) -> ISet<nat> {
    ISet::new(|x: nat| (exists|j: int| 0 <= j < theta.len() && #[trigger] theta[j] == x)
        || exists|i: int, j: int| 0 <= i < w.len() && 0 <= j < w[i].len() && #[trigger] w[i][j] == x)
}

proof fn lemma_candidate_value_contains(theta: Subst, w: Seq<EventView>, j: int, value: nat)
    requires 0 <= j < theta.len(), theta[j] == value,
    ensures n_pair_values(theta, w).contains(value),
{
    assert(exists|k: int| 0 <= k < theta.len() && #[trigger] theta[k] == value);
}

proof fn lemma_history_value_contains(theta: Subst, w: Seq<EventView>, i: int, j: int, value: nat)
    requires 0 <= i < w.len(), 0 <= j < w[i].len(), w[i][j] == value,
    ensures n_pair_values(theta, w).contains(value),
{
    assert(exists|k: int, l: int| 0 <= k < w.len() && 0 <= l < w[k].len()
        && #[trigger] w[k][l] == value);
}

// ===== proofs =====

// Parent-keyed triggers avoid conditional children and recursive-call fuel in SMT patterns.
#[verifier::opaque]
pub open spec fn test_mention_child(t: model::Test, i: int) -> Option<model::Test> {
    match t {
        model::Test::And(cs) | model::Test::Or(cs) => Some(cs[i]),
        _ => None,
    }
}

#[verifier::opaque]
pub open spec fn regex_mention_child(r: Regex<model::Test>, i: int) -> Option<Regex<model::Test>> {
    match r {
        Regex::Union(cs) | Regex::Concat(cs) | Regex::Intersect(cs) => Some(cs[i]),
        _ => None,
    }
}

/// `source_test` reads the valuation only at bound components.
pub proof fn lemma_source_test_local(template: FlatPair<u64>, index: nat, a: Subst, b: Subst, e: EventView)
    requires portable::structural_wf(template), agrees_on_binds(template, a, b),
    ensures numeric::source_test(template, index, a, e) == numeric::source_test(template, index, b, e),
    decreases index,
{
    reveal_with_fuel(numeric::source_test, 1);
    if index < template.tests@.len() {
        assert(portable::test_wf(template.head@, template.tests@[index as int], index));
        match template.tests@[index as int] {
            FlatTest::Atom { field, term, positive } => {
                if let FlatTerm::Variable(v) = term {
                    let j = portable::field_index(v);
                    assert(0 <= j < template.head@.len());
                    assert(template.head@[j] is Bind);
                    assert(numeric::head_view(template)[j] is Bind);
                    assert(language::field_value(a, v) == language::field_value(b, v));
                }
            },
            FlatTest::And(children) | FlatTest::Or(children) => {
                assert forall|i: int| 0 <= i < children@.len() implies
                    numeric::source_test(template, children@[i] as nat, a, e)
                        == numeric::source_test(template, children@[i] as nat, b, e) by {
                    assert(children@[i] < index);
                    lemma_source_test_local(template, children@[i] as nat, a, b, e);
                }
            },
            _ => {},
        }
    }
}

/// `source_regex` reads the valuation only at bound components.
pub proof fn lemma_source_regex_local(template: FlatPair<u64>, index: nat, a: Subst, b: Subst, w: Seq<EventView>)
    requires portable::structural_wf(template), agrees_on_binds(template, a, b),
    ensures numeric::source_regex(template, index, a, w) == numeric::source_regex(template, index, b, w),
    decreases index, 1nat,
{
    reveal_with_fuel(numeric::source_regex, 1);
    if index < template.regexes@.len() {
        assert(portable::regex_wf(template.regexes@[index as int], index, template.tests@.len()));
        match template.regexes@[index as int] {
            FlatRegex::Test(test) => {
                if w.len() == 1 {
                    lemma_source_test_local(template, test as nat, a, b, w[0]);
                }
            },
            FlatRegex::Union(children) | FlatRegex::Intersect(children) => {
                assert forall|i: int| 0 <= i < children@.len() implies
                    numeric::source_regex(template, children@[i] as nat, a, w)
                        == numeric::source_regex(template, children@[i] as nat, b, w) by {
                    assert(children@[i] < index);
                    lemma_source_regex_local(template, children@[i] as nat, a, b, w);
                }
            },
            FlatRegex::Concat(children) => {
                assert forall|i: int, p: Seq<EventView>| 0 <= i < children@.len() implies
                    numeric::source_regex(template, children@[i] as nat, a, p)
                        == numeric::source_regex(template, children@[i] as nat, b, p) by {
                    assert(children@[i] < index);
                    lemma_source_regex_local(template, children@[i] as nat, a, b, p);
                }
                if numeric::source_regex(template, index, a, w) {
                    let parts = choose|parts: Seq<Seq<EventView>>|
                        parts.len() == children@.len() && parts.flatten() == w
                        && forall|i: int| 0 <= i < children@.len() ==> children@[i] < index
                            && numeric::source_regex(template, children@[i] as nat, a, parts[i]);
                    assert forall|i: int| 0 <= i < children@.len() implies children@[i] < index
                        && numeric::source_regex(template, children@[i] as nat, b, parts[i]) by {}
                    assert(numeric::source_regex(template, index, b, w));
                }
                if numeric::source_regex(template, index, b, w) {
                    let parts = choose|parts: Seq<Seq<EventView>>|
                        parts.len() == children@.len() && parts.flatten() == w
                        && forall|i: int| 0 <= i < children@.len() ==> children@[i] < index
                            && numeric::source_regex(template, children@[i] as nat, b, parts[i]);
                    assert forall|i: int| 0 <= i < children@.len() implies children@[i] < index
                        && numeric::source_regex(template, children@[i] as nat, a, parts[i]) by {}
                    assert(numeric::source_regex(template, index, a, w));
                }
            },
            FlatRegex::Star(child) => {
                assert forall|p: Seq<EventView>|
                    numeric::source_regex(template, child as nat, a, p)
                        == #[trigger] numeric::source_regex(template, child as nat, b, p) by {
                    lemma_source_regex_local(template, child as nat, a, b, p);
                }
                if numeric::source_regex(template, index, a, w) {
                    let parts = choose|parts: Seq<Seq<EventView>>| parts.flatten() == w
                        && forall|i: int| 0 <= i < parts.len()
                            ==> numeric::source_regex(template, child as nat, a, parts[i]);
                    assert forall|i: int| 0 <= i < parts.len() implies
                        numeric::source_regex(template, child as nat, b, parts[i]) by {}
                    assert(numeric::source_regex(template, index, b, w));
                }
                if numeric::source_regex(template, index, b, w) {
                    let parts = choose|parts: Seq<Seq<EventView>>| parts.flatten() == w
                        && forall|i: int| 0 <= i < parts.len()
                            ==> numeric::source_regex(template, child as nat, b, parts[i]);
                    assert forall|i: int| 0 <= i < parts.len() implies
                        numeric::source_regex(template, child as nat, a, parts[i]) by {}
                    assert(numeric::source_regex(template, index, a, w));
                }
            },
            FlatRegex::Complement(child) => {
                lemma_source_regex_local(template, child as nat, a, b, w);
            },
            _ => {},
        }
    }
}

pub proof fn theorem_source_regex_local()
    ensures stmt_source_regex_local(),
{
    assert forall|template: FlatPair<u64>, a: Subst, b: Subst, w: Seq<EventView>|
        portable::structural_wf(template) && agrees_on_binds(template, a, b)
            implies (#[trigger] numeric::source_regex(template, template.root as nat, a, w)
                == #[trigger] numeric::source_regex(template, template.root as nat, b, w)) by {
        lemma_source_regex_local(template, template.root as nat, a, b, w);
    }
}

/// One instance of `stmt_front_end_denies`.
pub proof fn lemma_front_end_denies<E: Event>(
    rule: Rule<E>, flat: FlatRule<E::Component>, template: FlatPair<u64>,
    maps: enc::Codebook<E::Component>, later: enc::Codebook<E::Component>,
    domain: enc::Domain<E::Component>, n: NRule,
    candidate: Seq<E::Component>,
    history: Seq<Seq<E::Component>>,
    request: Seq<u64>, word: Seq<Seq<u64>>, theta: Subst, w: Seq<EventView>,
)
    requires
        front_end_ok(rule, flat, template, maps, domain), represents(n, rule.mode, template),
        candidate.len() == rule.head@.len(),
        enc::extends(maps, later, fl::component_equality::<E>()),
        enc::maps_wf(later, fl::component_equality::<E>(), domain),
        enc::event_encoded(later, fl::component_equality::<E>(), domain, candidate, request),
        enc::word_encoded(later, fl::component_equality::<E>(), domain, history, word),
        enc::event_representation(request, theta), enc::word_representation(word, w),
    ensures rule_violated_view(rule_view(rule), candidate, history) == n_rule_denies(n, theta, w),
{
    enc::lemma_dsl_later_maps_preservation::<E>(rule, flat, template, maps, later, domain,
        candidate, history, request, word);
    enc::lemma_topology_wf(flat.source, template);
    assert(template.head@.len() == request.len() && theta.len() == request.len());
    assert(n.head.len() == template.head@.len());
    let flat_head = portable::head_matches(template.head@, request, enc::numeric_equality());
    assert forall|i: int| #![trigger template.head@[i]] 0 <= i < template.head@.len() implies
        (match template.head@[i] {
            FlatHead::Constant(expected) => (enc::numeric_equality())(Component(i as u8), request[i], expected),
            _ => true,
        }) == (n.head[i] matches Some(v) ==> theta[i] == v) by {
        assert(n.head[i] == head_code(template.head@[i]));
        assert(theta[i] == request[i] as nat);
    }
    assert(flat_head == n_head_matches(n.head, theta));
    if flat_head {
        let head = numeric::head_view(template);
        let bound = language::head_bindings(head, theta);
        assert forall|i: int| 0 <= i < head.len() implies
            language::head_field_match(head[i], theta[i], bound[i]) by {
            assert(n.head[i] == head_code(template.head@[i]));
        }
        assert(language::head_match(head, theta, bound));
        assert forall|i: int| 0 <= i < word.len() implies word[i].len() == request.len() by {
            assert(enc::event_encoded(later, fl::component_equality::<E>(), domain, history[i], word[i]));
        }
        numeric::lemma_flat_regex(template, template.root as nat, request, theta, word, w, bound);
        assert forall|i: int| 0 <= i < head.len() && #[trigger] head[i] is Bind implies bound[i] == theta[i] by {}
        assert(agrees_on_binds(template, bound, theta));
        lemma_source_regex_local(template, template.root as nat, bound, theta, w);
        assert(language::event_wf(theta, theta.len())) by {
            assert forall|i: int| 0 <= i < theta.len() implies theta[i] <= u64::MAX by {
                assert(theta[i] == request[i] as nat);
            }
        }
        assert(n_lang(theta, n.tail, w) == numeric::source_regex(template, template.root as nat, theta, w));
    }
}

pub proof fn theorem_front_end_denies<E: Event>()
    ensures stmt_front_end_denies::<E>(),
{
    assert forall|rule: Rule<E>, flat: FlatRule<E::Component>, template: FlatPair<u64>,
        maps: enc::Codebook<E::Component>, later: enc::Codebook<E::Component>,
        domain: enc::Domain<E::Component>, n: NRule,
        candidate: Seq<E::Component>,
        history: Seq<Seq<E::Component>>,
        request: Seq<u64>, word: Seq<Seq<u64>>, theta: Subst, w: Seq<EventView>|
        #![trigger front_end_ok(rule, flat, template, maps, domain), represents(n, rule.mode, template),
            enc::extends(maps, later, fl::component_equality::<E>()),
            enc::event_encoded(later, fl::component_equality::<E>(), domain, candidate, request),
            enc::word_encoded(later, fl::component_equality::<E>(), domain, history, word),
            enc::event_representation(request, theta), enc::word_representation(word, w)]
        front_end_ok(rule, flat, template, maps, domain) && represents(n, rule.mode, template)
            && candidate.len() == rule.head@.len()
            && enc::extends(maps, later, fl::component_equality::<E>())
            && enc::maps_wf(later, fl::component_equality::<E>(), domain)
            && enc::event_encoded(later, fl::component_equality::<E>(), domain, candidate, request)
            && enc::word_encoded(later, fl::component_equality::<E>(), domain, history, word)
            && enc::event_representation(request, theta) && enc::word_representation(word, w)
        implies (rule_violated_view(rule_view(rule), candidate, history) == n_rule_denies(n, theta, w)) by {
        lemma_front_end_denies::<E>(rule, flat, template, maps, later, domain, n, candidate, history,
            request, word, theta, w);
    }
}

// ----- numeric genericity -----

pub open spec fn n_in_values(values: ISet<nat>, e: EventView) -> bool {
    forall|i: int| 0 <= i < e.len() ==> #[trigger] values.contains(e[i])
}

/// `b` is the renaming of an event `a` whose values lie in `values`.
pub open spec fn n_renamed(f: spec_fn(nat) -> nat, values: ISet<nat>) -> spec_fn(EventView, EventView) -> bool {
    |a: EventView, b: EventView| n_in_values(values, a) && b == n_rename_event(f, a)
}

pub open spec fn n_renamed_rev(f: spec_fn(nat) -> nat, values: ISet<nat>) -> spec_fn(EventView, EventView) -> bool {
    |b: EventView, a: EventView| n_in_values(values, a) && b == n_rename_event(f, a)
}

pub proof fn lemma_rename_field(f: spec_fn(nat) -> nat, e: EventView, c: Component)
    requires (c.0 as nat) < e.len(),
    ensures language::field_value(n_rename_event(f, e), c) == f(language::field_value(e, c)),
{}

pub proof fn lemma_in_values_field(values: ISet<nat>, e: EventView, c: Component)
    requires n_in_values(values, e), (c.0 as nat) < e.len(),
    ensures values.contains(language::field_value(e, c)),
{}

pub proof fn lemma_test_rename(t: model::Test, theta: Subst, f: spec_fn(nat) -> nat, fixed: ISet<nat>,
    values: ISet<nat>, e: EventView)
    requires n_renaming_ok(f, fixed, values), n_in_values(values, theta), n_in_values(values, e),
        forall|c: Component, v: nat| #[trigger] test_mentions(t, c, v) ==> fixed.contains(v),
    ensures model::test_holds(theta, t, e)
        == model::test_holds(n_rename_event(f, theta), t, n_rename_event(f, e)),
    decreases t,
{
    reveal_with_fuel(test_mentions, 1);
    reveal_with_fuel(model::test_holds, 1);
    match t {
        model::Test::Atom(model::Primitive::Eq(field, term), positive) => {
            if (field.0 as nat) < e.len() {
                lemma_rename_field(f, e, field);
                lemma_in_values_field(values, e, field);
                let x = language::field_value(e, field);
                match term {
                    model::GTerm::Constant(k) => {
                        assert(test_mentions(t, field, k));
                        assert(fixed.contains(k));
                        assert(f(x) == k <==> x == k);
                    },
                    model::GTerm::Variable(v) => {
                        if (v.0 as nat) < theta.len() {
                            lemma_rename_field(f, theta, v);
                            lemma_in_values_field(values, theta, v);
                            let y = language::field_value(theta, v);
                            assert(f(x) == f(y) <==> x == y);
                        }
                    },
                }
            }
        },
        model::Test::And(cs) | model::Test::Or(cs) => {
            assert forall|i: int| 0 <= i < cs.len() implies
                model::test_holds(theta, cs[i], e)
                    == model::test_holds(n_rename_event(f, theta), cs[i], n_rename_event(f, e)) by {
                assert forall|c: Component, v: nat| #[trigger] test_mentions(cs[i], c, v) implies fixed.contains(v) by {
                    reveal(test_mention_child);
                    assert(test_mention_child(t, i) == Some(cs[i]));
                    assert(test_mentions(t, c, v));
                }
                lemma_test_rename(cs[i], theta, f, fixed, values, e);
            }
        },
        _ => {},
    }
}

pub proof fn lemma_lang_rename(r: Regex<model::Test>, theta: Subst, f: spec_fn(nat) -> nat, fixed: ISet<nat>,
    values: ISet<nat>, u: Seq<EventView>, v: Seq<EventView>)
    requires n_renaming_ok(f, fixed, values), n_in_values(values, theta),
        enc::pointwise(u, v, n_renamed(f, values)),
        forall|c: Component, k: nat| #[trigger] regex_mentions(r, c, k) ==> fixed.contains(k),
    ensures language::numeric_lang(model::gsem(theta), r, u)
        == language::numeric_lang(model::gsem(n_rename_event(f, theta)), r, v),
    decreases r,
{
    reveal_with_fuel(language::numeric_lang, 1);
    reveal_with_fuel(regex_mentions, 1);
    let ftheta = n_rename_event(f, theta);
    let rel = n_renamed(f, values);
    let rev = n_renamed_rev(f, values);
    match r {
        Regex::Test(l) => {
            if u.len() == 1 {
                assert(rel(u[0], v[0]));
                assert forall|c: Component, k: nat| #[trigger] test_mentions(l, c, k) implies fixed.contains(k) by {
                    assert(regex_mentions(r, c, k));
                }
                lemma_test_rename(l, theta, f, fixed, values, u[0]);
            }
        },
        Regex::Union(cs) | Regex::Intersect(cs) => {
            assert forall|i: int| 0 <= i < cs.len() implies
                language::numeric_lang(model::gsem(theta), cs[i], u) == language::numeric_lang(model::gsem(ftheta), cs[i], v) by {
                assert forall|c: Component, k: nat| #[trigger] regex_mentions(cs[i], c, k) implies fixed.contains(k) by {
                    reveal(regex_mention_child);
                    assert(regex_mention_child(r, i) == Some(cs[i]));
                    assert(regex_mentions(r, c, k));
                }
                lemma_lang_rename(cs[i], theta, f, fixed, values, u, v);
            }
        },
        Regex::Not(b) => {
            assert forall|c: Component, k: nat| #[trigger] regex_mentions(*b, c, k) implies fixed.contains(k) by {
                assert(regex_mentions(r, c, k));
            }
            lemma_lang_rename(*b, theta, f, fixed, values, u, v);
        },
        Regex::Concat(cs) => {
            assert forall|i: int| #![trigger cs[i]] 0 <= i < cs.len() implies
                forall|c: Component, k: nat| #[trigger] regex_mentions(cs[i], c, k) ==> fixed.contains(k) by {
                assert forall|c: Component, k: nat| #[trigger] regex_mentions(cs[i], c, k) implies fixed.contains(k) by {
                    reveal(regex_mention_child);
                    assert(regex_mention_child(r, i) == Some(cs[i]));
                    assert(regex_mentions(r, c, k));
                }
            }
            if language::numeric_lang(model::gsem(theta), r, u) {
                let parts = choose|parts: Seq<Seq<EventView>>| parts.len() == cs.len() && u == parts.flatten()
                    && forall|i: int| 0 <= i < cs.len() ==> language::numeric_lang(model::gsem(theta), cs[i], parts[i]);
                assert(enc::pointwise(v, u, rev));
                enc::lemma_partition_lift(v, u, parts, rev);
                let lifted = choose|lifted: Seq<Seq<EventView>>| lifted.len() == parts.len() && v == lifted.flatten()
                    && forall|i: int| 0 <= i < parts.len() ==> enc::pointwise(lifted[i], parts[i], rev);
                assert forall|i: int| 0 <= i < cs.len() implies language::numeric_lang(model::gsem(ftheta), cs[i], lifted[i]) by {
                    assert(enc::pointwise(lifted[i], parts[i], rev));
                    assert(enc::pointwise(parts[i], lifted[i], rel));
                    lemma_lang_rename(cs[i], theta, f, fixed, values, parts[i], lifted[i]);
                }
                assert(language::numeric_lang(model::gsem(ftheta), r, v));
            }
            if language::numeric_lang(model::gsem(ftheta), r, v) {
                let parts = choose|parts: Seq<Seq<EventView>>| parts.len() == cs.len() && v == parts.flatten()
                    && forall|i: int| 0 <= i < cs.len() ==> language::numeric_lang(model::gsem(ftheta), cs[i], parts[i]);
                enc::lemma_partition_lift(u, v, parts, rel);
                let lifted = choose|lifted: Seq<Seq<EventView>>| lifted.len() == parts.len() && u == lifted.flatten()
                    && forall|i: int| 0 <= i < parts.len() ==> enc::pointwise(lifted[i], parts[i], rel);
                assert forall|i: int| 0 <= i < cs.len() implies language::numeric_lang(model::gsem(theta), cs[i], lifted[i]) by {
                    lemma_lang_rename(cs[i], theta, f, fixed, values, lifted[i], parts[i]);
                }
                assert(language::numeric_lang(model::gsem(theta), r, u));
            }
        },
        Regex::Star(b) => {
            assert forall|c: Component, k: nat| #[trigger] regex_mentions(*b, c, k) implies fixed.contains(k) by {
                assert(regex_mentions(r, c, k));
            }
            if language::numeric_lang(model::gsem(theta), r, u) {
                let parts = choose|parts: Seq<Seq<EventView>>| u == parts.flatten()
                    && forall|i: int| 0 <= i < parts.len() ==> language::numeric_lang(model::gsem(theta), *b, parts[i]);
                assert(enc::pointwise(v, u, rev));
                enc::lemma_partition_lift(v, u, parts, rev);
                let lifted = choose|lifted: Seq<Seq<EventView>>| lifted.len() == parts.len() && v == lifted.flatten()
                    && forall|i: int| 0 <= i < parts.len() ==> enc::pointwise(lifted[i], parts[i], rev);
                assert forall|i: int| 0 <= i < lifted.len() implies language::numeric_lang(model::gsem(ftheta), *b, lifted[i]) by {
                    assert(enc::pointwise(lifted[i], parts[i], rev));
                    assert(enc::pointwise(parts[i], lifted[i], rel));
                    lemma_lang_rename(*b, theta, f, fixed, values, parts[i], lifted[i]);
                }
                assert(language::numeric_lang(model::gsem(ftheta), r, v));
            }
            if language::numeric_lang(model::gsem(ftheta), r, v) {
                let parts = choose|parts: Seq<Seq<EventView>>| v == parts.flatten()
                    && forall|i: int| 0 <= i < parts.len() ==> language::numeric_lang(model::gsem(ftheta), *b, parts[i]);
                enc::lemma_partition_lift(u, v, parts, rel);
                let lifted = choose|lifted: Seq<Seq<EventView>>| lifted.len() == parts.len() && u == lifted.flatten()
                    && forall|i: int| 0 <= i < parts.len() ==> enc::pointwise(lifted[i], parts[i], rel);
                assert forall|i: int| 0 <= i < lifted.len() implies language::numeric_lang(model::gsem(theta), *b, lifted[i]) by {
                    lemma_lang_rename(*b, theta, f, fixed, values, lifted[i], parts[i]);
                }
                assert(language::numeric_lang(model::gsem(theta), r, u));
            }
        },
        _ => {},
    }
}

/// One instance of `stmt_numeric_genericity`.
pub proof fn lemma_numeric_genericity(rule: NRule, theta: Subst, w: Seq<EventView>, f: spec_fn(nat) -> nat)
    requires n_renaming_ok(f, n_rule_codes(rule), n_pair_values(theta, w)),
    ensures n_rule_denies(rule, theta, w) == n_rule_denies(rule, n_rename_event(f, theta), n_rename_history(f, w)),
{
    let fixed = n_rule_codes(rule);
    let values = n_pair_values(theta, w);
    let ftheta = n_rename_event(f, theta);
    let fw = n_rename_history(f, w);
    assert(n_in_values(values, theta)) by {
        assert forall|j: int| 0 <= j < theta.len() implies #[trigger] values.contains(theta[j]) by {
            lemma_candidate_value_contains(theta, w, j, theta[j]);
        }
    }
    assert forall|i: int| #![trigger w[i]] 0 <= i < w.len()
        implies n_renamed(f, values)(w[i], fw[i]) by {
        assert forall|j: int| 0 <= j < w[i].len() implies #[trigger] values.contains(w[i][j]) by {
            lemma_history_value_contains(theta, w, i, j, w[i][j]);
        }
    }
    assert(enc::pointwise(w, fw, n_renamed(f, values)));
    assert forall|c: Component, k: nat| #[trigger] regex_mentions(rule.tail, c, k) implies fixed.contains(k) by {
        assert(rule_mentions(rule, c, k));
    }
    lemma_lang_rename(rule.tail, theta, f, fixed, values, w, fw);
    if rule.head.len() == theta.len() {
        assert forall|i: int| 0 <= i < rule.head.len() && #[trigger] rule.head[i] is Some implies
            (theta[i] == rule.head[i]->Some_0 <==> ftheta[i] == rule.head[i]->Some_0) by {
            let k = rule.head[i]->Some_0;
            assert(exists|j: int| 0 <= j < rule.head.len() && #[trigger] rule.head[j] == Some(k));
            assert(fixed.contains(k));
            assert(values.contains(theta[i]));
            assert(ftheta[i] == f(theta[i]));
        }
    }
    assert(n_head_matches(rule.head, theta) == n_head_matches(rule.head, ftheta));
}

pub proof fn theorem_numeric_genericity()
    ensures stmt_numeric_genericity(),
{
    assert forall|rule: NRule, theta: Subst, w: Seq<EventView>, f: spec_fn(nat) -> nat|
        n_renaming_ok(f, n_rule_codes(rule), n_pair_values(theta, w))
            implies (n_rule_denies(rule, theta, w)
                == #[trigger] n_rule_denies(rule, n_rename_event(f, theta), n_rename_history(f, w))) by {
        lemma_numeric_genericity(rule, theta, w, f);
    }
}

} // verus!
