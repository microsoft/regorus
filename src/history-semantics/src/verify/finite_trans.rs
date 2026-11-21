//! Transition-level successor equations for the implementation (the
//! successor equations (S0)–(S6) of `finite_states::Model::contract`, for normalized transitions).
//!
//! A transition id `t` of a graph gets
//! - a *class* [`tcls`]: the literal and product values it may contribute (a single class
//!   suffices: for every non-sum node, the literal class and the product class coincide; an
//!   intersection's class is the `N(&·)` closure of its operands' classes, which covers merged
//!   leaves; a complement's class is the closure of the complemented operand class; a
//!   concatenation's class is `N(v s)` for the values `v` of its body's class);
//! - a *sum class* [`ycls`] bounding its value through conditionals and unions only (exact for
//!   conditional trees of leaves, used for the constant/test case (S1));
//! - its values [`tval`]: what `TransitionId::interpret` may return, with every normalized union,
//!   intersection, complement, and concatenation taken in the relations of `m_impl`;
//! - the normal form [`nf_sum`]: conditionals and unions over products, each an intersection of
//!   literals or a literal, a literal being a normal-form leaf, a complemented literal, or a
//!   concatenation of a product with normal-form suffixes.
//! The three relations are least fixpoints of one-step equations ([`lfp`]), unfolded by
//! [`lemma_tcls`], [`lemma_ycls`], [`lemma_tval`]. [`lemma_sum_sound`] shows that the values of
//! a normal-form transition are normalized unions of its class; [`lemma_succ_from_class`] turns
//! a class bound for the derivative of `p` into successors of `p` in `m_impl`.
use crate::verify::finite_impl::*;
use crate::verify::finite_link::*;
use crate::verify::finite_states::*;
use junco_core::kernel::verify as model;
use junco_core::verify::history_specs::Regex;
use vstd::prelude::*;

verus! {

pub open spec fn rconst(v: R) -> bool {
    v == Regex::<model::Test>::Empty || v == Regex::<model::Test>::Epsilon || v == Regex::<model::Test>::All
}

/// `⟨base⟩&` (`inter`) or `⟨base⟩+` in `m_impl`.
pub open spec fn cl(inter: bool, base: spec_fn(R) -> bool, v: R) -> bool {
    m_impl().built(inter, base, v)
}

/// `N(w s₁⋯sₙ)` for the lifted suffix ids `rs`.
pub open spec fn ccat(g: model::Graph, w: R, rs: Seq<nat>) -> R {
    r_cat(seq![w] + model::lift_regexes(g, rs))
}

// ===== least fixpoints =====

/// A relation between transition ids and trees.
pub type Rel = spec_fn(nat, R) -> bool;

pub open spec fn rel_le(a: Rel, b: Rel) -> bool {
    forall|t: nat, v: R| #[trigger] a(t, v) ==> b(t, v)
}

pub open spec fn step_mono(step: spec_fn(Rel, nat, R) -> bool) -> bool {
    forall|a: Rel, b: Rel, t: nat, v: R| #![trigger step(a, t, v), step(b, t, v)]
        rel_le(a, b) && step(a, t, v) ==> step(b, t, v)
}

pub open spec fn pre_closed(step: spec_fn(Rel, nat, R) -> bool, c: Rel) -> bool {
    forall|t: nat, v: R| #[trigger] step(c, t, v) ==> c(t, v)
}

pub open spec fn lfp(step: spec_fn(Rel, nat, R) -> bool, t: nat, v: R) -> bool {
    forall|c: Rel| #[trigger] pre_closed(step, c) ==> c(t, v)
}

pub open spec fn lfp_rel(step: spec_fn(Rel, nat, R) -> bool) -> Rel {
    |t: nat, v: R| lfp(step, t, v)
}

pub proof fn lemma_lfp_fold(step: spec_fn(Rel, nat, R) -> bool, t: nat, v: R)
    requires step_mono(step), step(lfp_rel(step), t, v),
    ensures lfp(step, t, v),
{
    assert forall|c: Rel| #[trigger] pre_closed(step, c) implies c(t, v) by {
        assert(rel_le(lfp_rel(step), c)) by {
            assert forall|x: nat, w: R| #[trigger] (lfp_rel(step))(x, w) implies c(x, w) by {
                assert(lfp(step, x, w));
            }
        }
        assert(step(c, t, v));
    }
}

pub proof fn lemma_lfp_unfold(step: spec_fn(Rel, nat, R) -> bool, t: nat, v: R)
    requires step_mono(step), lfp(step, t, v),
    ensures step(lfp_rel(step), t, v),
{
    let d: Rel = |x: nat, w: R| step(lfp_rel(step), x, w);
    assert(pre_closed(step, d)) by {
        assert forall|x: nat, w: R| #[trigger] step(d, x, w) implies d(x, w) by {
            assert(rel_le(d, lfp_rel(step))) by {
                assert forall|y: nat, u: R| #[trigger] d(y, u) implies (lfp_rel(step))(y, u) by {
                    lemma_lfp_fold(step, y, u);
                }
            }
        }
    }
}

// ===== the class =====

pub open spec fn kids(c: Rel, t: nat, cs: Seq<nat>, w: R) -> bool {
    exists|i: int| #![trigger cs[i]] 0 <= i < cs.len() && cs[i] < t && c(cs[i], w)
}

pub open spec fn negs(c: Rel, t: nat, k: nat, w: R) -> bool {
    exists|x: R| k < t && c(k, x) && w == #[trigger] r_not(x)
}

pub open spec fn apps(g: model::Graph, c: Rel, t: nat, k: nat, rs: Seq<nat>, v: R) -> bool {
    exists|w: R| k < t && c(k, w) && v == #[trigger] ccat(g, w, rs)
}

/// One step of the class equations.
pub open spec fn cls_step(g: model::Graph, c: Rel, t: nat, v: R) -> bool {
    if t >= g.transitions.len() { rconst(v) } else {
        match g.transitions[t as int] {
            model::TransitionNode::Const(r) => rconst(v) || v == model::lift_regex(g, r),
            model::TransitionNode::If(_, a, b) => (a < t && c(a, v)) || (b < t && c(b, v)),
            model::TransitionNode::Union(cs) => rconst(v) || kids(c, t, cs, v),
            model::TransitionNode::Intersect(cs) => cl(true, |w: R| kids(c, t, cs, w), v),
            model::TransitionNode::Not(k) => cl(true, |w: R| negs(c, t, k, w), v),
            model::TransitionNode::Append(k, rs) => rconst(v) || apps(g, c, t, k, rs, v),
        }
    }
}

pub open spec fn cls_steps(g: model::Graph) -> spec_fn(Rel, nat, R) -> bool {
    |c: Rel, t: nat, v: R| cls_step(g, c, t, v)
}

/// Class of a transition (see the module documentation).
pub open spec fn tcls(g: model::Graph, t: nat, v: R) -> bool {
    lfp(cls_steps(g), t, v)
}

pub open spec fn tc(g: model::Graph) -> Rel {
    lfp_rel(cls_steps(g))
}

/// One step of the sum-class equations.
pub open spec fn ycls_step(g: model::Graph, c: Rel, t: nat, v: R) -> bool {
    if t >= g.transitions.len() { true } else {
        match g.transitions[t as int] {
            model::TransitionNode::Const(r) => v == model::lift_regex(g, r),
            model::TransitionNode::If(_, a, b) => (a < t && c(a, v)) || (b < t && c(b, v)),
            model::TransitionNode::Union(cs) => cl(false, |w: R| kids(c, t, cs, w), v),
            _ => true,
        }
    }
}

pub open spec fn ycls_steps(g: model::Graph) -> spec_fn(Rel, nat, R) -> bool {
    |c: Rel, t: nat, v: R| ycls_step(g, c, t, v)
}

/// Sum class of a transition.
pub open spec fn ycls(g: model::Graph, t: nat, v: R) -> bool {
    lfp(ycls_steps(g), t, v)
}

pub open spec fn yc(g: model::Graph) -> Rel {
    lfp_rel(ycls_steps(g))
}

/// `vs` are values of the children `cs` (below `t`).
pub open spec fn kid_vals(c: Rel, t: nat, cs: Seq<nat>, vs: Seq<R>) -> bool {
    vs.len() == cs.len() && forall|i: int| #![trigger vs[i]] #![trigger cs[i]] 0 <= i < cs.len() ==> cs[i] < t && c(cs[i], vs[i])
}

/// One step of the value equations.
pub open spec fn val_step(g: model::Graph, c: Rel, t: nat, v: R) -> bool {
    if t >= g.transitions.len() { false } else {
        match g.transitions[t as int] {
            model::TransitionNode::Const(r) => v == model::lift_regex(g, r),
            model::TransitionNode::If(_, a, b) => (a < t && c(a, v)) || (b < t && c(b, v)),
            model::TransitionNode::Union(cs) =>
                exists|vs: Seq<R>| #[trigger] kid_vals(c, t, cs, vs) && (core().nset)(false, vs.to_set(), v),
            model::TransitionNode::Intersect(cs) =>
                exists|vs: Seq<R>| #[trigger] kid_vals(c, t, cs, vs) && (core().nset)(true, vs.to_set(), v),
            model::TransitionNode::Not(k) => negs(c, t, k, v),
            model::TransitionNode::Append(k, rs) => apps(g, c, t, k, rs, v),
        }
    }
}

pub open spec fn val_steps(g: model::Graph) -> spec_fn(Rel, nat, R) -> bool {
    |c: Rel, t: nat, v: R| val_step(g, c, t, v)
}

/// Values of a transition under some selection of the branches of its conditionals.
pub open spec fn tval(g: model::Graph, t: nat, v: R) -> bool {
    lfp(val_steps(g), t, v)
}

pub open spec fn tv(g: model::Graph) -> Rel {
    lfp_rel(val_steps(g))
}

// ----- monotonicity and unfolding -----

pub proof fn lemma_cl_mono(inter: bool, b1: spec_fn(R) -> bool, b2: spec_fn(R) -> bool, v: R)
    requires forall|w: R| #[trigger] b1(w) ==> b2(w), cl(inter, b1, v),
    ensures cl(inter, b2, v),
{
    lemma_built_mono(m_impl(), m_impl(), inter, b1, b2, v);
}

pub proof fn lemma_steps_mono(g: model::Graph)
    ensures step_mono(cls_steps(g)), step_mono(ycls_steps(g)), step_mono(val_steps(g)),
{
    assert forall|a: Rel, b: Rel, t: nat, v: R| #![trigger (cls_steps(g))(a, t, v), (cls_steps(g))(b, t, v)]
        rel_le(a, b) && (cls_steps(g))(a, t, v) implies (cls_steps(g))(b, t, v) by {
        if t < g.transitions.len() {
            match g.transitions[t as int] {
                model::TransitionNode::Union(cs) => {
                    if !rconst(v) {
                        let i = choose|i: int| #![trigger cs[i]] 0 <= i < cs.len() && cs[i] < t && a(cs[i], v);
                        assert(b(cs[i], v));
                    }
                },
                model::TransitionNode::Intersect(cs) => {
                    assert forall|w: R| #[trigger] kids(a, t, cs, w) implies kids(b, t, cs, w) by {
                        let i = choose|i: int| #![trigger cs[i]] 0 <= i < cs.len() && cs[i] < t && a(cs[i], w);
                        assert(b(cs[i], w));
                    }
                    lemma_cl_mono(true, |w: R| kids(a, t, cs, w), |w: R| kids(b, t, cs, w), v);
                },
                model::TransitionNode::Not(k) => {
                    assert forall|w: R| #[trigger] negs(a, t, k, w) implies negs(b, t, k, w) by {
                        let x = choose|x: R| k < t && a(k, x) && w == #[trigger] r_not(x);
                        assert(b(k, x));
                    }
                    lemma_cl_mono(true, |w: R| negs(a, t, k, w), |w: R| negs(b, t, k, w), v);
                },
                model::TransitionNode::Append(k, rs) => {
                    if !rconst(v) {
                        let w = choose|w: R| k < t && a(k, w) && v == #[trigger] ccat(g, w, rs);
                        assert(b(k, w));
                    }
                },
                _ => {},
            }
        }
    }
    assert forall|a: Rel, b: Rel, t: nat, v: R| #![trigger (ycls_steps(g))(a, t, v), (ycls_steps(g))(b, t, v)]
        rel_le(a, b) && (ycls_steps(g))(a, t, v) implies (ycls_steps(g))(b, t, v) by {
        if t < g.transitions.len() {
            match g.transitions[t as int] {
                model::TransitionNode::Union(cs) => {
                    assert forall|w: R| #[trigger] kids(a, t, cs, w) implies kids(b, t, cs, w) by {
                        let i = choose|i: int| #![trigger cs[i]] 0 <= i < cs.len() && cs[i] < t && a(cs[i], w);
                        assert(b(cs[i], w));
                    }
                    lemma_cl_mono(false, |w: R| kids(a, t, cs, w), |w: R| kids(b, t, cs, w), v);
                },
                _ => {},
            }
        }
    }
    assert forall|a: Rel, b: Rel, t: nat, v: R| #![trigger (val_steps(g))(a, t, v), (val_steps(g))(b, t, v)]
        rel_le(a, b) && (val_steps(g))(a, t, v) implies (val_steps(g))(b, t, v) by {
        if t < g.transitions.len() {
            match g.transitions[t as int] {
                model::TransitionNode::Union(cs) => {
                    let vs = choose|vs: Seq<R>| #[trigger] kid_vals(a, t, cs, vs) && (core().nset)(false, vs.to_set(), v);
                    assert(kid_vals(a, t, cs, vs));
                    assert forall|i: int| 0 <= i < cs.len() implies cs[i] < t && b(cs[i], #[trigger] vs[i]) by {
                        assert(cs[i] < t && a(cs[i], vs[i]));
                        assert(rel_le(a, b));
                    }
                    assert(kid_vals(b, t, cs, vs));
                },
                model::TransitionNode::Intersect(cs) => {
                    let vs = choose|vs: Seq<R>| #[trigger] kid_vals(a, t, cs, vs) && (core().nset)(true, vs.to_set(), v);
                    assert(kid_vals(a, t, cs, vs));
                    assert forall|i: int| 0 <= i < cs.len() implies cs[i] < t && b(cs[i], #[trigger] vs[i]) by {
                        assert(cs[i] < t && a(cs[i], vs[i]));
                        assert(rel_le(a, b));
                    }
                    assert(kid_vals(b, t, cs, vs));
                },
                model::TransitionNode::Not(k) => {
                    let x = choose|x: R| k < t && a(k, x) && v == #[trigger] r_not(x);
                    assert(b(k, x));
                },
                model::TransitionNode::Append(k, rs) => {
                    let w = choose|w: R| k < t && a(k, w) && v == #[trigger] ccat(g, w, rs);
                    assert(b(k, w));
                },
                _ => {},
            }
        }
    }
}

pub proof fn lemma_tcls(g: model::Graph, t: nat, v: R)
    ensures tcls(g, t, v) == cls_step(g, tc(g), t, v),
{
    lemma_steps_mono(g);
    if tcls(g, t, v) { lemma_lfp_unfold(cls_steps(g), t, v); }
    if cls_step(g, tc(g), t, v) { lemma_lfp_fold(cls_steps(g), t, v); }
}

pub proof fn lemma_ycls(g: model::Graph, t: nat, v: R)
    ensures ycls(g, t, v) == ycls_step(g, yc(g), t, v),
{
    lemma_steps_mono(g);
    if ycls(g, t, v) { lemma_lfp_unfold(ycls_steps(g), t, v); }
    if ycls_step(g, yc(g), t, v) { lemma_lfp_fold(ycls_steps(g), t, v); }
}

pub proof fn lemma_tval(g: model::Graph, t: nat, v: R)
    ensures tval(g, t, v) == val_step(g, tv(g), t, v),
{
    lemma_steps_mono(g);
    if tval(g, t, v) { lemma_lfp_unfold(val_steps(g), t, v); }
    if val_step(g, tv(g), t, v) { lemma_lfp_fold(val_steps(g), t, v); }
}

// ----- normal form -----

pub open spec fn nf_lit(g: model::Graph, t: nat) -> bool
    decreases t, 0nat,
{
    t < g.transitions.len() && match g.transitions[t as int] {
        model::TransitionNode::Const(r) => r < g.regexes.len() && regex_nf(model::lift_regex(g, r)),
        model::TransitionNode::Not(c) => c < t && nf_lit(g, c),
        model::TransitionNode::Append(c, rs) => c < t && nf_prod(g, c)
            && model::bounded(rs, g.regexes.len()) && nats_nf(g, rs),
        _ => false,
    }
}

pub open spec fn nf_prod(g: model::Graph, t: nat) -> bool
    decreases t, 1nat,
{
    t < g.transitions.len() && match g.transitions[t as int] {
        model::TransitionNode::Intersect(cs) => forall|i: int| 0 <= i < cs.len() ==> cs[i] < t && nf_lit(g, #[trigger] cs[i]),
        _ => nf_lit(g, t),
    }
}

pub open spec fn nf_sum(g: model::Graph, t: nat) -> bool
    decreases t, 2nat,
{
    t < g.transitions.len() && match g.transitions[t as int] {
        model::TransitionNode::If(_, a, b) => a < t && b < t && nf_sum(g, a) && nf_sum(g, b),
        model::TransitionNode::Union(cs) => forall|i: int| 0 <= i < cs.len() ==> cs[i] < t && nf_sum(g, #[trigger] cs[i]),
        _ => nf_prod(g, t),
    }
}

// ===== closures =====

pub proof fn lemma_cl_base(inter: bool, base: spec_fn(R) -> bool, v: R)
    requires base(v),
    ensures cl(inter, base, v),
{}

pub proof fn lemma_cl_const(inter: bool, base: spec_fn(R) -> bool, v: R)
    requires rconst(v),
    ensures cl(inter, base, v),
{}

/// `⟨⟨X⟩⟩ = ⟨X⟩`.
pub proof fn lemma_cl_idem(inter: bool, base: spec_fn(R) -> bool, v: R)
    requires cl(inter, |w: R| cl(inter, base, w), v),
    ensures cl(inter, base, v),
{
    let m = m_impl();
    assert forall|u: ISet<R>| m.has_consts(u) && (forall|w: R| #[trigger] base(w) ==> u.contains(w))
        && m.nset_closed(inter, u) implies #[trigger] u.contains(v) by {
        assert forall|w: R| #[trigger] cl(inter, base, w) implies u.contains(w) by {}
        assert(m.built(inter, |w: R| cl(inter, base, w), v));
    }
}

/// Normalized outputs of members of a closure are members.
pub proof fn lemma_cl_nset(inter: bool, base: spec_fn(R) -> bool, xs: Set<R>, v: R)
    requires forall|x: R| xs.contains(x) ==> cl(inter, base, x), (core().nset)(inter, xs, v),
    ensures cl(inter, base, v),
{
    let m = m_impl();
    lemma_models_agree();
    assert forall|u: ISet<R>| m.has_consts(u) && (forall|w: R| #[trigger] base(w) ==> u.contains(w))
        && m.nset_closed(inter, u) implies #[trigger] u.contains(v) by {
        assert forall|x: R| xs.contains(x) implies u.contains(x) by { assert(cl(inter, base, x)); }
        assert((m.nset)(inter, xs, v));
    }
}

/// Closures of normal forms consist of normal forms.
pub proof fn lemma_cl_nf(inter: bool, base: spec_fn(R) -> bool, v: R)
    requires forall|w: R| #[trigger] base(w) ==> regex_nf(w), cl(inter, base, v),
    ensures regex_nf(v),
{
    let m = m_impl();
    lemma_models_agree();
    let u = ISet::new(|w: R| regex_nf(w));
    assert(m.has_consts(u));
    assert forall|w: R| #[trigger] base(w) implies u.contains(w) by {}
    assert(m.nset_closed(inter, u)) by {
        assert forall|xs: Set<R>, w: R| (forall|x: R| xs.contains(x) ==> u.contains(x)) && #[trigger] (m.nset)(inter, xs, w)
            implies u.contains(w) by {
            assert(pre().nset_shape(inter, xs, w));
        }
    }
    assert(m.built(inter, base, v));
    assert(u.contains(v));
}

// ===== normal forms of values =====

pub proof fn lemma_not_nf(x: R)
    requires regex_nf(x),
    ensures regex_nf(r_not(x)),
{
    theorem_impl_contract();
    lemma_models_agree();
    assert(m_impl().not_shape(x));
}

pub proof fn lemma_cat_nf(xs: Seq<R>)
    requires forall|i: int| 0 <= i < xs.len() ==> regex_nf(#[trigger] xs[i]),
    ensures regex_nf(r_cat(xs)),
{
    theorem_impl_contract();
    lemma_models_agree();
    assert(m_impl().states(xs)) by {
        assert forall|i: int| 0 <= i < xs.len() implies m_impl().st(#[trigger] xs[i]) by {}
    }
    assert(m_impl().cat_shape(xs));
}

pub proof fn lemma_ccat_nf(g: model::Graph, w: R, rs: Seq<nat>)
    requires regex_nf(w), nats_nf(g, rs),
    ensures regex_nf(ccat(g, w, rs)),
{
    let s = seq![w] + model::lift_regexes(g, rs);
    assert forall|i: int| 0 <= i < s.len() implies regex_nf(#[trigger] s[i]) by {
        if i > 0 { assert(s[i] == model::lift_regex(g, rs[i - 1])); }
    }
    lemma_cat_nf(s);
}

/// Class members of a normal-form transition are normal forms.
pub proof fn lemma_tcls_nf(g: model::Graph, t: nat, v: R)
    requires nf_sum(g, t) || nf_prod(g, t) || nf_lit(g, t), tcls(g, t, v),
    ensures regex_nf(v),
    decreases t,
{
    lemma_tcls(g, t, v);
    match g.transitions[t as int] {
        model::TransitionNode::Const(r) => {},
        model::TransitionNode::If(_, a, b) => {
            if a < t && tcls(g, a, v) { lemma_tcls_nf(g, a, v); } else { lemma_tcls_nf(g, b, v); }
        },
        model::TransitionNode::Union(cs) => {
            if !rconst(v) {
                let i = choose|i: int| #![trigger cs[i]] 0 <= i < cs.len() && cs[i] < t && (tc(g))(cs[i], v);
                assert(nf_sum(g, cs[i]));
                lemma_tcls_nf(g, cs[i], v);
            }
        },
        model::TransitionNode::Intersect(cs) => {
            let base = |w: R| kids(tc(g), t, cs, w);
            assert forall|w: R| #[trigger] base(w) implies regex_nf(w) by {
                let i = choose|i: int| #![trigger cs[i]] 0 <= i < cs.len() && cs[i] < t && (tc(g))(cs[i], w);
                assert(nf_lit(g, cs[i]));
                lemma_tcls_nf(g, cs[i], w);
            }
            lemma_cl_nf(true, base, v);
        },
        model::TransitionNode::Not(c) => {
            let base = |w: R| negs(tc(g), t, c, w);
            assert forall|w: R| #[trigger] base(w) implies regex_nf(w) by {
                let x = choose|x: R| c < t && (tc(g))(c, x) && w == #[trigger] r_not(x);
                lemma_tcls_nf(g, c, x);
                lemma_not_nf(x);
            }
            lemma_cl_nf(true, base, v);
        },
        model::TransitionNode::Append(c, rs) => {
            if !rconst(v) {
                let w = choose|w: R| c < t && (tc(g))(c, w) && v == #[trigger] ccat(g, w, rs);
                lemma_tcls_nf(g, c, w);
                lemma_ccat_nf(g, w, rs);
            }
        },
    }
}

// ===== soundness of the classes =====

/// Values of literals and products are normal forms in their class.
pub proof fn lemma_prod_sound(g: model::Graph, t: nat, v: R)
    requires nf_prod(g, t), tval(g, t, v),
    ensures regex_nf(v), tcls(g, t, v),
    decreases t, 1nat,
{
    lemma_tval(g, t, v);
    lemma_tcls(g, t, v);
    match g.transitions[t as int] {
        model::TransitionNode::Intersect(cs) => {
            let vs = choose|vs: Seq<R>| #[trigger] kid_vals(tv(g), t, cs, vs) && (core().nset)(true, vs.to_set(), v);
            let base = |w: R| kids(tc(g), t, cs, w);
            assert forall|x: R| vs.to_set().contains(x) implies cl(true, base, x) by {
                broadcast use vstd::prelude::Seq::to_set_ensures;
                let i = choose|i: int| 0 <= i < vs.len() && vs[i] == x;
                assert(nf_lit(g, cs[i]));
                assert(tval(g, cs[i], vs[i]));
                lemma_lit_sound(g, cs[i], vs[i]);
                assert(base(x));
                lemma_cl_base(true, base, x);
            }
            lemma_cl_nset(true, base, vs.to_set(), v);
            lemma_models_agree();
            assert(pre().nset_shape(true, vs.to_set(), v));
        },
        _ => { lemma_lit_sound(g, t, v); },
    }
}

pub proof fn lemma_lit_sound(g: model::Graph, t: nat, v: R)
    requires nf_lit(g, t), tval(g, t, v),
    ensures regex_nf(v), tcls(g, t, v),
    decreases t, 0nat,
{
    lemma_tval(g, t, v);
    lemma_tcls(g, t, v);
    match g.transitions[t as int] {
        model::TransitionNode::Const(r) => {},
        model::TransitionNode::Not(c) => {
            let w = choose|w: R| c < t && (tv(g))(c, w) && v == #[trigger] r_not(w);
            lemma_lit_sound(g, c, w);
            lemma_not_nf(w);
            let base = |x: R| negs(tc(g), t, c, x);
            assert(base(v));
            lemma_cl_base(true, base, v);
        },
        model::TransitionNode::Append(c, rs) => {
            let w = choose|w: R| c < t && (tv(g))(c, w) && v == #[trigger] ccat(g, w, rs);
            lemma_prod_sound(g, c, w);
            lemma_ccat_nf(g, w, rs);
            assert(apps(g, tc(g), t, c, rs, v));
        },
        _ => {},
    }
}

/// Values of a normal-form transition are normalized unions of its class, and lie in its sum
/// class.
pub proof fn lemma_sum_sound(g: model::Graph, t: nat, v: R)
    requires nf_sum(g, t), tval(g, t, v),
    ensures regex_nf(v), cl(false, |w: R| tcls(g, t, w), v), ycls(g, t, v),
    decreases t, 2nat,
{
    lemma_tval(g, t, v);
    lemma_ycls(g, t, v);
    match g.transitions[t as int] {
        model::TransitionNode::If(_, a, b) => {
            let c = if a < t && tval(g, a, v) { a } else { b };
            lemma_sum_sound(g, c, v);
            assert forall|w: R| #[trigger] tcls(g, c, w) implies tcls(g, t, w) by { lemma_tcls(g, t, w); }
            lemma_cl_mono(false, |w: R| tcls(g, c, w), |w: R| tcls(g, t, w), v);
        },
        model::TransitionNode::Union(cs) => {
            let vs = choose|vs: Seq<R>| #[trigger] kid_vals(tv(g), t, cs, vs) && (core().nset)(false, vs.to_set(), v);
            let tb = |w: R| tcls(g, t, w);
            let yb = |w: R| kids(yc(g), t, cs, w);
            assert forall|x: R| vs.to_set().contains(x) implies cl(false, tb, x) && cl(false, yb, x) by {
                broadcast use vstd::prelude::Seq::to_set_ensures;
                let i = choose|i: int| 0 <= i < vs.len() && vs[i] == x;
                assert(nf_sum(g, cs[i]));
                assert(tval(g, cs[i], vs[i]));
                lemma_sum_sound(g, cs[i], vs[i]);
                assert forall|w: R| #[trigger] tcls(g, cs[i], w) implies tb(w) by {
                    lemma_tcls(g, t, w);
                    assert(kids(tc(g), t, cs, w));
                }
                lemma_cl_mono(false, |w: R| tcls(g, cs[i], w), tb, x);
                assert(ycls(g, cs[i], x));
                assert(yb(x));
                lemma_cl_base(false, yb, x);
            }
            lemma_cl_nset(false, tb, vs.to_set(), v);
            lemma_cl_nset(false, yb, vs.to_set(), v);
            lemma_models_agree();
            assert(pre().nset_shape(false, vs.to_set(), v));
        },
        _ => {
            lemma_prod_sound(g, t, v);
            lemma_cl_base(false, |w: R| tcls(g, t, w), v);
        },
    }
}

// ===== successors =====

/// The class bound of a derivative: the transition is a normal form whose class consists of
/// literals and products of `p`; for a constant or test `p`, its sum class consists of
/// constants.
pub open spec fn dclass(g: model::Graph, t: nat, p: R) -> bool {
    &&& nf_sum(g, t)
    &&& forall|w: R| #[trigger] tcls(g, t, w) ==> (m_impl().lit)(p, w) && (m_impl().prod)(p, w)
    &&& m_impl().base_kind(p) ==> forall|w: R| #[trigger] ycls(g, t, w) ==> rconst(w)
}

/// Every value of a transition with the class bound of `p` is a successor of `p` in `m_impl`.
pub proof fn lemma_succ_from_class(g: model::Graph, t: nat, p: R, v: R)
    requires regex_nf(p), dclass(g, t, p), tval(g, t, v),
    ensures (m_impl().succ)(p, v),
{
    lemma_sum_sound(g, t, v);
    lemma_models_agree();
    lemma_impl_gfp_shapes(p, v);
    if m_impl().base_kind(p) {
        assert(rconst(v));
        assert(m_impl().succ_shape(p, v));
    } else {
        lemma_cl_mono(false, |w: R| tcls(g, t, w), |w: R| (m_impl().prod)(p, w), v);
        assert(m_impl().succ_shape(p, v));
    }
    assert(g_succ(p, v));
}

// ===== stability under graph extension =====

pub open spec fn stable_at(a: model::Graph, b: model::Graph, t: nat) -> bool {
    &&& forall|v: R| #[trigger] tcls(a, t, v) == tcls(b, t, v)
    &&& forall|v: R| #[trigger] ycls(a, t, v) == ycls(b, t, v)
    &&& forall|v: R| #[trigger] tval(a, t, v) == tval(b, t, v)
    &&& nf_lit(a, t) == nf_lit(b, t) && nf_prod(a, t) == nf_prod(b, t) && nf_sum(a, t) == nf_sum(b, t)
}

/// Classes, values, and normal forms of existing transitions survive graph extension.
pub proof fn lemma_trans_stable(a: model::Graph, b: model::Graph, t: nat)
    requires model::graph_wf(a), model::graph_extends(a, b), t < a.transitions.len(),
    ensures stable_at(a, b, t),
    decreases t,
{
    model::lemma_graph_wf_elim(a);
    model::lemma_graph_transition_wf(a, t);
    assert(a.transitions[t as int] == b.transitions[t as int]) by {
        assert(a.transitions == b.transitions.subrange(0, a.transitions.len() as int));
    }
    let node = a.transitions[t as int];
    match node {
        model::TransitionNode::Const(r) => { model::lemma_lift_regex_stable(a, b, r); },
        model::TransitionNode::If(_, x, y) => { lemma_trans_stable(a, b, x); lemma_trans_stable(a, b, y); },
        model::TransitionNode::Union(cs) => {
            assert forall|i: int| 0 <= i < cs.len() implies #[trigger] stable_at(a, b, cs[i]) by {
                assert(cs[i] < t);
                lemma_trans_stable(a, b, cs[i]);
            }
        },
        model::TransitionNode::Intersect(cs) => {
            assert forall|i: int| 0 <= i < cs.len() implies #[trigger] stable_at(a, b, cs[i]) by {
                assert(cs[i] < t);
                lemma_trans_stable(a, b, cs[i]);
            }
        },
        model::TransitionNode::Not(k) => { lemma_trans_stable(a, b, k); },
        model::TransitionNode::Append(k, rs) => {
            lemma_trans_stable(a, b, k);
            assert forall|j: int| 0 <= j < rs.len() implies #[trigger] model::lift_regex(a, rs[j]) == model::lift_regex(b, rs[j]) by {
                model::lemma_lift_regex_stable(a, b, rs[j]);
            }
            assert(model::lift_regexes(a, rs) =~= model::lift_regexes(b, rs));
        },
    }
    assert(kids_stable(a, b, t)) by {
        match node {
            model::TransitionNode::Const(r) => {},
            model::TransitionNode::Union(cs) => {},
            model::TransitionNode::Intersect(cs) => {},
            model::TransitionNode::Append(k, rs) => {
                assert(model::bounded(rs, b.regexes.len())) by {
                    assert forall|j: int| 0 <= j < rs.len() implies #[trigger] rs[j] < b.regexes.len() by {}
                }
            },
            _ => {},
        }
    }
    lemma_tcls_stable_node(a, b, t);
    lemma_ycls_stable_node(a, b, t);
    lemma_tval_stable_node(a, b, t);
    lemma_nf_stable_node(a, b, t);
}

/// The children of `t` (in both graphs) are stable, and so are its leaf and suffixes.
pub open spec fn kids_stable(a: model::Graph, b: model::Graph, t: nat) -> bool {
    &&& t < a.transitions.len() && t < b.transitions.len() && a.transitions[t as int] == b.transitions[t as int]
    &&& match a.transitions[t as int] {
        model::TransitionNode::Const(r) => r < a.regexes.len() && r < b.regexes.len()
            && model::lift_regex(a, r) == model::lift_regex(b, r),
        model::TransitionNode::If(_, x, y) => x < t && y < t && stable_at(a, b, x) && stable_at(a, b, y),
        model::TransitionNode::Union(cs) => forall|i: int| 0 <= i < cs.len() ==> cs[i] < t && #[trigger] stable_at(a, b, cs[i]),
        model::TransitionNode::Intersect(cs) => forall|i: int| 0 <= i < cs.len() ==> cs[i] < t && #[trigger] stable_at(a, b, cs[i]),
        model::TransitionNode::Not(k) => k < t && stable_at(a, b, k),
        model::TransitionNode::Append(k, rs) => k < t && stable_at(a, b, k)
            && model::lift_regexes(a, rs) == model::lift_regexes(b, rs)
            && model::bounded(rs, a.regexes.len()) && model::bounded(rs, b.regexes.len()),
    }
}

pub proof fn lemma_tcls_stable_node(a: model::Graph, b: model::Graph, t: nat)
    requires kids_stable(a, b, t),
    ensures forall|v: R| #[trigger] tcls(a, t, v) == tcls(b, t, v),
{
    let node = a.transitions[t as int];
    assert forall|v: R| #[trigger] tcls(a, t, v) == tcls(b, t, v) by {
        lemma_tcls(a, t, v);
        lemma_tcls(b, t, v);
        match node {
            model::TransitionNode::Union(cs) => {
                if kids(tc(a), t, cs, v) {
                    let i = choose|i: int| #![trigger cs[i]] 0 <= i < cs.len() && cs[i] < t && (tc(a))(cs[i], v);
                    assert(stable_at(a, b, cs[i]));
                    assert(tcls(a, cs[i], v) == tcls(b, cs[i], v));
                }
                if kids(tc(b), t, cs, v) {
                    let i = choose|i: int| #![trigger cs[i]] 0 <= i < cs.len() && cs[i] < t && (tc(b))(cs[i], v);
                    assert(stable_at(a, b, cs[i]));
                    assert(tcls(a, cs[i], v) == tcls(b, cs[i], v));
                }
            },
            model::TransitionNode::Intersect(cs) => {
                assert forall|w: R| #[trigger] kids(tc(a), t, cs, w) == kids(tc(b), t, cs, w) by {
                    if kids(tc(a), t, cs, w) {
                        let i = choose|i: int| #![trigger cs[i]] 0 <= i < cs.len() && cs[i] < t && (tc(a))(cs[i], w);
                        assert(stable_at(a, b, cs[i]));
                        assert(tcls(a, cs[i], w) == tcls(b, cs[i], w));
                    }
                    if kids(tc(b), t, cs, w) {
                        let i = choose|i: int| #![trigger cs[i]] 0 <= i < cs.len() && cs[i] < t && (tc(b))(cs[i], w);
                        assert(stable_at(a, b, cs[i]));
                        assert(tcls(a, cs[i], w) == tcls(b, cs[i], w));
                    }
                }
                if cl(true, |w: R| kids(tc(a), t, cs, w), v) {
                    lemma_cl_mono(true, |w: R| kids(tc(a), t, cs, w), |w: R| kids(tc(b), t, cs, w), v);
                }
                if cl(true, |w: R| kids(tc(b), t, cs, w), v) {
                    lemma_cl_mono(true, |w: R| kids(tc(b), t, cs, w), |w: R| kids(tc(a), t, cs, w), v);
                }
            },
            model::TransitionNode::Not(k) => {
                assert forall|w: R| #[trigger] negs(tc(a), t, k, w) == negs(tc(b), t, k, w) by {
                    if negs(tc(a), t, k, w) {
                        let x = choose|x: R| k < t && (tc(a))(k, x) && w == #[trigger] r_not(x);
                        assert(tcls(a, k, x) == tcls(b, k, x));
                    }
                    if negs(tc(b), t, k, w) {
                        let x = choose|x: R| k < t && (tc(b))(k, x) && w == #[trigger] r_not(x);
                        assert(tcls(a, k, x) == tcls(b, k, x));
                    }
                }
                if cl(true, |w: R| negs(tc(a), t, k, w), v) {
                    lemma_cl_mono(true, |w: R| negs(tc(a), t, k, w), |w: R| negs(tc(b), t, k, w), v);
                }
                if cl(true, |w: R| negs(tc(b), t, k, w), v) {
                    lemma_cl_mono(true, |w: R| negs(tc(b), t, k, w), |w: R| negs(tc(a), t, k, w), v);
                }
            },
            model::TransitionNode::Append(k, rs) => {
                if apps(a, tc(a), t, k, rs, v) {
                    let w = choose|w: R| k < t && (tc(a))(k, w) && v == #[trigger] ccat(a, w, rs);
                    assert(tcls(a, k, w) == tcls(b, k, w));
                    assert(ccat(a, w, rs) == ccat(b, w, rs));
                }
                if apps(b, tc(b), t, k, rs, v) {
                    let w = choose|w: R| k < t && (tc(b))(k, w) && v == #[trigger] ccat(b, w, rs);
                    assert(tcls(a, k, w) == tcls(b, k, w));
                    assert(ccat(a, w, rs) == ccat(b, w, rs));
                }
            },
            model::TransitionNode::If(_, x, y) => {
                assert(tcls(a, x, v) == tcls(b, x, v));
                assert(tcls(a, y, v) == tcls(b, y, v));
            },
            _ => {},
        }
    }
}

pub proof fn lemma_ycls_stable_node(a: model::Graph, b: model::Graph, t: nat)
    requires kids_stable(a, b, t),
    ensures forall|v: R| #[trigger] ycls(a, t, v) == ycls(b, t, v),
{
    let node = a.transitions[t as int];
    assert forall|v: R| #[trigger] ycls(a, t, v) == ycls(b, t, v) by {
        lemma_ycls(a, t, v);
        lemma_ycls(b, t, v);
        match node {
            model::TransitionNode::Union(cs) => {
                assert forall|w: R| #[trigger] kids(yc(a), t, cs, w) == kids(yc(b), t, cs, w) by {
                    if kids(yc(a), t, cs, w) {
                        let i = choose|i: int| #![trigger cs[i]] 0 <= i < cs.len() && cs[i] < t && (yc(a))(cs[i], w);
                        assert(stable_at(a, b, cs[i]));
                        assert(ycls(a, cs[i], w) == ycls(b, cs[i], w));
                    }
                    if kids(yc(b), t, cs, w) {
                        let i = choose|i: int| #![trigger cs[i]] 0 <= i < cs.len() && cs[i] < t && (yc(b))(cs[i], w);
                        assert(stable_at(a, b, cs[i]));
                        assert(ycls(a, cs[i], w) == ycls(b, cs[i], w));
                    }
                }
                if cl(false, |w: R| kids(yc(a), t, cs, w), v) {
                    lemma_cl_mono(false, |w: R| kids(yc(a), t, cs, w), |w: R| kids(yc(b), t, cs, w), v);
                }
                if cl(false, |w: R| kids(yc(b), t, cs, w), v) {
                    lemma_cl_mono(false, |w: R| kids(yc(b), t, cs, w), |w: R| kids(yc(a), t, cs, w), v);
                }
            },
            model::TransitionNode::If(_, x, y) => {
                assert(ycls(a, x, v) == ycls(b, x, v));
                assert(ycls(a, y, v) == ycls(b, y, v));
            },
            _ => {},
        }
    }
}

pub proof fn lemma_tval_stable_node(a: model::Graph, b: model::Graph, t: nat)
    requires kids_stable(a, b, t),
    ensures forall|v: R| #[trigger] tval(a, t, v) == tval(b, t, v),
{
    let node = a.transitions[t as int];
    assert forall|v: R| #[trigger] tval(a, t, v) == tval(b, t, v) by {
        lemma_tval(a, t, v);
        lemma_tval(b, t, v);
        match node {
            model::TransitionNode::Union(cs) => { lemma_kid_vals_stable(a, b, t, cs, v, false); },
            model::TransitionNode::Intersect(cs) => { lemma_kid_vals_stable(a, b, t, cs, v, true); },
            model::TransitionNode::Not(k) => {
                if negs(tv(a), t, k, v) {
                    let x = choose|x: R| k < t && (tv(a))(k, x) && v == #[trigger] r_not(x);
                    assert(tval(a, k, x) == tval(b, k, x));
                }
                if negs(tv(b), t, k, v) {
                    let x = choose|x: R| k < t && (tv(b))(k, x) && v == #[trigger] r_not(x);
                    assert(tval(a, k, x) == tval(b, k, x));
                }
            },
            model::TransitionNode::Append(k, rs) => {
                if apps(a, tv(a), t, k, rs, v) {
                    let w = choose|w: R| k < t && (tv(a))(k, w) && v == #[trigger] ccat(a, w, rs);
                    assert(tval(a, k, w) == tval(b, k, w));
                    assert(ccat(a, w, rs) == ccat(b, w, rs));
                }
                if apps(b, tv(b), t, k, rs, v) {
                    let w = choose|w: R| k < t && (tv(b))(k, w) && v == #[trigger] ccat(b, w, rs);
                    assert(tval(a, k, w) == tval(b, k, w));
                    assert(ccat(a, w, rs) == ccat(b, w, rs));
                }
            },
            model::TransitionNode::If(_, x, y) => {
                assert(tval(a, x, v) == tval(b, x, v));
                assert(tval(a, y, v) == tval(b, y, v));
            },
            _ => {},
        }
    }
}

pub proof fn lemma_nf_stable_node(a: model::Graph, b: model::Graph, t: nat)
    requires kids_stable(a, b, t),
    ensures nf_lit(a, t) == nf_lit(b, t), nf_prod(a, t) == nf_prod(b, t), nf_sum(a, t) == nf_sum(b, t),
{
    let node = a.transitions[t as int];
    match node {
        model::TransitionNode::Const(r) => {},
        model::TransitionNode::Append(k, rs) => {
            assert(nats_nf(a, rs) == nats_nf(b, rs)) by {
                if nats_nf(a, rs) {
                    assert forall|j: int| 0 <= j < rs.len() implies regex_nf(#[trigger] model::lift_regex(b, rs[j])) by {
                        assert(model::lift_regexes(a, rs)[j] == model::lift_regex(a, rs[j]));
                        assert(model::lift_regexes(b, rs)[j] == model::lift_regex(b, rs[j]));
                    }
                }
                if nats_nf(b, rs) {
                    assert forall|j: int| 0 <= j < rs.len() implies regex_nf(#[trigger] model::lift_regex(a, rs[j])) by {
                        assert(model::lift_regexes(a, rs)[j] == model::lift_regex(a, rs[j]));
                        assert(model::lift_regexes(b, rs)[j] == model::lift_regex(b, rs[j]));
                    }
                }
            }
            assert(model::bounded(rs, a.regexes.len()));
        },
        model::TransitionNode::Union(cs) => {
            assert(nf_sum(a, t) == nf_sum(b, t)) by {
                if nf_sum(a, t) {
                    assert forall|i: int| 0 <= i < cs.len() implies cs[i] < t && nf_sum(b, #[trigger] cs[i]) by {
                        assert(stable_at(a, b, cs[i]));
                    }
                }
                if nf_sum(b, t) {
                    assert forall|i: int| 0 <= i < cs.len() implies cs[i] < t && nf_sum(a, #[trigger] cs[i]) by {
                        assert(stable_at(a, b, cs[i]));
                    }
                }
            }
        },
        model::TransitionNode::Intersect(cs) => {
            assert(nf_prod(a, t) == nf_prod(b, t)) by {
                if nf_prod(a, t) {
                    assert forall|i: int| 0 <= i < cs.len() implies cs[i] < t && nf_lit(b, #[trigger] cs[i]) by {
                        assert(stable_at(a, b, cs[i]));
                    }
                }
                if nf_prod(b, t) {
                    assert forall|i: int| 0 <= i < cs.len() implies cs[i] < t && nf_lit(a, #[trigger] cs[i]) by {
                        assert(stable_at(a, b, cs[i]));
                    }
                }
            }
        },
        _ => {},
    }
}

pub proof fn lemma_kid_vals_stable(a: model::Graph, b: model::Graph, t: nat, cs: Seq<nat>, v: R, inter: bool)
    requires forall|i: int| 0 <= i < cs.len() ==> #[trigger] stable_at(a, b, cs[i]),
    ensures (exists|vs: Seq<R>| #[trigger] kid_vals(tv(a), t, cs, vs) && (core().nset)(inter, vs.to_set(), v))
        == (exists|vs: Seq<R>| #[trigger] kid_vals(tv(b), t, cs, vs) && (core().nset)(inter, vs.to_set(), v)),
{
    assert forall|vs: Seq<R>| #[trigger] kid_vals(tv(a), t, cs, vs) == kid_vals(tv(b), t, cs, vs) by {
        if kid_vals(tv(a), t, cs, vs) {
            assert forall|i: int| #![trigger vs[i]] 0 <= i < cs.len() implies cs[i] < t && (tv(b))(cs[i], vs[i]) by {
                assert(stable_at(a, b, cs[i]));
                assert(tval(a, cs[i], vs[i]) == tval(b, cs[i], vs[i]));
            }
        }
        if kid_vals(tv(b), t, cs, vs) {
            assert forall|i: int| #![trigger vs[i]] 0 <= i < cs.len() implies cs[i] < t && (tv(a))(cs[i], vs[i]) by {
                assert(stable_at(a, b, cs[i]));
                assert(tval(a, cs[i], vs[i]) == tval(b, cs[i], vs[i]));
            }
        }
    }
    if exists|vs: Seq<R>| #[trigger] kid_vals(tv(a), t, cs, vs) && (core().nset)(inter, vs.to_set(), v) {
        let vs = choose|vs: Seq<R>| #[trigger] kid_vals(tv(a), t, cs, vs) && (core().nset)(inter, vs.to_set(), v);
        assert(kid_vals(tv(b), t, cs, vs));
    }
    if exists|vs: Seq<R>| #[trigger] kid_vals(tv(b), t, cs, vs) && (core().nset)(inter, vs.to_set(), v) {
        let vs = choose|vs: Seq<R>| #[trigger] kid_vals(tv(b), t, cs, vs) && (core().nset)(inter, vs.to_set(), v);
        assert(kid_vals(tv(a), t, cs, vs));
    }
}

} // verus!
