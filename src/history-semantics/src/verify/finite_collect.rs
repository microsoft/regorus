//! Classes of the outputs of `TransitionId::collect` (flattened unions and intersections of
//! transitions): the work lists of `TransitionMode::collect` hold members of the inputs
//! ([`collect_members`]), and the output's class is bounded by the union (intersection) of the
//! inputs' classes ([`collect_out`]).
use crate::normalize::verify as norm;
use crate::verify::finite_impl::*;
use crate::verify::finite_link::*;
use crate::verify::finite_machine::piece_of;
use crate::verify::finite_machine::*;
use crate::verify::finite_trans::*;
use junco_core::kernel::verify as model;
use junco_core::kernel::{RegexId, TransitionId};
use vstd::prelude::*;

verus! {

broadcast use junco_core::kernel::verify::group_kernel_views;

pub open spec fn tids(ids: Seq<TransitionId>) -> Seq<nat> {
    model::transition_ids(ids)
}

/// A flattened (non-constant) element: not a set of the connective's kind, and not a leaf of an
/// intersection (those are merged).
pub open spec fn flat_ok(g: model::Graph, inter: bool, x: nat) -> bool {
    x < g.transitions.len() && if inter {
        !(g.transitions[x as int] is Intersect) && !(g.transitions[x as int] is Const)
    } else {
        !(g.transitions[x as int] is Union)
    }
}

pub open spec fn const_piece(g: model::Graph, orig: Seq<nat>, inter: bool, r: nat) -> bool {
    exists|x: nat| #[trigger] piece_of(g, orig, inter, x) && x < g.transitions.len()
        && g.transitions[x as int] == model::TransitionNode::Const(r)
}

/// The work lists of `TransitionMode::collect` hold members of the inputs `orig`.
pub open spec fn collect_members(g: model::Graph, orig: Seq<nat>, inter: bool,
    pending: Seq<TransitionId>, flat: Seq<TransitionId>, constants: Seq<RegexId>) -> bool {
    &&& forall|k: int| #![trigger pending[k]] 0 <= k < pending.len() ==> piece_of(g, orig, inter, pending[k]@)
    &&& forall|k: int| #![trigger flat[k]] 0 <= k < flat.len() ==> piece_of(g, orig, inter, flat[k]@) && flat_ok(g, inter, flat[k]@)
    &&& forall|k: int| #![trigger constants[k]] 0 <= k < constants.len() ==> const_piece(g, orig, inter, constants[k]@)
    &&& !inter ==> constants.len() == 0
}

pub proof fn lemma_members_start(g: model::Graph, pending: Seq<TransitionId>, inter: bool)
    ensures collect_members(g, tids(pending), inter, pending, Seq::empty(), Seq::empty()),
{
    assert forall|k: int| 0 <= k < pending.len() implies #[trigger] piece_of(g, tids(pending), inter, pending[k]@) by {
        assert(tids(pending)[k] == pending[k]@);
        assert(tpiece(g, tids(pending)[k], inter, pending[k]@));
    }
}

pub proof fn lemma_members_pop(g: model::Graph, orig: Seq<nat>, inter: bool,
    prefix: Seq<TransitionId>, id: TransitionId, flat: Seq<TransitionId>, constants: Seq<RegexId>)
    requires collect_members(g, orig, inter, prefix.push(id), flat, constants),
    ensures collect_members(g, orig, inter, prefix, flat, constants), piece_of(g, orig, inter, id@),
{
    assert(prefix.push(id)[prefix.len() as int] == id);
    assert forall|k: int| 0 <= k < prefix.len() implies #[trigger] piece_of(g, orig, inter, prefix[k]@) by {
        assert(prefix.push(id)[k] == prefix[k]);
    }
}

pub proof fn lemma_members_expand(g: model::Graph, orig: Seq<nat>, inter: bool,
    prefix: Seq<TransitionId>, id: TransitionId, children: Seq<TransitionId>, flat: Seq<TransitionId>, constants: Seq<RegexId>,
    cs: Seq<nat>)
    requires model::graph_wf(g), model::bounded(orig, g.transitions.len()), id@ < g.transitions.len(),
        collect_members(g, orig, inter, prefix, flat, constants), piece_of(g, orig, inter, id@),
        g.transitions[id@ as int] == (if inter { model::TransitionNode::Intersect(cs) } else { model::TransitionNode::Union(cs) }),
        tids(children) == cs,
    ensures collect_members(g, orig, inter, prefix + children, flat, constants),
{
    let i = choose|i: int| #![trigger orig[i]] 0 <= i < orig.len() && tpiece(g, orig[i], inter, id@);
    assert forall|k: int| 0 <= k < (prefix + children).len() implies #[trigger] piece_of(g, orig, inter, (prefix + children)[k]@) by {
        if k < prefix.len() {
            assert((prefix + children)[k] == prefix[k]);
        } else {
            let j = k - prefix.len();
            assert((prefix + children)[k] == children[j]);
            assert(tids(children)[j] == children[j]@);
            lemma_tpiece_child(g, orig[i], inter, id@, cs, j);
        }
    }
}

pub proof fn lemma_members_const(g: model::Graph, orig: Seq<nat>, inter: bool,
    prefix: Seq<TransitionId>, id: TransitionId, flat: Seq<TransitionId>, constants: Seq<RegexId>, r: RegexId)
    requires inter, collect_members(g, orig, inter, prefix, flat, constants), piece_of(g, orig, inter, id@),
        id@ < g.transitions.len(), g.transitions[id@ as int] == model::TransitionNode::Const(r@),
    ensures collect_members(g, orig, inter, prefix, flat, constants.push(r)),
{
    assert forall|k: int| 0 <= k < constants.push(r).len() implies #[trigger] const_piece(g, orig, inter, constants.push(r)[k]@) by {
        if k < constants.len() { assert(constants.push(r)[k] == constants[k]); }
        else { assert(constants.push(r)[k] == r); assert(piece_of(g, orig, inter, id@)); }
    }
}

pub proof fn lemma_members_leaf(g: model::Graph, orig: Seq<nat>, inter: bool,
    prefix: Seq<TransitionId>, id: TransitionId, flat: Seq<TransitionId>, constants: Seq<RegexId>)
    requires collect_members(g, orig, inter, prefix, flat, constants), piece_of(g, orig, inter, id@), flat_ok(g, inter, id@),
    ensures collect_members(g, orig, inter, prefix, flat.push(id), constants),
{
    assert forall|k: int| 0 <= k < flat.push(id).len() implies #[trigger] piece_of(g, orig, inter, flat.push(id)[k]@)
        && flat_ok(g, inter, flat.push(id)[k]@) by {
        if k < flat.len() { assert(flat.push(id)[k] == flat[k]); }
    }
}

// ===== outputs =====

pub open spec fn all_nf(g: model::Graph, cs: Seq<nat>) -> bool {
    forall|k: int| 0 <= k < cs.len() ==> nf_sum(g, #[trigger] cs[k])
}

pub open spec fn all_prod(g: model::Graph, cs: Seq<nat>) -> bool {
    forall|k: int| 0 <= k < cs.len() ==> nf_prod(g, #[trigger] cs[k])
}

/// Class bound of an output of the collection of `cs`.
pub open spec fn cbound(g: model::Graph, cs: Seq<nat>, inter: bool, v: R) -> bool {
    if inter { cl(true, |w: R| any_x(avs(g, cs), w), v) } else { any_x(avs(g, cs), v) || rconst(v) }
}

/// An element allowed in the output of the collection of `cs`.
pub open spec fn elem_ok(g: model::Graph, cs: Seq<nat>, inter: bool, x: nat) -> bool {
    &&& x < g.transitions.len()
    &&& forall|v: R| #[trigger] tcls(g, x, v) ==> cbound(g, cs, inter, v)
    &&& !inter ==> forall|v: R| #[trigger] ycls(g, x, v) ==> cl(false, |w: R| any_y(avs(g, cs), w), v)
    &&& nf_sum(g, x)
    &&& inter && all_prod(g, cs) ==> nf_lit(g, x)
}

/// The output of the collection of normal-form `cs`: its class (and, for unions, its sum class)
/// is bounded by the inputs'; it is a normal form, except that an intersection of sums is an
/// intersection node whose children are allowed elements.
pub open spec fn collect_out(g: model::Graph, cs: Seq<nat>, inter: bool, out: nat) -> bool {
    &&& out < g.transitions.len()
    &&& forall|v: R| #[trigger] tcls(g, out, v) ==> cbound(g, cs, inter, v)
    &&& !inter ==> forall|v: R| #[trigger] ycls(g, out, v) ==> cl(false, |w: R| any_y(avs(g, cs), w), v)
    &&& !inter ==> nf_sum(g, out)
    &&& inter && all_prod(g, cs) ==> nf_prod(g, out)
    &&& inter ==> match g.transitions[out as int] {
        model::TransitionNode::Intersect(ds) => forall|j: int| 0 <= j < ds.len() ==> #[trigger] elem_ok(g, cs, inter, ds[j]),
        _ => nf_sum(g, out),
    }
}

/// An allowed element is an allowed output.
pub proof fn lemma_elem_out(g: model::Graph, cs: Seq<nat>, inter: bool, x: nat)
    requires elem_ok(g, cs, inter, x), inter ==> !(g.transitions[x as int] is Intersect),
    ensures collect_out(g, cs, inter, x),
{
    if inter && all_prod(g, cs) {
        assert(nf_lit(g, x));
        assert(nf_prod(g, x));
    }
}

/// Constant leaves are allowed elements.
pub proof fn lemma_const_elem(g: model::Graph, cs: Seq<nat>, inter: bool, x: nat, r: nat)
    requires model::graph_wf(g), x < g.transitions.len(), g.transitions[x as int] == model::TransitionNode::Const(r),
        r < g.regexes.len(), rconst(model::lift_regex(g, r)),
    ensures elem_ok(g, cs, inter, x),
{
    assert forall|v: R| #[trigger] tcls(g, x, v) implies cbound(g, cs, inter, v) by {
        lemma_tcls(g, x, v);
        if inter { lemma_cl_const(true, |w: R| any_x(avs(g, cs), w), v); }
    }
    assert forall|v: R| #[trigger] ycls(g, x, v) implies cl(false, |w: R| any_y(avs(g, cs), w), v) by {
        lemma_ycls(g, x, v);
        lemma_cl_const(false, |w: R| any_y(avs(g, cs), w), v);
    }
    assert(regex_nf(model::lift_regex(g, r)));
}

/// Members of normal-form inputs that are flattened elements are allowed elements in any
/// extension of the graph.
pub proof fn lemma_member_elem(g0: model::Graph, g: model::Graph, cs: Seq<nat>, inter: bool, x: nat)
    requires model::graph_wf(g0), model::graph_extends(g0, g), model::bounded(cs, g0.transitions.len()),
        all_nf(g0, cs), piece_of(g0, cs, inter, x), flat_ok(g0, inter, x),
    ensures elem_ok(g, cs, inter, x),
{
    let i = choose|i: int| #![trigger cs[i]] 0 <= i < cs.len() && tpiece(g0, cs[i], inter, x);
    lemma_tpiece_class(g0, cs[i], inter, x);
    lemma_trans_stable(g0, g, x);
    lemma_trans_stable(g0, g, cs[i]);
    lemma_avs_stable(g0, g, cs);
    assert(avs(g, cs)[i] == av_of(g, cs[i]));
    assert forall|v: R| #[trigger] tcls(g, x, v) implies cbound(g, cs, inter, v) by {
        assert(tcls(g0, x, v));
        assert(tcls(g0, cs[i], v));
        assert(tcls(g, cs[i], v));
        assert(any_x(avs(g, cs), v));
        if inter { lemma_cl_base(true, |w: R| any_x(avs(g, cs), w), v); }
    }
    if !inter {
        assert forall|v: R| #[trigger] ycls(g, x, v) implies cl(false, |w: R| any_y(avs(g, cs), w), v) by {
            assert(ycls(g0, x, v));
            assert(ycls(g0, cs[i], v));
            assert(ycls(g, cs[i], v));
            assert(any_y(avs(g, cs), v));
            lemma_cl_base(false, |w: R| any_y(avs(g, cs), w), v);
        }
    }
    assert(nf_sum(g0, cs[i]));
    if inter && all_prod(g, cs) {
        lemma_trans_stable(g0, g, cs[i]);
        assert(nf_prod(g, cs[i]));
        assert(nf_prod(g0, cs[i]));
        if x == cs[i] {
            assert(nf_lit(g0, x));
        }
    }
}

/// The regexes of constant members are normal forms in the class of the inputs.
pub proof fn lemma_const_piece(g0: model::Graph, cs: Seq<nat>, inter: bool, r: nat)
    requires model::graph_wf(g0), model::bounded(cs, g0.transitions.len()), all_nf(g0, cs), const_piece(g0, cs, inter, r),
    ensures r < g0.regexes.len(), regex_nf(model::lift_regex(g0, r)), any_x(avs(g0, cs), model::lift_regex(g0, r)),
{
    let x = choose|x: nat| #[trigger] piece_of(g0, cs, inter, x) && x < g0.transitions.len()
        && g0.transitions[x as int] == model::TransitionNode::Const(r);
    let i = choose|i: int| #![trigger cs[i]] 0 <= i < cs.len() && tpiece(g0, cs[i], inter, x);
    lemma_tpiece_class(g0, cs[i], inter, x);
    assert(nf_sum(g0, cs[i]));
    assert(nf_lit(g0, x));
    let v = model::lift_regex(g0, r);
    lemma_tcls(g0, x, v);
    assert(tcls(g0, cs[i], v));
    assert(avs(g0, cs)[i] == av_of(g0, cs[i]));
}

/// The merged leaf of an intersection is an allowed element.
pub proof fn lemma_leaf_elem(g0: model::Graph, g1: model::Graph, g: model::Graph, cs: Seq<nat>,
    constants: Seq<RegexId>, r: nat, t: nat)
    requires model::graph_wf(g0), model::graph_wf(g1), model::graph_wf(g), model::graph_extends(g0, g1), model::graph_extends(g1, g),
        model::bounded(cs, g0.transitions.len()), all_nf(g0, cs),
        forall|k: int| 0 <= k < constants.len() ==> #[trigger] const_piece(g0, cs, true, constants[k]@),
        norm::regex_ids_valid(g0, constants), r < g1.regexes.len(),
        norm::regex_set_flat_inputs(g0, constants, true) ==> norm::regex_set_shape(g0, g1, constants, true, r),
        t < g.transitions.len(), g.transitions[t as int] == model::TransitionNode::Const(r),
    ensures elem_ok(g, cs, true, t),
{
    assert(ids_nf(g0, constants)) by {
        assert forall|k: int| 0 <= k < constants.len() implies regex_nf(#[trigger] model::lift_regex(g0, constants[k]@)) by {
            lemma_const_piece(g0, cs, true, constants[k]@);
        }
    }
    lemma_flat_inputs(g0, constants, true);
    lemma_set_link(g0, g1, constants, true, r);
    model::lemma_graph_wf_elim(g1);
    model::lemma_lift_regex_stable(g1, g, r);
    lemma_avs_stable(g0, g, cs);
    let base = |w: R| any_x(avs(g, cs), w);
    assert forall|x: R| lift_set(g0, constants).contains(x) implies cl(true, base, x) by {
        broadcast use vstd::prelude::Seq::to_set_ensures;
        let k = choose|k: int| 0 <= k < lifts(g0, constants).len() && lifts(g0, constants)[k] == x;
        lemma_const_piece(g0, cs, true, constants[k]@);
        lemma_cl_base(true, base, x);
    }
    let m = model::lift_regex(g, r);
    lemma_cl_nset(true, base, lift_set(g0, constants), m);
    assert forall|v: R| #[trigger] tcls(g, t, v) implies cbound(g, cs, true, v) by {
        lemma_tcls(g, t, v);
        if rconst(v) { lemma_cl_const(true, base, v); }
    }
}

/// A union node of allowed elements is an allowed output.
pub proof fn lemma_union_node(g: model::Graph, cs: Seq<nat>, out: nat, flat: Seq<nat>)
    requires model::graph_wf(g), out < g.transitions.len(), g.transitions[out as int] == model::TransitionNode::Union(flat),
        forall|k: int| 0 <= k < flat.len() ==> #[trigger] elem_ok(g, cs, false, flat[k]),
    ensures collect_out(g, cs, false, out),
{
    model::lemma_graph_transition_wf(g, out);
    assert forall|v: R| #[trigger] tcls(g, out, v) implies cbound(g, cs, false, v) by {
        lemma_tcls(g, out, v);
        if !rconst(v) {
            let k = choose|k: int| #![trigger flat[k]] 0 <= k < flat.len() && flat[k] < out && (tc(g))(flat[k], v);
            assert(elem_ok(g, cs, false, flat[k]));
            assert(tcls(g, flat[k], v));
        }
    }
    let yb = |w: R| any_y(avs(g, cs), w);
    assert forall|v: R| #[trigger] ycls(g, out, v) implies cl(false, yb, v) by {
        lemma_ycls(g, out, v);
        assert forall|w: R| #[trigger] kids(yc(g), out, flat, w) implies cl(false, yb, w) by {
            let k = choose|k: int| #![trigger flat[k]] 0 <= k < flat.len() && flat[k] < out && (yc(g))(flat[k], w);
            assert(elem_ok(g, cs, false, flat[k]));
            assert(ycls(g, flat[k], w));
        }
        lemma_cl_mono(false, |w: R| kids(yc(g), out, flat, w), |w: R| cl(false, yb, w), v);
        lemma_cl_idem(false, yb, v);
    }
    assert forall|k: int| 0 <= k < flat.len() implies flat[k] < out && nf_sum(g, #[trigger] flat[k]) by {
        assert(elem_ok(g, cs, false, flat[k]));
    }
}

/// An intersection node of allowed elements is an allowed output.
pub proof fn lemma_inter_node(g: model::Graph, cs: Seq<nat>, out: nat, flat: Seq<nat>)
    requires model::graph_wf(g), out < g.transitions.len(), g.transitions[out as int] == model::TransitionNode::Intersect(flat),
        forall|k: int| 0 <= k < flat.len() ==> #[trigger] elem_ok(g, cs, true, flat[k]),
    ensures collect_out(g, cs, true, out),
{
    model::lemma_graph_transition_wf(g, out);
    let xb = |w: R| any_x(avs(g, cs), w);
    assert forall|v: R| #[trigger] tcls(g, out, v) implies cbound(g, cs, true, v) by {
        lemma_tcls(g, out, v);
        assert forall|w: R| #[trigger] kids(tc(g), out, flat, w) implies cl(true, xb, w) by {
            let k = choose|k: int| #![trigger flat[k]] 0 <= k < flat.len() && flat[k] < out && (tc(g))(flat[k], w);
            assert(elem_ok(g, cs, true, flat[k]));
            assert(tcls(g, flat[k], w));
        }
        lemma_cl_mono(true, |w: R| kids(tc(g), out, flat, w), |w: R| cl(true, xb, w), v);
        lemma_cl_idem(true, xb, v);
    }
    if all_prod(g, cs) {
        assert forall|k: int| 0 <= k < flat.len() implies flat[k] < out && nf_lit(g, #[trigger] flat[k]) by {
            assert(elem_ok(g, cs, true, flat[k]));
        }
    }
}

/// Allowed elements stay allowed in graph extensions.
pub proof fn lemma_elem_stable(g: model::Graph, h: model::Graph, cs: Seq<nat>, inter: bool, x: nat)
    requires model::graph_wf(g), model::graph_extends(g, h), model::bounded(cs, g.transitions.len()), elem_ok(g, cs, inter, x),
    ensures elem_ok(h, cs, inter, x), h.transitions[x as int] == g.transitions[x as int],
{
    lemma_trans_stable(g, h, x);
    lemma_avs_stable(g, h, cs);
    assert(h.transitions[x as int] == g.transitions[x as int]) by {
        assert(g.transitions == h.transitions.subrange(0, g.transitions.len() as int));
    }
    assert forall|v: R| #[trigger] tcls(h, x, v) implies cbound(h, cs, inter, v) by { assert(tcls(g, x, v)); }
    assert forall|v: R| #[trigger] ycls(h, x, v) && !inter implies cl(false, |w: R| any_y(avs(h, cs), w), v) by {
        assert(ycls(g, x, v));
    }
    if inter && all_prod(h, cs) {
        assert(all_prod(g, cs)) by {
            assert forall|k: int| 0 <= k < cs.len() implies nf_prod(g, #[trigger] cs[k]) by {
                lemma_trans_stable(g, h, cs[k]);
            }
        }
    }
}

/// An allowed element that is not an intersection node.
pub open spec fn elem_flat(g: model::Graph, cs: Seq<nat>, inter: bool, x: nat) -> bool {
    elem_ok(g, cs, inter, x) && (inter ==> !(g.transitions[x as int] is Intersect))
}

pub open spec fn set_tnode(inter: bool, ids: Seq<nat>) -> model::TransitionNode {
    if inter { model::TransitionNode::Intersect(ids) } else { model::TransitionNode::Union(ids) }
}

/// A set node interned later over allowed elements is an allowed output.
pub proof fn lemma_node_future(g: model::Graph, cs: Seq<nat>, inter: bool, ids: Seq<nat>)
    requires model::graph_wf(g), model::bounded(cs, g.transitions.len()),
        forall|k: int| 0 <= k < ids.len() ==> #[trigger] elem_flat(g, cs, inter, ids[k]),
    ensures forall|h: model::Graph, out: nat| model::graph_wf(h) && model::graph_extends(g, h) && out < h.transitions.len()
        && h.transitions[out as int] == set_tnode(inter, ids) ==> #[trigger] collect_out(h, cs, inter, out),
{
    assert forall|h: model::Graph, out: nat| model::graph_wf(h) && model::graph_extends(g, h) && out < h.transitions.len()
        && h.transitions[out as int] == set_tnode(inter, ids) implies #[trigger] collect_out(h, cs, inter, out) by {
        assert forall|k: int| 0 <= k < ids.len() implies #[trigger] elem_ok(h, cs, inter, ids[k]) by {
            assert(elem_flat(g, cs, inter, ids[k]));
            lemma_elem_stable(g, h, cs, inter, ids[k]);
        }
        if inter { lemma_inter_node(h, cs, out, ids); } else { lemma_union_node(h, cs, out, ids); }
    }
}

/// Allowed elements of a list stay allowed in graph extensions.
pub proof fn lemma_elems_stable(g: model::Graph, h: model::Graph, cs: Seq<nat>, inter: bool, ids: Seq<TransitionId>)
    requires model::graph_wf(g), model::graph_extends(g, h), model::bounded(cs, g.transitions.len()),
        forall|k: int| 0 <= k < ids.len() ==> #[trigger] elem_flat(g, cs, inter, ids[k]@),
    ensures forall|k: int| 0 <= k < ids.len() ==> #[trigger] elem_flat(h, cs, inter, ids[k]@),
{
    assert forall|k: int| 0 <= k < ids.len() implies #[trigger] elem_flat(h, cs, inter, ids[k]@) by {
        assert(elem_flat(g, cs, inter, ids[k]@));
        lemma_elem_stable(g, h, cs, inter, ids[k]@);
    }
}

/// The flattened members of `TransitionMode::collect` are allowed elements.
pub proof fn lemma_members_elems(g: model::Graph, cs: Seq<nat>, inter: bool, flat: Seq<TransitionId>, constants: Seq<RegexId>)
    requires model::graph_wf(g), model::bounded(cs, g.transitions.len()), all_nf(g, cs),
        collect_members(g, cs, inter, Seq::empty(), flat, constants),
    ensures forall|k: int| 0 <= k < flat.len() ==> #[trigger] elem_flat(g, cs, inter, flat[k]@),
{
    assert forall|k: int| 0 <= k < flat.len() implies #[trigger] elem_flat(g, cs, inter, flat[k]@) by {
        assert(piece_of(g, cs, inter, flat[k]@) && flat_ok(g, inter, flat[k]@));
        lemma_member_elem(g, g, cs, inter, flat[k]@);
    }
}

/// The constant transitions are allowed outputs.
pub proof fn lemma_const_out(g: model::Graph, cs: Seq<nat>, inter: bool, x: nat)
    requires model::graph_wf(g),
        x == g.constants.transition_empty || x == g.constants.transition_all || x == g.constants.transition_epsilon,
    ensures collect_out(g, cs, inter, x), elem_flat(g, cs, inter, x),
{
    model::lemma_graph_wf_elim(g);
    crate::normalize::verify::regex_constants(g);
    let c = g.constants;
    let r = if x == c.transition_empty { c.empty } else if x == c.transition_all { c.all } else { c.epsilon };
    assert(g.transitions[x as int] == model::TransitionNode::Const(r));
    lemma_const_elem(g, cs, inter, x, r);
    lemma_elem_out(g, cs, inter, x);
}

} // verus!
