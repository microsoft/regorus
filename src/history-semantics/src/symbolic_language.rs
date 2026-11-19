//! A compiled tail stepped by classes of events instead of events.
//!
//! The runtime steps a residual by one event in three parts: it derives the residual
//! symbolically, evaluates the derivative's atoms on the event under the rule's bindings, and
//! interprets the derivative under those truth values. [`SymbolicLanguage`] exposes the first and
//! last parts, so a caller that knows only which atoms hold, such as a static analysis over
//! classes of events, follows exactly the runtime's derivatives and successors. It also reads the
//! nodes of residuals and their tests, so such a caller can compare residuals by the shape of their
//! normal forms.
//!
//! The facade's contracts retain the runtime's language equivalences and graph-class bounds.
//! It preserves the shared precondition, a well-formed compiled pair, by owning the pair and
//! rejecting identifiers that do not belong to its graph. Read callbacks receive the exact node
//! view without changing the pair.
//! Error guarantees are conditional on graph membership for reads and derivatives, and on a
//! cached atom set with a correctly sized, zero-padded truth assignment for successors.

use alloc::vec::Vec;
use history_store::cache::EventClass;
use history_store::graph::RuntimeKernel;
use junco_core::errors::HistoryError;
use junco_core::flat::FlatPair;
use junco_core::kernel::{
    KernelStore, Primitive, RegexId, RegexView, TestId, TestView, TransitionId,
};
use junco_core::limits::Unmetered;
use junco_core::observation::ObservationWorld;
#[cfg(verus_keep_ghost)]
use junco_core::spec::semantics::resource_error;
use smallvec::SmallVec;

#[cfg(verus_keep_ghost)]
use crate::compile::verify as numeric;
#[cfg(verus_keep_ghost)]
use crate::normalize::verify as norm;
use crate::progress::CompiledPair;
#[cfg(verus_keep_ghost)]
use crate::progress::verify as reach;
use crate::symbolic::RegexDerivative;
#[cfg(verus_keep_ghost)]
use crate::symbolic::verify as symbolic;
#[cfg(verus_keep_ghost)]
use crate::verify::{finite_deriv as fder, finite_impl, finite_interp as fint};
#[cfg(verus_keep_ghost)]
use history_store::cache::verify::*;
#[cfg(verus_keep_ghost)]
use junco_core::kernel::verify as model;
#[cfg(verus_keep_ghost)]
use junco_core::observation::SmallVecSpecFns;
#[cfg(verus_keep_ghost)]
use junco_core::verify::history_assumptions::*;
#[cfg(verus_keep_ghost)]
use junco_core::verify::history_specs::{self as language, EventView, Regex, Subst};
#[cfg(verus_keep_ghost)]
use verify::*;
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
verus! {
broadcast use junco_core::kernel::verify::group_kernel_views;
}

/// A compiled tail whose residuals are stepped by classes of events.
///
/// A class is given by the truth values of the positive atoms that a residual's derivative
/// tests: every event with those truth values has the same successor, under any bindings that
/// realize them. Residuals are canonical within one language, so equal identifiers denote equal
/// normal forms.
///
/// The graph may be charged the budget given at compilation; an operation that would exceed it
/// fails with [`HistoryError::GraphBudget`]. The runtime's budget is
/// [`junco_core::limits::MAX_GRAPH_BYTES`] per compiled rule.
#[verus_verify]
#[verus_verify(external_derive)]
#[derive(Debug)]
pub struct SymbolicLanguage {
    pub(crate) pair: CompiledPair,
}

#[verus_verify]
impl SymbolicLanguage {
    /// Compiles a numeric tail into a fresh graph, as the runtime does, that may be charged
    /// `budget` bytes. Each of the graph's six arenas reserves `budget` bytes of address space,
    /// which is committed as it fills. `budget` must be a multiple of 16.
    /// With a layout-valid arena budget, a source with in-range backward references and a valid
    /// root cannot fail internally; this does not require a binding head for symbolic variables.
    #[verus_verify]
    #[verus_spec(result => ensures
        numeric::source_dag_wf(*template) && compile_budget_valid(budget)
            ==> language::no_invariant_failure(result),
        numeric::source_dag_wf(*template) && compile_budget_valid(budget)
            ==> (result matches Err(error) ==> resource_error(error)),
        result matches Ok(l) ==> language_wf(l)
        && finite_impl::regex_nf(model::lift_regex(graph(l), root(l)))
        && symbolic::regex_primitives(model::lift_regex(graph(l), root(l))).subset_of(numeric::source_primitives(*template))
        && forall|theta: Subst, word: Seq<EventView>| language::event_wf(theta, theta.len())
            ==> model::regex_lang(graph(l), theta, root(l), word)
                == numeric::source_regex(*template, template.root as nat, theta, word))]
    pub fn compile(template: &FlatPair<u64>, budget: usize) -> Result<Self, HistoryError> {
        proof! { reveal(language_wf); reveal(graph); reveal(root); }
        let pair = CompiledPair::compile(template, budget, &mut Unmetered, &mut ObservationWorld)?;
        Ok(Self { pair })
    }

    /// The residual of the empty history: the tail itself.
    #[verus_verify]
    #[verus_spec(result => requires language_wf(*self),
        ensures result@ == root(*self), result@ < graph(*self).regexes.len())]
    pub fn root(&self) -> RegexId {
        proof! { reveal(language_wf); reveal(graph); reveal(root); }
        self.pair.root
    }

    /// Whether `residual` is the canonical empty language. A residual whose language is empty
    /// need not be.
    #[verus_verify]
    #[verus_spec(result => requires language_wf(*self),
        ensures result ==> abs(*self, residual) == Regex::Empty)]
    pub fn is_empty(&self, residual: RegexId) -> bool {
        proof! { reveal(language_wf); reveal(graph); norm::regex_constants(graph(*self)); }
        residual == self.pair.store.constants().empty
    }

    /// Whether `residual` accepts the empty history.
    #[verus_verify]
    #[verus_spec(result => requires language_wf(*old(self)),
        ensures *final(self) == *old(self),
            residual@ < graph(*old(self)).regexes.len() ==> language::no_invariant_failure(result),
            residual@ < graph(*old(self)).regexes.len()
                ==> (result matches Err(error) ==> resource_error(error)),
            result matches Ok(value) ==> residual@ < graph(*final(self)).regexes.len()
                && value == language::nullable(abs(*final(self), residual)))]
    pub fn nullable(&mut self, residual: RegexId) -> Result<bool, HistoryError> {
        self.read_regex(
            residual,
            verus_exec_expr! {
                |node: RegexView<'_>| -> (value: bool)
                    ensures value == node.nullable,
                { node.nullable }
            },
        )
    }

    /// Reads the node of `residual`: its kind with its children, and its nullability. Unions and
    /// intersections list their children in increasing identifier order.
    #[verus_verify]
    #[verus_spec(result => requires language_wf(*old(self)),
        forall|view: RegexView<'_>| residual@ < graph(*old(self)).regexes.len()
            && view@ == graph(*old(self)).regexes[residual@ as int]
            ==> call_requires(read, (view,)),
        ensures *final(self) == *old(self),
            residual@ < graph(*old(self)).regexes.len() ==> language::no_invariant_failure(result),
            residual@ < graph(*old(self)).regexes.len()
                ==> (result matches Err(error) ==> resource_error(error)),
            result matches Ok(value) ==> exists|view: RegexView<'_>|
                residual@ < graph(*final(self)).regexes.len()
                && view@ == graph(*final(self)).regexes[residual@ as int]
                && abs(*final(self), residual) == model::lift_regex_kind(graph(*final(self)), view@.kind)
                && view.nullable == language::nullable(abs(*final(self), residual))
                && call_ensures(read, (view,), value))]
    pub fn read_regex<R>(
        &mut self,
        residual: RegexId,
        read: impl FnOnce(RegexView<'_>) -> R,
    ) -> Result<R, HistoryError> {
        proof! { reveal(language_wf); reveal(graph); }
        let (mut limits, mut world) = (Unmetered, ObservationWorld);
        let kernel = RuntimeKernel {
            store: &mut self.pair.store,
            limits: &mut limits,
            world: &mut world,
        };
        let view = kernel.regex(residual)?;
        proof! { norm::regex_unfold(kernel.graph(), residual@); }
        Ok(read(view))
    }

    /// Reads the node of `test`: an atom, a constant, or the conjunction or disjunction of its
    /// children, which are listed in increasing identifier order.
    #[verus_verify]
    #[verus_spec(result => requires language_wf(*old(self)),
        forall|view: TestView<'_>| test@ < graph(*old(self)).tests.len()
            && view@ == graph(*old(self)).tests[test@ as int] ==> call_requires(read, (view,)),
        ensures *final(self) == *old(self),
            test@ < graph(*old(self)).tests.len() ==> language::no_invariant_failure(result),
            test@ < graph(*old(self)).tests.len()
                ==> (result matches Err(error) ==> resource_error(error)),
            result matches Ok(value) ==> exists|view: TestView<'_>|
                test@ < graph(*final(self)).tests.len()
                && view@ == graph(*final(self)).tests[test@ as int]
                && call_ensures(read, (view,), value))]
    pub fn read_test<R>(
        &mut self,
        test: TestId,
        read: impl FnOnce(TestView<'_>) -> R,
    ) -> Result<R, HistoryError> {
        proof! { reveal(language_wf); reveal(graph); }
        let (mut limits, mut world) = (Unmetered, ObservationWorld);
        let kernel = RuntimeKernel {
            store: &mut self.pair.store,
            limits: &mut limits,
            world: &mut world,
        };
        Ok(read(kernel.test(test)?))
    }

    /// The derivative of `residual`, with the primitives of the positive atoms it tests in the
    /// order of the truth bits that [`SymbolicLanguage::successor`] takes.
    #[verus_verify]
    #[verus_spec(result => requires language_wf(*old(self)),
        ensures language_wf(*final(self)), frame(*old(self), *final(self)),
            residual@ < graph(*old(self)).regexes.len() ==> language::no_invariant_failure(result),
            residual@ < graph(*old(self)).regexes.len()
                ==> (result matches Err(error) ==> resource_error(error)),
            forall|i: int| 0 <= i < derivatives(*old(self)).len() && derivatives(*old(self))[i] is Some
                ==> i < derivatives(*final(self)).len() && derivatives(*final(self))[i] == derivatives(*old(self))[i],
            forall|t: TransitionId| has_atoms(*old(self), t) ==> has_atoms(*final(self), t)
                && atom_ids(*final(self), t) == atom_ids(*old(self), t),
            result matches Ok((t, prims)) ==> residual@ < graph(*old(self)).regexes.len()
                && symbolic::derivative_correct(graph(*final(self)), residual@, t)
                && fder::dbound(graph(*final(self)), residual@, t@)
                && has_atoms(*final(self), t)
                && reach::atoms_wf(graph(*final(self)), t@, atom_ids(*final(self), t))
                && residual@ < derivatives(*final(self)).len()
                && derivatives(*final(self))[residual@ as int] == Some(t)
                && prims@.len() == atom_ids(*final(self), t).len()
                && prims@.len() <= u32::MAX as nat + 1
                && prims@.len() + 63 <= usize::MAX
                && crate::verify::refinement::search::atoms_complete(abs(*final(self), residual), atom_primitives(*final(self), t))
                && atom_primitives(*final(self), t) == prims@.map_values(|p: Primitive| p@).to_set()
                && atom_primitives(*final(self), t).subset_of(residual_primitives(*final(self), residual))
                && forall|i: int| 0 <= i < prims@.len()
                    ==> model::lift_test(graph(*final(self)), atom_ids(*final(self), t)[i]@)
                        == model::Test::Atom(prims@[i]@, true))]
    pub fn derive(
        &mut self,
        residual: RegexId,
    ) -> Result<(TransitionId, Vec<Primitive>), HistoryError> {
        proof! { reveal(language_wf); reveal(graph); reveal(root); reveal(has_atoms); reveal(atom_ids); reveal(derivatives); }
        proof! { self.pair.store.lemma_node_count_bounds(); }
        proof_decl! { let ghost entry = self.pair; }
        let (mut limits, mut world) = (Unmetered, ObservationWorld);
        let transition = {
            let mut kernel = RuntimeKernel {
                store: &mut self.pair.store,
                limits: &mut limits,
                world: &mut world,
            };
            kernel.regex(residual)?;
            let result =
                RegexId::derivative(residual, &mut kernel, &mut self.pair.caches.derivatives);
            proof! {
                reveal(frame);
                reach::lemma_pair_symbolic_frame(entry, self.pair);
                assert forall|i: int| 0 <= i < entry.caches.derivatives@.len()
                    && entry.caches.derivatives@[i] is Some implies
                    i < self.pair.caches.derivatives@.len()
                    && self.pair.caches.derivatives@[i] == entry.caches.derivatives@[i] by {}
            }
            result?
        };
        proof_decl! { let ghost derived = self.pair.store.graph(); }
        self.pair
            .ensure_atoms(transition, &mut limits, &mut world)?;
        proof! {
            symbolic::derivative_correct_stable(derived, self.pair.store.graph(), residual@, transition);
            fder::lemma_dbound_stable(derived, self.pair.store.graph(), residual@, transition@);
            symbolic::derivative_extends(entry.store.graph(), self.pair.store.graph());
        }
        proof_decl! { let ghost collected = self.pair; }
        let atoms = CompiledPair::cached_atoms(self.pair.caches.atoms.as_slice(), transition)?;
        let kernel = RuntimeKernel {
            store: &mut self.pair.store,
            limits: &mut limits,
            world: &mut world,
        };
        let mut primitives: Vec<Primitive> = Vec::with_capacity(atoms.ids().len());
        let ids = atoms.ids();
        let mut index = 0;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant index <= ids@.len(), primitives@.len() == index,
                reach::pair_wf(collected), reach::pair_frame(entry, collected),
                residual@ < entry.store.graph().regexes.len(),
                reach::has_atoms(collected, transition),
                self.pair.caches == collected.caches, self.pair.root == collected.root,
                *kernel.store == collected.store,
                ids@ == collected.caches.atoms@[transition@ as int].unwrap()@,
                kernel.graph() == collected.store.graph(),
                reach::atoms_wf(kernel.graph(), transition@, ids@),
                symbolic::derivative_correct(kernel.graph(), residual@, transition),
                fder::dbound(kernel.graph(), residual@, transition@),
                forall|i: int| 0 <= i < primitives@.len()
                    ==> model::lift_test(kernel.graph(), ids@[i]@) == model::Test::Atom(primitives@[i]@, true),
            decreases ids@.len() - index,
        ))]
        while index < ids.len() {
            let id = ids[index];
            match kernel.test(id)? {
                TestView::Atom {
                    primitive,
                    positive: true,
                } => primitives.push(primitive),
                _ => return Err(HistoryError::invalid_atom_set()),
            }
            index += 1;
        }
        proof! {
            self.pair.store.lemma_node_count_bounds();
            reach::lemma_atom_count_bound(graph(*self), ids@);
            assert forall|i: int| 0 <= i < primitives@.len() implies
                graph(*self).tests[ids@[i]@ as int] == model::TestNode::Atom(primitives@[i]@, true) by {
                reveal_with_fuel(model::lift_test, 1);
            }
            assert(atom_ids(*self, transition).map_values(|id: TestId| match graph(*self).tests[id@ as int] {
                model::TestNode::Atom(p, _) => p,
                _ => model::Primitive::Eq(history_syntax::Component(0), model::GTerm::Constant(0)),
            }) =~= primitives@.map_values(|p: Primitive| p@));
            lemma_atoms_complete(*self, residual, transition);
            lemma_atoms_vocabulary(*self, residual, transition);
        }
        Ok((transition, primitives))
    }

    /// The residual after one event of the class whose atom truths are `truth`: bit `i % 64` of
    /// word `i / 64` is the truth of atom `i` of [`SymbolicLanguage::derive`]'s list.
    #[verus_verify]
    #[verus_spec(result => requires language_wf(*old(self)),
        ensures language_wf(*final(self)), frame(*old(self), *final(self)),
            has_atoms(*old(self), transition)
                && symbolic::assignment_valid(atom_ids(*old(self), transition).len(), truth@)
                ==> language::no_invariant_failure(result),
            has_atoms(*old(self), transition)
                && symbolic::assignment_valid(atom_ids(*old(self), transition).len(), truth@)
                ==> (result matches Err(error) ==> resource_error(error)),
            derivatives(*final(self)) == derivatives(*old(self)),
            forall|t: TransitionId| has_atoms(*old(self), t) ==> has_atoms(*final(self), t)
                && atom_ids(*final(self), t) == atom_ids(*old(self), t),
            has_atoms(*old(self), transition) ==> atom_ids(*final(self), transition) == atom_ids(*old(self), transition),
            result matches Ok(v) ==> has_atoms(*final(self), transition)
                && v@ < graph(*final(self)).regexes.len()
                && fint::entry_val(graph(*final(self)), transition@, v@)
                && successors(*final(self)).contains_key(ClassKey { transition, words: truth@ })
                && successors(*final(self))[ClassKey { transition, words: truth@ }] == v
                && forall|theta: Subst, e: EventView, w: Seq<EventView>|
                    language::event_wf(theta, theta.len())
                    && symbolic::truth_words_realize(graph(*final(self)), atom_ids(*final(self), transition), truth@, theta, e)
                    ==> model::regex_lang(graph(*final(self)), theta, v@, w)
                        == norm::transition_lang(graph(*final(self)), theta, transition, e, w))]
    pub fn successor(
        &mut self,
        transition: TransitionId,
        truth: &[u64],
    ) -> Result<RegexId, HistoryError> {
        proof! { reveal(language_wf); reveal(graph); reveal(root); reveal(has_atoms); reveal(atom_ids); reveal(successors); reveal(derivatives); }
        proof_decl! { let ghost entry = self.pair; }
        let (mut limits, mut world) = (Unmetered, ObservationWorld);
        {
            let kernel = RuntimeKernel {
                store: &mut self.pair.store,
                limits: &mut limits,
                world: &mut world,
            };
            kernel.transition(transition)?;
        }
        self.pair
            .ensure_atoms(transition, &mut limits, &mut world)?;
        let mut words = SmallVec::new();
        words.extend_from_slice(truth);
        let key = EventClass { transition, words };
        let result = self.pair.successor(key, &mut limits, &mut world);
        proof! { symbolic::derivative_extends(entry.store.graph(), self.pair.store.graph()); }
        result
    }
}

#[cfg(verus_keep_ghost)]
pub mod verify {
    use super::*;
    pub use crate::progress::verify::{lemma_assignment_set, lemma_zero_truth_words};
    use crate::verify::refinement::encoding as enc;
    use history_syntax::Component;

    verus! {
    broadcast use junco_core::kernel::verify::group_kernel_views;

    /// Exact arena layout readiness, retaining the runtime's established default budget case.
    pub open spec fn compile_budget_valid(budget: usize) -> bool {
        budget == junco_core::limits::MAX_GRAPH_BYTES
            || history_store::graph::verify::construction_layout(budget)
    }

    #[cfg(target_pointer_width = "64")]
    pub proof fn lemma_aligned_compile_budget(budget: usize)
        requires budget as int % 16 == 0,
        ensures compile_budget_valid(budget),
    {
        history_store::graph::verify::lemma_aligned_budget_layout(budget);
    }

    pub open(crate) spec fn language_wf(l: SymbolicLanguage) -> bool { reach::pair_wf(l.pair) }
    pub open(crate) spec fn graph(l: SymbolicLanguage) -> model::Graph { l.pair.store.graph() }
    pub open(crate) spec fn root(l: SymbolicLanguage) -> nat { l.pair.root@ }
    pub open spec fn abs(l: SymbolicLanguage, id: RegexId) -> Regex<model::Test> {
        model::lift_regex(graph(l), id@)
    }
    pub open(crate) spec fn atom_ids(l: SymbolicLanguage, t: TransitionId) -> Seq<TestId> {
        l.pair.caches.atoms@[t@ as int].unwrap()@
    }
    pub open(crate) spec fn has_atoms(l: SymbolicLanguage, t: TransitionId) -> bool {
        reach::has_atoms(l.pair, t)
    }
    pub open(crate) spec fn derivatives(l: SymbolicLanguage) -> Seq<Option<TransitionId>> {
        l.pair.caches.derivatives@
    }
    pub open(crate) spec fn successors(l: SymbolicLanguage) -> Map<ClassKey, RegexId> {
        successor_entries(l.pair.caches.successors)
    }
    pub open spec fn frame(a: SymbolicLanguage, b: SymbolicLanguage) -> bool {
        model::graph_extends(graph(a), graph(b)) && root(a) == root(b)
    }

    pub open spec fn residual_primitives(l: SymbolicLanguage, q: RegexId) -> Set<model::Primitive> {
        symbolic::regex_primitives(abs(l, q))
    }

    /// Primitive payloads that the analyzer can represent without an invariant error.
    pub open spec fn primitives_search_safe(ps: Set<model::Primitive>) -> bool {
        forall|p: model::Primitive| #[trigger] ps.contains(p) ==> match p {
            model::Primitive::Eq(_, model::GTerm::Constant(code)) => code <= u32::MAX,
            model::Primitive::Eq(field, model::GTerm::Variable(variable)) => field == variable,
        }
    }

    pub open spec fn residual_search_safe(l: SymbolicLanguage, q: RegexId) -> bool {
        primitives_search_safe(residual_primitives(l, q))
    }

    pub proof fn lemma_compiled_search_safe(template: FlatPair<u64>, l: SymbolicLanguage, q: RegexId)
        requires q@ == root(l),
            residual_primitives(l, q).subset_of(numeric::source_primitives(template)),
            forall|i: int| #![trigger template.tests@[i]] 0 <= i < template.tests@.len()
                ==> match template.tests@[i] {
                    junco_core::flat::FlatTest::Atom { field, term, .. } => match term {
                        junco_core::flat::FlatTerm::Constant(code) => code <= u32::MAX,
                        junco_core::flat::FlatTerm::Variable(variable) => field == variable,
                    },
                    _ => true,
                },
        ensures residual_search_safe(l, q),
    {
        assert forall|p: model::Primitive| residual_primitives(l, q).contains(p)
            implies match p {
                model::Primitive::Eq(_, model::GTerm::Constant(code)) => code <= u32::MAX,
                model::Primitive::Eq(field, model::GTerm::Variable(variable)) => field == variable,
            } by {
            numeric::lemma_source_primitive_prefix(template, template.tests@.len(), p);
            let i = choose|i: int| #![trigger template.tests@[i]] 0 <= i < template.tests@.len()
                && match template.tests@[i] {
                    junco_core::flat::FlatTest::Atom { field, term, .. } =>
                        p == model::Primitive::Eq(field, numeric::term_view(term)),
                    _ => false,
                };
        }
    }

    pub open spec fn primitive_codes(ps: Set<model::Primitive>, c: Component) -> Set<nat> {
        ps.filter(|p: model::Primitive| match p {
            model::Primitive::Eq(field, model::GTerm::Constant(_)) => field == c,
            _ => false,
        }).map(|p: model::Primitive| match p {
            model::Primitive::Eq(_, model::GTerm::Constant(v)) => v,
            _ => 0nat,
        })
    }

    pub open spec fn residual_codes(l: SymbolicLanguage, q: RegexId, c: Component) -> Set<nat> {
        primitive_codes(residual_primitives(l, q), c)
    }

    pub proof fn lemma_residual_vocabulary_frame(a: SymbolicLanguage, b: SymbolicLanguage, q: RegexId)
        requires language_wf(a), frame(a, b), q@ < graph(a).regexes.len(),
        ensures residual_primitives(a, q) == residual_primitives(b, q),
            forall|c: Component| residual_codes(a, q, c) == residual_codes(b, q, c),
    {
        lemma_language_wf(a);
        symbolic::lemma_regex_primitives_stable(graph(a), graph(b), q@);
    }

    pub proof fn lemma_primitive_codes_contains(ps: Set<model::Primitive>, c: Component, v: nat)
        ensures primitive_codes(ps, c).contains(v)
            == ps.contains(model::Primitive::Eq(c, model::GTerm::Constant(v))),
    {
        broadcast use vstd::set::group_set_lemmas;
        let selected = ps.filter(|p: model::Primitive| match p {
            model::Primitive::Eq(field, model::GTerm::Constant(_)) => field == c,
            _ => false,
        });
        let code = |p: model::Primitive| match p {
            model::Primitive::Eq(_, model::GTerm::Constant(v)) => v,
            _ => 0nat,
        };
        selected.lemma_map_contains(code, v);
        if primitive_codes(ps, c).contains(v) {
            let p = choose|p: model::Primitive| selected.contains(p) && code(p) == v;
            assert(p == model::Primitive::Eq(c, model::GTerm::Constant(v)));
        } else if ps.contains(model::Primitive::Eq(c, model::GTerm::Constant(v))) {
            assert(selected.contains(model::Primitive::Eq(c, model::GTerm::Constant(v))));
        }
    }

    pub proof fn lemma_primitive_codes_mono(a: Set<model::Primitive>, b: Set<model::Primitive>)
        requires a.subset_of(b),
        ensures forall|c: Component| primitive_codes(a, c).subset_of(primitive_codes(b, c)),
    {
        assert forall|c: Component| primitive_codes(a, c).subset_of(primitive_codes(b, c)) by {
            assert forall|v: nat| primitive_codes(a, c).contains(v) implies primitive_codes(b, c).contains(v) by {
                lemma_primitive_codes_contains(a, c, v);
                lemma_primitive_codes_contains(b, c, v);
            }
        }
    }

    pub proof fn lemma_compiled_source_codes(l: SymbolicLanguage, q: RegexId, template: FlatPair<u64>)
        requires residual_primitives(l, q).subset_of(numeric::source_primitives(template)),
        ensures forall|c: Component| residual_codes(l, q, c).subset_of(numeric::source_codes(template, c)),
    {
        lemma_primitive_codes_mono(residual_primitives(l, q), numeric::source_primitives(template));
    }

    pub proof fn lemma_residual_code_mentions(l: SymbolicLanguage, q: RegexId, c: Component, v: nat)
        ensures residual_codes(l, q, c).contains(v) == enc::regex_mentions(abs(l, q), c, v),
    {
        lemma_primitive_codes_contains(residual_primitives(l, q), c, v);
        symbolic::lemma_regex_primitive_code(abs(l, q), c, v);
    }

    pub proof fn lemma_successor_vocabulary(before: SymbolicLanguage, after: SymbolicLanguage,
        q: RegexId, t: TransitionId, v: RegexId)
        requires language_wf(before), language_wf(after), frame(before, after),
            q@ < graph(before).regexes.len(), crate::verify::finite_impl::regex_nf(abs(before, q)),
            fder::dbound(graph(before), q@, t@), fint::entry_val(graph(after), t@, v@),
        ensures residual_primitives(after, v).subset_of(residual_primitives(before, q)),
            forall|c: Component| residual_codes(after, v, c).subset_of(residual_codes(before, q, c)),
    {
        lemma_language_wf(before);
        crate::verify::refinement::finiteness::lemma_impl_successor_abstracts(
            graph(before), q@, t@, graph(after), v@);
        if abs(after, v) != abs(before, q) {
            symbolic::lemma_model_successor_vocab(abs(before, q), abs(after, v));
        }
        assert forall|c: Component| residual_codes(after, v, c).subset_of(residual_codes(before, q, c)) by {
            assert forall|k: nat| residual_codes(after, v, c).contains(k) implies residual_codes(before, q, c).contains(k) by {
                lemma_primitive_codes_contains(residual_primitives(after, v), c, k);
                lemma_primitive_codes_contains(residual_primitives(before, q), c, k);
            }
        }
    }

    pub proof fn lemma_language_wf(l: SymbolicLanguage)
        requires language_wf(l),
        ensures model::graph_wf(graph(l)), root(l) < graph(l).regexes.len(),
            forall|t: TransitionId| has_atoms(l, t) ==> t@ < graph(l).transitions.len()
                && reach::atoms_wf(graph(l), t@, atom_ids(l, t)),
    {}

    proof fn lemma_test_holds_atoms(g: model::Graph, id: nat, theta: Subst, e1: EventView, e2: EventView)
        requires model::graph_wf(g), id < g.tests.len(),
            forall|p: model::Primitive| reach::test_reaches_primitive(g, id, p)
                ==> model::primitive_holds(theta, p, e1) == model::primitive_holds(theta, p, e2),
        ensures model::test_holds(theta, model::lift_test(g, id), e1)
            == model::test_holds(theta, model::lift_test(g, id), e2),
        decreases id,
    {
        model::lemma_graph_test_wf(g, id);
        reveal_with_fuel(model::lift_test, 1);
        reveal_with_fuel(reach::test_reaches_primitive, 1);
        match g.tests[id as int] {
            model::TestNode::Atom(p, _) => {
                assert(reach::test_reaches_primitive(g, id, p));
            },
            model::TestNode::And(cs) | model::TestNode::Or(cs) => {
                assert forall|j: int| 0 <= j < cs.len() implies
                    model::test_holds(theta, model::lift_test(g, cs[j]), e1)
                        == model::test_holds(theta, model::lift_test(g, cs[j]), e2) by {
                    assert forall|p: model::Primitive| reach::test_reaches_primitive(g, cs[j], p) implies
                        model::primitive_holds(theta, p, e1) == model::primitive_holds(theta, p, e2) by {
                        assert(reach::test_edges(g, id) == cs);
                        assert(cs[j] < id);
                        assert(reach::test_edges(g, id)[j] == cs[j]);
                        assert(reach::test_reaches_primitive(g, id, p));
                    }
                    lemma_test_holds_atoms(g, cs[j], theta, e1, e2);
                }
            },
            _ => {},
        }
    }

    proof fn lemma_interp_transition_atoms(g: model::Graph, id: nat, theta: Subst, e1: EventView, e2: EventView)
        requires model::graph_wf(g), id < g.transitions.len(),
            forall|p: model::Primitive| reach::transition_reaches_primitive(g, id, p)
                ==> model::primitive_holds(theta, p, e1) == model::primitive_holds(theta, p, e2),
        ensures language::interp_transition(model::gsem(theta), e1, model::lift_transition(g, id))
            == language::interp_transition(model::gsem(theta), e2, model::lift_transition(g, id)),
        decreases id,
    {
        model::lemma_graph_transition_wf(g, id);
        reveal_with_fuel(model::lift_transition, 1);
        reveal_with_fuel(language::interp_transition, 2);
        reveal_with_fuel(model::lift_transitions, 1);
        reveal_with_fuel(reach::transition_reaches_primitive, 1);
        assert forall|j: int| #![trigger reach::transition_edges(g, id)[j]]
            0 <= j < reach::transition_edges(g, id).len() implies {
            let child = reach::transition_edges(g, id)[j];
            language::interp_transition(model::gsem(theta), e1, model::lift_transition(g, child))
                == language::interp_transition(model::gsem(theta), e2, model::lift_transition(g, child))
        } by {
            let child = reach::transition_edges(g, id)[j];
            assert(child < id);
            assert forall|p: model::Primitive| reach::transition_reaches_primitive(g, child, p) implies
                model::primitive_holds(theta, p, e1) == model::primitive_holds(theta, p, e2) by {
                assert(reach::transition_reaches_primitive(g, id, p));
            }
            lemma_interp_transition_atoms(g, child, theta, e1, e2);
        }
        match g.transitions[id as int] {
            model::TransitionNode::If(t, a, b) => {
                assert forall|p: model::Primitive| reach::test_reaches_primitive(g, t, p) implies
                    model::primitive_holds(theta, p, e1) == model::primitive_holds(theta, p, e2) by {
                    assert(reach::transition_tests(g, id) == seq![t]);
                    assert(reach::transition_tests(g, id)[0] == t);
                    assert(reach::transition_reaches_primitive(g, id, p));
                }
                lemma_test_holds_atoms(g, t, theta, e1, e2);
                assert(model::gsem(theta)(model::lift_test(g, t), e1)
                    == model::gsem(theta)(model::lift_test(g, t), e2));
                assert(reach::transition_edges(g, id)[0] == a);
                assert(reach::transition_edges(g, id)[1] == b);
                assert(language::interp_transition(model::gsem(theta), e1, model::lift_transition(g, a))
                    == language::interp_transition(model::gsem(theta), e2, model::lift_transition(g, a)));
                assert(language::interp_transition(model::gsem(theta), e1, model::lift_transition(g, b))
                    == language::interp_transition(model::gsem(theta), e2, model::lift_transition(g, b)));
                assert(language::interp_transition(model::gsem(theta), e1, model::lift_transition(g, id))
                    == language::interp_transition(model::gsem(theta), e2, model::lift_transition(g, id)));
            },
            model::TransitionNode::Union(cs) | model::TransitionNode::Intersect(cs) => {
                let left = Seq::new(cs.len(), |j: int|
                    language::interp_transition(model::gsem(theta), e1, model::lift_transitions(g, cs, id)[j]));
                let right = Seq::new(cs.len(), |j: int|
                    language::interp_transition(model::gsem(theta), e2, model::lift_transitions(g, cs, id)[j]));
                assert(left =~= right) by {
                    assert forall|j: int| 0 <= j < cs.len() implies left[j] == right[j] by {
                        assert(reach::transition_edges(g, id)[j] == cs[j]);
                    }
                }
                let l = language::interp_transition(model::gsem(theta), e1, model::lift_transition(g, id));
                let r = language::interp_transition(model::gsem(theta), e2, model::lift_transition(g, id));
                if g.transitions[id as int] is Union {
                    assert(l is Union && r is Union);
                    assert(l->Union_0 =~= left);
                    assert(r->Union_0 =~= right);
                } else {
                    assert(l is Intersect && r is Intersect);
                    assert(l->Intersect_0 =~= left);
                    assert(r->Intersect_0 =~= right);
                }
                assert(language::interp_transition(model::gsem(theta), e1, model::lift_transition(g, id))
                    == language::interp_transition(model::gsem(theta), e2, model::lift_transition(g, id)));
            },
            model::TransitionNode::Not(child) | model::TransitionNode::Append(child, _) => {
                assert(reach::transition_edges(g, id)[0] == child);
                assert(language::interp_transition(model::gsem(theta), e1, model::lift_transition(g, child))
                    == language::interp_transition(model::gsem(theta), e2, model::lift_transition(g, child)));
                assert(language::interp_transition(model::gsem(theta), e1, model::lift_transition(g, id))
                    == language::interp_transition(model::gsem(theta), e2, model::lift_transition(g, id)));
            },
            _ => {},
        }
    }

    pub proof fn lemma_transition_lang_atoms(g: model::Graph, t: TransitionId, theta: Subst,
        e1: EventView, e2: EventView, w: Seq<EventView>)
        requires model::graph_wf(g), t@ < g.transitions.len(),
            forall|p: model::Primitive| reach::transition_reaches_primitive(g, t@, p)
                ==> model::primitive_holds(theta, p, e1) == model::primitive_holds(theta, p, e2),
        ensures norm::transition_lang(g, theta, t, e1, w) == norm::transition_lang(g, theta, t, e2, w),
    {
        lemma_interp_transition_atoms(g, t@, theta, e1, e2);
    }

    spec fn node_code(n: model::TestNode) -> nat {
        match n {
            model::TestNode::Atom(model::Primitive::Eq(_, model::GTerm::Constant(v)), _) => v,
            _ => 0,
        }
    }
    spec fn graph_codes(g: model::Graph) -> Set<nat> {
        g.tests.map_values(|n: model::TestNode| node_code(n)).to_set()
    }

    proof fn lemma_test_codes(g: model::Graph, id: nat)
        requires model::graph_wf(g), id < g.tests.len(),
        ensures forall|c: Component, v: nat|
            enc::test_mentions(model::lift_test(g, id), c, v) ==> graph_codes(g).contains(v),
        decreases id,
    {
        model::lemma_graph_test_wf(g, id);
        reveal_with_fuel(model::lift_test, 1);
        reveal_with_fuel(enc::test_mentions, 1);
        let codes = g.tests.map_values(|n: model::TestNode| node_code(n));
        codes.to_set_ensures();
        assert(codes[id as int] == node_code(g.tests[id as int]));
        assert(codes.to_set().contains(codes[id as int]));
        assert(graph_codes(g) == codes.to_set());
        assert forall|c: Component, v: nat| enc::test_mentions(model::lift_test(g, id), c, v)
            implies graph_codes(g).contains(v) by {
            match g.tests[id as int] {
                model::TestNode::And(cs) | model::TestNode::Or(cs) => {
                    let ts = model::lift_tests(g, cs, id);
                    let j = choose|j: int| 0 <= j < ts.len() && enc::test_mentions(ts[j], c, v);
                    assert(ts[j] == model::lift_test(g, cs[j]));
                    lemma_test_codes(g, cs[j]);
                },
                _ => {},
            }
        }
    }

    proof fn lemma_regex_codes(g: model::Graph, id: nat)
        requires model::graph_wf(g), id < g.regexes.len(),
        ensures forall|c: Component, v: nat|
            enc::regex_mentions(model::lift_regex(g, id), c, v) ==> graph_codes(g).contains(v),
        decreases id,
    {
        norm::regex_unfold(g, id);
        reveal_with_fuel(enc::regex_mentions, 1);
        assert forall|c: Component, v: nat| enc::regex_mentions(model::lift_regex(g, id), c, v)
            implies graph_codes(g).contains(v) by {
            match g.regexes[id as int].kind {
                model::RegexKindNode::Test(t) => {
                    assert(enc::test_mentions(model::lift_test(g, t), c, v));
                    lemma_test_codes(g, t);
                    assert(graph_codes(g).contains(v));
                },
                model::RegexKindNode::Union(cs) | model::RegexKindNode::Concat(cs)
                | model::RegexKindNode::Intersect(cs) => {
                    let rs = model::lift_regexes(g, cs);
                    let j = choose|j: int| 0 <= j < rs.len() && enc::regex_mentions(rs[j], c, v);
                    assert(rs[j] == model::lift_regex(g, cs[j]));
                    lemma_regex_codes(g, cs[j]);
                    assert(graph_codes(g).contains(v));
                },
                model::RegexKindNode::Not(r) | model::RegexKindNode::Star(r) => {
                    lemma_regex_codes(g, r);
                    assert(enc::regex_mentions(model::lift_regex(g, r), c, v));
                    assert(graph_codes(g).contains(v));
                },
                _ => { assert(!enc::regex_mentions(model::lift_regex(g, id), c, v)); },
            }
        }
    }

    proof fn lemma_bounded_renaming(fixed: Set<nat>, values: Set<nat>) -> (f: spec_fn(nat) -> nat)
        requires fixed.len() + values.len() + 4 <= u64::MAX,
            forall|x: nat| fixed.contains(x) ==> x <= u64::MAX,
        ensures forall|x: nat, y: nat| #![trigger f(x), f(y)] f(x) == f(y) <==> x == y,
            forall|x: nat| fixed.contains(x) ==> f(x) == x,
            forall|x: nat| values.contains(x) ==> f(x) <= u64::MAX,
        decreases values.len(),
    {
        broadcast use vstd::set::group_set_lemmas;
        if values.len() == 0 {
            values.lemma_len0_is_empty();
            |x: nat| x
        } else {
            let x = values.choose();
            if x <= u64::MAX {
                let f = lemma_bounded_renaming(fixed.insert(x), values.remove(x));
                assert forall|z: nat| fixed.contains(z) implies f(z) == z by {
                    assert(fixed.insert(x).contains(z));
                }
                assert forall|z: nat| values.contains(z) implies f(z) <= u64::MAX by {
                    if z == x { assert(fixed.insert(x).contains(x)); }
                    else { assert(values.remove(x).contains(z)); }
                }
                f
            } else {
                let forbidden = fixed.union(values);
                vstd::set_lib::lemma_len_union(fixed, values);
                let candidates = Set::<nat>::range(0, forbidden.len() + 1);
                vstd::set_lib::range_set_properties(0nat, forbidden.len() + 1);
                assert(exists|y: nat| candidates.contains(y) && !forbidden.contains(y)) by {
                    if !exists|y: nat| candidates.contains(y) && !forbidden.contains(y) {
                        assert(candidates.subset_of(forbidden));
                        vstd::set_lib::lemma_len_subset(candidates, forbidden);
                    }
                }
                let y = choose|y: nat| candidates.contains(y) && !forbidden.contains(y);
                let rest = lemma_bounded_renaming(fixed.insert(y), values.remove(x));
                let swap = |z: nat| if z == x { y } else if z == y { x } else { z };
                let f = |z: nat| rest(swap(z));
                assert forall|a: nat, b: nat| #![trigger f(a), f(b)] f(a) == f(b) <==> a == b by {
                    assert(swap(a) == swap(b) <==> a == b);
                }
                assert forall|z: nat| fixed.contains(z) implies f(z) == z by {
                    assert(z != x && z != y);
                    assert(fixed.insert(y).contains(z));
                }
                assert forall|z: nat| values.contains(z) implies f(z) <= u64::MAX by {
                    if z == x { assert(fixed.insert(y).contains(y)); }
                    else { assert(z != y); assert(values.remove(x).contains(z)); }
                }
                f
            }
        }
    }

    pub open spec fn atom_primitives(l: SymbolicLanguage, t: TransitionId) -> Set<model::Primitive> {
        atom_ids(l, t).map_values(|id: TestId| match graph(l).tests[id@ as int] {
            model::TestNode::Atom(p, _) => p,
            _ => model::Primitive::Eq(history_syntax::Component(0), model::GTerm::Constant(0)),
        }).to_set()
    }

    pub proof fn lemma_atoms_vocabulary(l: SymbolicLanguage, q: RegexId, t: TransitionId)
        requires language_wf(l), has_atoms(l, t), q@ < derivatives(l).len(), derivatives(l)[q@ as int] == Some(t),
        ensures atom_primitives(l, t).subset_of(residual_primitives(l, q)),
    {
        broadcast use vstd::set::group_set_lemmas;
        reveal(language_wf); reveal(graph); reveal(has_atoms); reveal(atom_ids); reveal(derivatives);
        lemma_language_wf(l);
        symbolic::derivative_cached_bound(graph(l), derivatives(l), q, t);
        let ids = atom_ids(l, t);
        let ps = ids.map_values(|id: TestId| match graph(l).tests[id@ as int] {
            model::TestNode::Atom(p, _) => p,
            _ => model::Primitive::Eq(Component(0), model::GTerm::Constant(0)),
        });
        ps.to_set_ensures();
        assert forall|p: model::Primitive| atom_primitives(l, t).contains(p) implies residual_primitives(l, q).contains(p) by {
            let i = ps.lemma_contains_to_index(p);
            assert(graph(l).tests[ids[i]@ as int] == model::TestNode::Atom(p, true));
            assert(reach::has_positive(graph(l), ids, p));
            assert(reach::transition_reaches_primitive(graph(l), t@, p));
            symbolic::lemma_transition_primitives_lift(graph(l), t@, p);
        }
    }

    /// Renaming only candidate values permits the frozen all-`nat` completeness quantifier.
    pub proof fn lemma_atoms_complete(l: SymbolicLanguage, q: RegexId, t: TransitionId)
        requires language_wf(l), has_atoms(l, t), symbolic::derivative_correct(graph(l), q@, t),
        ensures crate::verify::refinement::search::atoms_complete(abs(l, q), atom_primitives(l, t)),
    {
        let g = graph(l);
        let fixed = graph_codes(g);
        lemma_language_wf(l);
        l.pair.store.lemma_constant_bounds();
        l.pair.store.lemma_node_count_bounds();
        g.tests.map_values(|n: model::TestNode| node_code(n)).lemma_cardinality_of_set();
        g.tests.map_values(|n: model::TestNode| node_code(n)).to_set_ensures();
        let primitives = atom_ids(l, t).map_values(|id: TestId| match g.tests[id@ as int] {
            model::TestNode::Atom(p, _) => p,
            _ => model::Primitive::Eq(Component(0), model::GTerm::Constant(0)),
        });
        primitives.to_set_ensures();
        assert(primitives.to_set() == atom_primitives(l, t));
        assert forall|v: nat| fixed.contains(v) implies v <= u64::MAX by {
            let i = choose|i: int| 0 <= i < g.tests.len() && node_code(g.tests[i]) == v;
            match g.tests[i] {
                model::TestNode::Atom(model::Primitive::Eq(c, model::GTerm::Constant(k)), positive) => {
                    assert(k <= u64::MAX);
                },
                _ => {},
            }
        }
        lemma_regex_codes(g, q@);
        assert forall|theta: Subst, e1: EventView, e2: EventView, w: Seq<EventView>|
            theta.len() <= history_syntax::MAX_ARITY
            && (forall|p: model::Primitive| atom_primitives(l, t).contains(p)
                ==> model::primitive_holds(theta, p, e1) == model::primitive_holds(theta, p, e2))
            implies language::numeric_lang(model::gsem(theta), abs(l, q), seq![e1] + w)
                == language::numeric_lang(model::gsem(theta), abs(l, q), seq![e2] + w) by {
            theta.lemma_cardinality_of_set();
            theta.to_set_ensures();
            let values = theta.to_set();
            let f = lemma_bounded_renaming(fixed, values);
            let ft = enc::n_rename_event(f, theta);
            let fe1 = enc::n_rename_event(f, e1);
            let fe2 = enc::n_rename_event(f, e2);
            let fw = enc::n_rename_history(f, w);
            assert forall|i: int| 0 <= i < ft.len() implies ft[i] <= u64::MAX by {
                assert(values.contains(theta[i]));
            }
            assert(language::event_wf(ft, ft.len()));
            assert(enc::n_renaming_ok(f, fixed.to_iset(), ISet::full()));
            assert forall|p: model::Primitive| reach::transition_reaches_primitive(g, t@, p) implies
                model::primitive_holds(ft, p, fe1) == model::primitive_holds(ft, p, fe2) by {
                assert(reach::has_positive(g, atom_ids(l, t), p));
                let i = choose|i: int| 0 <= i < atom_ids(l, t).len()
                    && atom_ids(l, t)[i]@ < g.tests.len()
                    && g.tests[atom_ids(l, t)[i]@ as int] == model::TestNode::Atom(p, true);
                assert(primitives[i] == p);
                assert(primitives.to_set().contains(primitives[i]));
                assert(atom_primitives(l, t).contains(p));
                let id = atom_ids(l, t)[i]@;
                lemma_test_codes(g, id);
                enc::lemma_test_rename(model::lift_test(g, id), theta, f, fixed.to_iset(), ISet::full(), e1);
                enc::lemma_test_rename(model::lift_test(g, id), theta, f, fixed.to_iset(), ISet::full(), e2);
            }
            lemma_transition_lang_atoms(g, t, ft, fe1, fe2, fw);
            let u1 = seq![e1] + w;
            let u2 = seq![e2] + w;
            let v1 = seq![fe1] + fw;
            let v2 = seq![fe2] + fw;
            assert(junco_core::verify::encoding::pointwise(u1, v1, enc::n_renamed(f, ISet::full())));
            assert(junco_core::verify::encoding::pointwise(u2, v2, enc::n_renamed(f, ISet::full())));
            enc::lemma_lang_rename(abs(l, q), theta, f, fixed.to_iset(), ISet::full(), u1, v1);
            enc::lemma_lang_rename(abs(l, q), theta, f, fixed.to_iset(), ISet::full(), u2, v2);
        }
    }
    }
}
