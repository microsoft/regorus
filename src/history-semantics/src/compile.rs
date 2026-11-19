#[cfg(verus_keep_ghost)]
use crate::normalize::verify as norm;
use crate::normalize::{RegexNormalize, TestNormalize};
use crate::progress::CompiledPair;
use crate::runtime::RuleRuntime;
#[cfg(verus_keep_ghost)]
use crate::symbolic::verify as vocab;
use alloc::vec::Vec;
use history_store::graph::{CanonicalStore, RuntimeKernel, allocation};
use history_store::store::Event as NumericEvent;
use history_syntax::MAX_ARITY;
#[cfg(any(verus_keep_ghost, test))]
use history_syntax::syntax::Component;
use junco_core::errors::HistoryError;
#[cfg(verus_keep_ghost)]
use junco_core::flat::verify as flat;
use junco_core::flat::{FlatHead, FlatPair, FlatRegex, FlatTerm, FlatTest};
#[cfg(verus_keep_ghost)]
use junco_core::kernel::verify as model;
use junco_core::kernel::*;
use junco_core::limits::Limits;
use junco_core::observation::ObservationWorld;
#[cfg(verus_keep_ghost)]
use junco_core::spec::semantics::resource_error;
#[cfg(verus_keep_ghost)]
use junco_core::verify::history_assumptions::KernelStoreSpec;
#[cfg(verus_keep_ghost)]
use junco_core::verify::history_specs as language;
#[cfg(verus_keep_ghost)]
use verify::*;
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
verus! {
broadcast use {junco_core::kernel::verify::group_kernel_views, vstd::set::group_set_lemmas};
}

#[cfg(verus_keep_ghost)]
verus! {
    pub closed spec fn bindings_match(template: FlatPair<u64>, request: NumericEvent, bindings: Bindings) -> bool {
        language::head_match(head_view(template), request@, bindings@)
    }

    pub closed spec fn head_rejects(template: FlatPair<u64>, request: NumericEvent) -> bool {
        !exists|theta: language::Subst| language::head_match(head_view(template), request@, theta)
    }

    pub(crate) proof fn lemma_bindings_match(template: FlatPair<u64>, request: NumericEvent, bindings: Bindings)
        ensures bindings_match(template, request, bindings)
            == language::head_match(head_view(template), request@, bindings@),
    { reveal(bindings_match); }

    pub(crate) proof fn lemma_head_rejects(template: FlatPair<u64>, request: NumericEvent)
        ensures head_rejects(template, request)
            == !exists|theta: language::Subst| language::head_match(head_view(template), request@, theta),
    { reveal(head_rejects); }
}

#[verus_verify]
impl RuleRuntime {
    /// Return coordinate bindings, or `None` for an arity or constant mismatch.
    #[verus_verify]
    #[verus_spec(result => ensures match result {
        Some(bindings) => bindings_match(*template, *request, bindings),
        None => head_rejects(*template, *request),
    })]
    pub fn bindings(template: &FlatPair<u64>, request: &NumericEvent) -> Option<Bindings> {
        proof! { reveal(bindings_match); reveal(head_rejects); }
        let arity = request.arity();
        if template.head.len() != arity {
            return None;
        }
        let mut slots = [0u64; MAX_ARITY];
        let mut index = 0;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant index <= arity <= MAX_ARITY,
                arity == request@.len(), template.head@.len() == arity,
                forall|i: int| 0 <= i < index ==> language::head_field_match(
                    template.head@[i]@, request@[i], slots@[i] as nat),
            decreases arity - index,
        ))]
        while index < arity {
            let value = request.component(index);
            let binding = match Self::bind_head(&template.head[index], value) {
                Some(binding) => binding,
                None => {
                    proof! {
                        assert forall|theta: language::Subst| !language::head_match(
                            head_view(*template), request@, theta) by {
                            if language::head_match(head_view(*template), request@, theta) {
                                assert(language::head_field_match(template.head@[index as int]@,
                                    request@[index as int], theta[index as int]));
                            }
                        }
                    }
                    return None;
                }
            };
            slots[index] = binding;
            index += 1;
        }
        let bindings = Bindings::new(&slots[..arity]);
        proof! {
            assert forall|i: int| 0 <= i < arity implies language::head_field_match(
                head_view(*template)[i], request@[i], bindings@[i]) by {
                assert(bindings@[i] == slots@[i] as nat);
            }
        }
        Some(bindings)
    }

    #[allow(
        clippy::missing_const_for_fn,
        reason = "Keep the existing operation and its Verus contract unchanged"
    )]
    #[verus_verify]
    #[verus_spec(result => ensures match result {
        Some(binding) => language::head_field_match(this@, value as nat, binding as nat),
        None => !exists|binding: nat| language::head_field_match(this@, value as nat, binding),
    })]
    fn bind_head(this: &FlatHead<u64>, value: u64) -> Option<u64> {
        match this {
            FlatHead::Any => Some(0),
            FlatHead::Constant(expected) if value == *expected => Some(0),
            FlatHead::Constant(_) => None,
            FlatHead::Bind => Some(value),
        }
    }
}

#[verus_verify]
impl CompiledPair {
    #[verus_verify]
    #[verus_spec(result => ensures
        result != Err(HistoryError::WrongHistoryOwner),
        !(result matches Err(HistoryError::InvalidPolicy { .. })),
        (id as nat) < values@.len() ==> language::no_invariant_failure(result),
        (id as nat) < values@.len()
            ==> (result matches Err(error) ==> resource_error(error)),
        result matches Ok(value) ==> (id as nat) < values@.len() && value == values@[id as int])]
    #[allow(
        clippy::option_if_let_else,
        reason = "Explicit matches preserve the Verus proof structure"
    )]
    fn lookup<T: Copy>(values: &[T], id: u32) -> KernelResult<T> {
        let index = match usize::try_from(id) {
            Ok(index) => index,
            Err(_) => return Err(HistoryError::invariant("source node index overflow")),
        };
        proof! { assert(index as nat == id as nat); }
        match values.get(index) {
            Some(value) => Ok(*value),
            None => Err(HistoryError::invariant("invalid source node reference")),
        }
    }

    #[verus_verify]
    #[verus_spec(result => ensures
        result != Err(HistoryError::WrongHistoryOwner),
        !(result matches Err(HistoryError::InvalidPolicy { .. })),
        (forall|i: int| 0 <= i < ids@.len() ==> #[trigger] ids@[i] < values@.len())
            ==> language::no_invariant_failure(result),
        (forall|i: int| 0 <= i < ids@.len() ==> #[trigger] ids@[i] < values@.len())
            ==> (result matches Err(error) ==> resource_error(error)),
        result matches Ok(found) ==> {
        found@.len() == ids@.len()
        && forall|i: int| 0 <= i < ids@.len()
            ==> #[trigger] ids@[i] < values@.len() && found@[i] == values@[ids@[i] as int]
    })]

    fn references<T: Copy>(
        values: &[T],
        ids: &[u32],
        world: &mut ObservationWorld,
    ) -> KernelResult<Vec<T>> {
        let mut found = Vec::new();
        allocation(world.try_reserve_vec_exact(&mut found, ids.len()))?;
        let mut index = 0;
        #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant index <= ids@.len(), found@.len() == index,
            forall|i: int| 0 <= i < index
                ==> #[trigger] ids@[i] < values@.len() && found@[i] == values@[ids@[i] as int],
        decreases ids@.len() - index,
    ))]
        while index < ids.len() {
            let id = match ids.get(index) {
                Some(id) => *id,
                None => return Err(HistoryError::invariant("missing source reference")),
            };
            proof! { assert(id == ids@[index as int]); }
            let value = Self::lookup(values, id)?;
            proof_decl! { let ghost previous = found@; }
            found.push(value);
            proof! {
                assert(index < usize::MAX);
                assert forall|i: int| 0 <= i <= index implies
                    #[trigger] ids@[i] < values@.len() && found@[i] == values@[ids@[i] as int] by {
                    if i < index {
                        assert(found@[i] == previous[i]);
                    } else {
                        assert(i == index);
                        assert(found@[i] == value);
                    }
                }
            }
            index = index.saturating_add(1);
        }
        Ok(found)
    }
    /// Build a fresh graph that may be charged `budget` bytes from immutable numeric source,
    /// including after exhaustion. The runtime passes [`junco_core::limits::MAX_GRAPH_BYTES`].
    /// A source DAG and a layout-valid arena budget exclude internal construction errors.
    #[allow(
        clippy::shadow_unrelated,
        reason = "Separate lowering loops retain their proof-local index bindings"
    )]
    #[verus_verify]
    #[verus_spec(result => ensures
        result != Err(HistoryError::WrongHistoryOwner),
        !(result matches Err(HistoryError::InvalidPolicy { .. })),
        (source_dag_wf(*template) || flat::structural_wf(*template))
            && (budget == junco_core::limits::MAX_GRAPH_BYTES
                || history_store::graph::verify::construction_layout(budget))
            ==> language::no_invariant_failure(result),
        (source_dag_wf(*template) || flat::structural_wf(*template))
            && (budget == junco_core::limits::MAX_GRAPH_BYTES
                || history_store::graph::verify::construction_layout(budget))
            ==> (result matches Err(error) ==> resource_error(error)),
        result matches Ok(pair) ==> {
        crate::progress::verify::pair_wf(pair)
        && crate::verify::finite_impl::regex_nf(model::lift_regex(pair.store.graph(), pair.root@))
        && vocab::regex_primitives(model::lift_regex(pair.store.graph(), pair.root@)).subset_of(source_primitives(*template))
        && forall|theta: language::Subst, word: Seq<language::EventView>| language::event_wf(theta, theta.len())
            ==> model::regex_lang(pair.store.graph(), theta, pair.root@, word)
                == source_regex(*template, template.root as nat, theta, word)
    })]
    #[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
    #[cfg_attr(verus_keep_ghost, verifier::rlimit(60))]

    pub(crate) fn compile<L: Limits>(
        template: &FlatPair<u64>,
        budget: usize,
        limits: &mut L,
        world: &mut ObservationWorld,
    ) -> KernelResult<Self> {
        proof! {
            if flat::structural_wf(*template) {
                lemma_structural_source_dag(*template);
            }
        }
        limits.checkpoint().map_err(HistoryError::from)?;
        let mut store = if budget == junco_core::limits::MAX_GRAPH_BYTES {
            CanonicalStore::new()?
        } else {
            CanonicalStore::with_budget(budget)?
        };
        let mut tests = Vec::new();
        let mut regexes = Vec::new();
        allocation(world.try_reserve_vec_exact(&mut tests, template.tests.len()))?;
        allocation(world.try_reserve_vec_exact(&mut regexes, template.regexes.len()))?;
        {
            let mut kernel = RuntimeKernel {
                store: &mut store,
                limits,
                world,
            };
            proof_decl! { let ghost restoration = kernel.restoration(); }
            proof! { crate::verify::finite_compile::lemma_compiled_empty(kernel.graph()); assert(tests@ =~= Seq::<TestId>::empty()); }
            let mut index = 0;
            #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant index <= template.tests@.len(), tests@.len() == index,
                kernel.valid_store(), kernel.errors_are_non_invariant(), model::graph_wf(kernel.graph()),
                kernel.errors_are_non_invalid_policy(),
                kernel.errors_are_resource(),
                kernel.restoration() == restoration,
                test_maps(kernel.graph(), *template, tests@),
                regex_maps(kernel.graph(), *template, regexes@), regexes@.len() == 0,
                crate::verify::finite_compile::compiled_nf(kernel.graph(), tests@, regexes@),
                tests_vocabulary(kernel.graph(), *template, tests@), regexes_vocabulary(kernel.graph(), *template, regexes@),
            decreases template.tests@.len() - index,
        ))]
            while index < template.tests.len() {
                kernel.checkpoint()?;
                let test = match template.tests.get(index) {
                    Some(test) => test,
                    None => return Err(HistoryError::invariant("missing numeric test node")),
                };
                proof_decl! { let ghost before = kernel.graph(); }
                proof_decl! { let ghost mut selected_ids = Seq::<TestId>::empty(); }
                proof! {
                    assert(*test == template.tests@[index as int]);
                    if source_dag_wf(*template) {
                        assert(source_test_dag(*test, index as nat));
                    }
                }
                let id = match test {
                    FlatTest::Bool(value) => {
                        if *value {
                            kernel.constants().test_true
                        } else {
                            kernel.constants().test_false
                        }
                    }
                    FlatTest::Atom {
                        field,
                        term,
                        positive,
                    } => kernel.intern_test(TestView::Atom {
                        primitive: Primitive::Eq {
                            field: *field,
                            term: match term {
                                FlatTerm::Constant(value) => Term::Constant(*value),
                                FlatTerm::Variable(field) => Term::Variable(*field),
                            },
                        },
                        positive: *positive,
                    })?,
                    FlatTest::And(children) => {
                        let selected = Self::references(&tests, children, kernel.world)?;
                        proof! {
                            selected_ids = selected@;
                            selected_tests_valid(kernel.graph(), *template, tests@, children@, selected@);
                        }
                        TestId::connective(&mut kernel, &selected, true)?
                    }
                    FlatTest::Or(children) => {
                        let selected = Self::references(&tests, children, kernel.world)?;
                        proof! {
                            selected_ids = selected@;
                            selected_tests_valid(kernel.graph(), *template, tests@, children@, selected@);
                        }
                        TestId::connective(&mut kernel, &selected, false)?
                    }
                };
                proof! {
                    maps_extend(before, kernel.graph(), *template, tests@, regexes@);
                    assert(test_correct(kernel.graph(), *template, index as nat, id)) by {
                        reveal_with_fuel(source_test, 1);
                        model::lemma_graph_wf_elim(kernel.graph());
                        assert forall|theta: language::Subst, event: language::EventView|
                            language::event_wf(theta, theta.len()) implies
                            norm::test_truth(kernel.graph(), theta, id@, event)
                                == source_test(*template, index as nat, theta, event) by {
                            match test {
                                FlatTest::Bool(_) | FlatTest::Atom { .. } => {
                                    norm::test_lemma_truth(kernel.graph(), theta, id@, event);
                                }
                                FlatTest::And(children) => {
                                    test_connective_transfer(kernel.graph(), *template, tests@,
                                        children@, selected_ids, theta, event, true);
                                }
                                FlatTest::Or(children) => {
                                    test_connective_transfer(kernel.graph(), *template, tests@,
                                        children@, selected_ids, theta, event, false);
                                }
                            }
                        }
                    }
                    match test {
                        FlatTest::Bool(_) | FlatTest::Atom { .. } => {
                            crate::verify::finite_compile::lemma_test_simple_nf(kernel.graph(), id@);
                        }
                        FlatTest::And(children) => {
                            crate::verify::finite_compile::lemma_connective_nf(before, kernel.graph(), tests@, regexes@,
                                children@, selected_ids, true, id@);
                        }
                        FlatTest::Or(children) => {
                            crate::verify::finite_compile::lemma_connective_nf(before, kernel.graph(), tests@, regexes@,
                                children@, selected_ids, false, id@);
                        }
                    }
                    lemma_vocabulary_stable(before, kernel.graph(), *template, tests@, regexes@);
                    model::lemma_graph_wf_elim(kernel.graph());
                    assert forall|p: model::Primitive| vocab::test_primitives(model::lift_test(kernel.graph(), id@)).contains(p)
                        implies source_primitives(*template).contains(p) by {
                        match test {
                            FlatTest::Bool(_) => {
                                reveal_with_fuel(model::lift_test, 1);
                                reveal_with_fuel(vocab::test_primitives, 1);
                                assert(!vocab::test_primitives(model::lift_test(kernel.graph(), id@)).contains(p));
                            },
                            FlatTest::Atom { field, term, .. } => {
                                reveal_with_fuel(model::lift_test, 1);
                                reveal_with_fuel(vocab::test_primitives, 1);
                                assert(p == model::Primitive::Eq(*field, term_view(*term)));
                                lemma_source_primitive_prefix(*template, template.tests@.len(), p);
                                assert(exists|j: int| #![trigger template.tests@[j]] 0 <= j < template.tests@.len() && match template.tests@[j] {
                                    FlatTest::Atom { field, term, .. } => p == model::Primitive::Eq(field, term_view(term)), _ => false,
                                });
                                assert(source_primitives(*template).contains(p));
                            },
                            FlatTest::And(children) => {
                                vocab::lemma_test_connective_primitives(before, kernel.graph(), selected_ids, true, id@, p);
                                let j = choose|j: int| 0 <= j < selected_ids.len()
                                    && vocab::test_primitives(model::lift_test(before, selected_ids[j]@)).contains(p);
                                assert(selected_ids[j] == tests@[children@[j] as int]);
                                assert(source_primitives(*template).contains(p));
                            },
                            FlatTest::Or(children) => {
                                vocab::lemma_test_connective_primitives(before, kernel.graph(), selected_ids, false, id@, p);
                                let j = choose|j: int| 0 <= j < selected_ids.len()
                                    && vocab::test_primitives(model::lift_test(before, selected_ids[j]@)).contains(p);
                                assert(selected_ids[j] == tests@[children@[j] as int]);
                                assert(source_primitives(*template).contains(p));
                            },
                        }
                    }
                    assert(tests_vocabulary(kernel.graph(), *template, tests@.push(id))) by {
                        assert forall|i: int| 0 <= i < tests@.push(id).len() implies tests@.push(id)[i]@ < kernel.graph().tests.len()
                            && vocab::test_primitives(model::lift_test(kernel.graph(), tests@.push(id)[i]@)).subset_of(source_primitives(*template)) by {
                            if i < tests@.len() { assert(tests@.push(id)[i] == tests@[i]); }
                            else { assert(tests@.push(id)[i] == id); }
                        }
                    }
                    crate::verify::finite_compile::lemma_push_test(before, kernel.graph(), tests@, regexes@, id);
                    test_push(kernel.graph(), *template, tests@, id);
                }
                tests.push(id);
                index = index.saturating_add(1);
            }
            let mut index = 0;
            #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant index <= template.regexes@.len(), regexes@.len() == index,
                kernel.valid_store(), kernel.errors_are_non_invariant(), model::graph_wf(kernel.graph()),
                kernel.errors_are_non_invalid_policy(),
                kernel.errors_are_resource(),
                kernel.restoration() == restoration,
                test_maps(kernel.graph(), *template, tests@), tests@.len() == template.tests@.len(),
                regex_maps(kernel.graph(), *template, regexes@),
                crate::verify::finite_compile::compiled_nf(kernel.graph(), tests@, regexes@),
                tests_vocabulary(kernel.graph(), *template, tests@), regexes_vocabulary(kernel.graph(), *template, regexes@),
            decreases template.regexes@.len() - index,
        ))]
            while index < template.regexes.len() {
                kernel.checkpoint()?;
                let regex = match template.regexes.get(index) {
                    Some(regex) => regex,
                    None => return Err(HistoryError::invariant("missing numeric regex node")),
                };
                proof_decl! { let ghost before = kernel.graph(); }
                proof_decl! { let ghost mut selected_ids = Seq::<RegexId>::empty(); }
                proof! {
                    assert(*regex == template.regexes@[index as int]);
                    if source_dag_wf(*template) {
                        assert(flat::regex_wf(*regex, index as nat, template.tests@.len()));
                    }
                }
                let id = match regex {
                    FlatRegex::Empty => kernel.constants().empty,
                    FlatRegex::All => kernel.constants().all,
                    FlatRegex::Epsilon => kernel.constants().epsilon,
                    FlatRegex::Test(test) => {
                        RegexId::from_test(&mut kernel, Self::lookup(&tests, *test)?)?
                    }
                    FlatRegex::Concat(children) => {
                        let selected = Self::references(&regexes, children, kernel.world)?;
                        proof! {
                            selected_ids = selected@;
                            selected_regexes_valid(kernel.graph(), *template, regexes@, children@, selected@);
                        }
                        RegexId::concat(&mut kernel, &selected)?
                    }
                    FlatRegex::Union(children) => {
                        let selected = Self::references(&regexes, children, kernel.world)?;
                        proof! {
                            selected_ids = selected@;
                            selected_regexes_valid(kernel.graph(), *template, regexes@, children@, selected@);
                        }
                        RegexId::set(&mut kernel, &selected, false)?
                    }
                    FlatRegex::Intersect(children) => {
                        let selected = Self::references(&regexes, children, kernel.world)?;
                        proof! {
                            selected_ids = selected@;
                            selected_regexes_valid(kernel.graph(), *template, regexes@, children@, selected@);
                        }
                        RegexId::set(&mut kernel, &selected, true)?
                    }
                    FlatRegex::Star(child) => {
                        RegexId::star(Self::lookup(&regexes, *child)?, &mut kernel)?
                    }
                    FlatRegex::Complement(child) => {
                        RegexId::not(Self::lookup(&regexes, *child)?, &mut kernel)?
                    }
                };
                proof! {
                    maps_extend(before, kernel.graph(), *template, tests@, regexes@);
                    assert(regex_correct(kernel.graph(), *template, index as nat, id)) by {
                        reveal_with_fuel(source_regex, 1);
                        norm::regex_constants(kernel.graph());
                        assert forall|theta: language::Subst, word: Seq<language::EventView>|
                            language::event_wf(theta, theta.len()) implies
                            model::regex_lang(kernel.graph(), theta, id@, word)
                                == source_regex(*template, index as nat, theta, word) by {
                            match regex {
                                FlatRegex::Test(test) => {
                                    assert((*test as nat) < tests@.len());
                                    assert(test_correct(kernel.graph(), *template, *test as nat,
                                        tests@[*test as int]));
                                    assert(model::regex_lang(kernel.graph(), theta, id@, word)
                                        == source_regex(*template, index as nat, theta, word));
                                }
                                FlatRegex::Concat(children) => {
                                    assert(selected_ids =~= Seq::new(children@.len(),
                                        |i: int| regexes@[children@[i] as int]));
                                    regex_concat_transfer(kernel.graph(), *template, regexes@, children@,
                                        index as nat, theta, word);
                                    assert(model::regex_lang(kernel.graph(), theta, id@, word)
                                        == source_regex(*template, index as nat, theta, word));
                                }
                                FlatRegex::Star(child) => {
                                    regex_star_transfer(kernel.graph(), *template, regexes@,
                                        *child as nat, theta, word);
                                    assert(model::regex_lang(kernel.graph(), theta, id@, word)
                                        == source_regex(*template, index as nat, theta, word));
                                }
                                FlatRegex::Union(children) => {
                                    regex_set_transfer(kernel.graph(), *template, regexes@,
                                        children@, selected_ids, theta, word, false);
                                    assert(model::regex_lang(kernel.graph(), theta, id@, word)
                                        == source_regex(*template, index as nat, theta, word));
                                }
                                FlatRegex::Intersect(children) => {
                                    regex_set_transfer(kernel.graph(), *template, regexes@,
                                        children@, selected_ids, theta, word, true);
                                    assert(model::regex_lang(kernel.graph(), theta, id@, word)
                                        == source_regex(*template, index as nat, theta, word));
                                }
                                FlatRegex::Complement(child) => {
                                    assert((*child as nat) < regexes@.len());
                                    assert(regex_correct(kernel.graph(), *template, *child as nat,
                                        regexes@[*child as int]));
                                    assert(template.regexes@[index as int] == FlatRegex::Complement(*child));
                                    assert(source_regex(*template, index as nat, theta, word)
                                        == ((*child as nat) < index && !source_regex(*template, *child as nat, theta, word)));
                                    assert(model::regex_lang(kernel.graph(), theta, id@, word)
                                        == !model::regex_lang(kernel.graph(), theta, regexes@[*child as int]@, word));
                                    assert(model::regex_lang(kernel.graph(), theta, id@, word)
                                        == source_regex(*template, index as nat, theta, word));
                                }
                                FlatRegex::Empty | FlatRegex::All | FlatRegex::Epsilon => {
                                    assert(model::regex_lang(kernel.graph(), theta, id@, word)
                                        == source_regex(*template, index as nat, theta, word));
                                }
                            }
                        }
                    }
                    match regex {
                        FlatRegex::Empty | FlatRegex::All | FlatRegex::Epsilon => {
                            crate::verify::finite_compile::lemma_regex_const_nf(kernel.graph(), id@);
                        }
                        FlatRegex::Test(test) => {
                            crate::verify::finite_compile::lemma_from_test_nf(before, kernel.graph(), tests@, regexes@, *test as int, id@);
                        }
                        FlatRegex::Concat(children) => {
                            crate::verify::finite_compile::lemma_concat_nf(before, kernel.graph(), tests@, regexes@, children@, selected_ids, id@);
                        }
                        FlatRegex::Union(children) => {
                            crate::verify::finite_compile::lemma_set_nf(before, kernel.graph(), tests@, regexes@, children@, selected_ids, false, id@);
                        }
                        FlatRegex::Intersect(children) => {
                            crate::verify::finite_compile::lemma_set_nf(before, kernel.graph(), tests@, regexes@, children@, selected_ids, true, id@);
                        }
                        FlatRegex::Star(child) => {
                            crate::verify::finite_compile::lemma_compiled_regex(before, tests@, regexes@, *child as int);
                        }
                        FlatRegex::Complement(child) => {
                            crate::verify::finite_compile::lemma_not_nf(before, kernel.graph(), tests@, regexes@, *child as int, id@);
                        }
                    }
                    lemma_vocabulary_stable(before, kernel.graph(), *template, tests@, regexes@);
                    lemma_regex_vocabulary(before, kernel.graph(), *template, tests@, regexes@, *regex, selected_ids, id@);
                    assert(regexes_vocabulary(kernel.graph(), *template, regexes@.push(id))) by {
                        assert forall|i: int| 0 <= i < regexes@.push(id).len() implies regexes@.push(id)[i]@ < kernel.graph().regexes.len()
                            && vocab::regex_primitives(model::lift_regex(kernel.graph(), regexes@.push(id)[i]@)).subset_of(source_primitives(*template)) by {
                            if i < regexes@.len() { assert(regexes@.push(id)[i] == regexes@[i]); }
                            else { assert(regexes@.push(id)[i] == id); }
                        }
                    }
                    crate::verify::finite_compile::lemma_push_regex(before, kernel.graph(), tests@, regexes@, id);
                    regex_push(kernel.graph(), *template, regexes@, id);
                }
                regexes.push(id);
                index = index.saturating_add(1);
            }
            proof! {
                assert(kernel.valid_store());
                assert(model::graph_wf(kernel.graph()));
                assert(regex_maps(kernel.graph(), *template, regexes@));
                assert(crate::verify::finite_compile::compiled_nf(kernel.graph(), tests@, regexes@));
                assert(regexes_vocabulary(kernel.graph(), *template, regexes@));
            }
        }
        proof! {
            assert(store.valid_store());
            assert(model::graph_wf(store.graph()));
            assert(regex_maps(store.graph(), *template, regexes@));
            assert(crate::verify::finite_compile::compiled_nf(store.graph(), tests@, regexes@));
        }
        let root = Self::lookup(&regexes, template.root)?;
        limits.checkpoint().map_err(HistoryError::from)?;
        proof! {
            assert(model::graph_wf(store.graph()));
            assert(regex_correct(store.graph(), *template, template.root as nat, root));
            crate::verify::finite_compile::lemma_compiled_regex(store.graph(), tests@, regexes@, template.root as int);
            assert(vocab::regex_primitives(model::lift_regex(store.graph(), root@)).subset_of(source_primitives(*template)));
        }
        Ok(CompiledPair::new(store, root))
    }
    /// The hot boundary checks coordinate bounds, then performs u64 equality and a checkpoint.
    #[allow(
        clippy::shadow_unrelated,
        reason = "Term fields mirror the matched Verus model variants"
    )]
    #[verus_verify]
    #[verus_spec(result => ensures
        result != Err(HistoryError::WrongHistoryOwner),
        language::no_invariant_failure(result),
        !(result matches Err(HistoryError::InvalidPolicy { .. })),
        result matches Err(error) ==> resource_error(error),
        result matches Ok(answer) ==> answer == model::primitive_holds(bindings@, primitive@, event@))]

    pub(crate) fn classify<L: Limits>(
        primitive: Primitive,
        event: &NumericEvent,
        bindings: &Bindings,
        limits: &mut L,
        _world: &mut ObservationWorld,
    ) -> KernelResult<bool> {
        limits.checkpoint().map_err(HistoryError::from)?;
        let Primitive::Eq { field, term } = primitive;
        let index = field.index();
        if index >= event.arity() {
            return Ok(false);
        }
        let left = event.component(index);
        // Variables read the request substitution, not another history-event coordinate.
        let right = match term {
            Term::Constant(value) => value,
            Term::Variable(field) => {
                let index = field.index();
                if index >= bindings.arity() {
                    return Ok(false);
                }
                bindings.get(index)
            }
        };
        Ok(left == right)
    }
}

#[cfg(verus_keep_ghost)]
pub mod verify {
    use super::*;
    pub use super::{bindings_match, head_rejects};
    pub(crate) use super::{lemma_bindings_match, lemma_head_rejects};
    use junco_core::verify::history_specs::{EventView, Subst};
    verus! {
    broadcast use {junco_core::kernel::verify::group_kernel_views, vstd::set::group_set_lemmas};
    /// Test references must point to earlier nodes; atoms need no head bindings
    /// for compilation into a symbolic graph.
    pub open spec fn source_test_dag(test: FlatTest<u64>, index: nat) -> bool {
        match test {
            FlatTest::And(children) | FlatTest::Or(children) =>
                flat::references_before(children@, index),
            _ => true,
        }
    }

    /// Reference well-formedness sufficient for compiling a numeric source DAG.
    pub open spec fn source_dag_wf(template: FlatPair<u64>) -> bool {
        template.root < template.regexes@.len()
        && (forall|i: int| 0 <= i < template.tests@.len() ==>
            source_test_dag(#[trigger] template.tests@[i], i as nat))
        && (forall|i: int| 0 <= i < template.regexes@.len() ==>
            flat::regex_wf(#[trigger] template.regexes@[i], i as nat, template.tests@.len()))
    }

    pub proof fn lemma_structural_source_dag(template: FlatPair<u64>)
        requires flat::structural_wf(template),
        ensures source_dag_wf(template),
    {
        reveal(flat::structural_wf);
        reveal(flat::prefix_wf);
        assert forall|i: int| 0 <= i < template.tests@.len() implies
            source_test_dag(template.tests@[i], i as nat) by {
            assert(flat::test_wf(template.head@, template.tests@[i], i as nat));
            reveal(flat::test_wf);
        }
    }

    #[verifier::opaque]
    pub open spec fn source_primitive_prefix(template: FlatPair<u64>, n: nat) -> Set<model::Primitive>
        decreases n,
    {
        if 0 < n <= template.tests@.len() {
            let prior = source_primitive_prefix(template, (n - 1) as nat);
            match template.tests@[n - 1] {
                FlatTest::Atom { field, term, .. } => prior.insert(model::Primitive::Eq(field, term_view(term))),
                _ => prior,
            }
        } else { Set::empty() }
    }

    pub open spec fn source_primitives(template: FlatPair<u64>) -> Set<model::Primitive> {
        source_primitive_prefix(template, template.tests@.len())
    }

    pub open spec fn source_codes(template: FlatPair<u64>, field: Component) -> Set<nat> {
        crate::symbolic_language::verify::primitive_codes(source_primitives(template), field)
    }

    pub proof fn lemma_source_code_member(template: FlatPair<u64>, field: Component, value: nat)
        requires source_codes(template, field).contains(value),
        ensures exists|i: int| #![trigger template.tests@[i]] 0 <= i < template.tests@.len()
            && match template.tests@[i] {
                FlatTest::Atom { field: f, term: FlatTerm::Constant(v), .. } => f == field && v as nat == value,
                _ => false,
            },
    {
        crate::symbolic_language::verify::lemma_primitive_codes_contains(source_primitives(template), field, value);
        let p = model::Primitive::Eq(field, model::GTerm::Constant(value));
        lemma_source_primitive_prefix(template, template.tests@.len(), p);
        let i = choose|i: int| #![trigger template.tests@[i]] 0 <= i < template.tests@.len() && match template.tests@[i] {
            FlatTest::Atom { field: f, term, .. } => p == model::Primitive::Eq(f, term_view(term)), _ => false,
        };
        assert(match template.tests@[i] {
            FlatTest::Atom { field: f, term: FlatTerm::Constant(v), .. } => f == field && v as nat == value,
            _ => false,
        });
    }

    pub proof fn lemma_source_codes_bounded(template: FlatPair<u64>, field: Component, bound: nat)
        requires forall|i: int| #![trigger template.tests@[i]] 0 <= i < template.tests@.len() ==> match template.tests@[i] {
            FlatTest::Atom { field: f, term: FlatTerm::Constant(v), .. } => f != field || v as nat <= bound,
            _ => true,
        },
        ensures forall|value: nat| source_codes(template, field).contains(value) ==> value <= bound,
    {
        assert forall|value: nat| source_codes(template, field).contains(value) implies value <= bound by {
            lemma_source_code_member(template, field, value);
            let i = choose|i: int| #![trigger template.tests@[i]] 0 <= i < template.tests@.len() && match template.tests@[i] {
                FlatTest::Atom { field: f, term: FlatTerm::Constant(v), .. } => f == field && v as nat == value,
                _ => false,
            };
        }
    }

    pub proof fn lemma_source_primitive_prefix(template: FlatPair<u64>, n: nat, p: model::Primitive)
        requires n <= template.tests@.len(),
        ensures source_primitive_prefix(template, n).contains(p) == (exists|i: int| #![trigger template.tests@[i]]
            0 <= i < n && match template.tests@[i] {
                FlatTest::Atom { field, term, .. } => p == model::Primitive::Eq(field, term_view(term)),
                _ => false,
            }),
        decreases n,
    {
        reveal_with_fuel(source_primitive_prefix, 1);
        if n > 0 {
            lemma_source_primitive_prefix(template, (n - 1) as nat, p);
            if exists|i: int| #![trigger template.tests@[i]] 0 <= i < n && match template.tests@[i] {
                FlatTest::Atom { field, term, .. } => p == model::Primitive::Eq(field, term_view(term)), _ => false,
            } {
                let i = choose|i: int| #![trigger template.tests@[i]] 0 <= i < n && match template.tests@[i] {
                    FlatTest::Atom { field, term, .. } => p == model::Primitive::Eq(field, term_view(term)), _ => false,
                };
                if i < n - 1 {
                    assert(exists|j: int| #![trigger template.tests@[j]] 0 <= j < n - 1 && match template.tests@[j] {
                        FlatTest::Atom { field, term, .. } => p == model::Primitive::Eq(field, term_view(term)), _ => false,
                    });
                } else { assert(i == n - 1); }
            }
            if source_primitive_prefix(template, (n - 1) as nat).contains(p) {
                let i = choose|i: int| #![trigger template.tests@[i]] 0 <= i < n - 1 && match template.tests@[i] {
                    FlatTest::Atom { field, term, .. } => p == model::Primitive::Eq(field, term_view(term)), _ => false,
                };
                assert(exists|j: int| #![trigger template.tests@[j]] 0 <= j < n && match template.tests@[j] {
                    FlatTest::Atom { field, term, .. } => p == model::Primitive::Eq(field, term_view(term)), _ => false,
                });
            }
        }
    }

    pub(crate) open spec fn tests_vocabulary(g: model::Graph, template: FlatPair<u64>, ids: Seq<TestId>) -> bool {
        forall|i: int| 0 <= i < ids.len() ==> ids[i]@ < g.tests.len()
            && (#[trigger] vocab::test_primitives(model::lift_test(g, ids[i]@))).subset_of(source_primitives(template))
    }

    pub(crate) open spec fn regexes_vocabulary(g: model::Graph, template: FlatPair<u64>, ids: Seq<RegexId>) -> bool {
        forall|i: int| 0 <= i < ids.len() ==> ids[i]@ < g.regexes.len()
            && (#[trigger] vocab::regex_primitives(model::lift_regex(g, ids[i]@))).subset_of(source_primitives(template))
    }

    pub(crate) proof fn lemma_vocabulary_stable(a: model::Graph, b: model::Graph, template: FlatPair<u64>, tests: Seq<TestId>, regexes: Seq<RegexId>)
        requires model::graph_wf(a), model::graph_extends(a, b), tests_vocabulary(a, template, tests), regexes_vocabulary(a, template, regexes),
        ensures tests_vocabulary(b, template, tests), regexes_vocabulary(b, template, regexes),
    {
        model::lemma_graph_wf_elim(a);
        assert forall|i: int| 0 <= i < tests.len() implies tests[i]@ < b.tests.len()
            && vocab::test_primitives(model::lift_test(b, tests[i]@)).subset_of(source_primitives(template)) by {
            assert(vocab::test_primitives(model::lift_test(a, tests[i]@)).subset_of(source_primitives(template)));
            model::lemma_lift_test_stable(a, b, tests[i]@);
        }
        assert forall|i: int| 0 <= i < regexes.len() implies regexes[i]@ < b.regexes.len()
            && vocab::regex_primitives(model::lift_regex(b, regexes[i]@)).subset_of(source_primitives(template)) by {
            assert(vocab::regex_primitives(model::lift_regex(a, regexes[i]@)).subset_of(source_primitives(template)));
            model::lemma_lift_regex_stable(a, b, regexes[i]@);
        }
    }

    pub(crate) proof fn lemma_selected_regexes_vocabulary(g: model::Graph, template: FlatPair<u64>, ids: Seq<RegexId>, children: Seq<u32>, selected: Seq<RegexId>)
        requires regexes_vocabulary(g, template, ids), selected.len() == children.len(),
            forall|i: int| 0 <= i < children.len() ==> #[trigger] children[i] < ids.len() && selected[i] == ids[children[i] as int],
        ensures norm::regex_ids_valid(g, selected),
            forall|i: int| 0 <= i < selected.len() ==> vocab::regex_primitives(model::lift_regex(g, selected[i]@)).subset_of(source_primitives(template)),
            forall|r: language::Regex<model::Test>| crate::verify::finite_link::lift_set(g, selected).contains(r) ==> vocab::regex_primitives(r).subset_of(source_primitives(template)),
    {
        assert forall|i: int| 0 <= i < selected.len() implies selected[i]@ < g.regexes.len()
            && vocab::regex_primitives(model::lift_regex(g, selected[i]@)).subset_of(source_primitives(template)) by {
            assert(selected[i] == ids[children[i] as int]);
            assert(vocab::regex_primitives(model::lift_regex(g, ids[children[i] as int]@)).subset_of(source_primitives(template)));
        }
        let rs = crate::verify::finite_link::lifts(g, selected);
        rs.to_set_ensures();
        assert forall|r: language::Regex<model::Test>| rs.to_set().contains(r) implies vocab::regex_primitives(r).subset_of(source_primitives(template)) by {
            let i = rs.lemma_contains_to_index(r);
            assert(rs[i] == model::lift_regex(g, selected[i]@));
        }
    }

    pub(crate) proof fn lemma_concat_vocabulary(a: model::Graph, b: model::Graph, template: FlatPair<u64>, ids: Seq<RegexId>, children: Seq<u32>, selected: Seq<RegexId>, out: nat)
        requires model::graph_wf(a), model::graph_wf(b), model::graph_extends(a, b),
            regexes_vocabulary(a, template, ids), selected.len() == children.len(),
            forall|i: int| 0 <= i < children.len() ==> #[trigger] children[i] < ids.len() && selected[i] == ids[children[i] as int],
            out < b.regexes.len(), norm::regex_concat_result(a, b, selected, out),
        ensures vocab::regex_primitives(model::lift_regex(b, out)).subset_of(source_primitives(template)),
    {
        lemma_selected_regexes_vocabulary(a, template, ids, children, selected);
        crate::verify::finite_link::lemma_concat_link(a, b, selected, out);
        vocab::lemma_cat_vocab(crate::verify::finite_link::lifts(a, selected), source_primitives(template));
    }

    pub(crate) proof fn lemma_set_vocabulary(a: model::Graph, b: model::Graph, template: FlatPair<u64>, tests: Seq<TestId>, ids: Seq<RegexId>, children: Seq<u32>, selected: Seq<RegexId>, inter: bool, out: nat)
        requires model::graph_wf(a), model::graph_wf(b), model::graph_extends(a, b),
            crate::verify::finite_compile::compiled_nf(a, tests, ids), regexes_vocabulary(a, template, ids),
            selected.len() == children.len(),
            forall|i: int| 0 <= i < children.len() ==> #[trigger] children[i] < ids.len() && selected[i] == ids[children[i] as int],
            out < b.regexes.len(),
            norm::regex_set_flat_inputs(a, selected, inter) ==> norm::regex_set_shape(a, b, selected, inter, out),
        ensures vocab::regex_primitives(model::lift_regex(b, out)).subset_of(source_primitives(template)),
    {
        lemma_selected_regexes_vocabulary(a, template, ids, children, selected);
        crate::verify::finite_compile::lemma_selected_nf(a, tests, ids, children, selected);
        crate::verify::finite_link::lemma_flat_inputs(a, selected, inter);
        crate::verify::finite_link::lemma_set_link(a, b, selected, inter, out);
        vocab::lemma_nset_vocab(inter, crate::verify::finite_link::lift_set(a, selected), model::lift_regex(b, out), source_primitives(template));
    }

    pub(crate) open spec fn selected_regex_refs(ids: Seq<RegexId>, children: Seq<u32>, selected: Seq<RegexId>) -> bool {
        selected.len() == children.len() && forall|i: int| 0 <= i < children.len()
            ==> #[trigger] children[i] < ids.len() && selected[i] == ids[children[i] as int]
    }

    pub(crate) proof fn lemma_regex_vocabulary(a: model::Graph, b: model::Graph, template: FlatPair<u64>, tests: Seq<TestId>, ids: Seq<RegexId>, node: FlatRegex, selected: Seq<RegexId>, out: nat)
        requires model::graph_wf(a), model::graph_wf(b), model::graph_extends(a, b), out < b.regexes.len(),
            crate::verify::finite_compile::compiled_nf(a, tests, ids), tests_vocabulary(b, template, tests),
            regexes_vocabulary(a, template, ids), regexes_vocabulary(b, template, ids),
            match node {
                FlatRegex::Concat(children) | FlatRegex::Union(children) | FlatRegex::Intersect(children) =>
                    selected_regex_refs(ids, children@, selected),
                _ => true,
            },
            match node {
                FlatRegex::Empty => out == b.constants.empty,
                FlatRegex::All => out == b.constants.all,
                FlatRegex::Epsilon => out == b.constants.epsilon,
                FlatRegex::Test(t) => t < tests.len() && if tests[t as int]@ == b.constants.test_false {
                    out == b.constants.empty
                } else { b.regexes[out as int].kind == model::RegexKindNode::Test(tests[t as int]@) },
                FlatRegex::Concat(_) => norm::regex_concat_result(a, b, selected, out),
                FlatRegex::Union(_) => norm::regex_set_flat_inputs(a, selected, false) ==> norm::regex_set_shape(a, b, selected, false, out),
                FlatRegex::Intersect(_) => norm::regex_set_flat_inputs(a, selected, true) ==> norm::regex_set_shape(a, b, selected, true, out),
                FlatRegex::Complement(child) => child < ids.len() && norm::regex_not_result(b, ids[child as int]@, out),
                FlatRegex::Star(child) => child < ids.len() && vocab::regex_primitives(model::lift_regex(b, out)).subset_of(
                    vocab::regex_primitives(model::lift_regex(b, ids[child as int]@))),
            },
        ensures vocab::regex_primitives(model::lift_regex(b, out)).subset_of(source_primitives(template)),
    {
        norm::regex_constants(b);
        reveal_with_fuel(vocab::regex_primitives, 1);
        match node {
            FlatRegex::Empty | FlatRegex::All | FlatRegex::Epsilon => {
                norm::regex_unfold(b, out);
            },
            FlatRegex::Test(t) => {
                norm::regex_unfold(b, out);
                assert(vocab::test_primitives(model::lift_test(b, tests[t as int]@)).subset_of(source_primitives(template)));
            },
            FlatRegex::Star(child) => {
                assert(vocab::regex_primitives(model::lift_regex(b, ids[child as int]@)).subset_of(source_primitives(template)));
            },
            FlatRegex::Complement(child) => {
                crate::verify::finite_compile::lemma_compiled_regex(a, tests, ids, child as int);
                model::lemma_graph_wf_elim(a);
                model::lemma_lift_regex_stable(a, b, ids[child as int]@);
                crate::verify::finite_link::lemma_not_link(b, ids[child as int]@, out);
                vocab::lemma_not_vocab(model::lift_regex(b, ids[child as int]@));
                assert(vocab::regex_primitives(model::lift_regex(b, ids[child as int]@)).subset_of(source_primitives(template)));
            },
            FlatRegex::Concat(children) => lemma_concat_vocabulary(a, b, template, ids, children@, selected, out),
            FlatRegex::Union(children) => lemma_set_vocabulary(a, b, template, tests, ids, children@, selected, false, out),
            FlatRegex::Intersect(children) => lemma_set_vocabulary(a, b, template, tests, ids, children@, selected, true, out),
        }
    }

    pub open spec fn term_view(term: FlatTerm<u64>) -> model::GTerm {
        match term {
            FlatTerm::Constant(value) => model::GTerm::Constant(value as nat),
            FlatTerm::Variable(field) => model::GTerm::Variable(field),
        }
    }



    pub open spec fn head_view(template: FlatPair<u64>) -> language::Head {
        template.head@.map(|i: int, field: FlatHead<u64>| field@)
    }

    /// Independent interpretation of a cold numeric test table. The index guard
    /// makes this total even for malformed templates; executable lookup rejects
    /// those references rather than treating this default as a verdict.
    pub open spec fn source_test(template: FlatPair<u64>, index: nat, theta: Subst, event: EventView) -> bool
        decreases index,
    {
        if index >= template.tests@.len() { false }
        else { match template.tests@[index as int] {
            FlatTest::Bool(value) => value,
            FlatTest::Atom { field, term, positive } =>
                model::primitive_holds(theta, model::Primitive::Eq(field, term_view(term)), event) == positive,
            FlatTest::And(children) => forall|i: int| 0 <= i < children@.len()
                ==> children@[i] < index && source_test(template, children@[i] as nat, theta, event),
            FlatTest::Or(children) => exists|i: int| 0 <= i < children@.len()
                && children@[i] < index && source_test(template, children@[i] as nat, theta, event),
        }}
    }

    /// Independent regex language over the template's postorder nodes.
    pub open spec fn source_regex(template: FlatPair<u64>, index: nat, theta: Subst, word: Seq<EventView>) -> bool
        decreases index,
    {
        if index >= template.regexes@.len() { false }
        else { match template.regexes@[index as int] {
            FlatRegex::Empty => false,
            FlatRegex::All => true,
            FlatRegex::Epsilon => word.len() == 0,
            FlatRegex::Test(test) => word.len() == 1 && source_test(template, test as nat, theta, word[0]),
            FlatRegex::Union(children) => exists|i: int| 0 <= i < children@.len()
                && children@[i] < index && source_regex(template, children@[i] as nat, theta, word),
            FlatRegex::Intersect(children) => forall|i: int| 0 <= i < children@.len()
                ==> children@[i] < index && source_regex(template, children@[i] as nat, theta, word),
            FlatRegex::Concat(children) => exists|parts: Seq<Seq<EventView>>|
                parts.len() == children@.len() && parts.flatten() == word
                && forall|i: int| 0 <= i < children@.len()
                    ==> children@[i] < index && source_regex(template, children@[i] as nat, theta, parts[i]),
            FlatRegex::Star(child) => child < index && exists|parts: Seq<Seq<EventView>>|
                parts.flatten() == word && forall|i: int| 0 <= i < parts.len()
                    ==> source_regex(template, child as nat, theta, parts[i]),
            FlatRegex::Complement(child) => child < index && !source_regex(template, child as nat, theta, word),
        }}
    }

    pub(crate) open(crate) spec fn test_correct(g: model::Graph, template: FlatPair<u64>, index: nat, id: TestId) -> bool {
        id@ < g.tests.len() && forall|theta: Subst, event: EventView| language::event_wf(theta, theta.len())
            ==> norm::test_truth(g, theta, id@, event) == source_test(template, index, theta, event)
    }

    pub(crate) open(crate) spec fn regex_correct(g: model::Graph, template: FlatPair<u64>, index: nat, id: RegexId) -> bool {
        id@ < g.regexes.len() && forall|theta: Subst, word: Seq<EventView>| language::event_wf(theta, theta.len())
            ==> model::regex_lang(g, theta, id@, word) == source_regex(template, index, theta, word)
    }

    pub(crate) open(crate) spec fn test_maps(g: model::Graph, template: FlatPair<u64>, ids: Seq<TestId>) -> bool {
        ids.len() <= template.tests@.len()
        && forall|i: int| 0 <= i < ids.len() ==> test_correct(g, template, i as nat, ids[i])
    }

    pub(crate) open(crate) spec fn regex_maps(g: model::Graph, template: FlatPair<u64>, ids: Seq<RegexId>) -> bool {
        ids.len() <= template.regexes@.len()
        && forall|i: int| 0 <= i < ids.len() ==> regex_correct(g, template, i as nat, ids[i])
    }

    pub(crate) proof fn maps_extend(before: model::Graph, after: model::Graph,
        template: FlatPair<u64>, tests: Seq<TestId>, regexes: Seq<RegexId>)
        requires model::graph_wf(before), model::graph_extends(before, after),
            test_maps(before, template, tests), regex_maps(before, template, regexes),
        ensures test_maps(after, template, tests), regex_maps(after, template, regexes),
    {
        model::lemma_graph_wf_elim(before);
        model::lemma_lift_stable_under_extends(before, after);
        assert forall|i: int| 0 <= i < tests.len() implies test_correct(after, template, i as nat, tests[i]) by {
            assert(test_correct(before, template, i as nat, tests[i]));
        }
        assert forall|i: int| 0 <= i < regexes.len() implies regex_correct(after, template, i as nat, regexes[i]) by {
            assert(regex_correct(before, template, i as nat, regexes[i]));
        }
    }

    pub(crate) proof fn test_push(g: model::Graph, template: FlatPair<u64>, tests: Seq<TestId>, id: TestId)
        requires test_maps(g, template, tests), tests.len() < template.tests@.len(),
            test_correct(g, template, tests.len(), id),
        ensures test_maps(g, template, tests.push(id)),
    {
        assert forall|i: int| 0 <= i < tests.push(id).len()
            implies test_correct(g, template, i as nat, tests.push(id)[i]) by {
            if i < tests.len() { assert(tests.push(id)[i] == tests[i]); }
            else { assert(i == tests.len()); }
        }
    }

    pub(crate) proof fn regex_push(g: model::Graph, template: FlatPair<u64>, regexes: Seq<RegexId>, id: RegexId)
        requires regex_maps(g, template, regexes), regexes.len() < template.regexes@.len(),
            regex_correct(g, template, regexes.len(), id),
        ensures regex_maps(g, template, regexes.push(id)),
    {
        assert forall|i: int| 0 <= i < regexes.push(id).len()
            implies regex_correct(g, template, i as nat, regexes.push(id)[i]) by {
            if i < regexes.len() { assert(regexes.push(id)[i] == regexes[i]); }
            else { assert(i == regexes.len()); }
        }
    }

    pub(crate) proof fn selected_tests_valid(g: model::Graph, template: FlatPair<u64>,
        ids: Seq<TestId>, children: Seq<u32>, selected: Seq<TestId>)
        requires test_maps(g, template, ids), selected.len() == children.len(),
            forall|i: int| 0 <= i < children.len()
                ==> #[trigger] children[i] < ids.len() && selected[i] == ids[children[i] as int],
        ensures norm::test_ids_valid(g, selected),
    {
        assert forall|i: int| 0 <= i < selected.len() implies selected[i]@ < g.tests.len() by {
            assert(children[i] < ids.len());
            assert(test_correct(g, template, children[i] as nat, ids[children[i] as int]));
        }
    }

    pub(crate) proof fn selected_regexes_valid(g: model::Graph, template: FlatPair<u64>,
        ids: Seq<RegexId>, children: Seq<u32>, selected: Seq<RegexId>)
        requires regex_maps(g, template, ids), selected.len() == children.len(),
            forall|i: int| 0 <= i < children.len()
                ==> #[trigger] children[i] < ids.len() && selected[i] == ids[children[i] as int],
        ensures norm::regex_ids_valid(g, selected),
    {
        assert forall|i: int| 0 <= i < selected.len() implies selected[i]@ < g.regexes.len() by {
            assert(children[i] < ids.len());
            assert(regex_correct(g, template, children[i] as nat, ids[children[i] as int]));
        }
    }

    pub(crate) proof fn test_connective_transfer(g: model::Graph, template: FlatPair<u64>,
        ids: Seq<TestId>, children: Seq<u32>, selected: Seq<TestId>,
        theta: Subst, event: EventView, and: bool)
        requires test_maps(g, template, ids), language::event_wf(theta, theta.len()),
            selected.len() == children.len(),
            forall|i: int| 0 <= i < children.len()
                ==> #[trigger] children[i] < ids.len() && selected[i] == ids[children[i] as int],
        ensures norm::test_combo(g, theta, selected, event, and)
            == if and {
                forall|i: int| 0 <= i < children.len()
                    ==> children[i] < ids.len() && source_test(template, children[i] as nat, theta, event)
            } else {
                exists|i: int| 0 <= i < children.len()
                    && children[i] < ids.len() && source_test(template, children[i] as nat, theta, event)
            },
    {
        reveal(norm::test_combo);
        assert forall|i: int| 0 <= i < children.len() implies
            #[trigger] model::test_holds(theta, model::lift_test(g, selected[i]@), event)
                == (children[i] < ids.len() && source_test(template, children[i] as nat, theta, event)) by {
            assert(children[i] < ids.len());
            assert(test_correct(g, template, children[i] as nat, ids[children[i] as int]));
        }
        norm::lemma_combo_pointwise(children.len(),
            |i: int| model::test_holds(theta, model::lift_test(g, selected[i]@), event),
            |i: int| children[i] < ids.len() && source_test(template, children[i] as nat, theta, event), and);
    }

    pub(crate) proof fn regex_set_transfer(g: model::Graph, template: FlatPair<u64>,
        ids: Seq<RegexId>, children: Seq<u32>, selected: Seq<RegexId>,
        theta: Subst, word: Seq<EventView>, intersect: bool)
        requires regex_maps(g, template, ids), language::event_wf(theta, theta.len()),
            selected.len() == children.len(),
            forall|i: int| 0 <= i < children.len()
                ==> #[trigger] children[i] < ids.len() && selected[i] == ids[children[i] as int],
        ensures norm::regex_combo(g, theta, selected, word, intersect)
            == if intersect {
                forall|i: int| 0 <= i < children.len()
                    ==> children[i] < ids.len() && source_regex(template, children[i] as nat, theta, word)
            } else {
                exists|i: int| 0 <= i < children.len()
                    && children[i] < ids.len() && source_regex(template, children[i] as nat, theta, word)
            },
    {
        reveal(norm::regex_combo);
        assert forall|i: int| 0 <= i < children.len() implies
            #[trigger] model::regex_lang(g, theta, selected[i]@, word)
                == (children[i] < ids.len() && source_regex(template, children[i] as nat, theta, word)) by {
            assert(children[i] < ids.len());
            assert(regex_correct(g, template, children[i] as nat, ids[children[i] as int]));
        }
        norm::lemma_combo_pointwise(children.len(),
            |i: int| model::regex_lang(g, theta, selected[i]@, word),
            |i: int| children[i] < ids.len() && source_regex(template, children[i] as nat, theta, word), intersect);
    }

    pub(crate) proof fn regex_concat_transfer(g: model::Graph, template: FlatPair<u64>,
        ids: Seq<RegexId>, children: Seq<u32>, index: nat, theta: Subst, word: Seq<EventView>)
        requires regex_maps(g, template, ids), ids.len() == index, language::event_wf(theta, theta.len()),
            forall|i: int| 0 <= i < children.len() ==> children[i] < ids.len(),
        ensures norm::concat_combo(g, theta,
            Seq::new(children.len(), |i: int| ids[children[i] as int]), word)
            == (exists|parts: Seq<Seq<EventView>>| parts.len() == children.len() && parts.flatten() == word
                && forall|i: int| 0 <= i < children.len()
                    ==> children[i] < index && source_regex(template, children[i] as nat, theta, parts[i])),
    {
        let selected = Seq::new(children.len(), |i: int| ids[children[i] as int]);
        let lifted = model::lift_regexes(g, model::regex_ids(selected));
        assert(lifted.len() == children.len());
        assert forall|i: int, piece: Seq<EventView>| 0 <= i < children.len() implies
            language::numeric_lang(model::gsem(theta), lifted[i], piece)
                == source_regex(template, children[i] as nat, theta, piece) by {
            assert(regex_correct(g, template, children[i] as nat, ids[children[i] as int]));
        }
        if norm::concat_combo(g, theta, selected, word) {
            let parts = choose|parts: Seq<Seq<EventView>>| parts.len() == lifted.len() && word == parts.flatten()
                && forall|i: int| 0 <= i < lifted.len()
                    ==> language::numeric_lang(model::gsem(theta), lifted[i], parts[i]);
            assert forall|i: int| 0 <= i < children.len() implies children[i] < index
                && source_regex(template, children[i] as nat, theta, parts[i]) by {}
            assert(exists|parts: Seq<Seq<EventView>>| parts.len() == children.len() && parts.flatten() == word
                && forall|i: int| 0 <= i < children.len()
                    ==> children[i] < index && source_regex(template, children[i] as nat, theta, parts[i]));
        }
        if exists|parts: Seq<Seq<EventView>>| parts.len() == children.len() && parts.flatten() == word
            && forall|i: int| 0 <= i < children.len()
                ==> children[i] < index && source_regex(template, children[i] as nat, theta, parts[i]) {
            let parts = choose|parts: Seq<Seq<EventView>>| parts.len() == children.len() && parts.flatten() == word
                && forall|i: int| 0 <= i < children.len()
                    ==> children[i] < index && source_regex(template, children[i] as nat, theta, parts[i]);
            assert forall|i: int| 0 <= i < lifted.len() implies
                language::numeric_lang(model::gsem(theta), lifted[i], parts[i]) by {}
            assert(norm::concat_combo(g, theta, selected, word));
        }
    }

    pub(crate) proof fn regex_star_transfer(g: model::Graph, template: FlatPair<u64>,
        ids: Seq<RegexId>, child: nat, theta: Subst, word: Seq<EventView>)
        requires regex_maps(g, template, ids), child < ids.len(), language::event_wf(theta, theta.len()),
        ensures language::numeric_lang(model::gsem(theta), language::Regex::Star(
            alloc::boxed::Box::new(model::lift_regex(g, ids[child as int]@))), word)
            == (exists|parts: Seq<Seq<EventView>>| parts.flatten() == word
                && forall|i: int| 0 <= i < parts.len() ==> source_regex(template, child, theta, parts[i])),
    {
        let regex = model::lift_regex(g, ids[child as int]@);
        assert(regex_correct(g, template, child, ids[child as int]));
        if language::numeric_lang(model::gsem(theta), language::Regex::Star(alloc::boxed::Box::new(regex)), word) {
            let parts = choose|parts: Seq<Seq<EventView>>| word == parts.flatten()
                && forall|i: int| 0 <= i < parts.len() ==> language::numeric_lang(model::gsem(theta), regex, parts[i]);
            assert forall|i: int| 0 <= i < parts.len() implies source_regex(template, child, theta, parts[i]) by {}
            assert(exists|parts: Seq<Seq<EventView>>| parts.flatten() == word
                && forall|i: int| 0 <= i < parts.len() ==> source_regex(template, child, theta, parts[i]));
        }
        if exists|parts: Seq<Seq<EventView>>| parts.flatten() == word
            && forall|i: int| 0 <= i < parts.len() ==> source_regex(template, child, theta, parts[i]) {
            let parts = choose|parts: Seq<Seq<EventView>>| parts.flatten() == word
                && forall|i: int| 0 <= i < parts.len() ==> source_regex(template, child, theta, parts[i]);
            assert forall|i: int| 0 <= i < parts.len() implies language::numeric_lang(model::gsem(theta), regex, parts[i]) by {}
            assert(language::numeric_lang(model::gsem(theta), language::Regex::Star(alloc::boxed::Box::new(regex)), word));
        }
    }

    use junco_core::flat::verify as portable;
    use junco_core::verify::encoding::{numeric_equality, pointwise, lemma_partition_lift, event_representation, event_relation, word_representation};

    /// Portable head matching and the numeric substitution agree coordinate by coordinate.
    pub proof fn lemma_flat_head(template: FlatPair<u64>, candidate: Seq<u64>, request: EventView)
        requires event_representation(candidate, request), 1 <= template.head@.len() <= MAX_ARITY,
        ensures portable::head_matches(template.head@, candidate, numeric_equality())
            == exists|theta: Subst| language::head_match(head_view(template), request, theta),
    {
        let theta = language::head_bindings(head_view(template), request);
        if portable::head_matches(template.head@, candidate, numeric_equality()) {
            assert forall|i: int| 0 <= i < template.head@.len() implies
                language::head_field_match(head_view(template)[i], request[i], theta[i]) by {
                assert(candidate[i] as nat == request[i]);
                assert(match template.head@[i] {
                    FlatHead::Constant(value) => candidate[i] == value, _ => true,
                });
            }
            assert(language::head_match(head_view(template), request, theta));
        }
        if exists|theta: Subst| language::head_match(head_view(template), request, theta) {
            let witness = choose|theta: Subst| language::head_match(head_view(template), request, theta);
            assert forall|i: int| 0 <= i < template.head@.len() implies match #[trigger] template.head@[i] {
                FlatHead::Constant(value) => candidate[i] == value,
                _ => true,
            } by {
                assert(language::head_field_match(head_view(template)[i], request[i], witness[i]));
                assert(candidate[i] as nat == request[i]);
            }
        }
    }

    pub proof fn lemma_flat_test(template: FlatPair<u64>, id: nat, candidate: Seq<u64>, request: EventView,
        event: Seq<u64>, numeric: EventView, theta: Subst)
        requires portable::structural_wf(template), id < template.tests@.len(),
            event_representation(candidate, request), event_representation(event, numeric),
            event.len() == candidate.len(),
            language::head_match(head_view(template), request, theta),
        ensures portable::test_sem(template.tests@, id, candidate, event, numeric_equality())
            == source_test(template, id, theta, numeric),
        decreases id,
    {
        reveal_with_fuel(portable::test_sem, 1);
        reveal_with_fuel(source_test, 1);
        assert(portable::test_wf(template.head@, template.tests@[id as int], id));
        match template.tests@[id as int] {
            FlatTest::Atom { field, term, positive } => {
                assert(0 <= portable::field_index(field) < template.head@.len());
                assert(language::field_value(numeric, field) == event[portable::field_index(field)] as nat);
                if let FlatTerm::Variable(variable) = term {
                    assert(field == variable);
                    assert(template.head@[portable::field_index(variable)] is Bind);
                    assert(language::head_field_match(head_view(template)[portable::field_index(variable)],
                        request[portable::field_index(variable)], theta[portable::field_index(variable)]));
                    assert(language::field_value(theta, variable) == candidate[portable::field_index(variable)] as nat);
                }
            },
            FlatTest::And(children) | FlatTest::Or(children) => {
                assert(portable::references_before(children@, id));
                assert forall|i: int| 0 <= i < children@.len() implies
                    portable::test_sem(template.tests@, children@[i] as nat, candidate, event, numeric_equality())
                        == source_test(template, children@[i] as nat, theta, numeric) by {
                    lemma_flat_test(template, children@[i] as nat, candidate, request, event, numeric, theta);
                }
            },
            _ => {},
        }
    }

    /// This bridge composes the portable encoding theorem with the actual graph compiler.
    pub proof fn lemma_flat_regex(template: FlatPair<u64>, id: nat, candidate: Seq<u64>, request: EventView,
        word: Seq<Seq<u64>>, numeric: Seq<EventView>, theta: Subst)
        requires portable::structural_wf(template), id < template.regexes@.len(),
            event_representation(candidate, request), word_representation(word, numeric),
            forall|i: int| 0 <= i < word.len() ==> word[i].len() == candidate.len(),
            language::head_match(head_view(template), request, theta),
        ensures portable::flat_lang(template.tests@, template.regexes@, id, candidate, word, numeric_equality())
            == source_regex(template, id, theta, numeric),
        decreases id,
    {
        reveal_with_fuel(portable::flat_lang, 1);
        reveal_with_fuel(source_regex, 1);
        assert(portable::regex_wf(template.regexes@[id as int], id, template.tests@.len()));
        assert forall|i: int| 0 <= i < word.len() implies portable::event_wf(word[i], candidate.len()) by {
            assert(event_representation(word[i], numeric[i]));
        }
        match template.regexes@[id as int] {
            FlatRegex::Test(test) => {
                if word.len() == 1 {
                    lemma_flat_test(template, test as nat, candidate, request, word[0], numeric[0], theta);
                }
            },
            FlatRegex::Union(children) | FlatRegex::Intersect(children) => {
                assert(portable::references_before(children@, id));
                assert forall|i: int| 0 <= i < children@.len() implies
                    portable::flat_lang(template.tests@, template.regexes@, children@[i] as nat, candidate, word, numeric_equality())
                        == source_regex(template, children@[i] as nat, theta, numeric) by {
                    lemma_flat_regex(template, children@[i] as nat, candidate, request, word, numeric, theta);
                }
            },
            FlatRegex::Concat(children) => {
                if portable::flat_lang(template.tests@, template.regexes@, id, candidate, word, numeric_equality()) {
                    let parts = choose|parts: Seq<Seq<Seq<u64>>>| parts.len() == children@.len() && word == parts.flatten()
                        && (forall|i: int| 0 <= i < parts.len() ==> portable::flat_lang(template.tests@, template.regexes@, children@[i] as nat, candidate, parts[i], numeric_equality()));
                    junco_core::verify::flatten::lemma_partition_arity(parts, candidate.len());
                    let reverse = |n: EventView, e: Seq<u64>| event_representation(e, n);
                    assert(pointwise(numeric, word, reverse));
                    lemma_partition_lift(numeric, word, parts, reverse);
                    let lifted = choose|lifted: Seq<Seq<EventView>>| lifted.len() == parts.len()
                        && numeric == lifted.flatten()
                        && forall|i: int| 0 <= i < parts.len() ==> pointwise(lifted[i], parts[i], reverse);
                    assert forall|i: int| 0 <= i < parts.len() implies
                        source_regex(template, children@[i] as nat, theta, lifted[i]) by {
                        assert(word_representation(parts[i], lifted[i]));
                        lemma_flat_regex(template, children@[i] as nat, candidate, request, parts[i], lifted[i], theta);
                    }
                    assert(source_regex(template, id, theta, numeric));
                }
                if source_regex(template, id, theta, numeric) {
                    let parts = choose|parts: Seq<Seq<EventView>>| parts.len() == children@.len() && numeric == parts.flatten()
                        && (forall|i: int| 0 <= i < parts.len() ==> source_regex(template, children@[i] as nat, theta, parts[i]));
                    lemma_partition_lift(word, numeric, parts, event_relation());
                    let lifted = choose|lifted: Seq<Seq<Seq<u64>>>| lifted.len() == parts.len()
                        && word == lifted.flatten()
                        && forall|i: int| 0 <= i < parts.len() ==> pointwise(lifted[i], parts[i], event_relation());
                    junco_core::verify::flatten::lemma_partition_arity(lifted, candidate.len());
                    assert forall|i: int| 0 <= i < parts.len() implies
                        portable::flat_lang(template.tests@, template.regexes@, children@[i] as nat, candidate, lifted[i], numeric_equality()) by {
                        lemma_flat_regex(template, children@[i] as nat, candidate, request, lifted[i], parts[i], theta);
                    }
                    assert(portable::flat_lang(template.tests@, template.regexes@, id, candidate, word, numeric_equality()));
                }
            },
            FlatRegex::Star(child) => {
                if portable::flat_lang(template.tests@, template.regexes@, id, candidate, word, numeric_equality()) {
                    let parts = choose|parts: Seq<Seq<Seq<u64>>>| word == parts.flatten()
                        && (forall|i: int| 0 <= i < parts.len() ==> portable::flat_lang(template.tests@, template.regexes@, child as nat, candidate, parts[i], numeric_equality()));
                    junco_core::verify::flatten::lemma_partition_arity(parts, candidate.len());
                    let reverse = |n: EventView, e: Seq<u64>| event_representation(e, n);
                    assert(pointwise(numeric, word, reverse));
                    lemma_partition_lift(numeric, word, parts, reverse);
                    let lifted = choose|lifted: Seq<Seq<EventView>>| lifted.len() == parts.len()
                        && numeric == lifted.flatten()
                        && forall|i: int| 0 <= i < parts.len() ==> pointwise(lifted[i], parts[i], reverse);
                    assert forall|i: int| 0 <= i < parts.len() implies
                        source_regex(template, child as nat, theta, lifted[i]) by {
                        assert(word_representation(parts[i], lifted[i]));
                        lemma_flat_regex(template, child as nat, candidate, request, parts[i], lifted[i], theta);
                    }
                    assert(source_regex(template, id, theta, numeric));
                }
                if source_regex(template, id, theta, numeric) {
                    let parts = choose|parts: Seq<Seq<EventView>>| numeric == parts.flatten()
                        && (forall|i: int| 0 <= i < parts.len() ==> source_regex(template, child as nat, theta, parts[i]));
                    lemma_partition_lift(word, numeric, parts, event_relation());
                    let lifted = choose|lifted: Seq<Seq<Seq<u64>>>| lifted.len() == parts.len()
                        && word == lifted.flatten()
                        && forall|i: int| 0 <= i < parts.len() ==> pointwise(lifted[i], parts[i], event_relation());
                    junco_core::verify::flatten::lemma_partition_arity(lifted, candidate.len());
                    assert forall|i: int| 0 <= i < parts.len() implies
                        portable::flat_lang(template.tests@, template.regexes@, child as nat, candidate, lifted[i], numeric_equality()) by {
                        lemma_flat_regex(template, child as nat, candidate, request, lifted[i], parts[i], theta);
                    }
                    assert(portable::flat_lang(template.tests@, template.regexes@, id, candidate, word, numeric_equality()));
                }
            },
            FlatRegex::Complement(child) => {
                lemma_flat_regex(template, child as nat, candidate, request, word, numeric, theta);
            },
            _ => {},
        }
    }
    }
}

#[cfg(test)]
mod tests {
    #![allow(clippy::unwrap_used, clippy::indexing_slicing)]

    use super::*;
    use alloc::vec;
    use history_store::store::HistoryStore;
    use junco_core::limits::{MAX_GRAPH_BYTES, Unmetered};

    fn event(arity: usize, value: u8) -> NumericEvent {
        let store = HistoryStore::new(arity);
        let slots: Vec<_> = (0..arity)
            .map(|index| {
                store
                    .intern(
                        Component::new(index),
                        &[value],
                        &mut Unmetered,
                        &mut ObservationWorld,
                    )
                    .unwrap()
            })
            .collect();
        store.event(&slots).unwrap()
    }

    fn template(head: Vec<FlatHead<u64>>) -> FlatPair<u64> {
        FlatPair {
            head,
            tests: Vec::new(),
            regexes: vec![FlatRegex::All],
            root: 0,
        }
    }

    #[test]
    fn head_binding_checks_every_coordinate_and_exact_arity() {
        for arity in 1..=MAX_ARITY {
            let request = event(arity, 17);
            let other = event(arity, 18);
            let mut source = template(vec![FlatHead::Bind; arity]);
            let bound = RuleRuntime::bindings(&source, &request).unwrap();
            assert_eq!(bound.arity(), arity);
            for index in 0..arity {
                assert_eq!(bound.get(index), request.component(index));
                source.head[index] = FlatHead::Any;
                assert_eq!(
                    RuleRuntime::bindings(&source, &request).unwrap().get(index),
                    0
                );
                source.head[index] = FlatHead::Constant(request.component(index));
                assert_eq!(
                    RuleRuntime::bindings(&source, &request).unwrap().get(index),
                    0
                );
                source.head[index] = FlatHead::Constant(other.component(index));
                assert_eq!(RuleRuntime::bindings(&source, &request), None);
                source.head[index] = FlatHead::Bind;
            }
            let _ = source.head.pop();
            assert_eq!(RuleRuntime::bindings(&source, &request), None);
            source.head.extend([FlatHead::Bind, FlatHead::Bind]);
            assert_eq!(RuleRuntime::bindings(&source, &request), None);
        }
    }

    #[test]
    fn classification_checks_event_and_substitution_bounds() {
        for arity in 1..=MAX_ARITY {
            let request = event(arity, 19);
            let values: Vec<_> = (0..arity).map(|index| request.component(index)).collect();
            let bindings = Bindings::new(&values);
            for index in 0..arity {
                let field = Component::new(index);
                for term in [
                    Term::Constant(request.component(index)),
                    Term::Variable(field),
                ] {
                    assert_eq!(
                        CompiledPair::classify(
                            Primitive::Eq { field, term },
                            &request,
                            &bindings,
                            &mut Unmetered,
                            &mut ObservationWorld,
                        ),
                        Ok(true)
                    );
                }
                assert_eq!(
                    CompiledPair::classify(
                        Primitive::Eq {
                            field,
                            term: Term::Constant(0)
                        },
                        &request,
                        &bindings,
                        &mut Unmetered,
                        &mut ObservationWorld,
                    ),
                    Ok(false)
                );
                assert_eq!(
                    CompiledPair::classify(
                        Primitive::Eq {
                            field,
                            term: Term::Variable(field)
                        },
                        &request,
                        &Bindings::new(&[]),
                        &mut Unmetered,
                        &mut ObservationWorld,
                    ),
                    Ok(false)
                );
            }
            for invalid in [u8::try_from(arity).unwrap(), u8::MAX] {
                for primitive in [
                    Primitive::Eq {
                        field: Component(invalid),
                        term: Term::Constant(0),
                    },
                    Primitive::Eq {
                        field: Component(0),
                        term: Term::Variable(Component(invalid)),
                    },
                ] {
                    assert_eq!(
                        CompiledPair::classify(
                            primitive,
                            &request,
                            &bindings,
                            &mut Unmetered,
                            &mut ObservationWorld,
                        ),
                        Ok(false)
                    );
                }
            }
        }
    }

    #[test]
    fn invalid_numeric_primitives_are_false_before_polarity() {
        for arity in 1..=MAX_ARITY {
            let request = event(arity, 20);
            let bindings = Bindings::new(&vec![0; arity]);
            for (field, term) in [
                (Component(u8::MAX), FlatTerm::Constant(0)),
                (Component(0), FlatTerm::Variable(Component(u8::MAX))),
            ] {
                for positive in [false, true] {
                    let source = FlatPair {
                        head: vec![FlatHead::Any; arity],
                        tests: vec![FlatTest::Atom {
                            field,
                            term: term.clone(),
                            positive,
                        }],
                        regexes: vec![FlatRegex::Test(0)],
                        root: 0,
                    };
                    let mut pair = CompiledPair::compile(
                        &source,
                        MAX_GRAPH_BYTES,
                        &mut Unmetered,
                        &mut ObservationWorld,
                    )
                    .unwrap();
                    let residual = pair
                        .fold(
                            pair.root,
                            &[request],
                            &bindings,
                            &mut Unmetered,
                            &mut ObservationWorld,
                        )
                        .unwrap();
                    assert_eq!(
                        pair.answer(residual, &mut Unmetered, &mut ObservationWorld),
                        Ok(!positive)
                    );
                }
            }
        }
    }
}
