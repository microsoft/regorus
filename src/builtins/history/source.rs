// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

#[cfg(verus_keep_ghost)]
use super::intern::verify::{ids_wf, interner_frame, lemma_interned_eq, lemma_interned_frame};
use super::intern::{Interner, StringId};
#[cfg(verus_keep_ghost)]
use super::kernel::verify as model;
#[cfg(verus_keep_ghost)]
use super::normalize::verify as norm;
use super::{
    error::HistoryError,
    graph::{
        allocation, checkpoint, invariant, sequence_bytes, ArenaStorage, CanonicalStore,
        ObservationWorld, RuntimeKernel, Storage,
    },
    kernel::*,
    normalize,
    progress::CompiledPair,
    work::WorkVec,
};
#[cfg(verus_keep_ghost)]
use crate::verify::history_assumptions::{KernelStoreSpec, SmallVecSpecFns, StorageSpec};
#[cfg(verus_keep_ghost)]
use crate::verify::history_specs as language;
#[cfg(verus_keep_ghost)]
use crate::verify::value_assumptions::object_iter_remaining;
#[cfg(verus_keep_ghost)]
use crate::verify::value_specs::{
    lemma_value_view_array, lemma_value_view_object, lemma_value_view_set, value_view, Data,
};
use crate::{
    utils::limits::ExecutionTimer,
    value::{Array, Object},
    Value,
};
use alloc::{
    boxed::Box,
    collections::BTreeMap,
    format,
    string::{String, ToString as _},
    vec::Vec,
};
use core::mem::size_of;
#[cfg(verus_keep_ghost)]
use verify::*;
use vstd::prelude::*;

#[verus_verify(external_body)]
fn child_path(at: &str, tag: &str, index: usize) -> String {
    format!("{at}.{tag}[{index}]")
}

// Keep the original Rc<str> Display conversion; str specialization can allocate differently.
#[verus_verify(external_body)]
#[verus_spec(result => ensures result@ == name@)]
fn native_shared_string(name: &crate::Rc<str>) -> String {
    name.to_string()
}

#[verus_verify]
fn invalid(path: &str, message: &'static str) -> HistoryError {
    HistoryError::InvalidPolicy {
        path: path.to_string(),
        message,
    }
}
#[verus_verify]
#[verus_spec(result => ensures result matches Ok((tag, payload))
    ==> language::tagged_payload(value_view(*value), tag@) == Some(value_view(*payload)))]
fn tagged<'a>(value: &'a Value, path: &str) -> KernelResult<(&'a str, &'a Value)> {
    let Value::Object(object) = value else {
        return Err(invalid(path, "expected a tagged object"));
    };
    if object.len() != 1 {
        return Err(invalid(path, "expected exactly one tag"));
    }
    let mut iter = object.iter_sorted();
    proof_decl! { let ghost entries = object_iter_remaining(iter); }
    let Some((key, payload)) = iter.next() else {
        return Err(invalid(path, "expected a tag"));
    };
    let Value::String(tag) = key else {
        return Err(invalid(path, "tag must be a string"));
    };
    proof! {
        lemma_value_view_object(*object);
        assert forall|candidate: Value| object@.contains_key(candidate) implies candidate == *key by {
            let i = choose|i: int| 0 <= i < entries.len() && entries[i].0 == candidate;
            assert(i == 0);
        }
        let fields = match value_view(*value) { Data::Object(fields) => fields, _ => Map::empty() };
        assert(fields.dom() =~= Set::empty().insert(Data::String(tag@)));
        assert(fields[Data::String(tag@)] == value_view(*payload));
    }
    Ok((tag, payload))
}
#[verus_verify]
#[verus_spec(result => ensures result matches Ok(values) ==> value_view(*value) == Data::Array(values_data(values@)))]
fn array<'a>(value: &'a Value, path: &str) -> KernelResult<&'a Array> {
    match value {
        Value::Array(values) => {
            proof! { lemma_array_data(*values); }
            Ok(values)
        }
        _ => Err(invalid(path, "expected an array")),
    }
}
#[verus_verify]
#[verus_spec(result => ensures result.is_ok() == (value_view(*value) == Data::Bool(true)))]
fn marker(value: &Value, path: &str) -> KernelResult<()> {
    if matches!(value, Value::Bool(true)) {
        Ok(())
    } else {
        Err(invalid(path, "marker must be true"))
    }
}
#[verus_verify]
#[verus_spec(result => ensures result matches Ok(value) ==> {
    (exists|candidate: Value| object@.contains_key(candidate) && value_view(candidate) == Data::String(key@) && object@[candidate] == *value)
    && (forall|k1: Value, k2: Value| object@.contains_key(k1) && object@.contains_key(k2)
        && value_view(k1) == value_view(k2) ==> k1 == k2)
})]
fn member<'a>(
    object: &'a Object,
    key: &str,
    path: &str,
    timer: &mut ExecutionTimer,
    world: &mut ObservationWorld,
) -> KernelResult<&'a Value> {
    checkpoint(timer, world)?;
    let mut iter = object.iter_sorted();
    let mut value: Option<&'a Value> = None;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            forall|i: int| 0 <= i < object_iter_remaining(iter).len() ==> {
                let entry = #[trigger] object_iter_remaining(iter)[i]; object@.contains_key(entry.0) && object@[entry.0] == entry.1
            },
            forall|k1: Value, k2: Value| object@.contains_key(k1) && object@.contains_key(k2)
                && value_view(k1) == value_view(k2) ==> k1 == k2,
            value matches Some(found) ==> exists|candidate: Value| object@.contains_key(candidate)
                && value_view(candidate) == Data::String(key@) && object@[candidate] == *found,
        decreases object_iter_remaining(iter).len(),
    ))]
    #[allow(clippy::while_let_on_iterator)]
    // The proof tracks this iterator's remaining entries.
    while let Some((candidate, entry)) = iter.next() {
        if matches!(candidate, Value::String(name) if &**name == key) {
            value = Some(entry);
            proof! { assert(value_view(*candidate) == Data::String(key@)); }
            break;
        }
    }
    checkpoint(timer, world)?;
    value.ok_or_else(|| invalid(path, "missing required member"))
}

#[verus_verify]
#[verus_verify(external_derive)]
#[derive(Debug, Default)]
pub(crate) struct Symbols {
    pub(crate) constants: Vec<Value>,
    pub(crate) paths: Vec<Box<[Value]>>,
    pub(crate) variables: Vec<String>,
}

/// Positional lookup hints persisted with the retained pair. No verified fact
/// depends on this performance oracle's contents.
// ponytail: one-position hint; add a second slot if profiles show shape ping-pong.
#[verus_verify]
#[verus_verify(external_derive)]
#[derive(Debug, Default)]
pub(crate) struct PairHints {
    /// Pattern node id, then object child in child order; empty for other nodes.
    pub(crate) pattern: Vec<Vec<usize>>,
    /// PathId, then path segment.
    pub(crate) paths: Vec<Vec<usize>>,
}

// Iterator-driven construction; hint contents are only a performance oracle.
#[verus_verify(external_body)]
pub(crate) fn pair_hints(pair: &CompiledPair) -> KernelResult<PairHints> {
    let mut hints = PairHints::default();
    allocation(hints.paths.try_reserve_exact(pair.symbols.paths.len()))?;
    for path in &pair.symbols.paths {
        let mut positions = Vec::new();
        allocation(positions.try_reserve_exact(path.len()))?;
        positions.resize(path.len(), 0);
        hints.paths.push(positions);
    }
    allocation(hints.pattern.try_reserve_exact(pair.pattern.nodes.len()))?;
    for node in &pair.pattern.nodes {
        let mut positions = Vec::new();
        if let PatternNode::Object(children) = node {
            allocation(positions.try_reserve_exact(children.len()))?;
            positions.resize(children.len(), 0);
        }
        hints.pattern.push(positions);
    }
    Ok(hints)
}
#[verus_verify]
struct SymbolBuilder {
    symbols: Symbols,
    constants: BTreeMap<Value, ConstId>,
    paths: BTreeMap<Vec<Value>, PathId>,
    variables: BTreeMap<String, VariableId>,
}
#[verus_verify]
impl SymbolBuilder {
    #[verus_spec(result =>
        ensures builder_wf(result), result.symbols@ == (model::Symbols {
            constants: Seq::empty(), paths: Seq::empty(), variables: Seq::empty(),
        }),
    )]
    fn new() -> Self {
        proof! {
            assert(values_data(Seq::<Value>::empty()) =~= Seq::<Data>::empty());
            assert(Seq::<Box<[Value]>>::empty().map(|i: int, path: Box<[Value]>| values_data(path@)) =~= Seq::<Seq<Data>>::empty());
            assert(Seq::<String>::empty().map(|i: int, name: String| name@) =~= Seq::<Seq<char>>::empty());
        }
        Self {
            symbols: Symbols {
                constants: Vec::new(),
                paths: Vec::new(),
                variables: Vec::new(),
            },
            constants: BTreeMap::new(),
            paths: BTreeMap::new(),
            variables: BTreeMap::new(),
        }
    }

    // Native Value ordering is semantic; vstd's BTree model uses structural keys.
    #[verus_verify(external_body)]
    #[verus_spec(result => ensures result == if self.constant_index().contains_key(value_view(*value)) {
        Some(self.constant_index()[value_view(*value)])
    } else { None })]
    fn lookup_constant(&self, value: &Value) -> Option<ConstId> {
        self.constants.get(value).copied()
    }

    #[verus_verify(external_body)]
    #[verus_spec(
        ensures final(self).constant_index() == old(self).constant_index().insert(value_view(value), id),
            final(self).path_index() == old(self).path_index(), final(self).variable_index() == old(self).variable_index(),
            final(self).symbols@ == old(self).symbols@,
    )]
    fn record_constant(&mut self, value: Value, id: ConstId) {
        self.constants.insert(value, id);
    }

    #[verus_verify(external_body)]
    #[verus_spec(result => ensures result == if self.path_index().contains_key(values_data(values@)) {
        Some(self.path_index()[values_data(values@)])
    } else { None })]
    fn lookup_path(&self, values: &[Value]) -> Option<PathId> {
        self.paths.get(values).copied()
    }

    #[verus_verify(external_body)]
    #[verus_spec(
        ensures final(self).path_index() == old(self).path_index().insert(values_data(values@), id),
            final(self).constant_index() == old(self).constant_index(), final(self).variable_index() == old(self).variable_index(),
            final(self).symbols@ == old(self).symbols@,
    )]
    fn record_path(&mut self, values: Vec<Value>, id: PathId) {
        self.paths.insert(values, id);
    }

    #[verus_verify(external_body)]
    #[verus_spec(result => ensures result == if self.variable_index().contains_key(name@) {
        Some(self.variable_index()[name@])
    } else { None })]
    fn lookup_variable(&self, name: &str) -> Option<VariableId> {
        self.variables.get(name).copied()
    }

    #[verus_verify(external_body)]
    #[verus_spec(
        ensures final(self).variable_index() == old(self).variable_index().insert(name@, id),
            final(self).constant_index() == old(self).constant_index(), final(self).path_index() == old(self).path_index(),
            final(self).symbols@ == old(self).symbols@,
    )]
    fn record_variable(&mut self, name: String, id: VariableId) {
        self.variables.insert(name, id);
    }

    #[verus_spec(result =>
        requires builder_wf(*old(self)), model::graph_wf(old(kernel).graph()), old(kernel).valid_store(),
        ensures builder_wf(*final(self)), symbols_extends(old(self).symbols@, final(self).symbols@),
            final(kernel).restoration() == old(kernel).restoration(),
            final(self).symbols@.paths == old(self).symbols@.paths,
            final(self).symbols@.variables == old(self).symbols@.variables,
            final(kernel).graph() == old(kernel).graph(), model::graph_wf(final(kernel).graph()), final(kernel).valid_store(),
            result matches Ok(id) ==> id@ < final(self).symbols@.constants.len()
                && final(self).symbols@.constants[id@ as int] == value_view(*value),
    )]
    fn constant<S: Storage>(
        &mut self,
        value: &Value,
        kernel: &mut RuntimeKernel<'_, S>,
    ) -> KernelResult<ConstId> {
        proof_decl! {
            let ghost initial_symbols = self.symbols@;
            let ghost initial_values = self.symbols.constants@;
            let ghost constants = self.constant_index(); let ghost paths = self.path_index(); let ghost variables = self.variable_index();
        }
        kernel.checkpoint()?;
        let existing = self.lookup_constant(value);
        kernel.checkpoint()?;
        if let Some(id) = existing {
            return Ok(id);
        }
        let projected = kernel.store.projected(size_of::<Value>())?;
        let id = ConstId::from_index(self.symbols.constants.len())?;
        allocation(kernel.world.try_reserve_vec(&mut self.symbols.constants, 1))?;
        self.symbols.constants.push(value.clone());
        proof! {
            assert(self.symbols.constants@ =~= initial_values.push(self.symbols.constants@.last()));
            lemma_values_data_push(initial_values, self.symbols.constants@.last());
            assert(self.symbols@ == (model::Symbols { constants: initial_symbols.constants.push(value_view(*value)), ..initial_symbols }));
        }
        self.record_constant(value.clone(), id);
        proof! {
            assert(self.constant_index() == constants.insert(value_view(*value), id));
            lemma_constant_insert_wf(initial_symbols, constants, paths, variables, value_view(*value), id);
            assert(builder_wf(*self));
        }
        kernel.store.set_charged_bytes(projected);
        kernel.checkpoint()?;
        Ok(id)
    }
    #[verus_spec(result =>
        requires builder_wf(*old(self)), model::graph_wf(old(kernel).graph()), old(kernel).valid_store(),
        ensures builder_wf(*final(self)), symbols_extends(old(self).symbols@, final(self).symbols@),
            final(kernel).restoration() == old(kernel).restoration(),
            final(self).symbols@.constants == old(self).symbols@.constants,
            final(self).symbols@.variables == old(self).symbols@.variables,
            final(kernel).graph() == old(kernel).graph(), model::graph_wf(final(kernel).graph()), final(kernel).valid_store(),
            result matches Ok(id) ==> id@ < final(self).symbols@.paths.len()
                && final(self).symbols@.paths[id@ as int] == values_data(values@)
                && forall|i: int| 0 <= i < values@.len() ==> value_view(values@[i]) != Data::Undefined,
    )]
    fn path<S: Storage>(
        &mut self,
        values: &Array,
        at: &str,
        kernel: &mut RuntimeKernel<'_, S>,
    ) -> KernelResult<PathId> {
        proof_decl! {
            let ghost entry = kernel.graph(); let ghost initial_symbols = self.symbols@;
            let ghost initial_paths = self.symbols.paths@; let ghost input = values_data(values@);
            let ghost constants = self.constant_index(); let ghost paths = self.path_index(); let ghost variables = self.variable_index();
        }
        let mut failure = None;
        let mut index = 0;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant index <= values@.len(), kernel.graph() == entry, model::graph_wf(kernel.graph()), kernel.valid_store(),
                kernel.restoration() == old(kernel).restoration(),
                forall|i: int| 0 <= i < index ==> value_view(values@[i]) != Data::Undefined,
            ensures kernel.graph() == entry, model::graph_wf(kernel.graph()), kernel.valid_store(),
                kernel.restoration() == old(kernel).restoration(),
                failure is None ==> forall|i: int| 0 <= i < values@.len() ==> value_view(values@[i]) != Data::Undefined,
            decreases values@.len() - index,
        ))]
        while index < values.len() {
            let value = values
                .get(index)
                .ok_or_else(|| invariant("invalid path index"))?;
            loop_try!(kernel.checkpoint(), failure);
            if matches!(value, Value::Undefined) {
                failure = Some(invalid(at, "path keys must be defined"));
                break;
            }
            index = index.saturating_add(1);
        }
        if let Some(error) = failure {
            return Err(error);
        }
        kernel.checkpoint()?;
        let existing = self.lookup_path(values.as_slice());
        kernel.checkpoint()?;
        if let Some(id) = existing {
            return Ok(id);
        }
        let bytes = size_of::<Box<[Value]>>()
            .checked_add(sequence_bytes::<Value>(values.len())?)
            .ok_or(HistoryError::GraphLimit {
                limit: MAX_GRAPH_BYTES,
            })?;
        let projected = kernel.store.projected(bytes)?;
        let id = PathId::from_index(self.symbols.paths.len())?;
        allocation(kernel.world.try_reserve_vec(&mut self.symbols.paths, 1))?;
        let mut path = Vec::new();
        allocation(kernel.world.try_reserve_exact_vec(&mut path, values.len()))?;
        let mut failure = None;
        let mut index = 0;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant index <= values@.len(), kernel.graph() == entry, model::graph_wf(kernel.graph()), kernel.valid_store(),
                kernel.restoration() == old(kernel).restoration(),
                input == values_data(values@), input.len() == values@.len(),
                values_data(path@) == input.take(index as int),
            ensures kernel.graph() == entry, model::graph_wf(kernel.graph()), kernel.valid_store(),
                kernel.restoration() == old(kernel).restoration(),
                index <= values@.len(), values_data(path@) == input.take(index as int),
                input == values_data(values@), input.len() == values@.len(),
                failure is None ==> index == values@.len(),
            decreases values@.len() - index,
        ))]
        while index < values.len() {
            let value = values
                .get(index)
                .ok_or_else(|| invariant("invalid path index"))?;
            loop_try!(kernel.checkpoint(), failure);
            proof_decl! { let ghost previous = path@; }
            path.push(value.clone());
            proof! {
                assert(input[index as int] == value_view(*value));
                lemma_values_data_push(previous, path@.last());
                assert(value_view(path@.last()) == input[index as int]);
                assert(input.take(index as int).push(input[index as int]) =~= input.take(index as int + 1));
                assert(values_data(path@) =~= input.take(index as int + 1));
            }
            index = index.saturating_add(1);
        }
        if let Some(error) = failure {
            return Err(error);
        }
        proof! {
            assert(input.take(index as int) =~= input);
            assert(values_data(path@) == input);
        }
        self.symbols.paths.push(path.clone().into_boxed_slice());
        proof! {
            assert(self.symbols.paths@ =~= initial_paths.push(self.symbols.paths@.last()));
            let copied = self.symbols.paths@.last()@;
            assert(path@.len() == copied.len());
            assert forall|i: int| 0 <= i < path@.len() implies cloned::<Value>(path@[i], copied[i]) by {}
            lemma_cloned_values_data(path@, copied);
            assert(self.symbols@.paths =~= initial_symbols.paths.push(input));
            assert(self.symbols@ == (model::Symbols { paths: initial_symbols.paths.push(input), ..initial_symbols }));
        }
        self.record_path(path, id);
        proof! {
            assert(self.path_index() == paths.insert(input, id));
            lemma_path_insert_wf(initial_symbols, constants, paths, variables, input, id);
            assert(builder_wf(*self));
        }
        kernel.store.set_charged_bytes(projected);
        kernel.checkpoint()?;
        Ok(id)
    }
    #[verus_spec(result =>
        requires builder_wf(*old(self)), model::graph_wf(old(kernel).graph()), old(kernel).valid_store(),
        ensures builder_wf(*final(self)), symbols_extends(old(self).symbols@, final(self).symbols@),
            final(kernel).restoration() == old(kernel).restoration(),
            final(self).symbols@.constants == old(self).symbols@.constants,
            final(self).symbols@.paths == old(self).symbols@.paths,
            final(kernel).graph() == old(kernel).graph(), model::graph_wf(final(kernel).graph()), final(kernel).valid_store(),
            result matches Ok(id) ==> id@ < final(self).symbols@.variables.len()
                && value_view(*value) == Data::String(final(self).symbols@.variables[id@ as int])
                && final(self).symbols@.variables[id@ as int].len() > 0
                && final(self).symbols@.variables.to_set() == old(self).symbols@.variables.to_set().insert(final(self).symbols@.variables[id@ as int]),
    )]
    fn declare<S: Storage>(
        &mut self,
        value: &Value,
        at: &str,
        kernel: &mut RuntimeKernel<'_, S>,
    ) -> KernelResult<VariableId> {
        proof_decl! {
            let ghost initial_symbols = self.symbols@;
            let ghost initial_values = self.symbols.variables@;
            let ghost constants = self.constant_index(); let ghost paths = self.path_index(); let ghost variables = self.variable_index();
        }
        let Value::String(name) = value else {
            return Err(invalid(at, "variable name must be a string"));
        };
        if name.is_empty() {
            return Err(invalid(at, "variable name must not be empty"));
        }
        kernel.checkpoint()?;
        let existing = self.lookup_variable(name);
        kernel.checkpoint()?;
        if let Some(id) = existing {
            proof! {
                assert(self.symbols@.variables[id@ as int] == name@);
                assert(self.symbols@.variables.to_set().contains(name@));
                assert(self.symbols@.variables.to_set().insert(name@) == initial_symbols.variables.to_set());
            }
            return Ok(id);
        }
        let bytes =
            size_of::<String>()
                .checked_add(name.len())
                .ok_or(HistoryError::GraphLimit {
                    limit: MAX_GRAPH_BYTES,
                })?;
        let projected = kernel.store.projected(bytes)?;
        let id = VariableId::from_index(self.symbols.variables.len())?;
        allocation(kernel.world.try_reserve_vec(&mut self.symbols.variables, 1))?;
        self.symbols.variables.push(native_shared_string(name));
        proof! {
            assert(self.symbols.variables@ =~= initial_values.push(self.symbols.variables@.last()));
            assert(self.symbols.variables@.last()@ == name@);
            assert(self.symbols@.variables =~= initial_symbols.variables.push(name@));
            assert(self.symbols@ == (model::Symbols { variables: initial_symbols.variables.push(name@), ..initial_symbols }));
            initial_symbols.variables.lemma_push_to_set_commute(name@);
            assert(self.symbols@.variables.to_set() =~= initial_symbols.variables.to_set().insert(name@));
        }
        self.record_variable(native_shared_string(name), id);
        proof! {
            assert(self.variable_index() == variables.insert(name@, id));
            lemma_variable_insert_wf(initial_symbols, constants, paths, variables, name@, id);
            assert(builder_wf(*self));
        }
        kernel.store.set_charged_bytes(projected);
        kernel.checkpoint()?;
        Ok(id)
    }
    #[verus_spec(result =>
        requires builder_wf(*old(self)), model::graph_wf(old(kernel).graph()), old(kernel).valid_store(),
        ensures builder_wf(*final(self)), symbols_extends(old(self).symbols@, final(self).symbols@),
            final(kernel).restoration() == old(kernel).restoration(),
            final(self).symbols@.variables == old(self).symbols@.variables,
            final(kernel).graph() == old(kernel).graph(), model::graph_wf(final(kernel).graph()), final(kernel).valid_store(),
            result matches Ok(term) ==> exists|decoded: language::Term| language::decodes_term(value_view(*value), decoded)
                && term_represents(final(self).symbols@, term@, decoded),
    )]
    fn term<S: Storage>(
        &mut self,
        value: &Value,
        at: &str,
        kernel: &mut RuntimeKernel<'_, S>,
    ) -> KernelResult<Term> {
        let (tag, payload) = tagged(value, at)?;
        match tag {
            "value" => {
                proof! { assert(language::decodes_term(value_view(*value), language::Term::Constant(value_view(*payload)))); }
                Ok(Term::Constant(self.constant(payload, kernel)?))
            }
            "var" => {
                let Value::String(name) = payload else {
                    return Err(invalid(at, "variable name must be a string"));
                };
                if name.is_empty() {
                    return Err(invalid(at, "variable name must not be empty"));
                }
                kernel.checkpoint()?;
                let variable = self.lookup_variable(name);
                kernel.checkpoint()?;
                proof! {
                    if let Some(id) = variable {
                        assert(language::decodes_term(value_view(*value), language::Term::Variable(name@)));
                        assert(term_represents(self.symbols@, model::GTerm::Variable(id@), language::Term::Variable(name@)));
                    }
                }
                Ok(Term::Variable(variable.ok_or_else(|| {
                    HistoryError::UnboundVariable {
                        name: name.to_string(),
                    }
                })?))
            }
            _ => Err(invalid(at, "unknown term tag")),
        }
    }
}

#[verus_verify]
#[verus_verify(external_derive)]
#[derive(Debug)]
enum PatternNode {
    Literal(ConstId),
    Variable(VariableId),
    Any,
    Object(Box<[(Value, usize)]>),
    Array(Box<[usize]>),
}
#[verus_verify]
#[verus_verify(external_derive)]
#[derive(Debug)]
pub(crate) struct CompiledPattern {
    nodes: Vec<PatternNode>,
    root: usize,
}
#[verus_verify]
enum PatternWork<'a> {
    Enter(&'a Value, String),
    Object { keys: Vec<Value>, start: usize },
    Array { len: usize, start: usize },
}
#[verus_verify]
impl CompiledPattern {
    #[verus_spec(result =>
        requires builder_wf(*old(symbols)), model::graph_wf(old(kernel).graph()), old(kernel).valid_store(),
            pattern_task_valid(task@), pattern_compile_work_valid(pattern_compile_work(old(work).view())),
        ensures builder_wf(*final(symbols)), symbols_extends(old(symbols).symbols@, final(symbols).symbols@),
            final(kernel).graph() == old(kernel).graph(), model::graph_wf(final(kernel).graph()), final(kernel).valid_store(),
            final(kernel).restoration() == old(kernel).restoration(),
            pattern_compile_work_valid(pattern_compile_work(final(work).view())),
            result matches Ok(node) ==> pattern_compile_step_effect(task@, old(symbols).symbols@, final(symbols).symbols@,
                old(results).view(), final(results).view(), pattern_compile_work(old(work).view()), pattern_compile_work(final(work).view()), node),
    )]
    fn compile_step<'source, S: Storage>(
        task: PatternWork<'source>,
        symbols: &mut SymbolBuilder,
        kernel: &mut RuntimeKernel<'_, S>,
        results: &mut WorkVec<usize>,
        work: &mut WorkVec<PatternWork<'source>>,
    ) -> KernelResult<Option<PatternNode>> {
        proof_decl! {
            let ghost initial_symbols = symbols.symbols@;
            let ghost initial_graph = kernel.graph();
            let ghost initial_results = results.view();
            let ghost initial_work = work.view();
            let ghost initial_pending = pattern_compile_work(work.view());
        }
        Ok(match task {
            PatternWork::Enter(value, at) => {
                let (tag, payload) = tagged(value, &at)?;
                match tag {
                    "value" => Some(PatternNode::Literal(symbols.constant(payload, kernel)?)),
                    "var" => Some(PatternNode::Variable(
                        symbols.declare(payload, &at, kernel)?,
                    )),
                    "any" => {
                        marker(payload, &at)?;
                        Some(PatternNode::Any)
                    }
                    "array" => {
                        let children = array(payload, &at)?;
                        kernel
                            .store
                            .projected(sequence_bytes::<usize>(children.len())?)?;
                        proof_decl! { let ghost before_finish = work.view(); }
                        work.push(PatternWork::Array {
                            len: children.len(),
                            start: results.len(),
                        });
                        proof! {
                            assert(pattern_compile_work(work.view()) =~= initial_pending.push(PendingPatternWork::Array(children@.len(), initial_results.len())));
                            lemma_pattern_pending_valid_push(initial_pending, PendingPatternWork::Array(children@.len(), initial_results.len()));
                        }
                        let mut index = children.len();
                        #[cfg_attr(verus_keep_ghost, verus_spec(
                            invariant index <= children@.len(),
                            builder_wf(*symbols), symbols.symbols@ == initial_symbols,
                            initial_symbols == old(symbols).symbols@, kernel.graph() == initial_graph,
                            initial_graph == old(kernel).graph(), model::graph_wf(kernel.graph()), kernel.valid_store(),
                            kernel.restoration() == old(kernel).restoration(),
                            results.view() == initial_results,
                            pattern_compile_work_valid(pattern_compile_work(work.view())),
                            pattern_compile_work_valid(initial_pending),
                                language::tagged_payload(value_view(*value), "array"@) == Some(Data::Array(values_data(children@))),
                                pattern_compile_work(work.view()) == initial_pending.push(PendingPatternWork::Array(children@.len(), initial_results.len()))
                                    + pattern_jobs(values_data(children@).skip(index as int)),
                            decreases index,
                        ))]
                        while index > 0 {
                            index -= 1;
                            let child = children
                                .get(index)
                                .ok_or_else(|| invariant("invalid pattern child"))?;
                            proof_decl! { let ghost before_push = work.view(); }
                            work.push(PatternWork::Enter(child, child_path(&at, "array", index)));
                            proof! {
                                let suffix = values_data(children@).skip(index as int);
                                assert(suffix[0] == value_view(*child));
                                assert(suffix.drop_first() =~= values_data(children@).skip(index as int + 1));
                                lemma_pattern_jobs_prepend(suffix);
                                assert(pattern_compile_work(work.view()) =~= pattern_compile_work(before_push).push(PendingPatternWork::Enter(value_view(*child))));
                                lemma_pattern_work_jobs_valid(initial_pending.push(PendingPatternWork::Array(children@.len(), initial_results.len())), suffix);
                            }
                            kernel.checkpoint()?;
                        }
                        proof! {
                            assert(values_data(children@).skip(0) =~= values_data(children@));
                            assert(pattern_compile_step_effect(task@, initial_symbols, symbols.symbols@, initial_results, results.view(), initial_pending, pattern_compile_work(work.view()), None));
                        }
                        None
                    }
                    "object" => {
                        let Value::Object(children) = payload else {
                            return Err(invalid(&at, "object pattern payload must be an object"));
                        };
                        kernel
                            .store
                            .projected(sequence_bytes::<(Value, usize)>(children.len())?)?;
                        let mut keys = Vec::new();
                        allocation(
                            kernel
                                .world
                                .try_reserve_exact_vec(&mut keys, children.len()),
                        )?;
                        let mut pending: WorkVec<(&Value, String)> = WorkVec::new();
                        let mut it = children.iter_sorted();
                        proof_decl! { let ghost entries = object_iter_remaining(it); }
                        proof! { assert(pattern_object_entries(*children, entries)); }
                        let mut index = 0_usize;
                        #[cfg_attr(verus_keep_ghost, verus_spec(
                            invariant index <= entries.len(), entries.len() <= usize::MAX,
                            builder_wf(*symbols), symbols.symbols@ == initial_symbols,
                            initial_symbols == old(symbols).symbols@, kernel.graph() == initial_graph,
                            initial_graph == old(kernel).graph(), model::graph_wf(kernel.graph()), kernel.valid_store(),
                            kernel.restoration() == old(kernel).restoration(),
                            results.view() == initial_results,
                            pattern_compile_work_valid(pattern_compile_work(work.view())),
                            pattern_compile_work_valid(initial_pending),
                                work.view() == initial_work, pattern_object_entries(*children, entries),
                                object_iter_remaining(it) == entries.skip(index as int),
                                keys@.len() == index, pending.view().len() == index,
                                forall|i: int| 0 <= i < index ==> value_view(keys@[i]) == value_view(entries[i].0)
                                    && *pending.view()[i].0 == entries[i].1,
                            ensures index == entries.len(),
                                kernel.restoration() == old(kernel).restoration(),
                            decreases entries.len() - index,
                        ))]
                        #[allow(clippy::while_let_on_iterator)]
                        // The proof tracks this iterator's remaining entries.
                        while let Some((key, child)) = it.next() {
                            kernel.checkpoint()?;
                            keys.push(key.clone());
                            pending.push((child, child_path(&at, "object", index)));
                            index = index.saturating_add(1);
                        }
                        proof_decl! {
                            let ghost key_data = values_data(keys@);
                            let ghost child_data = pattern_pending_children(pending.view());
                            let ghost before_finish = work.view();
                        }
                        proof! {
                            lemma_pattern_object_enumeration(*children, entries, key_data, child_data);
                        }
                        work.push(PatternWork::Object {
                            keys,
                            start: results.len(),
                        });
                        proof! {
                            assert(pattern_compile_work(work.view()) =~= initial_pending.push(PendingPatternWork::Object(key_data, initial_results.len())));
                            lemma_pattern_pending_valid_push(initial_pending, PendingPatternWork::Object(key_data, initial_results.len()));
                        }
                        let mut index = pending.len();
                        #[cfg_attr(verus_keep_ghost, verus_spec(
                            invariant index == pending.view().len(), index <= child_data.len(),
                            builder_wf(*symbols), symbols.symbols@ == initial_symbols,
                            initial_symbols == old(symbols).symbols@, kernel.graph() == initial_graph,
                            initial_graph == old(kernel).graph(), model::graph_wf(kernel.graph()), kernel.valid_store(),
                            kernel.restoration() == old(kernel).restoration(),
                            results.view() == initial_results,
                            pattern_compile_work_valid(pattern_compile_work(work.view())),
                            pattern_compile_work_valid(initial_pending),
                                key_data.no_duplicates(),
                                language::tagged_payload(value_view(*value), "object"@) == Some(value_view(*payload)),
                                value_view(*payload) is Object, key_data.to_set() == (value_view(*payload)->Object_0).dom(),
                                child_data.len() == key_data.len(),
                                forall|i: int| 0 <= i < key_data.len() ==> child_data[i] == (value_view(*payload)->Object_0)[key_data[i]],
                                pattern_pending_children(pending.view()) == child_data.take(index as int),
                                pattern_compile_work(work.view()) == initial_pending.push(PendingPatternWork::Object(key_data, initial_results.len()))
                                    + pattern_jobs(child_data.skip(index as int)),
                            decreases index,
                        ))]
                        while index > 0 {
                            proof_decl! { let ghost before_pop = pending.view(); let ghost before_push = work.view(); }
                            index -= 1;
                            let (child, path) = pending
                                .pop()
                                .ok_or_else(|| invariant("invalid pending pattern"))?;
                            proof! {
                                assert(value_view(*child) == pattern_pending_children(before_pop).last());
                                assert(pattern_pending_children(before_pop).last() == child_data[index as int]);
                                assert(pattern_pending_children(pending.view()) =~= child_data.take(index as int));
                            }
                            work.push(PatternWork::Enter(child, path));
                            proof! {
                                let suffix = child_data.skip(index as int);
                                assert(suffix[0] == value_view(*child));
                                assert(suffix.drop_first() =~= child_data.skip(index as int + 1));
                                lemma_pattern_jobs_prepend(suffix);
                                lemma_pattern_pending_valid_push(initial_pending, PendingPatternWork::Object(key_data, initial_results.len()));
                                assert(pattern_compile_work(work.view()) =~= pattern_compile_work(before_push).push(PendingPatternWork::Enter(value_view(*child))));
                                lemma_pattern_work_jobs_valid(initial_pending.push(PendingPatternWork::Object(key_data, initial_results.len())), suffix);
                                assert(pattern_compile_work(work.view()) =~= initial_pending.push(PendingPatternWork::Object(key_data, initial_results.len())) + pattern_jobs(suffix));
                            }
                        }
                        proof! {
                            assert(child_data.skip(0) =~= child_data);
                            assert(pattern_compile_step_effect(task@, initial_symbols, symbols.symbols@, initial_results, results.view(), initial_pending, pattern_compile_work(work.view()), None));
                        }
                        None
                    }
                    _ => return Err(invalid(&at, "unknown request pattern tag")),
                }
            }
            PatternWork::Array { len, start } => {
                let ids = results
                    .get(start..)
                    .ok_or_else(|| invariant("invalid pattern result stack"))?;
                if ids.len() != len {
                    return Err(invariant("invalid pattern arity"));
                }
                let mut children = Vec::new();
                allocation(kernel.world.try_reserve_exact_vec(&mut children, len))?;
                children.extend_from_slice(ids);
                results.truncate(start);
                proof! {
                    assert(task@ == PendingPatternWork::Array(len as nat, start as nat));
                    assert(start <= initial_results.len());
                    assert(initial_results.len() == start + len);
                    assert(results.view() == initial_results.take(start as int));
                    assert(children@ == initial_results.skip(start as int));
                    assert(pattern_compile_work(work.view()) == initial_pending);
                    assert(symbols.symbols@ == initial_symbols);
                    assert forall|boxed: Box<[usize]>| boxed@ == children@ implies pattern_compile_step_effect(task@, initial_symbols, symbols.symbols@, initial_results, results.view(), initial_pending, pattern_compile_work(work.view()), Some(PatternNode::Array(boxed))) by {}
                }
                Some(PatternNode::Array(children.into_boxed_slice()))
            }
            PatternWork::Object { keys, start } => {
                let ids = results
                    .get(start..)
                    .ok_or_else(|| invariant("invalid pattern result stack"))?;
                if ids.len() != keys.len() {
                    return Err(invariant("invalid pattern arity"));
                }
                let mut children: Vec<(Value, usize)> = Vec::new();
                allocation(
                    kernel
                        .world
                        .try_reserve_exact_vec(&mut children, keys.len()),
                )?;
                proof_decl! { let ghost original_keys = keys@; }
                let mut keys = keys;
                let mut index = 0_usize;
                #[cfg_attr(verus_keep_ghost, verus_spec(
                    invariant index <= original_keys.len(), keys@.len() == original_keys.len(),
                        builder_wf(*symbols), symbols.symbols@ == initial_symbols,
                        initial_symbols == old(symbols).symbols@, kernel.graph() == initial_graph,
                        initial_graph == old(kernel).graph(), model::graph_wf(kernel.graph()), kernel.valid_store(),
                        kernel.restoration() == old(kernel).restoration(),
                        results.view() == initial_results, work.view() == initial_work,
                        pattern_compile_work_valid(pattern_compile_work(work.view())),
                        ids@ == initial_results.skip(start as int), ids@.len() == original_keys.len(),
                        start <= initial_results.len(), original_keys.len() + start == initial_results.len(),
                        children@.len() == index,
                        forall|i: int| index <= i < original_keys.len() ==> keys@[i] == original_keys[i],
                        pattern_object_fields(children@) == Seq::new(index as nat, |i: int| (value_view(original_keys[i]), ids@[i])),
                    decreases original_keys.len() - index,
                ))]
                while index < keys.len() {
                    proof_decl! { let ghost position = index; let ghost previous_children = children@; }
                    proof! {
                        assert(pattern_object_fields(previous_children) == Seq::new(position as nat, |i: int| (value_view(original_keys[i]), ids@[i])));
                    }
                    let key_slice = keys.as_mut_slice();
                    let key = key_slice
                        .get_mut(index)
                        .ok_or_else(|| invariant("invalid pattern key"))?;
                    let key = core::mem::replace(key, Value::Undefined);
                    proof! { assert(value_view(key) == value_view(original_keys[position as int])); }
                    let id = ids
                        .get(index)
                        .ok_or_else(|| invariant("invalid pattern child"))?;
                    kernel.checkpoint()?;
                    proof_decl! { let ghost appended = (key, *id); }
                    children.push((key, *id));
                    index = index.saturating_add(1);
                    proof! {
                        assert(index == position + 1);
                        assert(children@[position as int] == appended);
                        assert(value_view(appended.0) == value_view(original_keys[position as int]));
                        assert(appended.1 == ids@[position as int]);
                        assert(pattern_object_fields(children@) =~= Seq::new(index as nat, |i: int| (value_view(original_keys[i]), ids@[i]))) by {
                            assert forall|i: int| 0 <= i < index implies pattern_object_fields(children@)[i] == (value_view(original_keys[i]), ids@[i]) by {
                                if i < position {
                                    assert(children@[i] == previous_children[i]);
                                    assert(pattern_object_fields(previous_children)[i] == (value_view(original_keys[i]), ids@[i]));
                                } else {
                                    assert(i == position);
                                    assert(children@[i] == appended);
                                }
                            }
                        }
                    }
                }
                results.truncate(start);
                proof! {
                    assert(task@ == PendingPatternWork::Object(values_data(original_keys), start as nat));
                    assert(results.view() == initial_results.take(start as int));
                    assert(pattern_compile_work(work.view()) == initial_pending);
                    assert(symbols.symbols@ == initial_symbols);
                    assert(children@.len() == original_keys.len());
                    assert forall|i: int| 0 <= i < original_keys.len() implies value_view(children@[i].0) == value_view(original_keys[i]) && children@[i].1 == initial_results[start + i] by {
                        assert(pattern_object_fields(children@)[i] == (value_view(original_keys[i]), ids@[i]));
                        assert(ids@[i] == initial_results[start + i]);
                    }
                    assert forall|boxed: Box<[(Value, usize)]>| boxed@ == children@ implies pattern_compile_step_effect(task@, initial_symbols, symbols.symbols@, initial_results, results.view(), initial_pending, pattern_compile_work(work.view()), Some(PatternNode::Object(boxed))) by {}
                }
                Some(PatternNode::Object(children.into_boxed_slice()))
            }
        })
    }
    #[verus_spec(result =>
        requires builder_wf(*old(symbols)), old(symbols).symbols@.variables.len() == 0,
            model::graph_wf(old(kernel).graph()), old(kernel).valid_store(),
        ensures builder_wf(*final(symbols)), symbols_extends(old(symbols).symbols@, final(symbols).symbols@),
            final(kernel).graph() == old(kernel).graph(), model::graph_wf(final(kernel).graph()), final(kernel).valid_store(),
            final(kernel).restoration() == old(kernel).restoration(),
            result matches Ok(pattern) ==> exists|head: language::Head| language::decodes_head(value_view(*source), head)
                && pattern_represents(pattern, final(symbols).symbols@, head),
    )]
    fn compile<S: Storage>(
        source: &Value,
        symbols: &mut SymbolBuilder,
        kernel: &mut RuntimeKernel<'_, S>,
    ) -> KernelResult<Self> {
        proof_decl! { let ghost initial_symbols = symbols.symbols@; let ghost initial_graph = kernel.graph(); }
        let mut nodes: Vec<PatternNode> = Vec::new();
        let mut results: WorkVec<usize> = WorkVec::new();
        let mut work: WorkVec<PatternWork<'_>> = WorkVec::new();
        work.push(PatternWork::Enter(source, "$.request".to_string()));
        proof! {
            assert(pattern_compile_work(work.view()) =~= seq![PendingPatternWork::Enter(value_view(*source))]);
            assert(pattern_heads(nodes@, symbols.symbols@, results.view()) =~= Seq::empty());
            lemma_pattern_vars(Seq::empty());
            assert(pattern_heads_vars(Seq::empty()) =~= Set::empty());
            assert forall|out: Seq<language::Head>| pattern_compile_run(pattern_compile_work(work.view()), pattern_heads(nodes@, symbols.symbols@, results.view()), out)
                implies out.len() == 1 && language::decodes_head(value_view(*source), out[0]) by {
                lemma_pattern_run_unfold(Seq::empty(), PendingPatternWork::Enter(value_view(*source)), Seq::empty(), out);
                let head = choose|head: language::Head| language::decodes_head(value_view(*source), head)
                    && pattern_compile_run(Seq::empty(), seq![head], out);
                assert(out == seq![head]);
            }
        }
        proof_decl! { let ghost mut scheduled = work.view(); }
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant builder_wf(*symbols), symbols_extends(initial_symbols, symbols.symbols@),
                initial_symbols == old(symbols).symbols@, initial_graph == old(kernel).graph(),
                kernel.graph() == initial_graph, model::graph_wf(kernel.graph()), kernel.valid_store(),
                kernel.restoration() == old(kernel).restoration(),
                pattern_nodes_wf(nodes@, symbols.symbols@), pattern_ids_valid(nodes@, results.view()),
                scheduled == work.view(),
                pattern_compile_work_valid(pattern_compile_work(work.view())),
                symbols.symbols@.variables.to_set() == pattern_heads_vars(pattern_heads(nodes@, symbols.symbols@, results.view())),
                forall|out: Seq<language::Head>| #[trigger] pattern_compile_run(pattern_compile_work(work.view()), pattern_heads(nodes@, symbols.symbols@, results.view()), out)
                    ==> out.len() == 1 && language::decodes_head(value_view(*source), out[0]),
            ensures work.view().len() == 0,
                kernel.restoration() == old(kernel).restoration(),
            decreases pattern_compile_measure(pattern_compile_work(work.view())),
        ))]
        while let Some(task) = work.pop() {
            proof_decl! {
                let ghost previous_nodes = nodes@;
                let ghost previous_symbols = symbols.symbols@;
                let ghost previous_results = results.view();
                let ghost pending = pattern_compile_work(work.view());
                let ghost job = task@;
            }
            proof! {
                assert(work.view().push(task) =~= scheduled);
                lemma_pattern_compile_work_push(work.view(), task);
                assert(pattern_compile_work(scheduled) == pending.push(job));
                assert(pattern_compile_work_valid(pending.push(job)));
                assert(pending.push(job)[pending.len() as int] == job);
                assert forall|i: int| 0 <= i < pending.len() implies pattern_task_valid(pending[i]) by {
                    assert(pending.push(job)[i] == pending[i]);
                }
                assert(pattern_task_valid(job));
                assert(pattern_compile_work_valid(pending));
                assert forall|out: Seq<language::Head>| pattern_compile_run(pending.push(job), pattern_heads(previous_nodes, previous_symbols, previous_results), out)
                    implies out.len() == 1 && language::decodes_head(value_view(*source), out[0]) by {}
            }
            kernel.checkpoint()?;
            let node = Self::compile_step(task, symbols, kernel, &mut results, &mut work)?;
            proof_decl! {
                let ghost next_nodes = pattern_output_nodes(previous_nodes, node);
                let ghost next_ids = pattern_output_ids(previous_nodes, results.view(), node);
            }
            proof! {
                vstd::std_specs::vec::axiom_spec_len(&nodes);
                lemma_source_symbols_transitive(initial_symbols, previous_symbols, symbols.symbols@);
                lemma_pattern_compile_transfer(previous_nodes, previous_symbols, symbols.symbols@, job, previous_results, results.view(), pending, pattern_compile_work(work.view()), node);
                lemma_pattern_compile_measure_step(job, previous_symbols, symbols.symbols@, previous_results, results.view(), pending, pattern_compile_work(work.view()), node);
                assert forall|out: Seq<language::Head>| pattern_compile_run(pattern_compile_work(work.view()), pattern_heads(next_nodes, symbols.symbols@, next_ids), out)
                    implies out.len() == 1 && language::decodes_head(value_view(*source), out[0]) by {
                    assert(pattern_compile_run(pending.push(job), pattern_heads(previous_nodes, previous_symbols, previous_results), out));
                }
            }
            if let Some(node) = node {
                let payload = match &node {
                    PatternNode::Array(ids) => sequence_bytes::<usize>(ids.len())?,
                    PatternNode::Object(fields) => sequence_bytes::<(Value, usize)>(fields.len())?,
                    _ => 0,
                };
                let bytes = size_of::<PatternNode>().checked_add(payload).ok_or(
                    HistoryError::GraphLimit {
                        limit: MAX_GRAPH_BYTES,
                    },
                )?;
                let projected = kernel.store.projected(bytes)?;
                allocation(kernel.world.try_reserve_vec(&mut nodes, 1))?;
                let id = nodes.len();
                nodes.push(node);
                kernel.store.set_charged_bytes(projected);
                results.push(id);
            }
            proof! { assert(nodes@ == next_nodes); assert(results.view() == next_ids); scheduled = work.view(); }
        }
        proof_decl! { let ghost completed = pattern_heads(nodes@, symbols.symbols@, results.view()); }
        proof! {
            assert(pattern_compile_run(pattern_compile_work(work.view()), completed, completed));
            assert(completed.len() == 1 && language::decodes_head(value_view(*source), completed[0]));
        }
        if results.len() != 1 {
            return Err(invariant("invalid pattern root"));
        }
        let root = results
            .pop()
            .ok_or_else(|| invariant("missing pattern root"))?;
        proof! {
            let head = pattern_head(nodes@, symbols.symbols@, root as int);
            assert(completed =~= seq![head]);
            lemma_pattern_vars(seq![head]);
            assert(pattern_heads_vars(seq![head]) =~= language::head_vars(head)) by {
                assert forall|name: Seq<char>| pattern_heads_vars(seq![head]).contains(name) == language::head_vars(head).contains(name) by {
                    if pattern_heads_vars(seq![head]).contains(name) {
                        let i = choose|i: int| 0 <= i < 1 && language::head_vars(seq![head][i]).contains(name);
                        assert(i == 0);
                    }
                }
            }
            assert(pattern_represents(Self { nodes, root }, symbols.symbols@, head));
        }
        Ok(Self { nodes, root })
    }
    #[verus_spec(result =>
        requires pattern_nodes_wf(self.nodes@, symbols@), task.0 < self.nodes@.len(),
            pattern_work_valid(*self, old(work).view()), old(bindings)@.len() == symbols@.variables.len(),
        ensures final(bindings)@.len() == old(bindings)@.len(), pattern_work_valid(*self, final(work).view()),
            result matches Ok(matched) ==> forall|theta: language::Subst|
                #[trigger] pattern_match_state(*self, symbols@, old(work).view().push(task), old(bindings)@, theta)
                    == (matched && pattern_match_state(*self, symbols@, final(work).view(), final(bindings)@, theta)),
            result matches Ok(true) ==> pattern_match_work(self.nodes@, final(work).view()) < pattern_match_work(self.nodes@, old(work).view().push(task)),
    )]
    #[expect(
        clippy::too_many_arguments,
        reason = "Keep lookup hints separate from verified matcher state."
    )]
    fn matches_step<'value>(
        &self,
        task: (usize, &'value Value),
        symbols: &Symbols,
        bindings: &mut [Value],
        work: &mut WorkVec<(usize, &'value Value)>,
        pattern_hints: &mut Vec<Vec<usize>>,
        timer: &mut ExecutionTimer,
        world: &mut ObservationWorld,
    ) -> KernelResult<bool> {
        proof_decl! { let ghost initial_work = work.view(); let ghost initial_bindings = bindings@; }
        proof! {
            reveal_with_fuel(pattern_head, 2);
            reveal_with_fuel(language::head_match, 2);
            assert(pattern_node_wf(self.nodes@, symbols@, task.0 as int));
            assert forall|theta: language::Subst| pattern_match_state(*self, symbols@, initial_work.push(task), initial_bindings, theta)
                == (partial_bindings(initial_bindings, symbols@, theta) && pattern_pending(*self, symbols@, initial_work, theta)
                    && language::head_match(pattern_head(self.nodes@, symbols@, task.0 as int), value_view(*task.1), theta)) by {
                lemma_pattern_match_state_push(*self, symbols@, initial_work, initial_bindings, task, theta);
            }
        }
        let (id, value) = task;
        checkpoint(timer, world)?;
        if matches!(value, Value::Undefined) {
            proof! {
                assert forall|theta: language::Subst| !language::head_match(pattern_head(self.nodes@, symbols@, task.0 as int), value_view(*value), theta) by {
                    lemma_head_undefined(pattern_head(self.nodes@, symbols@, task.0 as int), theta);
                }
                lemma_pattern_reject(*self, symbols@, initial_work, initial_bindings, task);
            }
            return Ok(false);
        }
        match self
            .nodes
            .get(id)
            .ok_or_else(|| invariant("invalid pattern node ID"))?
        {
            PatternNode::Any => {}
            PatternNode::Literal(id) => {
                let literal = symbols
                    .constants
                    .get(id.index()?)
                    .ok_or_else(|| invariant("invalid literal ID"))?;
                checkpoint(timer, world)?;
                let equal = value == literal;
                checkpoint(timer, world)?;
                if !equal {
                    proof! {
                        assert(pattern_head(self.nodes@, symbols@, task.0 as int) == language::Head::Literal(value_view(*literal)));
                        assert(value_view(*value) != value_view(*literal));
                        assert forall|theta: language::Subst| !language::head_match(pattern_head(self.nodes@, symbols@, task.0 as int), value_view(*value), theta) by {}
                        lemma_pattern_reject(*self, symbols@, initial_work, initial_bindings, task);
                    }
                    return Ok(false);
                }
            }
            PatternNode::Variable(id) => {
                let binding = bindings
                    .get_mut(id.index()?)
                    .ok_or_else(|| invariant("invalid variable ID"))?;
                if matches!(binding, Value::Undefined) {
                    *binding = value.clone();
                    proof! { assert(value_view(*binding) == value_view(*value)); }
                } else {
                    checkpoint(timer, world)?;
                    let equal = value == &*binding;
                    checkpoint(timer, world)?;
                    proof! { assert(equal == (value_view(*value) == value_view(*binding))); }
                    if !equal {
                        proof! {
                            assert(value_view(initial_bindings[id@ as int]) == value_view(*binding));
                            assert(value_view(*value) != value_view(*binding));
                            assert forall|theta: language::Subst| !pattern_match_state(*self, symbols@, initial_work.push(task), initial_bindings, theta) by {
                                lemma_pattern_match_state_push(*self, symbols@, initial_work, initial_bindings, task, theta);
                                assert(pattern_head(self.nodes@, symbols@, task.0 as int) == language::Head::Variable(symbols@.variables[id@ as int]));
                                assert(value_view(initial_bindings[id@ as int]) != Data::Undefined);
                            }
                        }
                        return Ok(false);
                    }
                }
                proof! {
                    assert(value_view(bindings@[id@ as int]) == value_view(*value));
                    lemma_pattern_binding_step(initial_bindings, bindings@, symbols@, id@ as int, value_view(*value));
                }
            }
            PatternNode::Array(children) => {
                proof! { assert(pattern_head(self.nodes@, symbols@, task.0 as int) is Array); }
                let Value::Array(values) = value else {
                    proof! { lemma_pattern_reject(*self, symbols@, initial_work, initial_bindings, task); }
                    return Ok(false);
                };
                proof! {
                    lemma_value_view_array(*values);
                    assert(value_view(*value)->Array_0 =~= values_data(values@));
                }
                if values.len() != children.len() {
                    proof! {
                        assert forall|theta: language::Subst| !language::head_match(pattern_head(self.nodes@, symbols@, task.0 as int), value_view(*value), theta) by {
                            lemma_pattern_array_match(self.nodes@, symbols@, task.0 as int, *children, values@, theta);
                        }
                        lemma_pattern_reject(*self, symbols@, initial_work, initial_bindings, task);
                    }
                    return Ok(false);
                }
                let mut failure = None;
                let mut index = 0_usize;
                #[cfg_attr(verus_keep_ghost, verus_spec(
                    invariant bindings@ == initial_bindings, pattern_work_valid(*self, work.view()),
                        pattern_node_wf(self.nodes@, symbols@, id as int), values@.len() == children@.len(),
                        task.0 == id, id < self.nodes@.len(),
                        forall|i: int| 0 <= i < children@.len() ==> children@[i] < id,
                        self.nodes@[id as int] == PatternNode::Array(*children), *task.1 == Value::Array(*values),
                        value_view(*task.1) == Data::Array(values_data(values@)),
                    invariant_except_break index <= children@.len(),
                        work.view().len() == initial_work.len() + index,
                        work.view().take(initial_work.len() as int) == initial_work,
                        forall|i: int| 0 <= i < index ==> work.view()[initial_work.len() + i].0 == children@[i]
                            && value_view(*work.view()[initial_work.len() + i].1) == value_view(values@[i]),
                    ensures pattern_work_valid(*self, work.view()), bindings@ == initial_bindings,
                        failure is None ==> index == children@.len()
                            && work.view().len() == initial_work.len() + index
                            && work.view().take(initial_work.len() as int) == initial_work
                            && forall|i: int| 0 <= i < index ==> work.view()[initial_work.len() + i].0 == children@[i]
                                && value_view(*work.view()[initial_work.len() + i].1) == value_view(values@[i]),
                    decreases children@.len() - index,
                ))]
                while index < children.len() {
                    proof_decl! { let ghost position = index; }
                    let child = children
                        .get(index)
                        .ok_or_else(|| invariant("invalid pattern child"))?;
                    let value = values
                        .get(index)
                        .ok_or_else(|| invariant("invalid pattern value"))?;
                    proof_decl! { let ghost previous_work = work.view(); }
                    proof! { assert(*child < self.nodes@.len()); }
                    work.push((*child, value));
                    proof! { lemma_pattern_work_push(*self, previous_work, (*child, value)); }
                    loop_try!(checkpoint(timer, world), failure);
                    index = index.saturating_add(1);
                    proof! {
                        assert(index == position + 1);
                        assert forall|i: int| 0 <= i < index implies work.view()[initial_work.len() + i].0 == children@[i]
                            && value_view(*work.view()[initial_work.len() + i].1) == value_view(values@[i]) by {
                            if i < position { assert(work.view()[initial_work.len() + i] == previous_work[initial_work.len() + i]); }
                            else { assert(i == position); }
                        }
                    }
                }
                if let Some(error) = failure {
                    return Err(error);
                }
                proof! {
                    assert forall|theta: language::Subst| pattern_match_state(*self, symbols@, initial_work.push(task), initial_bindings, theta)
                        == pattern_match_state(*self, symbols@, work.view(), bindings@, theta) by {
                        lemma_pattern_match_state_push(*self, symbols@, initial_work, initial_bindings, task, theta);
                        lemma_pattern_array_pending(*self, symbols@, initial_work, work.view(), children@, values@, children@.len() as int, theta);
                        lemma_pattern_array_match(self.nodes@, symbols@, task.0 as int, *children, values@, theta);
                    }
                    lemma_pattern_match_work_expand(self.nodes@, initial_work, task, work.view(), pattern_array_ids(children@));
                }
            }
            PatternNode::Object(children) => {
                proof! { assert(pattern_head(self.nodes@, symbols@, task.0 as int) is Object); }
                let Value::Object(values) = value else {
                    proof! { lemma_pattern_reject(*self, symbols@, initial_work, initial_bindings, task); }
                    return Ok(false);
                };
                let mut failure = None;
                let mut matched = true;
                let mut index = 0_usize;
                #[cfg_attr(verus_keep_ghost, verus_spec(
                    invariant bindings@ == initial_bindings, pattern_work_valid(*self, work.view()),
                        pattern_node_wf(self.nodes@, symbols@, id as int),
                        task.0 == id, id < self.nodes@.len(), *task.1 == *value,
                        forall|i: int| 0 <= i < children@.len() ==> children@[i].1 < id,
                        self.nodes@[id as int] == PatternNode::Object(*children), *value == Value::Object(*values),
                    invariant_except_break index <= children@.len(), matched,
                        work.view().len() == initial_work.len() + index,
                        work.view().take(initial_work.len() as int) == initial_work,
                        forall|i: int| 0 <= i < index ==> work.view()[initial_work.len() + i].0 == children@[i].1
                            && (value_view(*value)->Object_0).contains_key(value_view(children@[i].0))
                            && value_view(*work.view()[initial_work.len() + i].1) == (value_view(*value)->Object_0)[value_view(children@[i].0)],
                    ensures pattern_work_valid(*self, work.view()), bindings@ == initial_bindings,
                        failure is None && matched ==> index == children@.len()
                            && work.view().len() == initial_work.len() + index
                            && work.view().take(initial_work.len() as int) == initial_work
                            && forall|i: int| 0 <= i < index ==> work.view()[initial_work.len() + i].0 == children@[i].1
                                && (value_view(*value)->Object_0).contains_key(value_view(children@[i].0))
                                && value_view(*work.view()[initial_work.len() + i].1) == (value_view(*value)->Object_0)[value_view(children@[i].0)],
                        failure is None && !matched ==> forall|theta: language::Subst| !pattern_match_state(*self, symbols@, initial_work.push(task), initial_bindings, theta),
                    decreases children@.len() - index,
                ))]
                while index < children.len() {
                    let (key, child) = children
                        .get(index)
                        .ok_or_else(|| invariant("invalid pattern field"))?;
                    loop_try!(checkpoint(timer, world), failure);
                    let nodes = pattern_hints.as_mut_slice();
                    let selected = match nodes.get_mut(id) {
                        Some(node_hints) => {
                            let positions = node_hints.as_mut_slice();
                            match positions.get_mut(index) {
                                Some(hint) => values.get_hinted(key, hint),
                                None => values.get(key),
                            }
                        }
                        None => values.get(key),
                    };
                    proof! {
                        lemma_value_view_object(*values);
                        if let Some(selected) = selected {
                            let raw = choose|raw: Value| values@.contains_key(raw) && value_view(raw) == value_view(*key) && *selected == values@[raw];
                            assert((value_view(*value)->Object_0)[value_view(*key)] == value_view(*selected));
                        }
                    }
                    loop_try!(checkpoint(timer, world), failure);
                    match selected {
                        Some(selected) => {
                            proof_decl! { let ghost previous_work = work.view(); }
                            work.push((*child, selected));
                            proof! { lemma_pattern_work_push(*self, previous_work, (*child, selected)); }
                        }
                        None => {
                            proof! {
                                assert(!(value_view(*value)->Object_0).contains_key(value_view(*key)));
                                assert forall|theta: language::Subst| !language::head_match(pattern_head(self.nodes@, symbols@, task.0 as int), value_view(*value), theta) by {
                                    lemma_pattern_object_match(self.nodes@, symbols@, task.0 as int, *children, value_view(*value)->Object_0, theta);
                                    assert(0 <= index < children@.len());
                                }
                                lemma_pattern_reject(*self, symbols@, initial_work, initial_bindings, task);
                            }
                            matched = false;
                            break;
                        }
                    }
                    index = index.saturating_add(1);
                }
                if let Some(error) = failure {
                    return Err(error);
                }
                if !matched {
                    return Ok(false);
                }
                proof! {
                    assert forall|theta: language::Subst| pattern_match_state(*self, symbols@, initial_work.push(task), initial_bindings, theta)
                        == pattern_match_state(*self, symbols@, work.view(), bindings@, theta) by {
                        lemma_pattern_match_state_push(*self, symbols@, initial_work, initial_bindings, task, theta);
                        lemma_pattern_object_pending(*self, symbols@, initial_work, work.view(), children@, value_view(*value)->Object_0, children@.len() as int, theta);
                        lemma_pattern_object_match(self.nodes@, symbols@, task.0 as int, *children, value_view(*value)->Object_0, theta);
                    }
                    lemma_pattern_match_work_expand(self.nodes@, initial_work, task, work.view(), pattern_object_ids(children@));
                }
            }
        }
        proof! {
            if work.view() == initial_work {
                lemma_pattern_match_work_push(self.nodes@, initial_work, task);
            }
        }
        Ok(true)
    }
    #[verus_spec(result =>
        requires exists|head: language::Head| pattern_represents(*self, symbols@, head),
        ensures forall|head: language::Head| pattern_represents(*self, symbols@, head) ==> match result {
            Ok(Some(bindings)) => bindings@.len() == symbols@.variables.len()
                && (forall|i: int| 0 <= i < bindings@.len() ==> value_view(bindings@[i]) != Data::Undefined)
                && language::head_match(head, value_view(*request), theta_of(bindings@, symbols@))
                && theta_of(bindings@, symbols@).dom() == language::head_vars(head),
            Ok(None) => !(exists|theta: language::Subst| theta.dom() == language::head_vars(head)
                && language::head_match(head, value_view(*request), theta)),
            Err(_) => true,
        },
    )]
    pub(crate) fn matches(
        &self,
        request: &Value,
        symbols: &Symbols,
        pattern_hints: &mut Vec<Vec<usize>>,
        timer: &mut ExecutionTimer,
        world: &mut ObservationWorld,
    ) -> KernelResult<Option<Vec<Value>>> {
        proof! {
            let head = choose|head: language::Head| pattern_represents(*self, symbols@, head);
            assert(pattern_nodes_wf(self.nodes@, symbols@));
        }
        let mut bindings = Vec::new();
        allocation(world.try_reserve_exact_vec(&mut bindings, symbols.variables.len()))?;
        bindings.resize(symbols.variables.len(), Value::Undefined);
        let mut work: WorkVec<(usize, &Value)> = WorkVec::new();
        work.push((self.root, request));
        let mut matched = Ok(true);
        proof! {
            assert forall|theta: language::Subst| partial_bindings(bindings@, symbols@, theta) by {
                assert forall|i: int| 0 <= i < bindings@.len() implies value_view(bindings@[i]) == Data::Undefined by {}
            }
            assert forall|theta: language::Subst| language::head_match(pattern_head(self.nodes@, symbols@, self.root as int), value_view(*request), theta)
                == pattern_match_state(*self, symbols@, work.view(), bindings@, theta) by {
                lemma_pattern_match_state_push(*self, symbols@, Seq::empty(), bindings@, (self.root, request), theta);
            }
        }
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant pattern_nodes_wf(self.nodes@, symbols@), self.root < self.nodes@.len(),
                bindings@.len() == symbols@.variables.len(), pattern_work_valid(*self, work.view()),
                forall|theta: language::Subst| match matched {
                    Ok(answer) => #[trigger] language::head_match(pattern_head(self.nodes@, symbols@, self.root as int), value_view(*request), theta)
                        == (answer && pattern_match_state(*self, symbols@, work.view(), bindings@, theta)),
                    Err(_) => true,
                },
            ensures matches!(matched, Ok(true)) ==> work.view().len() == 0,
            decreases if matches!(matched, Ok(true)) { pattern_match_work(self.nodes@, work.view()) + 1 } else { 0 },
        ))]
        while matches!(matched, Ok(true)) {
            proof_decl! { let ghost previous_work = work.view(); let ghost previous_bindings = bindings@; }
            let Some(task) = work.pop() else {
                break;
            };
            proof! {
                assert(work.view().push(task) =~= previous_work);
            }
            proof_decl! { let ghost pending_work = work.view(); }
            matched = self.matches_step(
                task,
                symbols,
                bindings.as_mut_slice(),
                &mut work,
                pattern_hints,
                timer,
                world,
            );
            proof! {
                if let Ok(answer) = matched {
                    assert forall|theta: language::Subst| pattern_match_state(*self, symbols@, pending_work.push(task), previous_bindings, theta)
                        == (answer && pattern_match_state(*self, symbols@, work.view(), bindings@, theta)) by {}
                    assert forall|theta: language::Subst| language::head_match(pattern_head(self.nodes@, symbols@, self.root as int), value_view(*request), theta)
                        == (answer && pattern_match_state(*self, symbols@, work.view(), bindings@, theta)) by {
                        assert(language::head_match(pattern_head(self.nodes@, symbols@, self.root as int), value_view(*request), theta)
                            == pattern_match_state(*self, symbols@, previous_work, previous_bindings, theta));
                        assert(pattern_match_state(*self, symbols@, previous_work, previous_bindings, theta)
                            == (answer && pattern_match_state(*self, symbols@, work.view(), bindings@, theta)));
                    }
                }
            }
        }
        if !matched? {
            return Ok(None);
        }
        proof! {
            lemma_theta_of(bindings@, symbols@);
            assert(work.view().len() == 0);
            assert forall|head: language::Head| pattern_represents(*self, symbols@, head) implies
                language::head_match(head, value_view(*request), theta_of(bindings@, symbols@))
                && forall|i: int| 0 <= i < bindings@.len() ==> value_view(bindings@[i]) != Data::Undefined by {
                assert(language::head_match(head, value_view(*request), theta_of(bindings@, symbols@)));
                assert forall|i: int| 0 <= i < bindings@.len() implies value_view(bindings@[i]) != Data::Undefined by {
                    lemma_head_match_defined(head, value_view(*request), theta_of(bindings@, symbols@), symbols@.variables[i]);
                }
            }
        }
        checkpoint(timer, world)?;
        Ok(Some(bindings))
    }
}

#[verus_verify]
enum SourceWork<'a> {
    Regex(&'a Value, String),
    Test(&'a Value, String),
    RegexMany { tag: &'a str, start: usize },
    RegexOne(&'a str),
    TestMany { and: bool, start: usize },
    LiftTest,
}
#[verus_verify]
#[verus_spec(result =>
    requires model::graph_wf(old(kernel).graph()), old(kernel).valid_store(),
        source_ids_valid(old(kernel).graph(), children@, Seq::empty()),
    ensures model::graph_extends(old(kernel).graph(), final(kernel).graph()), model::graph_wf(final(kernel).graph()), final(kernel).valid_store(),
        final(kernel).restoration() == old(kernel).restoration(),
        result matches Ok(id) ==> source_native_many(final(kernel).graph(), id, children@, tag@),
)]
fn decode_regex_many<S: Storage>(
    kernel: &mut RuntimeKernel<'_, S>,
    children: &[RegexId],
    tag: &str,
) -> KernelResult<RegexId> {
    proof! { language::lemma_source_literals(); }
    if tag == "union" {
        let id = normalize::regex_union(kernel, children)?;
        proof! {
            assert(tag@ == "union"@);
            assert forall|sym: model::Symbols, bindings: Seq<Data>, word: Seq<Data>| model::symbols_wf(sym)
                implies model::regex_lang(kernel.graph(), sym, bindings, id@, word)
                    == (exists|i: int| 0 <= i < children@.len() && model::regex_lang(kernel.graph(), sym, bindings, children@[i]@, word)) by {
                assert(norm::regex_combo(kernel.graph(), sym, bindings, children@, word, false)
                    == (exists|i: int| 0 <= i < children@.len() && model::regex_lang(kernel.graph(), sym, bindings, children@[i]@, word)));
            }
            assert(source_native_many(kernel.graph(), id, children@, tag@));
        }
        Ok(id)
    } else if tag == "concat" {
        let id = normalize::regex_concat(kernel, children)?;
        proof! {
            assert(tag@ == "concat"@);
            assert forall|sym: model::Symbols, bindings: Seq<Data>, word: Seq<Data>| model::symbols_wf(sym)
                implies model::regex_lang(kernel.graph(), sym, bindings, id@, word)
                    == language::lang(model::gsem(sym, bindings), language::Regex::Concat(model::lift_regexes(kernel.graph(), model::regex_ids(children@))), word) by {
                assert(norm::concat_combo(kernel.graph(), sym, bindings, children@, word)
                    == language::lang(model::gsem(sym, bindings), language::Regex::Concat(model::lift_regexes(kernel.graph(), model::regex_ids(children@))), word));
            }
            assert(source_native_many(kernel.graph(), id, children@, tag@));
        }
        Ok(id)
    } else {
        let id = normalize::regex_intersect(kernel, children)?;
        proof! {
            assert(tag@ != "union"@ && tag@ != "concat"@);
            assert forall|sym: model::Symbols, bindings: Seq<Data>, word: Seq<Data>| model::symbols_wf(sym)
                implies model::regex_lang(kernel.graph(), sym, bindings, id@, word)
                    == (forall|i: int| 0 <= i < children@.len() ==> model::regex_lang(kernel.graph(), sym, bindings, children@[i]@, word)) by {
                assert(norm::regex_combo(kernel.graph(), sym, bindings, children@, word, true)
                    == (forall|i: int| 0 <= i < children@.len() ==> model::regex_lang(kernel.graph(), sym, bindings, children@[i]@, word)));
            }
            assert(source_native_many(kernel.graph(), id, children@, tag@));
        }
        Ok(id)
    }
}
#[verus_verify]
#[cfg_attr(verus_keep_ghost, verifier::rlimit(40))]
#[verus_spec(result =>
    requires builder_wf(*old(symbols)), model::graph_wf(old(kernel).graph()), old(kernel).valid_store(),
        source_ids_valid(old(kernel).graph(), old(regexes).view(), old(tests).view()),
    ensures builder_wf(*final(symbols)), symbols_extends(old(symbols).symbols@, final(symbols).symbols@),
        final(symbols).symbols@.variables == old(symbols).symbols@.variables,
        model::graph_extends(old(kernel).graph(), final(kernel).graph()), model::graph_wf(final(kernel).graph()), final(kernel).valid_store(),
        final(kernel).restoration() == old(kernel).restoration(),
        result is Ok ==> source_ids_valid(final(kernel).graph(), final(regexes).view(), final(tests).view())
            && (forall|source: Data| source_state(old(kernel).graph(), old(symbols).symbols@,
                source_work_view(old(work).view()).push(task@), old(regexes).view(), old(tests).view(), source)
                ==> source_state(final(kernel).graph(), final(symbols).symbols@,
                    source_work_view(final(work).view()), final(regexes).view(), final(tests).view(), source))
            && source_work_measure(source_work_view(final(work).view())) < source_work_measure(source_work_view(old(work).view()).push(task@)),
)]
fn decode_step<'source, S: Storage>(
    task: SourceWork<'source>,
    symbols: &mut SymbolBuilder,
    kernel: &mut RuntimeKernel<'_, S>,
    work: &mut WorkVec<SourceWork<'source>>,
    regexes: &mut WorkVec<RegexId>,
    tests: &mut WorkVec<TestId>,
) -> KernelResult<()> {
    proof_decl! {
        let ghost initial_graph = kernel.graph();
        let ghost initial_symbols = symbols.symbols@;
        let ghost pending = source_work_view(work.view());
        let ghost incoming = task@;
        let ghost initial_regexes = regexes.view();
        let ghost initial_tests = tests.view();
    }
    proof! { language::lemma_source_literals(); }
    match task {
        SourceWork::Regex(value, at) => {
            let (tag, payload) = tagged(value, &at)?;
            match tag {
                "empty" | "all" | "epsilon" => {
                    marker(payload, &at)?;
                    let constants = kernel.constants();
                    regexes.push(match tag {
                        "empty" => constants.empty,
                        "all" => constants.all,
                        _ => constants.epsilon,
                    });
                    proof! {
                        let id = regexes.view().last();
                        let tail = if tag@ == "empty"@ { language::Regex::Empty }
                            else if tag@ == "all"@ { language::Regex::All } else { language::Regex::Epsilon };
                        lemma_source_constant_tail(kernel.graph(), symbols.symbols@, id, tag@);
                        assert(language::decodes_tail(value_view(*value), tail));
                        lemma_source_leaf_effect(kernel.graph(), symbols.symbols@, pending, initial_regexes, initial_tests, value_view(*value), id, tail);
                        assert(source_effect(kernel.graph(), symbols.symbols@, pending.push(incoming), initial_regexes, initial_tests,
                            source_work_view(work.view()), regexes.view(), tests.view()));
                    }
                }
                "test" => {
                    work.push(SourceWork::LiftTest);
                    work.push(SourceWork::Test(payload, format!("{at}.test")));
                    proof! {
                        assert(source_work_view(work.view()) =~= pending.push(PendingSourceWork::LiftTest).push(PendingSourceWork::Test(value_view(*payload))));
                        lemma_source_unary_expansion_effect(kernel.graph(), symbols.symbols@, pending, initial_regexes, initial_tests, value_view(*value), tag@, value_view(*payload));
                        assert(source_effect(kernel.graph(), symbols.symbols@, pending.push(incoming), initial_regexes, initial_tests,
                            source_work_view(work.view()), regexes.view(), tests.view()));
                        assert(source_work_view(work.view()) =~= pending.push(PendingSourceWork::LiftTest) + source_jobs(seq![value_view(*payload)], false));
                        lemma_source_measure_expand(pending, incoming, value_view(*value), tag@, value_view(*payload), PendingSourceWork::LiftTest, seq![value_view(*payload)], false);
                    }
                }
                "star" | "not" => {
                    work.push(SourceWork::RegexOne(tag));
                    work.push(SourceWork::Regex(payload, format!("{at}.{tag}")));
                    proof! {
                        assert(source_work_view(work.view()) =~= pending.push(PendingSourceWork::RegexOne(tag@)).push(PendingSourceWork::Regex(value_view(*payload))));
                        lemma_source_unary_expansion_effect(kernel.graph(), symbols.symbols@, pending, initial_regexes, initial_tests, value_view(*value), tag@, value_view(*payload));
                        assert(source_effect(kernel.graph(), symbols.symbols@, pending.push(incoming), initial_regexes, initial_tests,
                            source_work_view(work.view()), regexes.view(), tests.view()));
                        assert(source_work_view(work.view()) =~= pending.push(PendingSourceWork::RegexOne(tag@)) + source_jobs(seq![value_view(*payload)], true));
                        lemma_source_measure_expand(pending, incoming, value_view(*value), tag@, value_view(*payload), PendingSourceWork::RegexOne(tag@), seq![value_view(*payload)], true);
                    }
                }
                "union" | "concat" | "intersect" => {
                    let children = array(payload, &at)?;
                    work.push(SourceWork::RegexMany {
                        tag,
                        start: regexes.len(),
                    });
                    let mut index = children.len();
                    #[cfg_attr(verus_keep_ghost, verus_spec(
                        invariant index <= children@.len(), kernel.graph() == initial_graph,
                            initial_graph == old(kernel).graph(), initial_symbols == old(symbols).symbols@,
                            incoming == PendingSourceWork::Regex(value_view(*value)),
                            kernel.valid_store(), model::graph_wf(kernel.graph()),
                            kernel.restoration() == old(kernel).restoration(),
                            symbols.symbols@ == initial_symbols, builder_wf(*symbols),
                            regexes.view() == initial_regexes, tests.view() == initial_tests,
                            source_work_view(work.view()) == pending.push(PendingSourceWork::RegexMany(tag@, initial_regexes.len()))
                                + source_jobs(values_data(children@).skip(index as int), true),
                        decreases index,
                    ))]
                    while index > 0 {
                        index = index.saturating_sub(1);
                        proof! {
                            assert(source_work_view(work.view()) == pending.push(PendingSourceWork::RegexMany(tag@, initial_regexes.len()))
                                + source_jobs(values_data(children@).skip(index as int + 1), true));
                        }
                        let child = children
                            .as_slice()
                            .get(index)
                            .ok_or_else(|| invariant("invalid regex source child"))?;
                        proof_decl! { let ghost before_push = work.view(); }
                        work.push(SourceWork::Regex(child, child_path(&at, tag, index)));
                        proof! {
                            let suffix = values_data(children@).skip(index as int);
                            assert(suffix[0] == value_view(*child));
                            assert(suffix.drop_first() =~= values_data(children@).skip(index as int + 1));
                            lemma_source_jobs_prepend(suffix, true);
                            assert(source_work_view(work.view()) =~= source_work_view(before_push).push(PendingSourceWork::Regex(value_view(*child))));
                            assert(source_work_view(work.view()) =~= pending.push(PendingSourceWork::RegexMany(tag@, initial_regexes.len()))
                                + source_jobs(values_data(children@).skip(index as int), true));
                        }
                        kernel.checkpoint()?;
                    }
                    proof! {
                        assert(values_data(children@).skip(0) =~= values_data(children@));
                        lemma_source_expansion_effect(kernel.graph(), symbols.symbols@, pending, initial_regexes, initial_tests, value_view(*value), tag@, values_data(children@), true);
                        assert(source_effect(kernel.graph(), symbols.symbols@, pending.push(incoming), initial_regexes, initial_tests,
                            source_work_view(work.view()), regexes.view(), tests.view()));
                        lemma_source_measure_expand(pending, incoming, value_view(*value), tag@, value_view(*payload),
                            PendingSourceWork::RegexMany(tag@, initial_regexes.len()), values_data(children@), true);
                    }
                }
                _ => return Err(invalid(&at, "unknown history regex tag")),
            }
        }
        SourceWork::Test(value, at) => {
            if let Value::Bool(value) = value {
                let constants = kernel.constants();
                tests.push(if *value {
                    constants.test_true
                } else {
                    constants.test_false
                });
                proof! {
                    let id = tests.view().last();
                    lemma_source_constant_test(kernel.graph(), symbols.symbols@, id, *value);
                    lemma_source_test_leaf_effect(kernel.graph(), symbols.symbols@, pending, initial_regexes, initial_tests, Data::Bool(*value), id, language::SrcTest::Bool(*value));
                    lemma_source_step_frame(initial_graph, kernel.graph(), initial_symbols, symbols.symbols@, pending.push(incoming), initial_regexes, initial_tests,
                        source_work_view(work.view()), regexes.view(), tests.view());
                    lemma_source_work_measure_push(pending, incoming);
                }
                return Ok(());
            }
            let (tag, payload) = tagged(value, &at)?;
            match tag {
                "and" | "or" => {
                    let children = array(payload, &at)?;
                    work.push(SourceWork::TestMany {
                        and: tag == "and",
                        start: tests.len(),
                    });
                    let mut index = children.len();
                    #[cfg_attr(verus_keep_ghost, verus_spec(
                        invariant index <= children@.len(), kernel.graph() == initial_graph,
                            initial_graph == old(kernel).graph(), initial_symbols == old(symbols).symbols@,
                            incoming == PendingSourceWork::Test(value_view(*value)),
                            kernel.valid_store(), model::graph_wf(kernel.graph()),
                            kernel.restoration() == old(kernel).restoration(),
                            symbols.symbols@ == initial_symbols, builder_wf(*symbols),
                            regexes.view() == initial_regexes, tests.view() == initial_tests,
                            source_work_view(work.view()) == pending.push(PendingSourceWork::TestMany(tag@ == "and"@, initial_tests.len()))
                                + source_jobs(values_data(children@).skip(index as int), false),
                        decreases index,
                    ))]
                    while index > 0 {
                        index = index.saturating_sub(1);
                        proof! {
                            assert(source_work_view(work.view()) == pending.push(PendingSourceWork::TestMany(tag@ == "and"@, initial_tests.len()))
                                + source_jobs(values_data(children@).skip(index as int + 1), false));
                        }
                        let child = children
                            .as_slice()
                            .get(index)
                            .ok_or_else(|| invariant("invalid test source child"))?;
                        proof_decl! { let ghost before_push = work.view(); }
                        work.push(SourceWork::Test(child, child_path(&at, tag, index)));
                        proof! {
                            let suffix = values_data(children@).skip(index as int);
                            assert(suffix[0] == value_view(*child));
                            assert(suffix.drop_first() =~= values_data(children@).skip(index as int + 1));
                            lemma_source_jobs_prepend(suffix, false);
                            assert(source_work_view(work.view()) =~= source_work_view(before_push).push(PendingSourceWork::Test(value_view(*child))));
                            assert(source_work_view(work.view()) =~= pending.push(PendingSourceWork::TestMany(tag@ == "and"@, initial_tests.len()))
                                + source_jobs(values_data(children@).skip(index as int), false));
                        }
                        kernel.checkpoint()?;
                    }
                    proof! {
                        assert(values_data(children@).skip(0) =~= values_data(children@));
                        lemma_source_expansion_effect(kernel.graph(), symbols.symbols@, pending, initial_regexes, initial_tests, value_view(*value), tag@, values_data(children@), false);
                        assert(source_effect(kernel.graph(), symbols.symbols@, pending.push(incoming), initial_regexes, initial_tests,
                            source_work_view(work.view()), regexes.view(), tests.view()));
                        lemma_source_measure_expand(pending, incoming, value_view(*value), tag@, value_view(*payload),
                            PendingSourceWork::TestMany(tag@ == "and"@, initial_tests.len()), values_data(children@), false);
                    }
                }
                "eq" | "neq" => {
                    let Value::Object(fields) = payload else {
                        return Err(invalid(&at, "comparison payload must be an object"));
                    };
                    if fields.len() != 2 {
                        return Err(invalid(&at, "comparison requires exactly path and term"));
                    }
                    let path_value = member(fields, "path", &at, kernel.timer, kernel.world)?;
                    let term_value = member(fields, "term", &at, kernel.timer, kernel.world)?;
                    proof! {
                        lemma_member_deep(*fields, "path"@, *path_value);
                        lemma_member_deep(*fields, "term"@, *term_value);
                        lemma_value_view_object(*fields);
                        let raw_path = choose|key: Value| fields@.contains_key(key) && value_view(key) == Data::String("path"@) && fields@[key] == *path_value;
                        let raw_term = choose|key: Value| fields@.contains_key(key) && value_view(key) == Data::String("term"@) && fields@[key] == *term_value;
                        let deep = value_view(*payload)->Object_0;
                        lemma_source_comparison_fields(fields@.dom(), deep, raw_path, raw_term, "path"@, "term"@, |key: Value| value_view(key));
                    }
                    let path = symbols.path(array(path_value, &at)?, &at, kernel)?;
                    proof_decl! { let ghost path_symbols = symbols.symbols@; }
                    proof! { lemma_source_symbols_future(initial_symbols, symbols.symbols@); }
                    let term = symbols.term(term_value, &at, kernel)?;
                    proof_decl! {
                        let ghost decoded = choose|decoded: language::Term| language::decodes_term(value_view(*term_value), decoded) && term_represents(symbols.symbols@, term@, decoded);
                    }
                    let presence = kernel.intern_test(TestView::Atom {
                        primitive: Primitive::HasValue(path),
                        positive: true,
                    })?;
                    proof_decl! { let ghost presence_graph = kernel.graph(); }
                    proof! { lemma_source_graph_future(initial_graph, kernel.graph()); }
                    let equality = kernel.intern_test(TestView::Atom {
                        primitive: Primitive::EqCore(path, term),
                        positive: tag == "eq",
                    })?;
                    proof_decl! { let ghost equality_graph = kernel.graph(); }
                    proof! { lemma_source_graph_future(initial_graph, kernel.graph()); }
                    tests.push(normalize::test_and(kernel, &[presence, equality])?);
                    proof! {
                        assert(kernel.graph().tests[presence@ as int] == presence_graph.tests[presence@ as int]);
                        assert(kernel.graph().tests[equality@ as int] == equality_graph.tests[equality@ as int]);
                        assert(symbols.symbols@.paths[path@ as int] == path_symbols.paths[path@ as int]);
                        let id = tests.view().last();
                        lemma_source_comparison_representation(kernel.graph(), symbols.symbols@, path@, term@, decoded, tag@ == "eq"@, presence, equality, id);
                        let predicate = if tag@ == "eq"@ { language::SrcTest::Eq(symbols.symbols@.paths[path@ as int], decoded) }
                            else { language::SrcTest::Neq(symbols.symbols@.paths[path@ as int], decoded) };
                        assert(language::decodes_test(value_view(*value), predicate));
                        lemma_source_test_leaf_effect(kernel.graph(), symbols.symbols@, pending, initial_regexes, initial_tests, value_view(*value), id, predicate);
                        assert(source_effect(kernel.graph(), symbols.symbols@, pending.push(incoming), initial_regexes, initial_tests,
                            source_work_view(work.view()), regexes.view(), tests.view()));
                    }
                }
                _ => return Err(invalid(&at, "unknown test tag")),
            }
        }
        SourceWork::RegexMany { tag, start } => {
            let children = regexes
                .get(start..)
                .ok_or_else(|| invariant("invalid regex source stack"))?;
            proof! { assert(children@ =~= initial_regexes.skip(start as int)); }
            let id = decode_regex_many(kernel, children, tag)?;
            regexes.truncate(start);
            regexes.push(id);
            proof! {
                lemma_source_reduce_many_effect(kernel.graph(), symbols.symbols@, pending, initial_regexes, initial_tests, tag@, start as nat, id);
                assert(source_effect(kernel.graph(), symbols.symbols@, pending.push(incoming), initial_regexes, initial_tests,
                    source_work_view(work.view()), regexes.view(), tests.view()));
            }
        }
        SourceWork::RegexOne(tag) => {
            let child = regexes
                .pop()
                .ok_or_else(|| invariant("missing regex operand"))?;
            regexes.push(if tag == "star" {
                normalize::regex_star(kernel, child)?
            } else {
                normalize::regex_not(kernel, child)?
            });
            proof! {
                lemma_source_reduce_one_effect(kernel.graph(), symbols.symbols@, pending, initial_regexes, initial_tests, tag@, regexes.view().last());
                assert(source_effect(kernel.graph(), symbols.symbols@, pending.push(incoming), initial_regexes, initial_tests,
                    source_work_view(work.view()), regexes.view(), tests.view()));
            }
        }
        SourceWork::TestMany { and, start } => {
            let children = tests
                .get(start..)
                .ok_or_else(|| invariant("invalid test source stack"))?;
            let id = if and {
                normalize::test_and(kernel, children)?
            } else {
                normalize::test_or(kernel, children)?
            };
            tests.truncate(start);
            tests.push(id);
            proof! {
                lemma_source_reduce_test_effect(kernel.graph(), symbols.symbols@, pending, initial_regexes, initial_tests, and, start as nat, id);
                assert(source_effect(kernel.graph(), symbols.symbols@, pending.push(incoming), initial_regexes, initial_tests,
                    source_work_view(work.view()), regexes.view(), tests.view()));
            }
        }
        SourceWork::LiftTest => {
            let test = tests
                .pop()
                .ok_or_else(|| invariant("missing test operand"))?;
            regexes.push(normalize::regex_test(kernel, test)?);
            proof! {
                lemma_source_reduce_lift_effect(kernel.graph(), symbols.symbols@, pending, initial_regexes, initial_tests, regexes.view().last());
                assert(source_effect(kernel.graph(), symbols.symbols@, pending.push(incoming), initial_regexes, initial_tests,
                    source_work_view(work.view()), regexes.view(), tests.view()));
            }
        }
    }
    proof! {
        assert(source_effect(kernel.graph(), symbols.symbols@, pending.push(incoming), initial_regexes, initial_tests,
            source_work_view(work.view()), regexes.view(), tests.view()));
        lemma_source_step_frame(initial_graph, kernel.graph(), initial_symbols, symbols.symbols@, pending.push(incoming), initial_regexes, initial_tests,
            source_work_view(work.view()), regexes.view(), tests.view());
        if source_work_view(work.view()) == pending {
            lemma_source_work_measure_push(pending, incoming);
        }
    }
    Ok(())
}
#[verus_verify]
#[verus_spec(result =>
    requires builder_wf(*old(symbols)), model::graph_wf(old(kernel).graph()), old(kernel).valid_store(),
    ensures builder_wf(*final(symbols)), symbols_extends(old(symbols).symbols@, final(symbols).symbols@),
        final(symbols).symbols@.variables == old(symbols).symbols@.variables,
        model::graph_extends(old(kernel).graph(), final(kernel).graph()), model::graph_wf(final(kernel).graph()), final(kernel).valid_store(),
        final(kernel).restoration() == old(kernel).restoration(),
        result matches Ok(root) ==> exists|tail: language::Regex<language::SrcTest>|
            language::decodes_tail(value_view(*source), tail) && tail_represents(final(kernel).graph(), final(symbols).symbols@, root, tail),
)]
fn decode_history<S: Storage>(
    source: &Value,
    symbols: &mut SymbolBuilder,
    kernel: &mut RuntimeKernel<'_, S>,
) -> KernelResult<RegexId> {
    let mut work: WorkVec<SourceWork<'_>> = WorkVec::new();
    let mut regexes: WorkVec<RegexId> = WorkVec::new();
    let mut tests: WorkVec<TestId> = WorkVec::new();
    work.push(SourceWork::Regex(source, "$.history".to_string()));
    proof! {
        lemma_source_initial(kernel.graph(), symbols.symbols@, value_view(*source));
        assert(source_work_view(work.view()) =~= seq![PendingSourceWork::Regex(value_view(*source))]);
    }
    proof_decl! { let ghost mut pending_work = work.view(); }
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant builder_wf(*symbols), symbols_extends(old(symbols).symbols@, symbols.symbols@),
            symbols.symbols@.variables == old(symbols).symbols@.variables,
            model::graph_extends(old(kernel).graph(), kernel.graph()), model::graph_wf(kernel.graph()), kernel.valid_store(),
            kernel.restoration() == old(kernel).restoration(),
            source_ids_valid(kernel.graph(), regexes.view(), tests.view()),
            work.view() == pending_work,
            source_state(kernel.graph(), symbols.symbols@, source_work_view(pending_work), regexes.view(), tests.view(), value_view(*source)),
        ensures work.view().len() == 0, pending_work.len() == 0,
            kernel.restoration() == old(kernel).restoration(),
        decreases source_work_measure(source_work_view(work.view())),
    ))]
    while let Some(task) = work.pop() {
        proof! {
            assert(pending_work =~= work.view().push(task));
            assert(source_work_view(work.view().push(task)) =~= source_work_view(work.view()).push(task@));
            assert(source_state(kernel.graph(), symbols.symbols@, source_work_view(work.view()).push(task@), regexes.view(), tests.view(), value_view(*source)));
            lemma_source_graph_future(old(kernel).graph(), kernel.graph());
            lemma_source_symbols_future(old(symbols).symbols@, symbols.symbols@);
        }
        kernel.checkpoint()?;
        decode_step(task, symbols, kernel, &mut work, &mut regexes, &mut tests)?;
        proof! {
            assert(source_state(kernel.graph(), symbols.symbols@, source_work_view(work.view()), regexes.view(), tests.view(), value_view(*source)));
            pending_work = work.view();
        }
    }
    if regexes.len() != 1 || !tests.is_empty() {
        return Err(invariant("invalid source root"));
    }
    proof! {
        assert(pending_work.len() == 0);
        assert(source_work_view(work.view()) =~= Seq::empty());
        lemma_source_final(kernel.graph(), symbols.symbols@, regexes.view(), tests.view(), value_view(*source));
    }
    regexes
        .pop()
        .ok_or_else(|| invariant("missing source root"))
}

#[verus_verify]
#[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
#[verus_spec(result =>
    requires old(store).valid_store(), model::graph_wf(old(store).graph()),
        builder_wf(*old(builder)), old(builder).symbols@.variables.len() == 0,
    ensures match result {
        Ok((pattern, root)) => final(store).valid_store()
            && model::graph_wf(final(store).graph()) && builder_wf(*final(builder))
            && (exists|head: language::Head| language::decodes_head(value_view(*request), head)
                && pattern_represents(pattern, final(builder).symbols@, head))
            && (exists|tail: language::Regex<language::SrcTest>| language::decodes_tail(value_view(*history), tail)
                && tail_represents(final(store).graph(), final(builder).symbols@, root, tail)),
        Err(_) => true,
    },
)]
fn compile_into(
    store: &mut CanonicalStore<ArenaStorage>,
    builder: &mut SymbolBuilder,
    request: &Value,
    history: &Value,
    timer: &mut ExecutionTimer,
    world: &mut ObservationWorld,
) -> KernelResult<(CompiledPattern, RegexId)> {
    let mut kernel = RuntimeKernel {
        store,
        timer,
        world,
    };
    let pattern = CompiledPattern::compile(request, builder, &mut kernel)?;
    proof_decl! {
        let ghost head_symbols = builder.symbols@;
        let ghost head = choose|head: language::Head| language::decodes_head(value_view(*request), head)
            && pattern_represents(pattern, head_symbols, head);
    }
    let root = decode_history(history, builder, &mut kernel)?;
    proof! {
        lemma_pattern_represents_extends(pattern, head_symbols, builder.symbols@, head);
        assert(exists|head: language::Head| language::decodes_head(value_view(*request), head)
            && pattern_represents(pattern, builder.symbols@, head));
        assert(kernel.store.valid_store());
        assert(kernel.store.graph() == kernel.graph());
        assert(exists|tail: language::Regex<language::SrcTest>| language::decodes_tail(value_view(*history), tail)
            && tail_represents(kernel.store.graph(), builder.symbols@, root, tail));
    }
    Ok((pattern, root))
}

#[verus_verify]
#[verus_spec(result => ensures result == Err(error))]
fn fail<T>(store: CanonicalStore<ArenaStorage>, error: HistoryError) -> KernelResult<T> {
    store.release();
    Err(error)
}

#[verus_verify]
#[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
#[verus_spec(result =>
    ensures match result {
        Ok(pair) => super::progress::verify::pair_wf(pair)
            && exists|head: language::Head, tail: language::Regex<language::SrcTest>|
                #[trigger] language::decodes_policy(value_view(*policy), head, tail) && super::progress::verify::pair_represents(pair, head, tail),
        Err(_) => true,
    },
)]
pub(crate) fn compile_pair(
    policy: &Value,
    timer: &mut ExecutionTimer,
    world: &mut ObservationWorld,
) -> KernelResult<CompiledPair> {
    checkpoint(timer, world)?;
    let Value::Object(fields) = policy else {
        return Err(invalid("$", "policy must be an object"));
    };
    if fields.len() != 2 {
        return Err(invalid("$", "policy requires exactly history and request"));
    }
    let request = member(fields, "request", "$", timer, world)?;
    let history = member(fields, "history", "$", timer, world)?;
    proof! {
        lemma_value_view_object(*fields);
        lemma_member_deep(*fields, "request"@, *request);
        lemma_member_deep(*fields, "history"@, *history);
        let request_key = choose|key: Value| fields@.contains_key(key) && value_view(key) == Data::String("request"@) && fields@[key] == *request;
        let history_key = choose|key: Value| fields@.contains_key(key) && value_view(key) == Data::String("history"@) && fields@[key] == *history;
        let data = match value_view(*policy) { Data::Object(data) => data, _ => Map::empty() };
        reveal_strlit("request");
        reveal_strlit("history");
        assert("request"@[0] == 'r');
        assert("history"@[0] == 'h');
        assert("request"@ != "history"@);
        lemma_source_comparison_fields(fields@.dom(), data, request_key, history_key, "request"@, "history"@, |key: Value| value_view(key));
    }
    let mut store = CanonicalStore::new(ArenaStorage::new()?, world)?;
    let mut builder = SymbolBuilder::new();
    let (pattern, root) =
        match compile_into(&mut store, &mut builder, request, history, timer, world) {
            Ok(compiled) => compiled,
            Err(error) => return fail(store, error),
        };
    proof! { assert(store.valid_store()); }
    proof_decl! {
        let ghost source_graph = store.graph(); let ghost source_symbols = builder.symbols@;
        let ghost head = choose|head: language::Head| language::decodes_head(value_view(*request), head)
            && pattern_represents(pattern, source_symbols, head);
        let ghost tail = choose|tail: language::Regex<language::SrcTest>| language::decodes_tail(value_view(*history), tail)
            && tail_represents(source_graph, source_symbols, root, tail);
    }
    if let Err(error) = checkpoint(timer, world) {
        return fail(store, error);
    }
    let mut interner = match allocation(Interner::new()) {
        Ok(interner) => interner,
        Err(error) => return fail(store, error),
    };
    let constant_ids = match interner.intern_values(&builder.symbols.constants, world) {
        Ok(ids) => ids,
        Err(error) => {
            interner.free();
            return fail(store, error);
        }
    };
    proof! {
        assert(language::decodes_policy(value_view(*policy), head, tail));
        assert(pattern_represents(pattern, builder.symbols@, head));
        assert(tail_represents(store.graph(), builder.symbols@, root, tail));
    }
    Ok(CompiledPair::new(
        store,
        builder.symbols,
        pattern,
        root,
        interner,
        constant_ids,
    ))
}

/// Exact array index denoted by a float: `Some(i)` iff `value == i` and `i` fits in `u64`.
#[verus_verify]
#[verus_spec(result => ensures result == crate::verify::value_numeric::float_index_spec(value))]
fn float_array_index(value: f64) -> Option<u64> {
    let bits = value.to_bits();
    let magnitude = bits & 0x7fff_ffff_ffff_ffff;
    proof! {
        vstd::arithmetic::power2::lemma2_to64();
        vstd::arithmetic::power2::lemma2_to64_rest();
        crate::verify::value_numeric::lemma_float_bits(value, bits);
        crate::verify::value_numeric::lemma_f64_fields(value);
    }
    if magnitude == 0 {
        return Some(0);
    }
    if bits & 0x8000_0000_0000_0000 != 0 {
        return None;
    }
    let raw = magnitude >> 52;
    let fraction = magnitude & 0x000f_ffff_ffff_ffff;
    let significand = fraction | (1_u64 << 52);
    proof! {
        assert(fraction < 0x0010_0000_0000_0000u64) by(bit_vector)
            requires fraction == (magnitude & 0x000f_ffff_ffff_ffffu64);
        assert(significand == 0x0010_0000_0000_0000u64 + fraction) by(bit_vector)
            requires fraction < 0x0010_0000_0000_0000u64,
                significand == (fraction | (1u64 << 52));
        if 1023 <= raw <= 1086 {
            assert(significand as int == crate::verify::number_specs::f64_scaled_significand(value));
        }
        if 1075 <= raw <= 1086 {
            let shift = (raw - 1075) as u64;
            assert(significand <= (u64::MAX >> shift)) by(bit_vector)
                requires shift <= 11, significand < 0x0020_0000_0000_0000u64;
            vstd::bits::lemma_u64_mul_pow2_le_max_iff_max_shr(significand, shift, u64::MAX);
            vstd::bits::lemma_u64_shl_is_mul(significand, shift);
        }
    }
    match raw {
        1023..=1074 => {
            let shift = 1075 - raw;
            proof! {
                vstd::bits::lemma_u64_pow2_no_overflow(shift as nat);
                vstd::bits::lemma_u64_shl_is_mul(1, shift);
                vstd::bits::lemma_u64_low_bits_mask_is_mod(significand, shift as nat);
                vstd::bits::lemma_u64_shr_is_div(significand, shift);
                assert(((1u64 << shift) - 1) as u64
                    == vstd::bits::low_bits_mask(shift as nat) as u64);
            }
            if significand & ((1_u64 << shift) - 1) != 0 {
                return None;
            }
            Some(significand >> shift)
        }
        1075..=1086 => Some(significand << (raw - 1075)),
        _ => None,
    }
}

#[verus_verify]
#[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
#[verus_spec(result => ensures match result {
    Ok(selected) => option_value_data(selected) == language::select(value_view(*event), values_data(path@)),
    Err(_) => true,
})]
fn select<'a>(
    event: &'a Value,
    path: &[Value],
    hints: &mut Vec<usize>,
    timer: &mut ExecutionTimer,
    world: &mut ObservationWorld,
) -> KernelResult<Option<&'a Value>> {
    let mut current = event;
    let mut index = 0;
    proof! { assert(path@.skip(0) =~= path@); }
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant index <= path@.len(),
            language::select(value_view(*current), values_data(path@.skip(index as int)))
                == language::select(value_view(*event), values_data(path@)),
        decreases path@.len() - index,
    ))]
    while index < path.len() {
        let key = path
            .get(index)
            .ok_or_else(|| invariant("invalid selection cursor"))?;
        checkpoint(timer, world)?;
        let next = match current {
            Value::Object(values) => {
                proof! { lemma_value_view_object(*values); }
                let positions = hints.as_mut_slice();
                match positions.get_mut(index) {
                    Some(hint) => values.get_hinted(key, hint),
                    None => values.get(key),
                }
            }
            Value::Set(values) => {
                proof! { lemma_value_view_set(*values); }
                values.get(key)
            }
            Value::Array(values) => {
                proof! { Array::lemma_len_bound(&**values); lemma_array_data(*values); }
                match key {
                    Value::Number(number) => {
                        let converted = match number {
                            crate::number::Number::Float(f) => float_array_index(*f),
                            _ => number.as_u64(),
                        };
                        proof! { lemma_index_matches_array_index(number@, converted, values@.len()); }
                        match converted {
                            Some(index) => match usize::try_from(index) {
                                Ok(index) => values.get(index),
                                Err(_) => None,
                            },
                            None => None,
                        }
                    }
                    _ => None,
                }
            }
            _ => None,
        };
        proof! {
            lemma_values_data_tail(path@, index as int);
            lemma_source_select_cons(value_view(*current), value_view(*key), values_data(path@.skip(index as int + 1)));
            lemma_source_select_single(value_view(*current), value_view(*key));
            match current {
                Value::Object(_) => { assert(selected_step_data(next) == language::select(value_view(*current), seq![value_view(*key)])); },
                Value::Set(_) => { assert(selected_step_data(next) == language::select(value_view(*current), seq![value_view(*key)])); },
                Value::Array(_) => { assert(selected_step_data(next) == language::select(value_view(*current), seq![value_view(*key)])); },
                _ => { assert(selected_step_data(next) == language::select(value_view(*current), seq![value_view(*key)])); },
            }
        }
        checkpoint(timer, world)?;
        let Some(next) = next else {
            return Ok(None);
        };
        if matches!(next, Value::Undefined) {
            return Ok(None);
        }
        current = next;
        index = index.saturating_add(1);
    }
    Ok(if matches!(current, Value::Undefined) {
        None
    } else {
        Some(current)
    })
}
#[verus_verify]
#[verus_spec(result =>
    requires selections_wf(old(selections)@, symbols@, value_view(*event)),
        old(interner).inv(), ids_wf(*old(interner), bindings@, binding_ids@),
        ids_wf(*old(interner), symbols.constants@, constant_ids@),
    ensures selections_wf(final(selections)@, symbols@, value_view(*event)),
        final(interner).inv(), interner_frame(*old(interner), *final(interner)),
        result matches Ok(answer) ==> answer == model::test_holds(
            symbols@, values_data(bindings@), model::Test::Atom(primitive@, true), value_view(*event)))]
#[expect(
    clippy::too_many_arguments,
    reason = "Keep lookup accelerators separate from semantic inputs."
)]
pub(crate) fn classify<'e>(
    primitive: Primitive,
    event: &'e Value,
    bindings: &[Value],
    binding_ids: &[Option<StringId>],
    symbols: &Symbols,
    constant_ids: &[Option<StringId>],
    interner: &mut Interner,
    path_hints: &mut Vec<Vec<usize>>,
    selections: &mut Vec<Option<Option<&'e Value>>>,
    timer: &mut ExecutionTimer,
    world: &mut ObservationWorld,
) -> KernelResult<bool> {
    checkpoint(timer, world)?;
    let path = match primitive {
        Primitive::HasValue(path) | Primitive::EqCore(path, _) => path,
    };
    let path_index = path.index()?;
    let path = symbols
        .paths
        .get(path_index)
        .ok_or_else(|| invariant("invalid event path ID"))?;
    let cached: Option<Option<&Value>> = match selections.get(path_index) {
        Some(cached) => *cached,
        None => None,
    };
    let selected = match cached {
        Some(selected) => selected,
        None => {
            let paths = path_hints.as_mut_slice();
            let selected = match paths.get_mut(path_index) {
                Some(hints) => select(event, path, hints, timer, world)?,
                None => {
                    let mut none: Vec<usize> = Vec::new();
                    select(event, path, &mut none, timer, world)?
                }
            };
            let slots = selections.as_mut_slice();
            if let Some(slot) = slots.get_mut(path_index) {
                *slot = Some(selected);
            }
            selected
        }
    };
    let answer = match primitive {
        Primitive::HasValue(_) => selected.is_some(),
        Primitive::EqCore(_, term) => {
            let (expected, expected_id) = match term {
                Term::Constant(id) => {
                    let index = id.index()?;
                    let expected = symbols
                        .constants
                        .get(index)
                        .ok_or_else(|| invariant("invalid constant ID"))?;
                    (
                        expected,
                        match constant_ids.get(index) {
                            Some(Some(id)) => Some(*id),
                            _ => None,
                        },
                    )
                }
                Term::Variable(id) => {
                    let index = id.index()?;
                    let expected = bindings
                        .get(index)
                        .ok_or_else(|| invariant("invalid binding ID"))?;
                    (
                        expected,
                        match binding_ids.get(index) {
                            Some(Some(id)) => Some(*id),
                            _ => None,
                        },
                    )
                }
            };
            match selected {
                None => false,
                Some(value) => match (value, expected_id) {
                    (Value::String(text), Some(expected_id)) => {
                        proof_decl! { let ghost before = *interner; }
                        match interner.intern(text) {
                            Some(id) => {
                                proof! {
                                    let chars = match expected { Value::String(text) => text@, _ => Seq::empty() };
                                    lemma_interned_frame(before, *interner, expected_id, chars);
                                    lemma_interned_eq(*interner, text@, id, chars, expected_id);
                                }
                                id.0 == expected_id.0
                            }
                            None => value == expected,
                        }
                    }
                    _ => value == expected,
                },
            }
        }
    };
    checkpoint(timer, world)?;
    Ok(answer)
}

#[cfg(verus_keep_ghost)]
pub(crate) mod verify {
    use super::*;
    verus! {
    pub proof fn lemma_source_jobs_prepend(children: Seq<Data>, regex: bool)
        requires children.len() > 0,
        ensures source_jobs(children.drop_first(), regex).push(if regex { PendingSourceWork::Regex(children[0]) } else { PendingSourceWork::Test(children[0]) }) == source_jobs(children, regex),
    {
        let before = source_jobs(children.drop_first(), regex);
        let task = if regex { PendingSourceWork::Regex(children[0]) } else { PendingSourceWork::Test(children[0]) };
        assert(before.push(task) =~= source_jobs(children, regex));
    }

    pub proof fn lemma_source_graph_future(a: model::Graph, b: model::Graph)
        requires model::graph_extends(a, b),
        ensures forall|c: model::Graph| model::graph_extends(b, c) ==> model::graph_extends(a, c),
    {
        assert forall|c: model::Graph| model::graph_extends(b, c) implies model::graph_extends(a, c) by {
            assert forall|i: int| 0 <= i < a.tests.len() implies a.tests[i] == c.tests[i] by { assert(a.tests[i] == b.tests[i]); }
            assert forall|i: int| 0 <= i < a.regexes.len() implies a.regexes[i] == c.regexes[i] by { assert(a.regexes[i] == b.regexes[i]); }
            assert forall|i: int| 0 <= i < a.transitions.len() implies a.transitions[i] == c.transitions[i] by { assert(a.transitions[i] == b.transitions[i]); }
        }
    }

    pub proof fn lemma_source_symbols_future(a: model::Symbols, b: model::Symbols)
        requires symbols_extends(a, b),
        ensures forall|c: model::Symbols| symbols_extends(b, c) ==> symbols_extends(a, c),
    {
        assert forall|c: model::Symbols| symbols_extends(b, c) implies symbols_extends(a, c) by { lemma_source_symbols_transitive(a, b, c); }
    }

    // Decoder proof definitions; included in source::verify, not a trusted decoder.
    pub open spec fn source_sem(theta: language::Subst) -> spec_fn(language::SrcTest, Data) -> bool {
        |test: language::SrcTest, event: Data| language::src_test_holds(theta, test, event)
    }

    // Extension closure permits symbols to grow while native normalization is
    // specified parametrically over all symbol tables, including later tables.
    pub open spec fn tail_represents(g: model::Graph, sym: model::Symbols, root: RegexId, tail: language::Regex<language::SrcTest>) -> bool {
        root@ < g.regexes.len()
        && forall|later: model::Symbols, bindings: Seq<Data>, theta: language::Subst, word: Seq<Data>|
            symbols_extends(sym, later) && later.variables == sym.variables
            && model::symbols_wf(later) && bindings_agree(later, bindings, theta)
            ==> model::regex_lang(g, later, bindings, root@, word)
                == language::lang(source_sem(theta), tail, word)
    }

    pub open spec fn source_test_represents(g: model::Graph, sym: model::Symbols, root: TestId, test: language::SrcTest) -> bool {
        root@ < g.tests.len()
        && forall|later: model::Symbols, bindings: Seq<Data>, theta: language::Subst, event: Data|
            symbols_extends(sym, later) && later.variables == sym.variables
            && model::symbols_wf(later) && bindings_agree(later, bindings, theta)
            ==> model::test_holds(later, bindings, model::lift_test(g, root@), event)
                == language::src_test_holds(theta, test, event)
    }

    pub proof fn lemma_source_symbols_transitive(a: model::Symbols, b: model::Symbols, c: model::Symbols)
        requires symbols_extends(a, b), symbols_extends(b, c),
        ensures symbols_extends(a, c),
    {
        assert forall|i: int| 0 <= i < a.constants.len() implies a.constants[i] == c.constants[i] by {
            assert(a.constants[i] == b.constants[i]);
        }
        assert forall|i: int| 0 <= i < a.paths.len() implies a.paths[i] == c.paths[i] by {
            assert(a.paths[i] == b.paths[i]);
        }
        assert forall|i: int| 0 <= i < a.variables.len() implies a.variables[i] == c.variables[i] by {
            assert(a.variables[i] == b.variables[i]);
        }
    }

    pub proof fn lemma_tail_represents_frame(g0: model::Graph, g1: model::Graph, s0: model::Symbols, s1: model::Symbols, root: RegexId, tail: language::Regex<language::SrcTest>)
        requires model::graph_wf(g0), model::graph_extends(g0, g1), symbols_extends(s0, s1),
            s1.variables == s0.variables, model::symbols_wf(s1), tail_represents(g0, s0, root, tail),
        ensures tail_represents(g1, s1, root, tail),
    {
        assert(model::tables_wf(g0)) by { model::lemma_graph_wf_elim(g0); }
        model::lemma_lift_regex_stable(g0, g1, root@);
        assert forall|later: model::Symbols, bindings: Seq<Data>, theta: language::Subst, word: Seq<Data>|
            symbols_extends(s1, later) && later.variables == s1.variables
            && model::symbols_wf(later) && bindings_agree(later, bindings, theta)
            implies model::regex_lang(g1, later, bindings, root@, word)
                == language::lang(source_sem(theta), tail, word) by {
            lemma_source_symbols_transitive(s0, s1, later);
            assert(model::regex_lang(g0, later, bindings, root@, word) == language::lang(source_sem(theta), tail, word));
        }
    }

    pub proof fn lemma_source_test_frame(g0: model::Graph, g1: model::Graph, s0: model::Symbols, s1: model::Symbols, root: TestId, test: language::SrcTest)
        requires model::graph_wf(g0), model::graph_extends(g0, g1), symbols_extends(s0, s1),
            s1.variables == s0.variables, model::symbols_wf(s1), source_test_represents(g0, s0, root, test),
        ensures source_test_represents(g1, s1, root, test),
    {
        model::lemma_lift_test_stable(g0, g1, root@);
        assert forall|later: model::Symbols, bindings: Seq<Data>, theta: language::Subst, event: Data|
            symbols_extends(s1, later) && later.variables == s1.variables
            && model::symbols_wf(later) && bindings_agree(later, bindings, theta)
            implies model::test_holds(later, bindings, model::lift_test(g1, root@), event)
                == language::src_test_holds(theta, test, event) by {
            lemma_source_symbols_transitive(s0, s1, later);
            assert(model::test_holds(later, bindings, model::lift_test(g0, root@), event) == language::src_test_holds(theta, test, event));
        }
    }

    pub enum PendingSourceWork {
        Regex(Data), Test(Data), RegexMany(Seq<char>, nat), RegexOne(Seq<char>), TestMany(bool, nat), LiftTest,
    }

    impl View for SourceWork<'_> {
        type V = PendingSourceWork;
        open(super) spec fn view(&self) -> PendingSourceWork {
            match self {
                SourceWork::Regex(value, _) => PendingSourceWork::Regex(value_view(**value)),
                SourceWork::Test(value, _) => PendingSourceWork::Test(value_view(**value)),
                SourceWork::RegexMany { tag, start } => PendingSourceWork::RegexMany(tag@, *start as nat),
                SourceWork::RegexOne(tag) => PendingSourceWork::RegexOne(tag@),
                SourceWork::TestMany { and, start } => PendingSourceWork::TestMany(*and, *start as nat),
                SourceWork::LiftTest => PendingSourceWork::LiftTest,
            }
        }
    }

    pub(super) open spec fn source_work_view(work: Seq<SourceWork<'_>>) -> Seq<PendingSourceWork> {
        work.map(|i: int, task: SourceWork<'_>| task@)
    }

    pub open spec fn source_many(tag: Seq<char>, children: Seq<language::Regex<language::SrcTest>>) -> language::Regex<language::SrcTest> {
        if tag == "union"@ { language::Regex::Union(children) }
        else if tag == "concat"@ { language::Regex::Concat(children) }
        else { language::Regex::Intersect(children) }
    }

    pub open spec fn source_one(tag: Seq<char>, child: language::Regex<language::SrcTest>) -> language::Regex<language::SrcTest> {
        if tag == "star"@ { language::Regex::Star(Box::new(child)) }
        else { language::Regex::Not(Box::new(child)) }
    }

    pub open spec fn source_test_many(and: bool, children: Seq<language::SrcTest>) -> language::SrcTest {
        if and { language::SrcTest::And(children) } else { language::SrcTest::Or(children) }
    }

    // This is a relation on independently decoded witnesses, not an executable
    // decoder. Each pending source consumes its OWN witness; reduction uses the
    // recorded result-stack offset, preserving association and concatenation order.
    pub open spec fn source_run(work: Seq<PendingSourceWork>, regexes: Seq<language::Regex<language::SrcTest>>, tests: Seq<language::SrcTest>, out_regexes: Seq<language::Regex<language::SrcTest>>, out_tests: Seq<language::SrcTest>) -> bool
        decreases work.len(),
    {
        if work.len() == 0 { regexes == out_regexes && tests == out_tests }
        else {
            let rest = work.drop_last();
            match work.last() {
                PendingSourceWork::Regex(data) => exists|tail: language::Regex<language::SrcTest>|
                    language::decodes_tail(data, tail) && source_run(rest, regexes.push(tail), tests, out_regexes, out_tests),
                PendingSourceWork::Test(data) => exists|test: language::SrcTest|
                    language::decodes_test(data, test) && source_run(rest, regexes, tests.push(test), out_regexes, out_tests),
                PendingSourceWork::RegexMany(tag, start) => start <= regexes.len()
                    && source_run(rest, regexes.take(start as int).push(source_many(tag, regexes.skip(start as int))), tests, out_regexes, out_tests),
                PendingSourceWork::RegexOne(tag) => regexes.len() > 0
                    && source_run(rest, regexes.drop_last().push(source_one(tag, regexes.last())), tests, out_regexes, out_tests),
                PendingSourceWork::TestMany(and, start) => start <= tests.len()
                    && source_run(rest, regexes, tests.take(start as int).push(source_test_many(and, tests.skip(start as int))), out_regexes, out_tests),
                PendingSourceWork::LiftTest => tests.len() > 0
                    && source_run(rest, regexes.push(language::Regex::Test(tests.last())), tests.drop_last(), out_regexes, out_tests),
            }
        }
    }

    pub open spec fn source_safe(work: Seq<PendingSourceWork>, regexes: Seq<language::Regex<language::SrcTest>>, tests: Seq<language::SrcTest>, source: Data) -> bool {
        forall|out_regexes: Seq<language::Regex<language::SrcTest>>, out_tests: Seq<language::SrcTest>|
            source_run(work, regexes, tests, out_regexes, out_tests)
            ==> out_regexes.len() == 1 && out_tests.len() == 0 && language::decodes_tail(source, out_regexes[0])
    }

    pub open spec fn source_stacks_represents(g: model::Graph, sym: model::Symbols, regexes: Seq<RegexId>, tests: Seq<TestId>, tails: Seq<language::Regex<language::SrcTest>>, predicates: Seq<language::SrcTest>) -> bool {
        regexes.len() == tails.len() && tests.len() == predicates.len()
        && (forall|i: int| 0 <= i < regexes.len() ==> tail_represents(g, sym, regexes[i], tails[i]))
        && (forall|i: int| 0 <= i < tests.len() ==> source_test_represents(g, sym, tests[i], predicates[i]))
    }

    pub open spec fn source_state(g: model::Graph, sym: model::Symbols, work: Seq<PendingSourceWork>, regexes: Seq<RegexId>, tests: Seq<TestId>, source: Data) -> bool {
        exists|tails: Seq<language::Regex<language::SrcTest>>, predicates: Seq<language::SrcTest>|
            source_stacks_represents(g, sym, regexes, tests, tails, predicates)
            && source_safe(work, tails, predicates, source)
    }

    pub proof fn lemma_source_stacks_frame(g0: model::Graph, g1: model::Graph, s0: model::Symbols, s1: model::Symbols, regexes: Seq<RegexId>, tests: Seq<TestId>, tails: Seq<language::Regex<language::SrcTest>>, predicates: Seq<language::SrcTest>)
        requires model::graph_wf(g0), model::graph_extends(g0, g1), symbols_extends(s0, s1), s1.variables == s0.variables,
            model::symbols_wf(s1), source_stacks_represents(g0, s0, regexes, tests, tails, predicates),
        ensures source_stacks_represents(g1, s1, regexes, tests, tails, predicates),
    {
        assert forall|i: int| 0 <= i < regexes.len() implies tail_represents(g1, s1, regexes[i], tails[i]) by {
            lemma_tail_represents_frame(g0, g1, s0, s1, regexes[i], tails[i]);
        }
        assert forall|i: int| 0 <= i < tests.len() implies source_test_represents(g1, s1, tests[i], predicates[i]) by {
            lemma_source_test_frame(g0, g1, s0, s1, tests[i], predicates[i]);
        }
    }

    pub proof fn lemma_source_state_frame(g0: model::Graph, g1: model::Graph, s0: model::Symbols, s1: model::Symbols, work: Seq<PendingSourceWork>, regexes: Seq<RegexId>, tests: Seq<TestId>, source: Data)
        requires model::graph_wf(g0), model::graph_extends(g0, g1), symbols_extends(s0, s1), s1.variables == s0.variables,
            model::symbols_wf(s1), source_state(g0, s0, work, regexes, tests, source),
        ensures source_state(g1, s1, work, regexes, tests, source),
    {
        let (tails, predicates) = choose|tails: Seq<language::Regex<language::SrcTest>>, predicates: Seq<language::SrcTest>|
            source_stacks_represents(g0, s0, regexes, tests, tails, predicates) && source_safe(work, tails, predicates, source);
        lemma_source_stacks_frame(g0, g1, s0, s1, regexes, tests, tails, predicates);
        assert(source_state(g1, s1, work, regexes, tests, source));
    }

    pub open spec fn source_jobs(children: Seq<Data>, regex: bool) -> Seq<PendingSourceWork> {
        Seq::new(children.len(), |i: int| if regex { PendingSourceWork::Regex(children[children.len() - 1 - i]) }
            else { PendingSourceWork::Test(children[children.len() - 1 - i]) })
    }

    pub proof fn lemma_source_run_jobs(work: Seq<PendingSourceWork>, children: Seq<Data>, regex: bool, rs: Seq<language::Regex<language::SrcTest>>, ts: Seq<language::SrcTest>, out_rs: Seq<language::Regex<language::SrcTest>>, out_ts: Seq<language::SrcTest>)
        requires source_run(work + source_jobs(children, regex), rs, ts, out_rs, out_ts),
        ensures if regex {
            exists|tails: Seq<language::Regex<language::SrcTest>>| tails.len() == children.len()
                && (forall|i: int| 0 <= i < children.len() ==> language::decodes_tail(children[i], tails[i]))
                && source_run(work, rs + tails, ts, out_rs, out_ts)
        } else {
            exists|predicates: Seq<language::SrcTest>| predicates.len() == children.len()
                && (forall|i: int| 0 <= i < children.len() ==> language::decodes_test(children[i], predicates[i]))
                && source_run(work, rs, ts + predicates, out_rs, out_ts)
        },
        decreases children.len(),
    {
        if children.len() == 0 {
            assert(source_jobs(children, regex) =~= Seq::empty());
            if regex { assert(rs + Seq::empty() =~= rs); }
            else { assert(ts + Seq::empty() =~= ts); }
        } else {
            let jobs = source_jobs(children, regex);
            assert(jobs.drop_last() =~= source_jobs(children.drop_first(), regex));
            assert((work + jobs).drop_last() =~= work + source_jobs(children.drop_first(), regex));
            if regex {
                let tail = choose|tail: language::Regex<language::SrcTest>| language::decodes_tail(children[0], tail)
                    && source_run(work + source_jobs(children.drop_first(), regex), rs.push(tail), ts, out_rs, out_ts);
                lemma_source_run_jobs(work, children.drop_first(), regex, rs.push(tail), ts, out_rs, out_ts);
                let tails = choose|tails: Seq<language::Regex<language::SrcTest>>| tails.len() == children.drop_first().len()
                    && (forall|i: int| 0 <= i < children.drop_first().len() ==> language::decodes_tail(children.drop_first()[i], tails[i]))
                    && source_run(work, rs.push(tail) + tails, ts, out_rs, out_ts);
                let all = seq![tail] + tails;
                assert(rs.push(tail) + tails =~= rs + all);
                assert forall|i: int| 0 <= i < children.len() implies language::decodes_tail(children[i], all[i]) by {
                    if i > 0 { assert(children[i] == children.drop_first()[i - 1]); }
                }
                assert(exists|all: Seq<language::Regex<language::SrcTest>>| all.len() == children.len()
                    && (forall|i: int| 0 <= i < children.len() ==> language::decodes_tail(children[i], all[i]))
                    && source_run(work, rs + all, ts, out_rs, out_ts));
            } else {
                let test = choose|test: language::SrcTest| language::decodes_test(children[0], test)
                    && source_run(work + source_jobs(children.drop_first(), regex), rs, ts.push(test), out_rs, out_ts);
                lemma_source_run_jobs(work, children.drop_first(), regex, rs, ts.push(test), out_rs, out_ts);
                let predicates = choose|predicates: Seq<language::SrcTest>| predicates.len() == children.drop_first().len()
                    && (forall|i: int| 0 <= i < children.drop_first().len() ==> language::decodes_test(children.drop_first()[i], predicates[i]))
                    && source_run(work, rs, ts.push(test) + predicates, out_rs, out_ts);
                let all = seq![test] + predicates;
                assert(ts.push(test) + predicates =~= ts + all);
                assert forall|i: int| 0 <= i < children.len() implies language::decodes_test(children[i], all[i]) by {
                    if i > 0 { assert(children[i] == children.drop_first()[i - 1]); }
                }
                assert(exists|all: Seq<language::SrcTest>| all.len() == children.len()
                    && (forall|i: int| 0 <= i < children.len() ==> language::decodes_test(children[i], all[i]))
                    && source_run(work, rs, ts + all, out_rs, out_ts));
            }
        }
    }

    pub open spec fn source_refines(before: Seq<PendingSourceWork>, rs: Seq<language::Regex<language::SrcTest>>, ts: Seq<language::SrcTest>, after: Seq<PendingSourceWork>, next_rs: Seq<language::Regex<language::SrcTest>>, next_ts: Seq<language::SrcTest>) -> bool {
        forall|out_rs: Seq<language::Regex<language::SrcTest>>, out_ts: Seq<language::SrcTest>|
            source_run(after, next_rs, next_ts, out_rs, out_ts) ==> source_run(before, rs, ts, out_rs, out_ts)
    }

    pub open spec fn source_effect(g: model::Graph, sym: model::Symbols, before: Seq<PendingSourceWork>, rs: Seq<RegexId>, ts: Seq<TestId>, after: Seq<PendingSourceWork>, next_rs: Seq<RegexId>, next_ts: Seq<TestId>) -> bool {
        forall|tails: Seq<language::Regex<language::SrcTest>>, predicates: Seq<language::SrcTest>|
            source_stacks_represents(g, sym, rs, ts, tails, predicates)
            ==> exists|next_tails: Seq<language::Regex<language::SrcTest>>, next_predicates: Seq<language::SrcTest>|
                source_stacks_represents(g, sym, next_rs, next_ts, next_tails, next_predicates)
                && source_refines(before, tails, predicates, after, next_tails, next_predicates)
    }

    pub proof fn lemma_source_effect_state(g: model::Graph, sym: model::Symbols, before: Seq<PendingSourceWork>, rs: Seq<RegexId>, ts: Seq<TestId>, after: Seq<PendingSourceWork>, next_rs: Seq<RegexId>, next_ts: Seq<TestId>, source: Data)
        requires source_effect(g, sym, before, rs, ts, after, next_rs, next_ts), source_state(g, sym, before, rs, ts, source),
        ensures source_state(g, sym, after, next_rs, next_ts, source),
    {
        let (tails, predicates) = choose|tails: Seq<language::Regex<language::SrcTest>>, predicates: Seq<language::SrcTest>|
            source_stacks_represents(g, sym, rs, ts, tails, predicates) && source_safe(before, tails, predicates, source);
        let (next_tails, next_predicates) = choose|next_tails: Seq<language::Regex<language::SrcTest>>, next_predicates: Seq<language::SrcTest>|
            source_stacks_represents(g, sym, next_rs, next_ts, next_tails, next_predicates)
                && source_refines(before, tails, predicates, after, next_tails, next_predicates);
        assert(source_safe(after, next_tails, next_predicates, source));
        assert(source_state(g, sym, after, next_rs, next_ts, source));
    }

    pub proof fn lemma_source_leaf_effect(g: model::Graph, sym: model::Symbols, pending: Seq<PendingSourceWork>, rs: Seq<RegexId>, ts: Seq<TestId>, data: Data, id: RegexId, tail: language::Regex<language::SrcTest>)
        requires tail_represents(g, sym, id, tail), language::decodes_tail(data, tail),
        ensures source_effect(g, sym, pending.push(PendingSourceWork::Regex(data)), rs, ts, pending, rs.push(id), ts),
    {
        assert forall|tails: Seq<language::Regex<language::SrcTest>>, predicates: Seq<language::SrcTest>|
            source_stacks_represents(g, sym, rs, ts, tails, predicates)
            implies exists|next_tails: Seq<language::Regex<language::SrcTest>>, next_predicates: Seq<language::SrcTest>|
                source_stacks_represents(g, sym, rs.push(id), ts, next_tails, next_predicates)
                && source_refines(pending.push(PendingSourceWork::Regex(data)), tails, predicates, pending, next_tails, next_predicates) by {
            assert(source_stacks_represents(g, sym, rs.push(id), ts, tails.push(tail), predicates));
            assert forall|out_rs: Seq<language::Regex<language::SrcTest>>, out_ts: Seq<language::SrcTest>|
                source_run(pending, tails.push(tail), predicates, out_rs, out_ts)
                implies source_run(pending.push(PendingSourceWork::Regex(data)), tails, predicates, out_rs, out_ts) by {
                reveal_with_fuel(source_run, 2);
                assert(pending.push(PendingSourceWork::Regex(data)).drop_last() =~= pending);
                assert(exists|r: language::Regex<language::SrcTest>| language::decodes_tail(data, r)
                    && source_run(pending, tails.push(r), predicates, out_rs, out_ts));
            }
        }
    }

    pub proof fn lemma_source_test_leaf_effect(g: model::Graph, sym: model::Symbols, pending: Seq<PendingSourceWork>, rs: Seq<RegexId>, ts: Seq<TestId>, data: Data, id: TestId, test: language::SrcTest)
        requires source_test_represents(g, sym, id, test), language::decodes_test(data, test),
        ensures source_effect(g, sym, pending.push(PendingSourceWork::Test(data)), rs, ts, pending, rs, ts.push(id)),
    {
        assert forall|tails: Seq<language::Regex<language::SrcTest>>, predicates: Seq<language::SrcTest>|
            source_stacks_represents(g, sym, rs, ts, tails, predicates)
            implies exists|next_tails: Seq<language::Regex<language::SrcTest>>, next_predicates: Seq<language::SrcTest>|
                source_stacks_represents(g, sym, rs, ts.push(id), next_tails, next_predicates)
                && source_refines(pending.push(PendingSourceWork::Test(data)), tails, predicates, pending, next_tails, next_predicates) by {
            assert(source_stacks_represents(g, sym, rs, ts.push(id), tails, predicates.push(test)));
            assert forall|out_rs: Seq<language::Regex<language::SrcTest>>, out_ts: Seq<language::SrcTest>|
                source_run(pending, tails, predicates.push(test), out_rs, out_ts)
                implies source_run(pending.push(PendingSourceWork::Test(data)), tails, predicates, out_rs, out_ts) by {
                reveal_with_fuel(source_run, 2);
                assert(pending.push(PendingSourceWork::Test(data)).drop_last() =~= pending);
                assert(exists|t: language::SrcTest| language::decodes_test(data, t)
                    && source_run(pending, tails, predicates.push(t), out_rs, out_ts));
            }
        }
    }

    pub proof fn lemma_source_expansion_refines(pending: Seq<PendingSourceWork>, data: Data, tag: Seq<char>, children: Seq<Data>, regex: bool, rs: Seq<language::Regex<language::SrcTest>>, ts: Seq<language::SrcTest>)
        requires language::tagged_payload(data, tag) == Some(Data::Array(children)),
            if regex { tag == "union"@ || tag == "concat"@ || tag == "intersect"@ } else { tag == "and"@ || tag == "or"@ },
        ensures source_refines(pending.push(if regex { PendingSourceWork::Regex(data) } else { PendingSourceWork::Test(data) }), rs, ts,
            pending.push(if regex { PendingSourceWork::RegexMany(tag, rs.len()) } else { PendingSourceWork::TestMany(tag == "and"@, ts.len()) })
                + source_jobs(children, regex), rs, ts),
    {
        let finish = if regex { PendingSourceWork::RegexMany(tag, rs.len()) } else { PendingSourceWork::TestMany(tag == "and"@, ts.len()) };
        assert forall|out_rs: Seq<language::Regex<language::SrcTest>>, out_ts: Seq<language::SrcTest>|
            source_run(pending.push(finish) + source_jobs(children, regex), rs, ts, out_rs, out_ts)
            implies source_run(pending.push(if regex { PendingSourceWork::Regex(data) } else { PendingSourceWork::Test(data) }), rs, ts, out_rs, out_ts) by {
            reveal_with_fuel(source_run, 3);
            assert(pending.push(finish).drop_last() =~= pending);
            assert(pending.push(if regex { PendingSourceWork::Regex(data) } else { PendingSourceWork::Test(data) }).drop_last() =~= pending);
            lemma_source_run_jobs(pending.push(finish), children, regex, rs, ts, out_rs, out_ts);
            if regex {
                let tails = choose|tails: Seq<language::Regex<language::SrcTest>>| tails.len() == children.len()
                    && (forall|i: int| 0 <= i < children.len() ==> language::decodes_tail(children[i], tails[i]))
                    && source_run(pending.push(finish), rs + tails, ts, out_rs, out_ts);
                assert((rs + tails).take(rs.len() as int) =~= rs);
                assert((rs + tails).skip(rs.len() as int) =~= tails);
                let tail = source_many(tag, tails);
                assert(language::decodes_tail(data, tail));
                assert(source_run(pending, rs.push(tail), ts, out_rs, out_ts));
                assert(exists|r: language::Regex<language::SrcTest>| language::decodes_tail(data, r)
                    && source_run(pending, rs.push(r), ts, out_rs, out_ts));
            } else {
                let predicates = choose|predicates: Seq<language::SrcTest>| predicates.len() == children.len()
                    && (forall|i: int| 0 <= i < children.len() ==> language::decodes_test(children[i], predicates[i]))
                    && source_run(pending.push(finish), rs, ts + predicates, out_rs, out_ts);
                assert((ts + predicates).take(ts.len() as int) =~= ts);
                assert((ts + predicates).skip(ts.len() as int) =~= predicates);
                let test = source_test_many(tag == "and"@, predicates);
                assert(language::decodes_test(data, test));
                assert(source_run(pending, rs, ts.push(test), out_rs, out_ts));
                assert(exists|t: language::SrcTest| language::decodes_test(data, t)
                    && source_run(pending, rs, ts.push(t), out_rs, out_ts));
            }
        }
    }

    pub proof fn lemma_source_expansion_effect(g: model::Graph, sym: model::Symbols, pending: Seq<PendingSourceWork>, rs: Seq<RegexId>, ts: Seq<TestId>, data: Data, tag: Seq<char>, children: Seq<Data>, regex: bool)
        requires language::tagged_payload(data, tag) == Some(Data::Array(children)),
            if regex { tag == "union"@ || tag == "concat"@ || tag == "intersect"@ } else { tag == "and"@ || tag == "or"@ },
        ensures source_effect(g, sym, pending.push(if regex { PendingSourceWork::Regex(data) } else { PendingSourceWork::Test(data) }), rs, ts,
            pending.push(if regex { PendingSourceWork::RegexMany(tag, rs.len()) } else { PendingSourceWork::TestMany(tag == "and"@, ts.len()) })
                + source_jobs(children, regex), rs, ts),
    {
        assert forall|tails: Seq<language::Regex<language::SrcTest>>, predicates: Seq<language::SrcTest>|
            source_stacks_represents(g, sym, rs, ts, tails, predicates)
            implies exists|next_tails: Seq<language::Regex<language::SrcTest>>, next_predicates: Seq<language::SrcTest>|
                source_stacks_represents(g, sym, rs, ts, next_tails, next_predicates)
                && source_refines(pending.push(if regex { PendingSourceWork::Regex(data) } else { PendingSourceWork::Test(data) }), tails, predicates,
                    pending.push(if regex { PendingSourceWork::RegexMany(tag, rs.len()) } else { PendingSourceWork::TestMany(tag == "and"@, ts.len()) }) + source_jobs(children, regex), next_tails, next_predicates) by {
            lemma_source_expansion_refines(pending, data, tag, children, regex, tails, predicates);
        }
    }

    pub proof fn lemma_source_unary_expansion_effect(g: model::Graph, sym: model::Symbols, pending: Seq<PendingSourceWork>, rs: Seq<RegexId>, ts: Seq<TestId>, data: Data, tag: Seq<char>, payload: Data)
        requires language::tagged_payload(data, tag) == Some(payload), tag == "star"@ || tag == "not"@ || tag == "test"@,
        ensures source_effect(g, sym, pending.push(PendingSourceWork::Regex(data)), rs, ts,
            pending.push(if tag == "test"@ { PendingSourceWork::LiftTest } else { PendingSourceWork::RegexOne(tag) })
                .push(if tag == "test"@ { PendingSourceWork::Test(payload) } else { PendingSourceWork::Regex(payload) }), rs, ts),
    {
        let after = pending.push(if tag == "test"@ { PendingSourceWork::LiftTest } else { PendingSourceWork::RegexOne(tag) })
            .push(if tag == "test"@ { PendingSourceWork::Test(payload) } else { PendingSourceWork::Regex(payload) });
        assert forall|tails: Seq<language::Regex<language::SrcTest>>, predicates: Seq<language::SrcTest>|
            source_stacks_represents(g, sym, rs, ts, tails, predicates)
            implies exists|next_tails: Seq<language::Regex<language::SrcTest>>, next_predicates: Seq<language::SrcTest>|
                source_stacks_represents(g, sym, rs, ts, next_tails, next_predicates)
                && source_refines(pending.push(PendingSourceWork::Regex(data)), tails, predicates, after, next_tails, next_predicates) by {
            assert forall|out_rs: Seq<language::Regex<language::SrcTest>>, out_ts: Seq<language::SrcTest>|
                source_run(after, tails, predicates, out_rs, out_ts)
                implies source_run(pending.push(PendingSourceWork::Regex(data)), tails, predicates, out_rs, out_ts) by {
                reveal_with_fuel(source_run, 3);
                assert(after.drop_last().drop_last() =~= pending);
                assert(pending.push(PendingSourceWork::Regex(data)).drop_last() =~= pending);
                if tag == "test"@ {
                    let test = choose|test: language::SrcTest| language::decodes_test(payload, test)
                        && source_run(after.drop_last(), tails, predicates.push(test), out_rs, out_ts);
                    assert(predicates.push(test).drop_last() =~= predicates);
                    let tail = language::Regex::Test(test);
                    assert(language::decodes_tail(data, tail));
                    assert(source_run(pending, tails.push(tail), predicates, out_rs, out_ts));
                    assert(exists|r: language::Regex<language::SrcTest>| language::decodes_tail(data, r)
                        && source_run(pending, tails.push(r), predicates, out_rs, out_ts));
                } else {
                    let child = choose|child: language::Regex<language::SrcTest>| language::decodes_tail(payload, child)
                        && source_run(after.drop_last(), tails.push(child), predicates, out_rs, out_ts);
                    assert(tails.push(child).drop_last() =~= tails);
                    let tail = source_one(tag, child);
                    assert(language::decodes_tail(data, tail));
                    assert(source_run(pending, tails.push(tail), predicates, out_rs, out_ts));
                    assert(exists|r: language::Regex<language::SrcTest>| language::decodes_tail(data, r)
                        && source_run(pending, tails.push(r), predicates, out_rs, out_ts));
                }
            }
        }
    }

    pub open spec fn source_native_many(g: model::Graph, out: RegexId, children: Seq<RegexId>, tag: Seq<char>) -> bool {
        out@ < g.regexes.len() && forall|sym: model::Symbols, bindings: Seq<Data>, word: Seq<Data>| model::symbols_wf(sym)
            ==> model::regex_lang(g, sym, bindings, out@, word) == if tag == "union"@ {
                exists|i: int| 0 <= i < children.len() && model::regex_lang(g, sym, bindings, children[i]@, word)
            } else if tag == "concat"@ {
                language::lang(model::gsem(sym, bindings), language::Regex::Concat(model::lift_regexes(g, model::regex_ids(children))), word)
            } else {
                forall|i: int| 0 <= i < children.len() ==> model::regex_lang(g, sym, bindings, children[i]@, word)
            }
    }

    pub proof fn lemma_source_many_representation(g: model::Graph, sym: model::Symbols, children: Seq<RegexId>, tails: Seq<language::Regex<language::SrcTest>>, tag: Seq<char>, out: RegexId)
        requires children.len() == tails.len(), source_native_many(g, out, children, tag),
            forall|i: int| 0 <= i < children.len() ==> tail_represents(g, sym, children[i], tails[i]),
        ensures tail_represents(g, sym, out, source_many(tag, tails)),
    {
        assert forall|later: model::Symbols, bindings: Seq<Data>, theta: language::Subst, word: Seq<Data>|
            symbols_extends(sym, later) && later.variables == sym.variables && model::symbols_wf(later) && bindings_agree(later, bindings, theta)
            implies model::regex_lang(g, later, bindings, out@, word) == language::lang(source_sem(theta), source_many(tag, tails), word) by {
            reveal_with_fuel(language::lang, 2);
            language::lemma_lang_union(source_sem(theta), tails, word);
            language::lemma_lang_intersect(source_sem(theta), tails, word);
            assert(model::regex_lang(g, later, bindings, out@, word) == if tag == "union"@ {
                exists|i: int| 0 <= i < children.len() && model::regex_lang(g, later, bindings, children[i]@, word)
            } else if tag == "concat"@ {
                language::lang(model::gsem(later, bindings), language::Regex::Concat(model::lift_regexes(g, model::regex_ids(children))), word)
            } else { forall|i: int| 0 <= i < children.len() ==> model::regex_lang(g, later, bindings, children[i]@, word) });
            assert forall|i: int, part: Seq<Data>| 0 <= i < children.len()
                implies model::regex_lang(g, later, bindings, children[i]@, part) == language::lang(source_sem(theta), tails[i], part) by {
                assert(tail_represents(g, sym, children[i], tails[i]));
            }
            if tag == "concat"@ {
                let lifted = model::lift_regexes(g, model::regex_ids(children));
                assert(lifted.len() == tails.len());
                assert forall|parts: Seq<Seq<Data>>| parts.len() == tails.len()
                    implies (forall|i: int| 0 <= i < tails.len() ==> language::lang(model::gsem(later, bindings), lifted[i], parts[i]))
                        == (forall|i: int| 0 <= i < tails.len() ==> language::lang(source_sem(theta), tails[i], parts[i])) by {
                    assert forall|i: int| 0 <= i < tails.len()
                        implies language::lang(model::gsem(later, bindings), lifted[i], parts[i]) == language::lang(source_sem(theta), tails[i], parts[i]) by {
                        assert(lifted[i] == model::lift_regex(g, children[i]@));
                    }
                }
                if language::lang(model::gsem(later, bindings), language::Regex::Concat(lifted), word) {
                    let parts = choose|parts: Seq<Seq<Data>>| parts.len() == lifted.len() && word == parts.flatten()
                        && forall|i: int| 0 <= i < lifted.len() ==> language::lang(model::gsem(later, bindings), lifted[i], parts[i]);
                    assert(language::lang(source_sem(theta), language::Regex::Concat(tails), word));
                }
                if language::lang(source_sem(theta), language::Regex::Concat(tails), word) {
                    let parts = choose|parts: Seq<Seq<Data>>| parts.len() == tails.len() && word == parts.flatten()
                        && forall|i: int| 0 <= i < tails.len() ==> language::lang(source_sem(theta), tails[i], parts[i]);
                    assert(language::lang(model::gsem(later, bindings), language::Regex::Concat(lifted), word));
                }
            } else if tag == "union"@ {
                if model::regex_lang(g, later, bindings, out@, word) {
                    let i = choose|i: int| 0 <= i < children.len() && model::regex_lang(g, later, bindings, children[i]@, word);
                    assert(language::lang(source_sem(theta), tails[i], word));
                    assert(exists|j: int| 0 <= j < tails.len() && language::lang(source_sem(theta), tails[j], word));
                    assert(language::lang(source_sem(theta), language::Regex::Union(tails), word));
                }
                if language::lang(source_sem(theta), language::Regex::Union(tails), word) {
                    let i = choose|i: int| 0 <= i < tails.len() && language::lang(source_sem(theta), tails[i], word);
                    assert(model::regex_lang(g, later, bindings, children[i]@, word));
                    assert(model::regex_lang(g, later, bindings, out@, word));
                }
            } else {
                if model::regex_lang(g, later, bindings, out@, word) {
                    assert forall|i: int| 0 <= i < tails.len() implies language::lang(source_sem(theta), tails[i], word) by {}
                }
                if language::lang(source_sem(theta), language::Regex::Intersect(tails), word) {
                    assert forall|i: int| 0 <= i < children.len() implies model::regex_lang(g, later, bindings, children[i]@, word) by {
                        assert(language::lang(source_sem(theta), tails[i], word));
                    }
                }
            }
        }
    }

    pub open spec fn source_native_one(g: model::Graph, out: RegexId, child: RegexId, tag: Seq<char>) -> bool {
        out@ < g.regexes.len() && forall|sym: model::Symbols, bindings: Seq<Data>, word: Seq<Data>| model::symbols_wf(sym)
            ==> model::regex_lang(g, sym, bindings, out@, word) == if tag == "star"@ {
                language::lang(model::gsem(sym, bindings), language::Regex::Star(Box::new(model::lift_regex(g, child@))), word)
            } else { !model::regex_lang(g, sym, bindings, child@, word) }
    }

    pub proof fn lemma_source_one_representation(g: model::Graph, sym: model::Symbols, child: RegexId, tail: language::Regex<language::SrcTest>, tag: Seq<char>, out: RegexId)
        requires tail_represents(g, sym, child, tail), source_native_one(g, out, child, tag),
        ensures tail_represents(g, sym, out, source_one(tag, tail)),
    {
        assert forall|later: model::Symbols, bindings: Seq<Data>, theta: language::Subst, word: Seq<Data>|
            symbols_extends(sym, later) && later.variables == sym.variables && model::symbols_wf(later) && bindings_agree(later, bindings, theta)
            implies model::regex_lang(g, later, bindings, out@, word) == language::lang(source_sem(theta), source_one(tag, tail), word) by {
            assert forall|part: Seq<Data>| model::regex_lang(g, later, bindings, child@, part) == language::lang(source_sem(theta), tail, part) by {}
            if tag == "star"@ {
                let native = model::lift_regex(g, child@);
                if language::lang(model::gsem(later, bindings), language::Regex::Star(Box::new(native)), word) {
                    let parts = choose|parts: Seq<Seq<Data>>| word == parts.flatten()
                        && forall|i: int| 0 <= i < parts.len() ==> language::lang(model::gsem(later, bindings), native, parts[i]);
                    assert forall|i: int| 0 <= i < parts.len() implies language::lang(source_sem(theta), tail, parts[i]) by {}
                    assert(language::lang(source_sem(theta), language::Regex::Star(Box::new(tail)), word));
                }
                if language::lang(source_sem(theta), language::Regex::Star(Box::new(tail)), word) {
                    let parts = choose|parts: Seq<Seq<Data>>| word == parts.flatten()
                        && forall|i: int| 0 <= i < parts.len() ==> language::lang(source_sem(theta), tail, parts[i]);
                    assert forall|i: int| 0 <= i < parts.len() implies language::lang(model::gsem(later, bindings), native, parts[i]) by {}
                    assert(language::lang(model::gsem(later, bindings), language::Regex::Star(Box::new(native)), word));
                }
            }
        }
    }

    pub open spec fn source_native_test_many(g: model::Graph, out: TestId, children: Seq<TestId>, and: bool) -> bool {
        out@ < g.tests.len() && forall|sym: model::Symbols, bindings: Seq<Data>, event: Data| model::symbols_wf(sym)
            ==> model::test_holds(sym, bindings, model::lift_test(g, out@), event) == if and {
                forall|i: int| 0 <= i < children.len() ==> model::test_holds(sym, bindings, model::lift_test(g, children[i]@), event)
            } else {
                exists|i: int| 0 <= i < children.len() && model::test_holds(sym, bindings, model::lift_test(g, children[i]@), event)
            }
    }

    pub proof fn lemma_source_test_connectives(theta: language::Subst, predicates: Seq<language::SrcTest>, event: Data)
        ensures language::src_test_holds(theta, language::SrcTest::And(predicates), event)
                == (forall|i: int| 0 <= i < predicates.len() ==> language::src_test_holds(theta, predicates[i], event)),
            language::src_test_holds(theta, language::SrcTest::Or(predicates), event)
                == (exists|i: int| 0 <= i < predicates.len() && language::src_test_holds(theta, predicates[i], event)),
    {
        if language::src_test_holds(theta, language::SrcTest::And(predicates), event) {
            assert forall|i: int| 0 <= i < predicates.len() implies language::src_test_holds(theta, predicates[i], event) by {
                assert(language::src_test_holds(theta, language::SrcTest::And(predicates), event));
            }
        }
        if language::src_test_holds(theta, language::SrcTest::Or(predicates), event) {
            let i = choose|i: int| 0 <= i < predicates.len() && language::src_test_holds(theta, predicates[i], event);
            assert(exists|j: int| 0 <= j < predicates.len() && language::src_test_holds(theta, predicates[j], event));
        }
        if exists|i: int| 0 <= i < predicates.len() && language::src_test_holds(theta, predicates[i], event) {
            let i = choose|i: int| 0 <= i < predicates.len() && language::src_test_holds(theta, predicates[i], event);
            assert(language::src_test_holds(theta, language::SrcTest::Or(predicates), event));
        }
    }

    pub proof fn lemma_source_test_many_representation(g: model::Graph, sym: model::Symbols, children: Seq<TestId>, predicates: Seq<language::SrcTest>, and: bool, out: TestId)
        requires children.len() == predicates.len(), source_native_test_many(g, out, children, and),
            forall|i: int| 0 <= i < children.len() ==> source_test_represents(g, sym, children[i], predicates[i]),
        ensures source_test_represents(g, sym, out, source_test_many(and, predicates)),
    {
        assert forall|later: model::Symbols, bindings: Seq<Data>, theta: language::Subst, event: Data|
            symbols_extends(sym, later) && later.variables == sym.variables && model::symbols_wf(later) && bindings_agree(later, bindings, theta)
            implies model::test_holds(later, bindings, model::lift_test(g, out@), event) == language::src_test_holds(theta, source_test_many(and, predicates), event) by {
            reveal_with_fuel(language::src_test_holds, 2);
            lemma_source_test_connectives(theta, predicates, event);
            assert forall|i: int| 0 <= i < children.len()
                implies model::test_holds(later, bindings, model::lift_test(g, children[i]@), event) == language::src_test_holds(theta, predicates[i], event) by {}
            assert(model::test_holds(later, bindings, model::lift_test(g, out@), event) == if and {
                forall|i: int| 0 <= i < children.len() ==> model::test_holds(later, bindings, model::lift_test(g, children[i]@), event)
            } else { exists|i: int| 0 <= i < children.len() && model::test_holds(later, bindings, model::lift_test(g, children[i]@), event) });
            if and {
                if model::test_holds(later, bindings, model::lift_test(g, out@), event) {
                    assert forall|i: int| 0 <= i < predicates.len() implies language::src_test_holds(theta, predicates[i], event) by {}
                }
                if language::src_test_holds(theta, language::SrcTest::And(predicates), event) {
                    assert forall|i: int| 0 <= i < children.len() implies model::test_holds(later, bindings, model::lift_test(g, children[i]@), event) by {
                        assert(language::src_test_holds(theta, predicates[i], event));
                    }
                }
            } else {
                if model::test_holds(later, bindings, model::lift_test(g, out@), event) {
                    let i = choose|i: int| 0 <= i < children.len() && model::test_holds(later, bindings, model::lift_test(g, children[i]@), event);
                    assert(language::src_test_holds(theta, predicates[i], event));
                    assert(exists|j: int| 0 <= j < predicates.len() && language::src_test_holds(theta, predicates[j], event));
                    assert(language::src_test_holds(theta, language::SrcTest::Or(predicates), event));
                }
                if language::src_test_holds(theta, language::SrcTest::Or(predicates), event) {
                    let i = choose|i: int| 0 <= i < predicates.len() && language::src_test_holds(theta, predicates[i], event);
                    assert(model::test_holds(later, bindings, model::lift_test(g, children[i]@), event));
                    assert(model::test_holds(later, bindings, model::lift_test(g, out@), event));
                }
            }
        }
    }

    pub open spec fn source_native_lift(g: model::Graph, out: RegexId, test: TestId) -> bool {
        out@ < g.regexes.len() && forall|sym: model::Symbols, bindings: Seq<Data>, word: Seq<Data>| model::symbols_wf(sym)
            ==> model::regex_lang(g, sym, bindings, out@, word)
                == (word.len() == 1 && model::test_holds(sym, bindings, model::lift_test(g, test@), word[0]))
    }

    pub proof fn lemma_source_lift_representation(g: model::Graph, sym: model::Symbols, test: TestId, predicate: language::SrcTest, out: RegexId)
        requires source_test_represents(g, sym, test, predicate), source_native_lift(g, out, test),
        ensures tail_represents(g, sym, out, language::Regex::Test(predicate)),
    {
        assert forall|later: model::Symbols, bindings: Seq<Data>, theta: language::Subst, word: Seq<Data>|
            symbols_extends(sym, later) && later.variables == sym.variables && model::symbols_wf(later) && bindings_agree(later, bindings, theta)
            implies model::regex_lang(g, later, bindings, out@, word) == language::lang(source_sem(theta), language::Regex::Test(predicate), word) by {}
    }

    pub proof fn lemma_source_reduce_many_effect(g: model::Graph, sym: model::Symbols, pending: Seq<PendingSourceWork>, rs: Seq<RegexId>, ts: Seq<TestId>, tag: Seq<char>, start: nat, out: RegexId)
        requires start <= rs.len(), source_native_many(g, out, rs.skip(start as int), tag),
        ensures source_effect(g, sym, pending.push(PendingSourceWork::RegexMany(tag, start)), rs, ts,
            pending, rs.take(start as int).push(out), ts),
    {
        assert forall|tails: Seq<language::Regex<language::SrcTest>>, predicates: Seq<language::SrcTest>|
            source_stacks_represents(g, sym, rs, ts, tails, predicates)
            implies exists|next_tails: Seq<language::Regex<language::SrcTest>>, next_predicates: Seq<language::SrcTest>|
                source_stacks_represents(g, sym, rs.take(start as int).push(out), ts, next_tails, next_predicates)
                && source_refines(pending.push(PendingSourceWork::RegexMany(tag, start)), tails, predicates, pending, next_tails, next_predicates) by {
            assert forall|i: int| 0 <= i < rs.skip(start as int).len()
                implies tail_represents(g, sym, rs.skip(start as int)[i], tails.skip(start as int)[i]) by { assert(rs.skip(start as int)[i] == rs[start + i]); }
            lemma_source_many_representation(g, sym, rs.skip(start as int), tails.skip(start as int), tag, out);
            let next = tails.take(start as int).push(source_many(tag, tails.skip(start as int)));
            assert(source_stacks_represents(g, sym, rs.take(start as int).push(out), ts, next, predicates));
            assert(source_refines(pending.push(PendingSourceWork::RegexMany(tag, start)), tails, predicates, pending, next, predicates)) by {
                reveal_with_fuel(source_run, 2);
                assert(pending.push(PendingSourceWork::RegexMany(tag, start)).drop_last() =~= pending);
            }
        }
    }

    pub proof fn lemma_source_reduce_one_effect(g: model::Graph, sym: model::Symbols, pending: Seq<PendingSourceWork>, rs: Seq<RegexId>, ts: Seq<TestId>, tag: Seq<char>, out: RegexId)
        requires rs.len() > 0, source_native_one(g, out, rs.last(), tag),
        ensures source_effect(g, sym, pending.push(PendingSourceWork::RegexOne(tag)), rs, ts, pending, rs.drop_last().push(out), ts),
    {
        assert forall|tails: Seq<language::Regex<language::SrcTest>>, predicates: Seq<language::SrcTest>|
            source_stacks_represents(g, sym, rs, ts, tails, predicates)
            implies exists|next_tails: Seq<language::Regex<language::SrcTest>>, next_predicates: Seq<language::SrcTest>|
                source_stacks_represents(g, sym, rs.drop_last().push(out), ts, next_tails, next_predicates)
                && source_refines(pending.push(PendingSourceWork::RegexOne(tag)), tails, predicates, pending, next_tails, next_predicates) by {
            lemma_source_one_representation(g, sym, rs.last(), tails.last(), tag, out);
            let next = tails.drop_last().push(source_one(tag, tails.last()));
            assert(source_stacks_represents(g, sym, rs.drop_last().push(out), ts, next, predicates));
            assert(source_refines(pending.push(PendingSourceWork::RegexOne(tag)), tails, predicates, pending, next, predicates)) by {
                reveal_with_fuel(source_run, 2);
                assert(pending.push(PendingSourceWork::RegexOne(tag)).drop_last() =~= pending);
            }
        }
    }

    pub proof fn lemma_source_reduce_test_effect(g: model::Graph, sym: model::Symbols, pending: Seq<PendingSourceWork>, rs: Seq<RegexId>, ts: Seq<TestId>, and: bool, start: nat, out: TestId)
        requires start <= ts.len(), source_native_test_many(g, out, ts.skip(start as int), and),
        ensures source_effect(g, sym, pending.push(PendingSourceWork::TestMany(and, start)), rs, ts,
            pending, rs, ts.take(start as int).push(out)),
    {
        assert forall|tails: Seq<language::Regex<language::SrcTest>>, predicates: Seq<language::SrcTest>|
            source_stacks_represents(g, sym, rs, ts, tails, predicates)
            implies exists|next_tails: Seq<language::Regex<language::SrcTest>>, next_predicates: Seq<language::SrcTest>|
                source_stacks_represents(g, sym, rs, ts.take(start as int).push(out), next_tails, next_predicates)
                && source_refines(pending.push(PendingSourceWork::TestMany(and, start)), tails, predicates, pending, next_tails, next_predicates) by {
            assert forall|i: int| 0 <= i < ts.skip(start as int).len()
                implies source_test_represents(g, sym, ts.skip(start as int)[i], predicates.skip(start as int)[i]) by { assert(ts.skip(start as int)[i] == ts[start + i]); }
            lemma_source_test_many_representation(g, sym, ts.skip(start as int), predicates.skip(start as int), and, out);
            let next = predicates.take(start as int).push(source_test_many(and, predicates.skip(start as int)));
            assert(source_stacks_represents(g, sym, rs, ts.take(start as int).push(out), tails, next));
            assert(source_refines(pending.push(PendingSourceWork::TestMany(and, start)), tails, predicates, pending, tails, next)) by {
                reveal_with_fuel(source_run, 2);
                assert(pending.push(PendingSourceWork::TestMany(and, start)).drop_last() =~= pending);
            }
        }
    }

    pub proof fn lemma_source_reduce_lift_effect(g: model::Graph, sym: model::Symbols, pending: Seq<PendingSourceWork>, rs: Seq<RegexId>, ts: Seq<TestId>, out: RegexId)
        requires ts.len() > 0, source_native_lift(g, out, ts.last()),
        ensures source_effect(g, sym, pending.push(PendingSourceWork::LiftTest), rs, ts, pending, rs.push(out), ts.drop_last()),
    {
        assert forall|tails: Seq<language::Regex<language::SrcTest>>, predicates: Seq<language::SrcTest>|
            source_stacks_represents(g, sym, rs, ts, tails, predicates)
            implies exists|next_tails: Seq<language::Regex<language::SrcTest>>, next_predicates: Seq<language::SrcTest>|
                source_stacks_represents(g, sym, rs.push(out), ts.drop_last(), next_tails, next_predicates)
                && source_refines(pending.push(PendingSourceWork::LiftTest), tails, predicates, pending, next_tails, next_predicates) by {
            lemma_source_lift_representation(g, sym, ts.last(), predicates.last(), out);
            let next = tails.push(language::Regex::Test(predicates.last()));
            assert(source_stacks_represents(g, sym, rs.push(out), ts.drop_last(), next, predicates.drop_last()));
            assert(source_refines(pending.push(PendingSourceWork::LiftTest), tails, predicates, pending, next, predicates.drop_last())) by {
                reveal_with_fuel(source_run, 2);
                assert(pending.push(PendingSourceWork::LiftTest).drop_last() =~= pending);
            }
        }
    }

    pub proof fn lemma_source_constant_tail(g: model::Graph, sym: model::Symbols, out: RegexId, tag: Seq<char>)
        requires model::graph_wf(g), tag == "empty"@ || tag == "all"@ || tag == "epsilon"@,
            out@ == if tag == "empty"@ { g.constants.empty } else if tag == "all"@ { g.constants.all } else { g.constants.epsilon },
        ensures tail_represents(g, sym, out, if tag == "empty"@ { language::Regex::Empty } else if tag == "all"@ { language::Regex::All } else { language::Regex::Epsilon }),
    {
        model::lemma_graph_wf_elim(g);
        reveal_with_fuel(model::lift_regex, 2);
        assert forall|later: model::Symbols, bindings: Seq<Data>, theta: language::Subst, word: Seq<Data>|
            symbols_extends(sym, later) && later.variables == sym.variables && model::symbols_wf(later) && bindings_agree(later, bindings, theta)
            implies model::regex_lang(g, later, bindings, out@, word) == language::lang(source_sem(theta),
                if tag == "empty"@ { language::Regex::Empty } else if tag == "all"@ { language::Regex::All } else { language::Regex::Epsilon }, word) by {}
    }

    pub proof fn lemma_source_constant_test(g: model::Graph, sym: model::Symbols, out: TestId, value: bool)
        requires model::graph_wf(g), out@ == if value { g.constants.test_true } else { g.constants.test_false },
        ensures source_test_represents(g, sym, out, language::SrcTest::Bool(value)),
    {
        model::lemma_graph_wf_elim(g);
        reveal_with_fuel(model::lift_test, 2);
        assert forall|later: model::Symbols, bindings: Seq<Data>, theta: language::Subst, event: Data|
            symbols_extends(sym, later) && later.variables == sym.variables && model::symbols_wf(later) && bindings_agree(later, bindings, theta)
            implies model::test_holds(later, bindings, model::lift_test(g, out@), event) == language::src_test_holds(theta, language::SrcTest::Bool(value), event) by {}
    }

    pub proof fn lemma_source_comparison_representation(g: model::Graph, sym: model::Symbols, path: nat, term: model::GTerm, decoded: language::Term, positive: bool, presence: TestId, equality: TestId, out: TestId)
        requires path < sym.paths.len(), term_represents(sym, term, decoded),
            presence@ < g.tests.len(), g.tests[presence@ as int] == model::TestNode::Atom(model::Primitive::HasValue(path), true),
            equality@ < g.tests.len(), g.tests[equality@ as int] == model::TestNode::Atom(model::Primitive::EqCore(path, term), positive),
            source_native_test_many(g, out, seq![presence, equality], true),
        ensures source_test_represents(g, sym, out, if positive { language::SrcTest::Eq(sym.paths[path as int], decoded) } else { language::SrcTest::Neq(sym.paths[path as int], decoded) }),
    {
        assert forall|later: model::Symbols, bindings: Seq<Data>, theta: language::Subst, event: Data|
            symbols_extends(sym, later) && later.variables == sym.variables && model::symbols_wf(later) && bindings_agree(later, bindings, theta)
            implies model::test_holds(later, bindings, model::lift_test(g, out@), event) == language::src_test_holds(theta,
                if positive { language::SrcTest::Eq(sym.paths[path as int], decoded) } else { language::SrcTest::Neq(sym.paths[path as int], decoded) }, event) by {
            assert(later.paths[path as int] == sym.paths[path as int]);
            assert(term_represents(later, term, decoded));
            match (term, decoded) {
                (model::GTerm::Constant(c), language::Term::Constant(value)) => { assert(later.constants[c as int] == value); },
                (model::GTerm::Variable(v), language::Term::Variable(name)) => { assert(theta[name] == bindings[v as int]); },
                _ => {},
            }
            assert(model::primitive_holds(later, bindings, model::Primitive::EqCore(path, term), event)
                == (language::select(event, sym.paths[path as int]) == Some(language::term_value(theta, decoded))));
            reveal_with_fuel(model::lift_test, 2);
            assert(model::test_holds(later, bindings, model::lift_test(g, presence@), event)
                == (language::select(event, sym.paths[path as int]) is Some));
            assert(model::test_holds(later, bindings, model::lift_test(g, equality@), event)
                == ((language::select(event, sym.paths[path as int]) == Some(language::term_value(theta, decoded))) == positive));
            assert((forall|i: int| 0 <= i < 2 ==> model::test_holds(later, bindings, model::lift_test(g, seq![presence, equality][i]@), event))
                == (model::test_holds(later, bindings, model::lift_test(g, presence@), event)
                    && model::test_holds(later, bindings, model::lift_test(g, equality@), event))) by {}
            match language::select(event, sym.paths[path as int]) { Some(_) => {}, None => {} }
        }
    }

    pub proof fn lemma_source_step_frame(g0: model::Graph, g1: model::Graph, s0: model::Symbols, s1: model::Symbols, before: Seq<PendingSourceWork>, rs: Seq<RegexId>, ts: Seq<TestId>, after: Seq<PendingSourceWork>, next_rs: Seq<RegexId>, next_ts: Seq<TestId>)
        requires model::graph_wf(g0), model::graph_extends(g0, g1), symbols_extends(s0, s1), s1.variables == s0.variables,
            model::symbols_wf(s1), source_effect(g1, s1, before, rs, ts, after, next_rs, next_ts),
        ensures forall|source: Data| source_state(g0, s0, before, rs, ts, source) ==> source_state(g1, s1, after, next_rs, next_ts, source),
    {
        assert forall|source: Data| source_state(g0, s0, before, rs, ts, source)
            implies source_state(g1, s1, after, next_rs, next_ts, source) by {
            lemma_source_state_frame(g0, g1, s0, s1, before, rs, ts, source);
            lemma_source_effect_state(g1, s1, before, rs, ts, after, next_rs, next_ts, source);
        }
    }

    pub proof fn lemma_source_comparison_fields<A>(raw: Set<A>, deep: Map<Data, Data>, first: A, second: A, first_name: Seq<char>, second_name: Seq<char>, project: spec_fn(A) -> Data)
        requires raw.len() == 2, raw.contains(first), raw.contains(second), first_name != second_name,
            project(first) == Data::String(first_name), project(second) == Data::String(second_name),
            forall|key: Data| deep.contains_key(key) <==> exists|entry: A| raw.contains(entry) && project(entry) == key,
        ensures deep.dom() == Set::empty().insert(Data::String(first_name)).insert(Data::String(second_name)),
    {
        broadcast use vstd::set::group_set_lemmas;
        let pair = Set::empty().insert(first).insert(second);
        assert(first != second);
        assert(pair.subset_of(raw));
        assert(pair.len() == 2);
        vstd::set_lib::lemma_subset_equality(pair, raw);
        assert forall|key: Data| deep.dom().contains(key)
            implies key == Data::String(first_name) || key == Data::String(second_name) by {
            let entry = choose|entry: A| raw.contains(entry) && project(entry) == key;
            assert(entry == first || entry == second);
        }
        assert(deep.dom() =~= Set::empty().insert(Data::String(first_name)).insert(Data::String(second_name)));
    }

    pub open spec fn source_ids_valid(g: model::Graph, rs: Seq<RegexId>, ts: Seq<TestId>) -> bool {
        (forall|i: int| 0 <= i < rs.len() ==> rs[i]@ < g.regexes.len())
        && (forall|i: int| 0 <= i < ts.len() ==> ts[i]@ < g.tests.len())
    }

    pub proof fn lemma_source_initial(g: model::Graph, sym: model::Symbols, source: Data)
        ensures source_state(g, sym, seq![PendingSourceWork::Regex(source)], Seq::empty(), Seq::empty(), source),
    {
        let rs = Seq::<language::Regex<language::SrcTest>>::empty();
        let ts = Seq::<language::SrcTest>::empty();
        assert(source_stacks_represents(g, sym, Seq::empty(), Seq::empty(), rs, ts));
        assert(source_safe(seq![PendingSourceWork::Regex(source)], rs, ts, source)) by {
            reveal_with_fuel(source_run, 3);
            assert(seq![PendingSourceWork::Regex(source)].drop_last() =~= Seq::empty());
        }
        assert(source_state(g, sym, seq![PendingSourceWork::Regex(source)], Seq::empty(), Seq::empty(), source));
    }

    pub proof fn lemma_source_final(g: model::Graph, sym: model::Symbols, rs: Seq<RegexId>, ts: Seq<TestId>, source: Data)
        requires rs.len() == 1, ts.len() == 0, source_state(g, sym, Seq::empty(), rs, ts, source),
        ensures exists|tail: language::Regex<language::SrcTest>| language::decodes_tail(source, tail) && tail_represents(g, sym, rs[0], tail),
    {
        let (tails, predicates) = choose|tails: Seq<language::Regex<language::SrcTest>>, predicates: Seq<language::SrcTest>|
            source_stacks_represents(g, sym, rs, ts, tails, predicates) && source_safe(Seq::empty(), tails, predicates, source);
        assert(source_run(Seq::empty(), tails, predicates, tails, predicates));
        assert(language::decodes_tail(source, tails[0]));
        assert(exists|tail: language::Regex<language::SrcTest>| language::decodes_tail(source, tail) && tail_represents(g, sym, rs[0], tail));
    }


    pub open spec fn values_data(values: Seq<Value>) -> Seq<Data> {
        values.map(|i: int, value: Value| value_view(value))
    }

    impl View for Symbols {
        type V = model::Symbols;
        open(crate) spec fn view(&self) -> model::Symbols {
            model::Symbols {
                constants: values_data(self.constants@),
                paths: self.paths@.map(|i: int, path: Box<[Value]>| values_data(path@)),
                variables: self.variables@.map(|i: int, name: String| name@),
            }
        }
    }

    // Defined key projections give empty maps without an initialization assumption.
    impl SymbolBuilder {
        pub(super) open spec fn constant_index(&self) -> Map<Data, ConstId> {
            let raw = self.constants@;
            Map::new(raw.dom().map(|key: Value| value_view(key)), |data: Data| {
                let key = choose|key: Value| raw.contains_key(key) && value_view(key) == data;
                if raw.contains_key(key) { raw[key] } else { arbitrary() }
            })
        }
        pub(super) open spec fn path_index(&self) -> Map<Seq<Data>, PathId> {
            let raw = self.paths@;
            Map::new(raw.dom().map(|key: Vec<Value>| values_data(key@)), |data: Seq<Data>| {
                let key = choose|key: Vec<Value>| raw.contains_key(key) && values_data(key@) == data;
                if raw.contains_key(key) { raw[key] } else { arbitrary() }
            })
        }
        pub(super) open spec fn variable_index(&self) -> Map<Seq<char>, VariableId> {
            let raw = self.variables@;
            Map::new(raw.dom().map(|key: String| key@), |name: Seq<char>| {
                let key = choose|key: String| raw.contains_key(key) && key@ == name;
                if raw.contains_key(key) { raw[key] } else { arbitrary() }
            })
        }
    }

    pub open spec fn symbols_extends(before: model::Symbols, after: model::Symbols) -> bool {
        before.constants.is_prefix_of(after.constants) && before.paths.is_prefix_of(after.paths)
            && before.variables.is_prefix_of(after.variables)
    }


    pub(super) open spec fn builder_tables_wf(
        sym: model::Symbols, constants: Map<Data, ConstId>, paths: Map<Seq<Data>, PathId>, variables: Map<Seq<char>, VariableId>,
    ) -> bool {
        model::symbols_wf(sym)
        && (forall|data: Data| constants.contains_key(data)
            <==> exists|i: int| 0 <= i < sym.constants.len() && sym.constants[i] == data)
        && (forall|i: int| 0 <= i < sym.constants.len() ==> constants.contains_key(sym.constants[i])
            && constants[sym.constants[i]]@ == i)
        && (forall|data: Seq<Data>| paths.contains_key(data)
            <==> exists|i: int| 0 <= i < sym.paths.len() && sym.paths[i] == data)
        && (forall|i: int| 0 <= i < sym.paths.len() ==> paths.contains_key(sym.paths[i])
            && paths[sym.paths[i]]@ == i)
        && (forall|name: Seq<char>| variables.contains_key(name)
            <==> exists|i: int| 0 <= i < sym.variables.len() && sym.variables[i] == name)
        && (forall|i: int| 0 <= i < sym.variables.len() ==> variables.contains_key(sym.variables[i])
            && variables[sym.variables[i]]@ == i)
    }

    pub(super) open spec fn builder_wf(builder: SymbolBuilder) -> bool {
        builder_tables_wf(builder.symbols@, builder.constant_index(), builder.path_index(), builder.variable_index())
    }

    pub open spec fn term_represents(sym: model::Symbols, term: model::GTerm, source: language::Term) -> bool {
        match (term, source) {
            (model::GTerm::Constant(index), language::Term::Constant(value)) => index < sym.constants.len() && sym.constants[index as int] == value,
            (model::GTerm::Variable(index), language::Term::Variable(name)) => index < sym.variables.len() && sym.variables[index as int] == name,
            _ => false,
        }
    }

    pub open spec fn bindings_agree(sym: model::Symbols, bindings: Seq<Data>, theta: language::Subst) -> bool {
        bindings.len() == sym.variables.len()
            && forall|i: int| 0 <= i < sym.variables.len() ==> theta.contains_key(sym.variables[i]) && theta[sym.variables[i]] == bindings[i]
    }

    pub open spec fn theta_of(bindings: Seq<Value>, sym: model::Symbols) -> language::Subst {
        let count = if bindings.len() < sym.variables.len() { bindings.len() } else { sym.variables.len() };
        Map::new(sym.variables.take(count as int).to_set(), |name: Seq<char>| {
            let i = choose|i: int| 0 <= i < sym.variables.len() && i < bindings.len() && sym.variables[i] == name;
            if 0 <= i < bindings.len() { value_view(bindings[i]) } else { arbitrary() }
        })
    }

    pub enum PendingPatternWork {
        Enter(Data), Array(nat, nat), Object(Seq<Data>, nat),
    }

    impl View for PatternWork<'_> {
        type V = PendingPatternWork;
        open(super) spec fn view(&self) -> PendingPatternWork {
            match self {
                PatternWork::Enter(value, _) => PendingPatternWork::Enter(value_view(**value)),
                PatternWork::Array { len, start } => PendingPatternWork::Array(*len as nat, *start as nat),
                PatternWork::Object { keys, start } => PendingPatternWork::Object(values_data(keys@), *start as nat),
            }
        }
    }

    pub(super) open spec fn pattern_compile_work(work: Seq<PatternWork<'_>>) -> Seq<PendingPatternWork> {
        work.map(|i: int, task: PatternWork<'_>| task@)
    }

    pub open(super) spec fn pattern_task_valid(task: PendingPatternWork) -> bool {
        match task { PendingPatternWork::Object(keys, _) => keys.no_duplicates(), _ => true }
    }

    pub open(super) spec fn pattern_compile_work_valid(work: Seq<PendingPatternWork>) -> bool {
        forall|i: int| 0 <= i < work.len() ==> pattern_task_valid(work[i])
    }

    pub open(super) spec fn pattern_jobs(children: Seq<Data>) -> Seq<PendingPatternWork> {
        Seq::new(children.len(), |i: int| PendingPatternWork::Enter(children[children.len() - 1 - i]))
    }

    pub open(super) spec fn pattern_object_fields(fields: Seq<(Value, usize)>) -> Seq<(Data, usize)> {
        fields.map(|i: int, field: (Value, usize)| (value_view(field.0), field.1))
    }

    pub(super) open spec fn pattern_compile_step_effect(task: PendingPatternWork, before: model::Symbols, after: model::Symbols,
        inputs: Seq<usize>, results: Seq<usize>, pending: Seq<PendingPatternWork>, work: Seq<PendingPatternWork>, output: Option<PatternNode>) -> bool {
        match task {
            PendingPatternWork::Enter(data) => match output {
                Some(PatternNode::Literal(index)) => index@ < after.constants.len()
                    && language::tagged_payload(data, "value"@) == Some(after.constants[index@ as int])
                    && after.variables == before.variables && results == inputs && work == pending,
                Some(PatternNode::Variable(index)) => index@ < after.variables.len()
                    && language::tagged_payload(data, "var"@) == Some(Data::String(after.variables[index@ as int]))
                    && after.variables[index@ as int].len() > 0
                    && after.variables.to_set() == before.variables.to_set().insert(after.variables[index@ as int])
                    && results == inputs && work == pending,
                Some(PatternNode::Any) => language::tagged_payload(data, "any"@) == Some(Data::Bool(true))
                    && after == before && results == inputs && work == pending,
                None => after == before && results == inputs && (
                    (exists|children: Seq<Data>| language::tagged_payload(data, "array"@) == Some(Data::Array(children))
                        && work == pending.push(PendingPatternWork::Array(children.len(), inputs.len())) + pattern_jobs(children))
                    || (exists|fields: Map<Data, Data>, keys: Seq<Data>, children: Seq<Data>|
                        language::tagged_payload(data, "object"@) == Some(Data::Object(fields))
                        && keys.no_duplicates() && keys.to_set() == fields.dom() && children.len() == keys.len()
                        && (forall|i: int| 0 <= i < keys.len() ==> children[i] == fields[keys[i]])
                        && work == pending.push(PendingPatternWork::Object(keys, inputs.len())) + pattern_jobs(children))),
                _ => false,
            },
            PendingPatternWork::Array(len, start) => after == before && work == pending && start <= inputs.len()
                && inputs.len() == start + len && results == inputs.take(start as int)
                && match output { Some(PatternNode::Array(children)) => children@ == inputs.skip(start as int), _ => false },
            PendingPatternWork::Object(keys, start) => after == before && work == pending && start <= inputs.len()
                && inputs.len() == start + keys.len() && results == inputs.take(start as int)
                && match output {
                    Some(PatternNode::Object(fields)) => fields@.len() == keys.len()
                        && forall|i: int| 0 <= i < keys.len() ==> value_view(fields@[i].0) == keys[i] && fields@[i].1 == inputs[start + i],
                    _ => false,
                },
        }
    }

    pub(super) open spec fn pattern_heads(nodes: Seq<PatternNode>, sym: model::Symbols, ids: Seq<usize>) -> Seq<language::Head> {
        ids.map(|i: int, id: usize| pattern_head(nodes, sym, id as int))
    }

    pub(super) open spec fn pattern_ids_valid(nodes: Seq<PatternNode>, ids: Seq<usize>) -> bool {
        forall|i: int| 0 <= i < ids.len() ==> ids[i] < nodes.len()
    }

    pub open(super) spec fn pattern_heads_vars(heads: Seq<language::Head>) -> Set<Seq<char>> {
        language::head_vars(language::Head::Array(heads))
    }

    pub open(super) spec fn pattern_fields_head(keys: Seq<Data>, heads: Seq<language::Head>) -> Map<Data, language::Head> {
        Map::new(keys.to_set(), |key: Data| {
            let i = choose|i: int| 0 <= i < keys.len() && keys[i] == key;
            heads[i]
        })
    }

    pub open(super) spec fn pattern_compile_run(work: Seq<PendingPatternWork>, heads: Seq<language::Head>, output: Seq<language::Head>) -> bool
        decreases work.len(),
    {
        if work.len() == 0 { heads == output }
        else {
            let rest = work.drop_last();
            match work.last() {
                PendingPatternWork::Enter(data) => exists|head: language::Head| language::decodes_head(data, head)
                    && pattern_compile_run(rest, heads.push(head), output),
                PendingPatternWork::Array(len, start) => start <= heads.len() && heads.len() == start + len
                    && pattern_compile_run(rest, heads.take(start as int).push(language::Head::Array(heads.skip(start as int))), output),
                PendingPatternWork::Object(keys, start) => start <= heads.len() && heads.len() == start + keys.len()
                    && keys.no_duplicates()
                    && pattern_compile_run(rest, heads.take(start as int).push(language::Head::Object(pattern_fields_head(keys, heads.skip(start as int)))), output),
            }
        }
    }

    pub(super) proof fn lemma_pattern_jobs_prepend(children: Seq<Data>)
        requires children.len() > 0,
        ensures pattern_jobs(children) == pattern_jobs(children.drop_first()).push(PendingPatternWork::Enter(children[0])),
    {
        assert(pattern_jobs(children) =~= pattern_jobs(children.drop_first()).push(PendingPatternWork::Enter(children[0])));
    }

    pub(super) proof fn lemma_pattern_compile_work_push(work: Seq<PatternWork<'_>>, task: PatternWork<'_>)
        ensures pattern_compile_work(work.push(task)) == pattern_compile_work(work).push(task@),
    {
        assert(pattern_compile_work(work.push(task)) =~= pattern_compile_work(work).push(task@));
    }

    pub(super) proof fn lemma_pattern_pending_valid_push(work: Seq<PendingPatternWork>, task: PendingPatternWork)
        requires pattern_compile_work_valid(work), pattern_task_valid(task),
        ensures pattern_compile_work_valid(work.push(task)),
    {
        assert forall|i: int| 0 <= i < work.push(task).len() implies pattern_task_valid(work.push(task)[i]) by {
            if i < work.len() { assert(work.push(task)[i] == work[i]); }
            else { assert(work.push(task)[i] == task); }
        }
    }

    pub(super) proof fn lemma_pattern_object_enumeration(object: crate::Rc<Object>, entries: Seq<(Value, Value)>, keys: Seq<Data>, children: Seq<Data>)
        requires keys.len() == entries.len(), children.len() == entries.len(),
            forall|i: int| 0 <= i < entries.len() ==> object@.contains_key(entries[i].0)
                && object@[entries[i].0] == entries[i].1 && keys[i] == value_view(entries[i].0) && children[i] == value_view(entries[i].1),
            forall|i: int, j: int| 0 <= i < j < entries.len() ==> entries[i].0 != entries[j].0,
            forall|key: Value| object@.contains_key(key) ==> exists|i: int| 0 <= i < entries.len() && entries[i].0 == key,
            forall|k1: Value, k2: Value| object@.contains_key(k1) && object@.contains_key(k2) && value_view(k1) == value_view(k2) ==> k1 == k2,
        ensures keys.no_duplicates(), keys.to_set() == (value_view(Value::Object(object))->Object_0).dom(),
            forall|i: int| 0 <= i < keys.len() ==> children[i] == (value_view(Value::Object(object))->Object_0)[keys[i]],
    {
        lemma_value_view_object(object);
        keys.to_set_ensures();
        let fields = value_view(Value::Object(object))->Object_0;
        assert forall|i: int, j: int| 0 <= i < j < keys.len() implies keys[i] != keys[j] by {
            assert(entries[i].0 != entries[j].0);
        }
        assert forall|key: Data| keys.to_set().contains(key) == fields.contains_key(key) by {
            if keys.to_set().contains(key) {
                let i = choose|i: int| 0 <= i < keys.len() && keys[i] == key;
                assert(object@.contains_key(entries[i].0));
            }
            if fields.contains_key(key) {
                let raw = choose|raw: Value| object@.contains_key(raw) && value_view(raw) == key;
                let i = choose|i: int| 0 <= i < entries.len() && entries[i].0 == raw;
                assert(keys[i] == key);
            }
        }
        assert(keys.to_set() =~= fields.dom());
    }
    pub open(super) spec fn pattern_object_entries(object: crate::Rc<Object>, entries: Seq<(Value, Value)>) -> bool {
        entries.len() == object@.dom().len()
        && (forall|i: int| 0 <= i < entries.len() ==> object@.contains_key(entries[i].0) && object@[entries[i].0] == entries[i].1)
        && (forall|i: int, j: int| 0 <= i < j < entries.len() ==> entries[i].0 != entries[j].0)
        && (forall|key: Value| object@.contains_key(key) ==> exists|i: int| 0 <= i < entries.len() && entries[i].0 == key)
        && (forall|k1: Value, k2: Value| object@.contains_key(k1) && object@.contains_key(k2) && value_view(k1) == value_view(k2) ==> k1 == k2)
    }

    pub open(super) spec fn pattern_pending_children(pending: Seq<(&Value, String)>) -> Seq<Data> {
        pending.map(|i: int, item: (&Value, String)| value_view(*item.0))
    }

    pub(super) proof fn lemma_pattern_work_jobs_valid(work: Seq<PendingPatternWork>, children: Seq<Data>)
        requires pattern_compile_work_valid(work),
        ensures pattern_compile_work_valid(work + pattern_jobs(children)),
    {
        assert forall|i: int| 0 <= i < (work + pattern_jobs(children)).len() implies pattern_task_valid((work + pattern_jobs(children))[i]) by {
            if i < work.len() { assert((work + pattern_jobs(children))[i] == work[i]); }
            else { assert((work + pattern_jobs(children))[i] == pattern_jobs(children)[i - work.len()]); }
        }
    }

    pub(super) open spec fn pattern_output_nodes(nodes: Seq<PatternNode>, node: Option<PatternNode>) -> Seq<PatternNode> {
        match node { Some(node) => nodes.push(node), None => nodes }
    }
    pub(super) open spec fn pattern_output_ids(nodes: Seq<PatternNode>, ids: Seq<usize>, node: Option<PatternNode>) -> Seq<usize> {
        match node { Some(_) => ids.push(nodes.len() as usize), None => ids }
    }

    pub(super) proof fn lemma_pattern_vars(heads: Seq<language::Head>)
        ensures forall|name: Seq<char>| pattern_heads_vars(heads).contains(name)
            <==> exists|i: int| 0 <= i < heads.len() && language::head_vars(heads[i]).contains(name),
    {
        language::lemma_head_vars_array(heads);
    }

    pub(super) proof fn lemma_pattern_vars_push(heads: Seq<language::Head>, head: language::Head)
        ensures pattern_heads_vars(heads.push(head)) == pattern_heads_vars(heads).union(language::head_vars(head)),
    {
        lemma_pattern_vars_concat(heads, seq![head]);
        lemma_pattern_vars(seq![head]);
        assert(pattern_heads_vars(seq![head]) =~= language::head_vars(head)) by {
            assert forall|name: Seq<char>| pattern_heads_vars(seq![head]).contains(name) == language::head_vars(head).contains(name) by {
                if pattern_heads_vars(seq![head]).contains(name) {
                    let i = choose|i: int| 0 <= i < 1 && language::head_vars(seq![head][i]).contains(name);
                    assert(i == 0);
                }
            }
        }
        assert(heads + seq![head] =~= heads.push(head));
    }

    pub(super) proof fn lemma_pattern_vars_concat(left: Seq<language::Head>, right: Seq<language::Head>)
        ensures pattern_heads_vars(left + right) == pattern_heads_vars(left).union(pattern_heads_vars(right)),
    {
        lemma_pattern_vars(left); lemma_pattern_vars(right); lemma_pattern_vars(left + right);
        assert forall|name: Seq<char>| pattern_heads_vars(left + right).contains(name)
            == pattern_heads_vars(left).union(pattern_heads_vars(right)).contains(name) by {
            if pattern_heads_vars(left + right).contains(name) {
                let i = choose|i: int| 0 <= i < (left + right).len() && language::head_vars((left + right)[i]).contains(name);
                if i < left.len() { assert((left + right)[i] == left[i]); }
                else { assert((left + right)[i] == right[i - left.len()]); }
            }
            if pattern_heads_vars(left).contains(name) {
                let i = choose|i: int| 0 <= i < left.len() && language::head_vars(left[i]).contains(name);
                assert((left + right)[i] == left[i]);
            }
            if pattern_heads_vars(right).contains(name) {
                let i = choose|i: int| 0 <= i < right.len() && language::head_vars(right[i]).contains(name);
                assert((left + right)[left.len() + i] == right[i]);
            }
        }
        assert(pattern_heads_vars(left + right) =~= pattern_heads_vars(left).union(pattern_heads_vars(right)));
    }

    pub(super) proof fn lemma_pattern_fields(keys: Seq<Data>, heads: Seq<language::Head>)
        requires keys.no_duplicates(), keys.len() == heads.len(),
        ensures pattern_fields_head(keys, heads).dom() == keys.to_set(),
            forall|i: int| 0 <= i < keys.len() ==> pattern_fields_head(keys, heads)[keys[i]] == heads[i],
            language::head_vars(language::Head::Object(pattern_fields_head(keys, heads))) == pattern_heads_vars(heads),
    {
        keys.to_set_ensures();
        assert forall|i: int| 0 <= i < keys.len() implies pattern_fields_head(keys, heads)[keys[i]] == heads[i] by {
            let j = choose|j: int| 0 <= j < keys.len() && keys[j] == keys[i];
            assert(i == j);
        }
        let fields = pattern_fields_head(keys, heads);
        language::lemma_head_vars_object(fields); lemma_pattern_vars(heads);
        assert forall|name: Seq<char>| language::head_vars(language::Head::Object(fields)).contains(name)
            == pattern_heads_vars(heads).contains(name) by {
            if language::head_vars(language::Head::Object(fields)).contains(name) {
                let key = choose|key: Data| fields.contains_key(key) && language::head_vars(fields[key]).contains(name);
                let i = choose|i: int| 0 <= i < keys.len() && keys[i] == key;
                assert(fields[key] == heads[i]);
            }
            if pattern_heads_vars(heads).contains(name) {
                let i = choose|i: int| 0 <= i < heads.len() && language::head_vars(heads[i]).contains(name);
                assert(fields.contains_key(keys[i]) && fields[keys[i]] == heads[i]);
            }
        }
        assert(language::head_vars(language::Head::Object(fields)) =~= pattern_heads_vars(heads));
    }

    pub(super) proof fn lemma_pattern_node_frame(before: Seq<PatternNode>, after: Seq<PatternNode>, sym: model::Symbols, id: int)
        requires pattern_nodes_wf(before, sym), before.is_prefix_of(after), 0 <= id < before.len(),
        ensures pattern_node_wf(after, sym, id), pattern_head(before, sym, id) == pattern_head(after, sym, id),
        decreases id,
    {
        assert(pattern_node_wf(before, sym, id)); assert(before[id] == after[id]);
        match before[id] {
            PatternNode::Array(children) => {
                assert forall|i: int| 0 <= i < children@.len() implies pattern_head(before, sym, children@[i] as int) == pattern_head(after, sym, children@[i] as int) by {
                    lemma_pattern_node_frame(before, after, sym, children@[i] as int);
                }
                let left = pattern_head(before, sym, id)->Array_0;
                let right = pattern_head(after, sym, id)->Array_0;
                assert(left =~= right) by {
                    assert forall|i: int| 0 <= i < left.len() implies left[i] == right[i] by {
                        assert(left[i] == pattern_head(before, sym, children@[i] as int));
                        assert(right[i] == pattern_head(after, sym, children@[i] as int));
                    }
                }
            },
            PatternNode::Object(fields) => {
                assert forall|i: int| 0 <= i < fields@.len() implies pattern_head(before, sym, fields@[i].1 as int) == pattern_head(after, sym, fields@[i].1 as int) by {
                    lemma_pattern_node_frame(before, after, sym, fields@[i].1 as int);
                }
                let left = pattern_head(before, sym, id)->Object_0;
                let right = pattern_head(after, sym, id)->Object_0;
                assert(left.dom() == right.dom());
                assert forall|key: Data| left.contains_key(key) implies left[key] == right[key] by {
                    let i = choose|i: int| 0 <= i < fields@.len() && value_view(fields@[i].0) == key;
                    assert(left[key] == pattern_head(before, sym, fields@[i].1 as int));
                    assert(right[key] == pattern_head(after, sym, fields@[i].1 as int));
                }
                assert(left =~= right);
            }, _ => {},
        }
    }

    pub(super) proof fn lemma_pattern_run_jobs(work: Seq<PendingPatternWork>, children: Seq<Data>, heads: Seq<language::Head>, output: Seq<language::Head>)
        requires pattern_compile_run(work + pattern_jobs(children), heads, output),
        ensures exists|decoded: Seq<language::Head>| decoded.len() == children.len()
            && (forall|i: int| 0 <= i < children.len() ==> language::decodes_head(children[i], decoded[i]))
            && pattern_compile_run(work, heads + decoded, output),
        decreases children.len(),
    {
        if children.len() == 0 {
            assert(pattern_jobs(children) =~= Seq::empty()); assert(heads + Seq::empty() =~= heads);
        } else {
            lemma_pattern_jobs_prepend(children);
            assert((work + pattern_jobs(children)).drop_last() =~= work + pattern_jobs(children.drop_first()));
            let head = choose|head: language::Head| language::decodes_head(children[0], head)
                && pattern_compile_run(work + pattern_jobs(children.drop_first()), heads.push(head), output);
            lemma_pattern_run_jobs(work, children.drop_first(), heads.push(head), output);
            let rest = choose|rest: Seq<language::Head>| rest.len() == children.drop_first().len()
                && (forall|i: int| 0 <= i < children.drop_first().len() ==> language::decodes_head(children.drop_first()[i], rest[i]))
                && pattern_compile_run(work, heads.push(head) + rest, output);
            let all = seq![head] + rest;
            assert(heads.push(head) + rest =~= heads + all);
            assert forall|i: int| 0 <= i < children.len() implies language::decodes_head(children[i], all[i]) by {
                if i > 0 { assert(children.drop_first()[i - 1] == children[i]); }
            }
            assert(exists|all: Seq<language::Head>| all.len() == children.len()
                && (forall|i: int| 0 <= i < children.len() ==> language::decodes_head(children[i], all[i]))
                && pattern_compile_run(work, heads + all, output));
        }
    }
    pub(super) proof fn lemma_pattern_run_unfold(work: Seq<PendingPatternWork>, task: PendingPatternWork, heads: Seq<language::Head>, output: Seq<language::Head>)
        ensures pattern_compile_run(work.push(task), heads, output) == match task {
            PendingPatternWork::Enter(data) => exists|head: language::Head| language::decodes_head(data, head) && pattern_compile_run(work, heads.push(head), output),
            PendingPatternWork::Array(len, start) => start <= heads.len() && heads.len() == start + len
                && pattern_compile_run(work, heads.take(start as int).push(language::Head::Array(heads.skip(start as int))), output),
            PendingPatternWork::Object(keys, start) => start <= heads.len() && heads.len() == start + keys.len() && keys.no_duplicates()
                && pattern_compile_run(work, heads.take(start as int).push(language::Head::Object(pattern_fields_head(keys, heads.skip(start as int)))), output),
        },
    {
        reveal_with_fuel(pattern_compile_run, 2);
        assert(work.push(task).drop_last() =~= work);
        assert(work.push(task).last() == task);
    }

    #[verifier::rlimit(60)]
    pub(super) proof fn lemma_pattern_compile_transfer(nodes: Seq<PatternNode>, before: model::Symbols, after: model::Symbols,
        task: PendingPatternWork, inputs: Seq<usize>, results: Seq<usize>, pending: Seq<PendingPatternWork>, work: Seq<PendingPatternWork>, output: Option<PatternNode>)
        requires pattern_nodes_wf(nodes, before), nodes.len() <= usize::MAX, symbols_extends(before, after), model::symbols_wf(after),
            pattern_ids_valid(nodes, inputs), pattern_task_valid(task),
            pattern_compile_step_effect(task, before, after, inputs, results, pending, work, output),
        ensures
            pattern_nodes_wf(pattern_output_nodes(nodes, output), after),
            pattern_ids_valid(pattern_output_nodes(nodes, output), pattern_output_ids(nodes, results, output)),
            before.variables.to_set() == pattern_heads_vars(pattern_heads(nodes, before, inputs))
                ==> after.variables.to_set() == pattern_heads_vars(pattern_heads(pattern_output_nodes(nodes, output), after, pattern_output_ids(nodes, results, output))),
            forall|out: Seq<language::Head>| #[trigger] pattern_compile_run(work, pattern_heads(pattern_output_nodes(nodes, output), after, pattern_output_ids(nodes, results, output)), out)
                ==> pattern_compile_run(pending.push(task), pattern_heads(nodes, before, inputs), out),
    {
        let old_heads = pattern_heads(nodes, before, inputs);
        assert(old_heads.len() == inputs.len());
        reveal(pattern_compile_step_effect);
        assert forall|id: int| 0 <= id < nodes.len() implies pattern_node_wf(nodes, after, id) by {
            lemma_pattern_head_extends(nodes, before, after, id);
        }
        assert(pattern_nodes_wf(nodes, after));
        assert(pattern_heads(nodes, after, inputs) =~= old_heads) by {
            assert forall|i: int| 0 <= i < inputs.len() implies pattern_heads(nodes, after, inputs)[i] == old_heads[i] by {
                lemma_pattern_head_extends(nodes, before, after, inputs[i] as int);
            }
        }
        if output is None {
            assert(after == before && results == inputs);
            match task {
                PendingPatternWork::Enter(data) => {
                    assert forall|out: Seq<language::Head>| pattern_compile_run(work, old_heads, out) implies pattern_compile_run(pending.push(task), old_heads, out) by {
                        lemma_pattern_run_unfold(pending, task, old_heads, out);
                        if exists|children: Seq<Data>| language::tagged_payload(data, "array"@) == Some(Data::Array(children))
                            && work == pending.push(PendingPatternWork::Array(children.len(), inputs.len())) + pattern_jobs(children) {
                            let children = choose|children: Seq<Data>| language::tagged_payload(data, "array"@) == Some(Data::Array(children))
                                && work == pending.push(PendingPatternWork::Array(children.len(), inputs.len())) + pattern_jobs(children);
                            lemma_pattern_run_jobs(pending.push(PendingPatternWork::Array(children.len(), inputs.len())), children, old_heads, out);
                            let decoded = choose|decoded: Seq<language::Head>| decoded.len() == children.len()
                                && (forall|i: int| 0 <= i < children.len() ==> language::decodes_head(children[i], decoded[i]))
                                && pattern_compile_run(pending.push(PendingPatternWork::Array(children.len(), inputs.len())), old_heads + decoded, out);
                            assert((old_heads + decoded).take(old_heads.len() as int) =~= old_heads);
                            assert((old_heads + decoded).skip(old_heads.len() as int) =~= decoded);
                            assert(language::decodes_head(data, language::Head::Array(decoded)));
                            lemma_pattern_run_unfold(pending, PendingPatternWork::Array(children.len(), inputs.len()), old_heads + decoded, out);
                            assert(pattern_compile_run(pending, old_heads.push(language::Head::Array(decoded)), out));
                            assert(exists|head: language::Head| language::decodes_head(data, head) && pattern_compile_run(pending, old_heads.push(head), out));
                        } else {
                            let (fields, keys, children) = choose|fields: Map<Data, Data>, keys: Seq<Data>, children: Seq<Data>|
                                language::tagged_payload(data, "object"@) == Some(Data::Object(fields))
                                && keys.no_duplicates() && keys.to_set() == fields.dom() && children.len() == keys.len()
                                && (forall|i: int| 0 <= i < keys.len() ==> children[i] == fields[keys[i]])
                                && work == pending.push(PendingPatternWork::Object(keys, inputs.len())) + pattern_jobs(children);
                            lemma_pattern_run_jobs(pending.push(PendingPatternWork::Object(keys, inputs.len())), children, old_heads, out);
                            let decoded = choose|decoded: Seq<language::Head>| decoded.len() == children.len()
                                && (forall|i: int| 0 <= i < children.len() ==> language::decodes_head(children[i], decoded[i]))
                                && pattern_compile_run(pending.push(PendingPatternWork::Object(keys, inputs.len())), old_heads + decoded, out);
                            lemma_pattern_fields(keys, decoded);
                            keys.to_set_ensures();
                            let hs = pattern_fields_head(keys, decoded);
                            assert forall|key: Data| hs.contains_key(key) implies language::decodes_head(fields[key], hs[key]) by {
                                let i = choose|i: int| 0 <= i < keys.len() && keys[i] == key;
                                assert(hs[key] == decoded[i] && children[i] == fields[key]);
                            }
                            assert(language::decodes_head(data, language::Head::Object(hs)));
                            assert((old_heads + decoded).take(old_heads.len() as int) =~= old_heads);
                            assert((old_heads + decoded).skip(old_heads.len() as int) =~= decoded);
                            lemma_pattern_run_unfold(pending, PendingPatternWork::Object(keys, inputs.len()), old_heads + decoded, out);
                            assert(pattern_compile_run(pending, old_heads.push(language::Head::Object(hs)), out));
                            assert(exists|head: language::Head| language::decodes_head(data, head) && pattern_compile_run(pending, old_heads.push(head), out));
                        }
                    }
                }, _ => {},
            }
            return;
        }
        let node = output->Some_0;
        let next = nodes.push(node);
        assert(nodes.is_prefix_of(next));
        match task {
            PendingPatternWork::Enter(_) => {},
            PendingPatternWork::Array(len, start) => {
                match node { PatternNode::Array(children) => {
                    assert forall|i: int| 0 <= i < children@.len() implies children@[i] < nodes.len() by {
                        assert(children@[i] == inputs[start + i]);
                    }
                }, _ => {} }
            },
            PendingPatternWork::Object(keys, start) => {
                match node { PatternNode::Object(fields) => {
                    assert(fields@.len() == keys.len());
                    assert forall|i: int| 0 <= i < fields@.len() implies fields@[i].1 < nodes.len() by {
                        assert(0 <= i < keys.len());
                        assert(value_view(fields@[i].0) == keys[i]);
                        assert(fields@[i].1 == inputs[start + i]);
                        assert(0 <= start + i < inputs.len());
                    }
                    assert forall|i: int, j: int| 0 <= i < j < fields@.len() implies value_view(fields@[i].0) != value_view(fields@[j].0) by { assert(keys[i] != keys[j]); }
                }, _ => {} }
            },
        }
        assert(pattern_node_wf(next, after, nodes.len() as int));
        assert forall|id: int| 0 <= id < next.len() implies pattern_node_wf(next, after, id) by {
            if id < nodes.len() { lemma_pattern_node_frame(nodes, next, after, id); }
        }
        assert(pattern_nodes_wf(next, after));
        assert forall|i: int| 0 <= i < inputs.len() implies pattern_head(next, after, inputs[i] as int) == old_heads[i] by {
            lemma_pattern_node_frame(nodes, next, after, inputs[i] as int);
        }
        let head = pattern_head(next, after, nodes.len() as int);
        let final_ids = results.push(nodes.len() as usize);
        let new_heads = pattern_heads(next, after, final_ids);
        match task {
            PendingPatternWork::Enter(data) => {
                assert(new_heads =~= old_heads.push(head));
                assert(language::decodes_head(data, head));
                if before.variables.to_set() == pattern_heads_vars(old_heads) {
                    assert(old_heads.push(head).drop_last() =~= old_heads);
                    lemma_pattern_vars_push(old_heads, head);
                    match node {
                        PatternNode::Literal(_) | PatternNode::Any => { assert(language::head_vars(head) =~= Set::empty()); },
                        PatternNode::Variable(index) => { assert(language::head_vars(head) =~= Set::empty().insert(after.variables[index@ as int])); },
                        _ => {},
                    }
                    assert(after.variables.to_set() =~= pattern_heads_vars(new_heads));
                }
                assert forall|out: Seq<language::Head>| pattern_compile_run(work, new_heads, out) implies pattern_compile_run(pending.push(task), old_heads, out) by {
                    lemma_pattern_run_unfold(pending, task, old_heads, out);
                    assert(exists|head: language::Head| language::decodes_head(data, head) && pattern_compile_run(pending, old_heads.push(head), out));
                }
            },
            PendingPatternWork::Array(len, start) => {
                let tail = old_heads.skip(start as int);
                match node { PatternNode::Array(children) => {
                    let hs = head->Array_0;
                    assert(hs =~= tail) by {
                        assert forall|i: int| 0 <= i < hs.len() implies hs[i] == tail[i] by {
                            assert(children@[i] == inputs[start + i]);
                            assert(hs[i] == pattern_head(next, after, children@[i] as int));
                        }
                    }
                }, _ => {} }
                assert(head == language::Head::Array(tail));
                assert(new_heads =~= old_heads.take(start as int).push(head));
                language::lemma_head_vars_array(tail); lemma_pattern_vars(tail);
                assert(language::head_vars(head) =~= pattern_heads_vars(tail));
                lemma_pattern_vars_concat(old_heads.take(start as int), tail);
                assert(old_heads.take(start as int) + tail =~= old_heads);
                assert(new_heads.drop_last() =~= old_heads.take(start as int));
                lemma_pattern_vars_push(old_heads.take(start as int), head);
                assert(pattern_heads_vars(new_heads) == pattern_heads_vars(old_heads));
                assert forall|out: Seq<language::Head>| pattern_compile_run(work, new_heads, out) implies pattern_compile_run(pending.push(task), old_heads, out) by { lemma_pattern_run_unfold(pending, task, old_heads, out); }
            },
            PendingPatternWork::Object(keys, start) => {
                let tail = old_heads.skip(start as int);
                lemma_pattern_fields(keys, tail);
                let expected = pattern_fields_head(keys, tail);
                match node { PatternNode::Object(fields) => {
                    let actual = head->Object_0;
                    let field_keys = fields@.map(|i: int, field: (Value, usize)| value_view(field.0));
                    assert(field_keys =~= keys);
                    keys.to_set_ensures();
                    assert(actual.dom() == expected.dom());
                    assert forall|key: Data| actual.contains_key(key) implies actual[key] == expected[key] by {
                        let i = choose|i: int| 0 <= i < keys.len() && keys[i] == key;
                        let j = choose|j: int| 0 <= j < fields@.len() && value_view(fields@[j].0) == key;
                        assert(i == j);
                        assert(actual[key] == pattern_head(next, after, fields@[i].1 as int));
                        assert(fields@[i].1 == inputs[start + i]);
                        assert(expected[key] == tail[i]);
                    }
                    assert(actual =~= expected);
                }, _ => {} }
                assert(head == language::Head::Object(expected));
                assert(new_heads =~= old_heads.take(start as int).push(head));
                lemma_pattern_vars_concat(old_heads.take(start as int), tail);
                assert(old_heads.take(start as int) + tail =~= old_heads);
                assert(new_heads.drop_last() =~= old_heads.take(start as int));
                lemma_pattern_vars_push(old_heads.take(start as int), head);
                assert(pattern_heads_vars(new_heads) == pattern_heads_vars(old_heads));
                assert forall|out: Seq<language::Head>| pattern_compile_run(work, new_heads, out) implies pattern_compile_run(pending.push(task), old_heads, out) by { lemma_pattern_run_unfold(pending, task, old_heads, out); }
            },
        }
    }

    pub(super) open spec fn pattern_node_wf(nodes: Seq<PatternNode>, sym: model::Symbols, id: int) -> bool {
        0 <= id < nodes.len() && match nodes[id] {
            PatternNode::Literal(index) => index@ < sym.constants.len(),
            PatternNode::Variable(index) => index@ < sym.variables.len(),
            PatternNode::Any => true,
            PatternNode::Array(children) => forall|i: int| 0 <= i < children@.len() ==> children@[i] < id,
            PatternNode::Object(fields) =>
                (forall|i: int| 0 <= i < fields@.len() ==> fields@[i].1 < id)
                && (forall|i: int, j: int| 0 <= i < j < fields@.len()
                    ==> value_view(fields@[i].0) != value_view(fields@[j].0)),
        }
    }

    pub(super) open spec fn pattern_nodes_wf(nodes: Seq<PatternNode>, sym: model::Symbols) -> bool {
        model::symbols_wf(sym) && forall|id: int| 0 <= id < nodes.len() ==> pattern_node_wf(nodes, sym, id)
    }

    pub(super) open spec fn pattern_head(nodes: Seq<PatternNode>, sym: model::Symbols, id: int) -> language::Head
        decreases id,
    {
        if 0 <= id < nodes.len() {
            match nodes[id] {
                PatternNode::Literal(index) => language::Head::Literal(sym.constants[index@ as int]),
                PatternNode::Variable(index) => language::Head::Variable(sym.variables[index@ as int]),
                PatternNode::Any => language::Head::Any,
                PatternNode::Array(children) => language::Head::Array(children@.map(|i: int, child: usize|
                    if child < id { pattern_head(nodes, sym, child as int) } else { arbitrary() })),
                PatternNode::Object(fields) => language::Head::Object(Map::new(
                    fields@.map(|i: int, field: (Value, usize)| value_view(field.0)).to_set(),
                    |key: Data| {
                        let i = choose|i: int| 0 <= i < fields@.len() && value_view(fields@[i].0) == key;
                        if 0 <= i < fields@.len() && fields@[i].1 < id {
                            pattern_head(nodes, sym, fields@[i].1 as int)
                        } else { arbitrary() }
                    })),
            }
        } else { arbitrary() }
    }

    pub open(super) spec fn pattern_represents(pattern: CompiledPattern, sym: model::Symbols, head: language::Head) -> bool {
        pattern_nodes_wf(pattern.nodes@, sym) && pattern.root < pattern.nodes@.len()
            && pattern_head(pattern.nodes@, sym, pattern.root as int) == head
            && sym.variables.to_set() == language::head_vars(head)
    }

    pub(super) proof fn lemma_pattern_head_extends(
        nodes: Seq<PatternNode>, before: model::Symbols, after: model::Symbols, id: int,
    )
        requires pattern_nodes_wf(nodes, before), symbols_extends(before, after), model::symbols_wf(after),
            0 <= id < nodes.len(),
        ensures pattern_node_wf(nodes, after, id),
            pattern_head(nodes, before, id) == pattern_head(nodes, after, id),
        decreases id,
    {
        reveal_with_fuel(pattern_head, 2);
        assert(pattern_node_wf(nodes, before, id));
        assert(before.constants.len() <= after.constants.len());
        assert(before.variables.len() <= after.variables.len());
        assert forall|i: int| 0 <= i < before.constants.len() implies before.constants[i] == after.constants[i] by {}
        assert forall|i: int| 0 <= i < before.variables.len() implies before.variables[i] == after.variables[i] by {}
        match nodes[id] {
            PatternNode::Array(children) => {
                assert forall|i: int| 0 <= i < children@.len() implies
                    pattern_head(nodes, before, children@[i] as int) == pattern_head(nodes, after, children@[i] as int) by {
                    lemma_pattern_head_extends(nodes, before, after, children@[i] as int);
                }
                let left = pattern_head(nodes, before, id)->Array_0;
                let right = pattern_head(nodes, after, id)->Array_0;
                assert(left.len() == right.len());
                assert forall|i: int| 0 <= i < left.len() implies left[i] == right[i] by {
                    assert(left[i] == pattern_head(nodes, before, children@[i] as int));
                    assert(right[i] == pattern_head(nodes, after, children@[i] as int));
                }
                assert(left =~= right);
                assert(pattern_head(nodes, before, id) == pattern_head(nodes, after, id));
            },
            PatternNode::Object(fields) => {
                assert forall|i: int| 0 <= i < fields@.len() implies
                    pattern_head(nodes, before, fields@[i].1 as int) == pattern_head(nodes, after, fields@[i].1 as int) by {
                    lemma_pattern_head_extends(nodes, before, after, fields@[i].1 as int);
                }
                let left = pattern_head(nodes, before, id)->Object_0;
                let right = pattern_head(nodes, after, id)->Object_0;
                assert(left.dom() == right.dom());
                assert forall|key: Data| left.contains_key(key) implies left[key] == right[key] by {
                    let i = choose|i: int| 0 <= i < fields@.len() && value_view(fields@[i].0) == key;
                    assert(left[key] == pattern_head(nodes, before, fields@[i].1 as int));
                    assert(right[key] == pattern_head(nodes, after, fields@[i].1 as int));
                }
                assert(left =~= right);
                assert(pattern_head(nodes, before, id) == pattern_head(nodes, after, id));
            },
            PatternNode::Literal(index) => {
                assert(pattern_head(nodes, before, id) == pattern_head(nodes, after, id));
            },
            PatternNode::Variable(index) => {
                assert(pattern_head(nodes, before, id) == pattern_head(nodes, after, id));
            },
            PatternNode::Any => {},
        }
    }

    pub proof fn lemma_pattern_represents_extends(
        pattern: CompiledPattern, before: model::Symbols, after: model::Symbols, head: language::Head,
    )
        requires pattern_represents(pattern, before, head), symbols_extends(before, after),
            model::symbols_wf(after), after.variables == before.variables,
        ensures pattern_represents(pattern, after, head),
    {
        assert forall|id: int| 0 <= id < pattern.nodes@.len() implies pattern_node_wf(pattern.nodes@, after, id) by {
            lemma_pattern_head_extends(pattern.nodes@, before, after, id);
        }
        lemma_pattern_head_extends(pattern.nodes@, before, after, pattern.root as int);
    }

    pub open(super) spec fn pattern_work_valid(pattern: CompiledPattern, work: Seq<(usize, &Value)>) -> bool {
        forall|i: int| 0 <= i < work.len() ==> work[i].0 < pattern.nodes@.len()
    }

    pub open(super) spec fn partial_bindings(bindings: Seq<Value>, sym: model::Symbols, theta: language::Subst) -> bool {
        bindings.len() == sym.variables.len()
        && forall|i: int| 0 <= i < bindings.len() && value_view(bindings[i]) != Data::Undefined
            ==> theta.contains_key(sym.variables[i]) && theta[sym.variables[i]] == value_view(bindings[i])
    }

    pub open(super) spec fn pattern_pending(pattern: CompiledPattern, sym: model::Symbols, work: Seq<(usize, &Value)>, theta: language::Subst) -> bool {
        forall|i: int| 0 <= i < work.len()
            ==> language::head_match(pattern_head(pattern.nodes@, sym, work[i].0 as int), value_view(*work[i].1), theta)
    }

    pub open(super) spec fn pattern_match_state(pattern: CompiledPattern, sym: model::Symbols, work: Seq<(usize, &Value)>, bindings: Seq<Value>, theta: language::Subst) -> bool {
        partial_bindings(bindings, sym, theta) && pattern_pending(pattern, sym, work, theta)
    }

    pub(super) proof fn lemma_pattern_pending_push(pattern: CompiledPattern, sym: model::Symbols, work: Seq<(usize, &Value)>, task: (usize, &Value), theta: language::Subst)
        ensures pattern_pending(pattern, sym, work.push(task), theta)
            == (pattern_pending(pattern, sym, work, theta)
                && language::head_match(pattern_head(pattern.nodes@, sym, task.0 as int), value_view(*task.1), theta)),
    {
        if pattern_pending(pattern, sym, work.push(task), theta) {
            assert forall|i: int| 0 <= i < work.len() implies language::head_match(
                pattern_head(pattern.nodes@, sym, work[i].0 as int), value_view(*work[i].1), theta) by {
                assert(work.push(task)[i] == work[i]);
            }
            assert(work.push(task)[work.len() as int] == task);
        }
        if pattern_pending(pattern, sym, work, theta)
            && language::head_match(pattern_head(pattern.nodes@, sym, task.0 as int), value_view(*task.1), theta) {
            assert forall|i: int| 0 <= i < work.push(task).len() implies language::head_match(
                pattern_head(pattern.nodes@, sym, work.push(task)[i].0 as int), value_view(*work.push(task)[i].1), theta) by {
                if i < work.len() { assert(work.push(task)[i] == work[i]); }
                else { assert(work.push(task)[i] == task); }
            }
        }
    }

    pub(super) proof fn lemma_head_match_defined(head: language::Head, request: Data, theta: language::Subst, name: Seq<char>)
        requires language::head_match(head, request, theta), language::head_vars(head).contains(name),
        ensures theta.contains_key(name), theta[name] != Data::Undefined,
        decreases head,
    {
        match head {
            language::Head::Array(children) => {
                language::lemma_head_vars_array(children);
                let i = choose|i: int| 0 <= i < children.len() && language::head_vars(children[i]).contains(name);
                match request { Data::Array(values) => lemma_head_match_defined(children[i], values[i], theta, name), _ => {} }
            },
            language::Head::Object(fields) => {
                language::lemma_head_vars_object(fields);
                let key = choose|key: Data| fields.contains_key(key) && language::head_vars(fields[key]).contains(name);
                match request { Data::Object(values) => lemma_head_match_defined(fields[key], values[key], theta, name), _ => {} }
            },
            _ => {},
        }
    }

    pub(crate) proof fn lemma_theta_of(bindings: Seq<Value>, sym: model::Symbols)
        requires model::symbols_wf(sym), bindings.len() == sym.variables.len(),
        ensures theta_of(bindings, sym).dom() == sym.variables.to_set(),
            partial_bindings(bindings, sym, theta_of(bindings, sym)),
            forall|i: int| 0 <= i < bindings.len() ==> theta_of(bindings, sym)[sym.variables[i]] == value_view(bindings[i]),
    {
        assert(sym.variables.take(sym.variables.len() as int) =~= sym.variables);
        assert forall|i: int| 0 <= i < bindings.len() implies theta_of(bindings, sym).contains_key(sym.variables[i])
            && theta_of(bindings, sym)[sym.variables[i]] == value_view(bindings[i]) by {
            let j = choose|j: int| 0 <= j < sym.variables.len() && j < bindings.len() && sym.variables[j] == sym.variables[i];
            assert(j == i);
        }
    }


    pub(super) proof fn lemma_pattern_match_state_push(pattern: CompiledPattern, sym: model::Symbols, work: Seq<(usize, &Value)>, bindings: Seq<Value>, task: (usize, &Value), theta: language::Subst)
        ensures pattern_match_state(pattern, sym, work.push(task), bindings, theta)
            == (partial_bindings(bindings, sym, theta) && pattern_pending(pattern, sym, work, theta)
                && language::head_match(pattern_head(pattern.nodes@, sym, task.0 as int), value_view(*task.1), theta)),
    {
        lemma_pattern_pending_push(pattern, sym, work, task, theta);
    }

    pub(super) proof fn lemma_pattern_reject(pattern: CompiledPattern, sym: model::Symbols, work: Seq<(usize, &Value)>, bindings: Seq<Value>, task: (usize, &Value))
        requires forall|theta: language::Subst| !language::head_match(pattern_head(pattern.nodes@, sym, task.0 as int), value_view(*task.1), theta),
        ensures forall|theta: language::Subst| !pattern_match_state(pattern, sym, work.push(task), bindings, theta),
    {
        assert forall|theta: language::Subst| !pattern_match_state(pattern, sym, work.push(task), bindings, theta) by {
            lemma_pattern_match_state_push(pattern, sym, work, bindings, task, theta);
        }
    }

    pub(super) proof fn lemma_head_undefined(head: language::Head, theta: language::Subst)
        ensures !language::head_match(head, Data::Undefined, theta),
    {
        match head { language::Head::Literal(_) => {}, language::Head::Variable(_) => {}, language::Head::Any => {},
            language::Head::Array(_) => {}, language::Head::Object(_) => {} }
    }

    pub(super) proof fn lemma_pattern_array_pending(pattern: CompiledPattern, sym: model::Symbols, initial: Seq<(usize, &Value)>, work: Seq<(usize, &Value)>, children: Seq<usize>, values: Seq<Value>, count: int, theta: language::Subst)
        requires 0 <= count <= children.len(), count <= values.len(), work.len() == initial.len() + count,
            work.take(initial.len() as int) == initial,
            forall|i: int| 0 <= i < count ==> work[initial.len() + i].0 == children[i]
                && value_view(*work[initial.len() + i].1) == value_view(values[i]),
        ensures pattern_pending(pattern, sym, work, theta)
            == (pattern_pending(pattern, sym, initial, theta)
                && forall|i: int| 0 <= i < count ==> language::head_match(pattern_head(pattern.nodes@, sym, children[i] as int), value_view(values[i]), theta)),
    {
        if pattern_pending(pattern, sym, work, theta) {
            assert forall|i: int| 0 <= i < initial.len() implies language::head_match(pattern_head(pattern.nodes@, sym, initial[i].0 as int), value_view(*initial[i].1), theta) by {
                assert(work[i] == initial[i]);
            }
            assert forall|i: int| 0 <= i < count implies language::head_match(pattern_head(pattern.nodes@, sym, children[i] as int), value_view(values[i]), theta) by {
                assert(0 <= initial.len() + i < work.len());
            }
        }
        if pattern_pending(pattern, sym, initial, theta)
            && forall|i: int| 0 <= i < count ==> language::head_match(pattern_head(pattern.nodes@, sym, children[i] as int), value_view(values[i]), theta) {
            assert forall|i: int| 0 <= i < work.len() implies language::head_match(pattern_head(pattern.nodes@, sym, work[i].0 as int), value_view(*work[i].1), theta) by {
                if i < initial.len() { assert(work[i] == initial[i]); }
                else {
                    let j = i - initial.len();
                    assert(0 <= j < count);
                    assert(work[initial.len() + j].0 == children[j]);
                    assert(value_view(*work[initial.len() + j].1) == value_view(values[j]));
                    assert(language::head_match(pattern_head(pattern.nodes@, sym, children[j] as int), value_view(values[j]), theta));
                }
            }
        }
    }

    pub(super) proof fn lemma_pattern_work_push(pattern: CompiledPattern, work: Seq<(usize, &Value)>, task: (usize, &Value))
        requires pattern_work_valid(pattern, work), task.0 < pattern.nodes@.len(),
        ensures pattern_work_valid(pattern, work.push(task)),
    {
        assert forall|i: int| 0 <= i < work.push(task).len() implies work.push(task)[i].0 < pattern.nodes@.len() by {
            if i < work.len() { assert(work.push(task)[i] == work[i]); }
            else { assert(work.push(task)[i] == task); }
        }
    }

    pub(super) proof fn lemma_pattern_array_match(nodes: Seq<PatternNode>, sym: model::Symbols, id: int, children: Box<[usize]>, values: Seq<Value>, theta: language::Subst)
        requires pattern_node_wf(nodes, sym, id), nodes[id] == PatternNode::Array(children),
        ensures language::head_match(pattern_head(nodes, sym, id), Data::Array(values_data(values)), theta)
            == (children@.len() == values.len() && forall|i: int| 0 <= i < children@.len()
                ==> language::head_match(pattern_head(nodes, sym, children@[i] as int), value_view(values[i]), theta)),
    {
        reveal_with_fuel(pattern_head, 2);
        reveal_with_fuel(language::head_match, 2);
        assert(pattern_head(nodes, sym, id) is Array);
        let heads = pattern_head(nodes, sym, id)->Array_0;
        assert(heads.len() == children@.len());
        assert forall|i: int| 0 <= i < heads.len() implies heads[i] == pattern_head(nodes, sym, children@[i] as int) by {}
        if language::head_match(pattern_head(nodes, sym, id), Data::Array(values_data(values)), theta) {
            assert forall|i: int| 0 <= i < children@.len() implies language::head_match(
                pattern_head(nodes, sym, children@[i] as int), value_view(values[i]), theta) by {
                assert(language::head_match(heads[i], values_data(values)[i], theta));
            }
        }
        if children@.len() == values.len() && forall|i: int| 0 <= i < children@.len()
            ==> language::head_match(pattern_head(nodes, sym, children@[i] as int), value_view(values[i]), theta) {
            assert forall|i: int| 0 <= i < heads.len() implies language::head_match(heads[i], values_data(values)[i], theta) by {
                assert(language::head_match(pattern_head(nodes, sym, children@[i] as int), value_view(values[i]), theta));
            }
        }
    }

    pub(super) proof fn lemma_pattern_object_match(nodes: Seq<PatternNode>, sym: model::Symbols, id: int, fields: Box<[(Value, usize)]>, values: Map<Data, Data>, theta: language::Subst)
        requires pattern_node_wf(nodes, sym, id), nodes[id] == PatternNode::Object(fields),
        ensures language::head_match(pattern_head(nodes, sym, id), Data::Object(values), theta)
            == (forall|i: int| 0 <= i < fields@.len() ==> values.contains_key(value_view(fields@[i].0))
                && language::head_match(pattern_head(nodes, sym, fields@[i].1 as int), values[value_view(fields@[i].0)], theta)),
    {
        reveal_with_fuel(pattern_head, 2);
        let heads = pattern_head(nodes, sym, id)->Object_0;
        let keys = fields@.map(|i: int, field: (Value, usize)| value_view(field.0));
        keys.to_set_ensures();
        assert forall|i: int| 0 <= i < fields@.len() implies heads.contains_key(value_view(fields@[i].0))
            && heads[value_view(fields@[i].0)] == pattern_head(nodes, sym, fields@[i].1 as int) by {
            let key = value_view(fields@[i].0);
            assert(keys[i] == key);
            assert(keys.to_set().contains(key));
            let j = choose|j: int| 0 <= j < fields@.len() && value_view(fields@[j].0) == key;
            assert(i == j) by {
                if i < j { assert(value_view(fields@[i].0) != value_view(fields@[j].0)); }
                if j < i { assert(value_view(fields@[j].0) != value_view(fields@[i].0)); }
            }
        }
        if forall|i: int| 0 <= i < fields@.len() ==> values.contains_key(value_view(fields@[i].0))
            && language::head_match(pattern_head(nodes, sym, fields@[i].1 as int), values[value_view(fields@[i].0)], theta) {
            assert forall|key: Data| heads.contains_key(key) implies values.contains_key(key) && language::head_match(heads[key], values[key], theta) by {
                let keys = fields@.map(|i: int, field: (Value, usize)| value_view(field.0));
                let i = choose|i: int| 0 <= i < keys.len() && keys[i] == key;
                assert(value_view(fields@[i].0) == key);
            }
        }
    }

    pub(super) proof fn lemma_pattern_object_pending(pattern: CompiledPattern, sym: model::Symbols, initial: Seq<(usize, &Value)>, work: Seq<(usize, &Value)>, fields: Seq<(Value, usize)>, values: Map<Data, Data>, count: int, theta: language::Subst)
        requires 0 <= count <= fields.len(), work.len() == initial.len() + count,
            work.take(initial.len() as int) == initial,
            forall|i: int| 0 <= i < count ==> work[initial.len() + i].0 == fields[i].1
                && values.contains_key(value_view(fields[i].0))
                && value_view(*work[initial.len() + i].1) == values[value_view(fields[i].0)],
        ensures pattern_pending(pattern, sym, work, theta)
            == (pattern_pending(pattern, sym, initial, theta)
                && forall|i: int| 0 <= i < count ==> language::head_match(pattern_head(pattern.nodes@, sym, fields[i].1 as int), values[value_view(fields[i].0)], theta)),
    {
        if pattern_pending(pattern, sym, work, theta) {
            assert forall|i: int| 0 <= i < initial.len() implies language::head_match(pattern_head(pattern.nodes@, sym, initial[i].0 as int), value_view(*initial[i].1), theta) by {
                assert(work[i] == initial[i]);
            }
            assert forall|i: int| 0 <= i < count implies language::head_match(pattern_head(pattern.nodes@, sym, fields[i].1 as int), values[value_view(fields[i].0)], theta) by {
                assert(0 <= initial.len() + i < work.len());
            }
        }
        if pattern_pending(pattern, sym, initial, theta)
            && forall|i: int| 0 <= i < count ==> language::head_match(pattern_head(pattern.nodes@, sym, fields[i].1 as int), values[value_view(fields[i].0)], theta) {
            assert forall|i: int| 0 <= i < work.len() implies language::head_match(pattern_head(pattern.nodes@, sym, work[i].0 as int), value_view(*work[i].1), theta) by {
                if i < initial.len() { assert(work[i] == initial[i]); }
                else {
                    let j = i - initial.len();
                    assert(0 <= j < count);
                    assert(work[initial.len() + j].0 == fields[j].1);
                    assert(value_view(*work[initial.len() + j].1) == values[value_view(fields[j].0)]);
                    assert(language::head_match(pattern_head(pattern.nodes@, sym, fields[j].1 as int), values[value_view(fields[j].0)], theta));
                }
            }
        }
    }
    pub(super) proof fn lemma_pattern_binding_step(before: Seq<Value>, after: Seq<Value>, sym: model::Symbols, index: int, request: Data)
        requires before.len() == sym.variables.len(), after.len() == before.len(), 0 <= index < before.len(),
            request != Data::Undefined, value_view(after[index]) == request,
            value_view(before[index]) == Data::Undefined || value_view(before[index]) == request,
            forall|i: int| 0 <= i < before.len() && i != index ==> value_view(before[i]) == value_view(after[i]),
        ensures forall|theta: language::Subst| partial_bindings(after, sym, theta)
            == (partial_bindings(before, sym, theta) && language::head_match(language::Head::Variable(sym.variables[index]), request, theta)),
    {
        assert forall|theta: language::Subst| partial_bindings(after, sym, theta)
            == (partial_bindings(before, sym, theta) && language::head_match(language::Head::Variable(sym.variables[index]), request, theta)) by {
            if partial_bindings(after, sym, theta) {
                assert(theta.contains_key(sym.variables[index]) && theta[sym.variables[index]] == request);
                assert forall|i: int| 0 <= i < before.len() && value_view(before[i]) != Data::Undefined implies
                    theta.contains_key(sym.variables[i]) && theta[sym.variables[i]] == value_view(before[i]) by {
                    if i == index { assert(value_view(before[i]) == request); }
                    else { assert(value_view(before[i]) == value_view(after[i])); }
                }
            }
            if partial_bindings(before, sym, theta) && language::head_match(language::Head::Variable(sym.variables[index]), request, theta) {
                assert forall|i: int| 0 <= i < after.len() && value_view(after[i]) != Data::Undefined implies
                    theta.contains_key(sym.variables[i]) && theta[sym.variables[i]] == value_view(after[i]) by {
                    if i == index { assert(value_view(after[i]) == request); }
                    else { assert(value_view(before[i]) == value_view(after[i])); }
                }
            }
        }
    }

    pub proof fn lemma_member_deep(object: crate::Rc<Object>, key: Seq<char>, value: Value)
        requires
            forall|k1: Value, k2: Value| object@.contains_key(k1) && object@.contains_key(k2)
                && value_view(k1) == value_view(k2) ==> k1 == k2,
            exists|candidate: Value| object@.contains_key(candidate) && value_view(candidate) == Data::String(key) && object@[candidate] == value,
        ensures match value_view(Value::Object(object)) {
            Data::Object(fields) => fields.contains_key(Data::String(key)) && fields[Data::String(key)] == value_view(value),
            _ => false,
        },
    {
        lemma_value_view_object(object);
        let candidate = choose|candidate: Value| object@.contains_key(candidate)
            && value_view(candidate) == Data::String(key) && object@[candidate] == value;
    }

    use crate::verify::number_specs::NumberView;
    use crate::verify::value_numeric::{self as vnum, Numeric};
    use vstd::arithmetic::{div_mod::*, power2::*};

    pub open spec fn source_native_index(converted: Option<u64>, limit: nat) -> Option<int> {
        match converted { Some(index) => if index < limit { Some(index as int) } else { None }, None => None }
    }

    pub open spec fn source_mathematical_index(number: Numeric, limit: nat) -> Option<int> {
        match language::array_index(number) {
            Some(index) => if 0 <= index < limit { Some(index) } else { None },
            None => None,
        }
    }

    pub proof fn lemma_index_matches_array_index(number: NumberView, converted: Option<u64>, limit: nat)
        requires
            limit <= usize::MAX,
            match number {
                NumberView::Integer(n) => if 0 <= n <= u64::MAX {
                    converted matches Some(v) && v as int == n
                } else {
                    converted is None
                },
                NumberView::Float(f) => converted == vnum::float_index_spec(f),
            },
        ensures source_native_index(converted, limit) == source_mathematical_index(vnum::numeric_of(number), limit),
    {
        assert(usize::MAX as nat <= u64::MAX as nat) by(compute);
        lemma_pow2_pos(1074);
        let scale = pow2(1074) as int;
        match number {
            NumberView::Integer(n) => {
                assert(vnum::scaled_units(number) == n * scale) by(nonlinear_arith)
                    requires vnum::scaled_units(number) == if n < 0 { -((-n) * scale) } else { n * scale };
                lemma_mod_multiples_basic(n, scale);
                lemma_div_multiples_vanish(n, scale);
                assert(scale * n == n * scale) by(nonlinear_arith);
                assert((n * scale >= 0) == (n >= 0)) by(nonlinear_arith)
                    requires scale > 0;
            },
            NumberView::Float(f) => {
                vnum::lemma_float_index_matches_numeric(f);
                let units = vnum::scaled_units(number);
                if let Some(i) = converted {
                    lemma_mod_multiples_basic(i as int, scale);
                    lemma_div_multiples_vanish(i as int, scale);
                    assert(scale * (i as int) == (i as int) * scale) by(nonlinear_arith);
                    assert(i as int * scale >= 0) by(nonlinear_arith)
                        requires scale > 0;
                } else if vnum::numeric_of(number).rank == 0 && units >= 0 && units % scale == 0 {
                    // The only remaining None case: an integer beyond u64, so beyond every array.
                    assert(units / scale > u64::MAX);
                }
            },
        }
    }


    pub open spec fn option_value_data(value: Option<&Value>) -> Option<Data> {
        match value { Some(value) => Some(value_view(*value)), None => None }
    }

    pub open spec fn selections_wf(selections: Seq<Option<Option<&Value>>>, sym: model::Symbols, event: Data) -> bool {
        forall|i: int| 0 <= i < selections.len() && (#[trigger] selections[i]) is Some
            ==> i < sym.paths.len() && option_value_data(selections[i].unwrap()) == language::select(event, sym.paths[i])
    }

    pub open spec fn selected_step_data(value: Option<&Value>) -> Option<Data> {
        match value {
            Some(value) => if value_view(*value) == Data::Undefined { None } else { Some(value_view(*value)) },
            None => None,
        }
    }

    pub proof fn lemma_array_data(array: crate::Rc<Array>)
        ensures value_view(Value::Array(array)) == Data::Array(values_data(array@)),
    {
        lemma_value_view_array(array);
        let data = match value_view(Value::Array(array)) { Data::Array(data) => data, _ => Seq::empty() };
        assert(data =~= values_data(array@));
    }

    pub proof fn lemma_source_select_cons(event: Data, key: Data, tail: Seq<Data>)
        ensures language::select(event, seq![key] + tail) == match language::select(event, seq![key]) {
            Some(next) => language::select(next, tail), None => None,
        },
    {
        reveal_with_fuel(language::select, 3);
        let path = seq![key] + tail;
        assert(path[0] == key);
        assert(path.drop_first() =~= tail);
        assert(seq![key].drop_first() =~= Seq::<Data>::empty());
        if event != Data::Undefined {
            let next = match event {
                Data::Object(fields) => if fields.contains_key(key) { Some(fields[key]) } else { None },
                Data::Set(values) => if values.contains(key) { Some(key) } else { None },
                Data::Array(values) => match key {
                    Data::Number(number) => match language::array_index(number) {
                        Some(index) => if 0 <= index < values.len() { Some(values[index]) } else { None },
                        None => None,
                    },
                    _ => None,
                },
                _ => None,
            };
            match next { Some(next) => { if next == Data::Undefined { assert(language::select(next, tail) == None); } }, None => {} }
        }
    }

    pub proof fn lemma_values_data_tail(values: Seq<Value>, index: int)
        requires 0 <= index < values.len(),
        ensures values_data(values.skip(index)) == seq![value_view(values[index])] + values_data(values.skip(index + 1)),
    {
        assert(values_data(values.skip(index)) =~= seq![value_view(values[index])] + values_data(values.skip(index + 1)));
    }


    pub(super) proof fn lemma_constant_insert_wf(
        sym: model::Symbols, constants: Map<Data, ConstId>, paths: Map<Seq<Data>, PathId>, variables: Map<Seq<char>, VariableId>,
        data: Data, id: ConstId,
    )
        requires builder_tables_wf(sym, constants, paths, variables), !constants.contains_key(data), id@ == sym.constants.len(),
        ensures builder_tables_wf(model::Symbols { constants: sym.constants.push(data), ..sym }, constants.insert(data, id), paths, variables),
    {
        let after = sym.constants.push(data);
        if sym.constants.contains(data) {
            let i = choose|i: int| 0 <= i < sym.constants.len() && sym.constants[i] == data;
            assert(constants.contains_key(data));
        }
        assert(!sym.constants.contains(data));
        assert(after.no_duplicates());
        assert forall|key: Data| constants.insert(data, id).contains_key(key)
            <==> (exists|i: int| 0 <= i < after.len() && after[i] == key) by {
            if key == data {
                assert(after[sym.constants.len() as int] == data);
            } else if constants.contains_key(key) {
                let i = choose|i: int| 0 <= i < sym.constants.len() && sym.constants[i] == key;
                assert(after[i] == key);
            } else if exists|i: int| 0 <= i < after.len() && after[i] == key {
                let i = choose|i: int| 0 <= i < after.len() && after[i] == key;
                assert(i < sym.constants.len());
                assert(constants.contains_key(key));
            }
        }
        assert forall|i: int| 0 <= i < after.len() implies constants.insert(data, id).contains_key(after[i])
            && constants.insert(data, id)[after[i]]@ == i by {
            if i < sym.constants.len() {
                assert(after[i] != data);
                assert(constants[sym.constants[i]]@ == i);
            } else {
                assert(i == sym.constants.len());
            }
        }
    }

    pub(super) proof fn lemma_values_data_push(values: Seq<Value>, value: Value)
        ensures values_data(values.push(value)) == values_data(values).push(value_view(value)),
    {
        assert(values_data(values.push(value)) =~= values_data(values).push(value_view(value)));
    }


    pub proof fn lemma_source_select_single(event: Data, key: Data)
        ensures language::select(event, seq![key]) == {
            let next = if event == Data::Undefined { None } else { match event {
                Data::Object(fields) => if fields.contains_key(key) { Some(fields[key]) } else { None },
                Data::Set(values) => if values.contains(key) { Some(key) } else { None },
                Data::Array(values) => match key {
                    Data::Number(number) => match language::array_index(number) {
                        Some(index) => if 0 <= index < values.len() { Some(values[index]) } else { None },
                        None => None,
                    }, _ => None,
                }, _ => None,
            }};
            match next { Some(value) => if value == Data::Undefined { None } else { Some(value) }, None => None }
        },
    {
        reveal_with_fuel(language::select, 3);
        assert(seq![key].drop_first() =~= Seq::<Data>::empty());
    }


    pub(super) proof fn lemma_path_insert_wf(
        sym: model::Symbols, constants: Map<Data, ConstId>, paths: Map<Seq<Data>, PathId>, variables: Map<Seq<char>, VariableId>,
        data: Seq<Data>, id: PathId,
    )
        requires builder_tables_wf(sym, constants, paths, variables), !paths.contains_key(data), id@ == sym.paths.len(),
        ensures builder_tables_wf(model::Symbols { paths: sym.paths.push(data), ..sym }, constants, paths.insert(data, id), variables),
    {
        let after = sym.paths.push(data);
        if sym.paths.contains(data) {
            let i = choose|i: int| 0 <= i < sym.paths.len() && sym.paths[i] == data;
            assert(paths.contains_key(data));
        }
        assert(!sym.paths.contains(data));
        assert(after.no_duplicates());
        assert forall|key: Seq<Data>| paths.insert(data, id).contains_key(key)
            <==> (exists|i: int| 0 <= i < after.len() && after[i] == key) by {
            if key == data { assert(after[sym.paths.len() as int] == data); }
            else if paths.contains_key(key) {
                let i = choose|i: int| 0 <= i < sym.paths.len() && sym.paths[i] == key;
                assert(after[i] == key);
            } else if exists|i: int| 0 <= i < after.len() && after[i] == key {
                let i = choose|i: int| 0 <= i < after.len() && after[i] == key;
                assert(i < sym.paths.len()); assert(paths.contains_key(key));
            }
        }
        assert forall|i: int| 0 <= i < after.len() implies paths.insert(data, id).contains_key(after[i])
            && paths.insert(data, id)[after[i]]@ == i by {
            if i < sym.paths.len() { assert(after[i] != data); assert(paths[sym.paths[i]]@ == i); }
            else { assert(i == sym.paths.len()); }
        }
    }

    pub(super) proof fn lemma_variable_insert_wf(
        sym: model::Symbols, constants: Map<Data, ConstId>, paths: Map<Seq<Data>, PathId>, variables: Map<Seq<char>, VariableId>,
        name: Seq<char>, id: VariableId,
    )
        requires builder_tables_wf(sym, constants, paths, variables), !variables.contains_key(name), id@ == sym.variables.len(), name.len() > 0,
        ensures builder_tables_wf(model::Symbols { variables: sym.variables.push(name), ..sym }, constants, paths, variables.insert(name, id)),
    {
        let after = sym.variables.push(name);
        if sym.variables.contains(name) {
            let i = choose|i: int| 0 <= i < sym.variables.len() && sym.variables[i] == name;
            assert(variables.contains_key(name));
        }
        assert(!sym.variables.contains(name));
        assert(after.no_duplicates());
        assert forall|i: int| 0 <= i < after.len() implies after[i].len() > 0 by {
            if i < sym.variables.len() { assert(sym.variables[i].len() > 0); }
        }
        assert forall|key: Seq<char>| variables.insert(name, id).contains_key(key)
            <==> (exists|i: int| 0 <= i < after.len() && after[i] == key) by {
            if key == name { assert(after[sym.variables.len() as int] == name); }
            else if variables.contains_key(key) {
                let i = choose|i: int| 0 <= i < sym.variables.len() && sym.variables[i] == key;
                assert(after[i] == key);
            } else if exists|i: int| 0 <= i < after.len() && after[i] == key {
                let i = choose|i: int| 0 <= i < after.len() && after[i] == key;
                assert(i < sym.variables.len()); assert(variables.contains_key(key));
            }
        }
        assert forall|i: int| 0 <= i < after.len() implies variables.insert(name, id).contains_key(after[i])
            && variables.insert(name, id)[after[i]]@ == i by {
            if i < sym.variables.len() { assert(after[i] != name); assert(variables[sym.variables[i]]@ == i); }
            else { assert(i == sym.variables.len()); }
        }
    }


    pub(super) proof fn lemma_cloned_values_data(original: Seq<Value>, copied: Seq<Value>)
        requires original.len() == copied.len(),
            forall|i: int| 0 <= i < original.len() ==> cloned::<Value>(original[i], copied[i]),
        ensures values_data(original) == values_data(copied),
    {
        assert forall|i: int| 0 <= i < original.len() implies value_view(original[i]) == value_view(copied[i]) by {
            if original[i] != copied[i] {
                assert(vstd::pervasive::strictly_cloned::<Value>(original[i], copied[i]));
            }
        }
        assert(values_data(original) =~= values_data(copied));
    }

    // Termination measures for the source worklists. `data_work` is the structural size of
    // policy/request data; set elements and object keys are never traversed, so they weigh nothing.
    pub open spec fn data_work(d: Data) -> nat
        decreases d, 1nat, 0nat,
    {
        match d {
            Data::Array(cs) => 1 + data_seq_work(d, cs),
            Data::Object(fs) => 1 + data_map_work(d, fs, fs.dom()),
            _ => 1,
        }
    }

    pub open spec fn data_seq_work(bound: Data, cs: Seq<Data>) -> nat
        decreases bound, 0nat, cs.len(),
        when forall|i: int| 0 <= i < cs.len() ==> is_smaller_than(cs[i], bound)
    {
        if cs.len() == 0 { 0 } else { data_work(cs[0]) + data_seq_work(bound, cs.drop_first()) }
    }

    pub open spec fn data_map_work(bound: Data, fs: Map<Data, Data>, keys: Set<Data>) -> nat
        decreases bound, 0nat, keys.len(),
        when keys.subset_of(fs.dom()) && forall|k: Data| fs.dom().contains(k) ==> is_smaller_than(fs[k], bound)
    {
        if keys.is_empty() { 0 } else {
            let k = keys.choose();
            1 + data_work(fs[k]) + data_map_work(bound, fs, keys.remove(k))
        }
    }

    pub open spec fn data_list_work(cs: Seq<Data>) -> nat
        decreases cs.len(),
    {
        if cs.len() == 0 { 0 } else { data_work(cs[0]) + data_list_work(cs.drop_first()) }
    }

    pub proof fn lemma_data_seq_work(bound: Data, cs: Seq<Data>)
        requires forall|i: int| 0 <= i < cs.len() ==> is_smaller_than(cs[i], bound),
        ensures data_seq_work(bound, cs) == data_list_work(cs),
        decreases cs.len(),
    {
        if cs.len() > 0 {
            assert forall|i: int| 0 <= i < cs.drop_first().len() implies is_smaller_than(cs.drop_first()[i], bound) by {
                assert(cs.drop_first()[i] == cs[i + 1]);
            }
            lemma_data_seq_work(bound, cs.drop_first());
        }
    }

    pub proof fn lemma_data_map_work_remove(bound: Data, fs: Map<Data, Data>, keys: Set<Data>, k: Data)
        requires keys.subset_of(fs.dom()), keys.contains(k),
            forall|key: Data| fs.dom().contains(key) ==> is_smaller_than(fs[key], bound),
        ensures data_map_work(bound, fs, keys) == 1 + data_work(fs[k]) + data_map_work(bound, fs, keys.remove(k)),
        decreases keys.len(),
    {
        broadcast use vstd::set::group_set_lemmas;
        let c = keys.choose();
        if c != k {
            lemma_data_map_work_remove(bound, fs, keys.remove(c), k);
            lemma_data_map_work_remove(bound, fs, keys.remove(k), c);
            assert(keys.remove(c).remove(k) =~= keys.remove(k).remove(c));
        }
    }

    pub proof fn lemma_data_map_work_values(bound: Data, fs: Map<Data, Data>, keys: Set<Data>, ks: Seq<Data>, children: Seq<Data>)
        requires keys.subset_of(fs.dom()), forall|key: Data| fs.dom().contains(key) ==> is_smaller_than(fs[key], bound),
            ks.no_duplicates(), forall|i: int| 0 <= i < ks.len() ==> keys.contains(ks[i]),
            children.len() == ks.len(), forall|i: int| 0 <= i < ks.len() ==> children[i] == fs[ks[i]],
        ensures data_list_work(children) <= data_map_work(bound, fs, keys),
        decreases ks.len(),
    {
        broadcast use vstd::set::group_set_lemmas;
        if ks.len() > 0 {
            let k = ks[0];
            let rest = ks.drop_first();
            lemma_data_map_work_remove(bound, fs, keys, k);
            assert forall|i: int, j: int| 0 <= i < rest.len() && 0 <= j < rest.len() && i != j implies rest[i] != rest[j] by {
                assert(rest[i] == ks[i + 1] && rest[j] == ks[j + 1]);
            }
            assert forall|i: int| 0 <= i < rest.len() implies keys.remove(k).contains(rest[i]) && children.drop_first()[i] == fs[rest[i]] by {
                assert(rest[i] == ks[i + 1] && ks[i + 1] != ks[0]);
            }
            lemma_data_map_work_values(bound, fs, keys.remove(k), rest, children.drop_first());
        }
    }

    pub proof fn lemma_data_work_array(cs: Seq<Data>)
        ensures data_work(Data::Array(cs)) == 1 + data_list_work(cs),
    {
        let bound = Data::Array(cs);
        let field: Seq<Data> = get_variant_field(bound, "Array", "0");
        assert(is_smaller_than(field, bound));
        assert forall|i: int| 0 <= i < cs.len() implies is_smaller_than(cs[i], bound) by {
            assert(is_smaller_than(cs[i], cs));
        }
        lemma_data_seq_work(bound, cs);
    }

    pub proof fn lemma_data_object_smaller(fs: Map<Data, Data>)
        ensures forall|key: Data| fs.dom().contains(key) ==> is_smaller_than(fs[key], Data::Object(fs)),
    {
        let bound = Data::Object(fs);
        let field: Map<Data, Data> = get_variant_field(bound, "Object", "0");
        assert(is_smaller_than(field, bound));
        assert forall|key: Data| fs.dom().contains(key) implies is_smaller_than(fs[key], bound) by {
            vstd::map::axiom_map_index_decreases(fs, key);
            assert(is_smaller_than(fs[key], fs));
        }
    }

    pub proof fn lemma_data_work_object(fs: Map<Data, Data>, ks: Seq<Data>, children: Seq<Data>)
        requires ks.no_duplicates(), forall|i: int| 0 <= i < ks.len() ==> fs.dom().contains(ks[i]),
            children.len() == ks.len(), forall|i: int| 0 <= i < ks.len() ==> children[i] == fs[ks[i]],
        ensures data_list_work(children) < data_work(Data::Object(fs)),
    {
        lemma_data_object_smaller(fs);
        lemma_data_map_work_values(Data::Object(fs), fs, fs.dom(), ks, children);
    }

    pub proof fn lemma_tagged_payload_work(d: Data, tag: Seq<char>, payload: Data)
        requires language::tagged_payload(d, tag) == Some(payload),
        ensures data_work(d) == 2 + data_work(payload),
    {
        broadcast use vstd::set::group_set_lemmas;
        let fs = d->Object_0;
        let key = Data::String(tag);
        lemma_data_object_smaller(fs);
        lemma_data_map_work_remove(d, fs, fs.dom(), key);
        assert(fs.dom().remove(key) =~= Set::empty());
    }

    pub open spec fn pattern_task_work(task: PendingPatternWork) -> nat {
        match task { PendingPatternWork::Enter(d) => data_work(d), _ => 1 }
    }

    pub open spec fn pattern_compile_measure(work: Seq<PendingPatternWork>) -> nat
        decreases work.len(),
    {
        if work.len() == 0 { 0 } else { pattern_compile_measure(work.drop_last()) + pattern_task_work(work.last()) }
    }

    pub proof fn lemma_pattern_compile_measure_append(a: Seq<PendingPatternWork>, b: Seq<PendingPatternWork>)
        ensures pattern_compile_measure(a + b) == pattern_compile_measure(a) + pattern_compile_measure(b),
        decreases b.len(),
    {
        if b.len() > 0 {
            assert((a + b).drop_last() =~= a + b.drop_last());
            lemma_pattern_compile_measure_append(a, b.drop_last());
        } else {
            assert(a + b =~= a);
        }
    }

    pub proof fn lemma_pattern_jobs_measure(children: Seq<Data>)
        ensures pattern_compile_measure(pattern_jobs(children)) == data_list_work(children),
        decreases children.len(),
    {
        if children.len() > 0 {
            lemma_pattern_jobs_prepend(children);
            lemma_pattern_jobs_measure(children.drop_first());
            let rest = pattern_jobs(children.drop_first());
            assert(rest.push(PendingPatternWork::Enter(children[0])).drop_last() =~= rest);
        } else {
            assert(pattern_jobs(children) =~= Seq::empty());
        }
    }

    pub proof fn lemma_pattern_compile_measure_expand(pending: Seq<PendingPatternWork>, marker: PendingPatternWork, children: Seq<Data>)
        requires pattern_task_work(marker) == 1,
        ensures pattern_compile_measure(pending.push(marker) + pattern_jobs(children)) == pattern_compile_measure(pending) + 1 + data_list_work(children),
    {
        assert(pending.push(marker).drop_last() =~= pending);
        lemma_pattern_compile_measure_append(pending.push(marker), pattern_jobs(children));
        lemma_pattern_jobs_measure(children);
    }

    pub(super) proof fn lemma_pattern_compile_measure_step(task: PendingPatternWork, before: model::Symbols, after: model::Symbols,
        inputs: Seq<usize>, results: Seq<usize>, pending: Seq<PendingPatternWork>, work: Seq<PendingPatternWork>, output: Option<PatternNode>)
        requires pattern_compile_step_effect(task, before, after, inputs, results, pending, work, output),
        ensures pattern_compile_measure(work) < pattern_compile_measure(pending.push(task)),
    {
        assert(pending.push(task).drop_last() =~= pending);
        if let PendingPatternWork::Enter(data) = task {
            if output is None {
                if exists|children: Seq<Data>| language::tagged_payload(data, "array"@) == Some(Data::Array(children))
                    && work == pending.push(PendingPatternWork::Array(children.len(), inputs.len())) + pattern_jobs(children) {
                    let children = choose|children: Seq<Data>| language::tagged_payload(data, "array"@) == Some(Data::Array(children))
                        && work == pending.push(PendingPatternWork::Array(children.len(), inputs.len())) + pattern_jobs(children);
                    lemma_tagged_payload_work(data, "array"@, Data::Array(children));
                    lemma_data_work_array(children);
                    lemma_pattern_compile_measure_expand(pending, PendingPatternWork::Array(children.len(), inputs.len()), children);
                } else {
                    let (fields, keys, children) = choose|fields: Map<Data, Data>, keys: Seq<Data>, children: Seq<Data>|
                        language::tagged_payload(data, "object"@) == Some(Data::Object(fields))
                        && keys.no_duplicates() && keys.to_set() == fields.dom() && children.len() == keys.len()
                        && (forall|i: int| 0 <= i < keys.len() ==> children[i] == fields[keys[i]])
                        && work == pending.push(PendingPatternWork::Object(keys, inputs.len())) + pattern_jobs(children);
                    assert forall|i: int| 0 <= i < keys.len() implies fields.dom().contains(keys[i]) by {
                        assert(keys.to_set().contains(keys[i]));
                    }
                    lemma_tagged_payload_work(data, "object"@, Data::Object(fields));
                    lemma_data_work_object(fields, keys, children);
                    lemma_pattern_compile_measure_expand(pending, PendingPatternWork::Object(keys, inputs.len()), children);
                }
            }
        }
    }

    pub(super) open spec fn pattern_array_ids(children: Seq<usize>) -> Seq<nat> {
        children.map_values(|child: usize| child as nat)
    }

    pub(super) open spec fn pattern_object_ids(fields: Seq<(Value, usize)>) -> Seq<nat> {
        fields.map_values(|field: (Value, usize)| field.1 as nat)
    }

    pub(super) open spec fn pattern_work_ids(work: Seq<(usize, &Value)>) -> Seq<nat> {
        work.map_values(|task: (usize, &Value)| task.0 as nat)
    }

    /// Size of the compiled-pattern subtree at `id`; children always precede their parent.
    pub(super) open spec fn pattern_node_work(nodes: Seq<PatternNode>, id: nat) -> nat
        decreases id, 1nat, 0nat,
    {
        if id >= nodes.len() { 0 } else {
            match nodes[id as int] {
                PatternNode::Array(children) => 1 + pattern_children_work(nodes, pattern_array_ids(children@), id),
                PatternNode::Object(fields) => 1 + pattern_children_work(nodes, pattern_object_ids(fields@), id),
                _ => 1,
            }
        }
    }

    pub(super) open spec fn pattern_children_work(nodes: Seq<PatternNode>, children: Seq<nat>, bound: nat) -> nat
        decreases bound, 0nat, children.len(),
    {
        if children.len() == 0 { 0 } else {
            pattern_children_work(nodes, children.drop_last(), bound)
                + if children.last() < bound { pattern_node_work(nodes, children.last()) } else { 0 }
        }
    }

    pub(super) open spec fn pattern_match_work(nodes: Seq<PatternNode>, work: Seq<(usize, &Value)>) -> nat {
        pattern_children_work(nodes, pattern_work_ids(work), nodes.len())
    }

    pub(super) proof fn lemma_pattern_children_work_append(nodes: Seq<PatternNode>, a: Seq<nat>, b: Seq<nat>, bound: nat)
        ensures pattern_children_work(nodes, a + b, bound) == pattern_children_work(nodes, a, bound) + pattern_children_work(nodes, b, bound),
        decreases b.len(),
    {
        if b.len() > 0 {
            assert((a + b).drop_last() =~= a + b.drop_last());
            lemma_pattern_children_work_append(nodes, a, b.drop_last(), bound);
        } else {
            assert(a + b =~= a);
        }
    }

    pub(super) proof fn lemma_pattern_children_work_bound(nodes: Seq<PatternNode>, children: Seq<nat>, b1: nat, b2: nat)
        requires forall|i: int| 0 <= i < children.len() ==> children[i] < b1 && children[i] < b2,
        ensures pattern_children_work(nodes, children, b1) == pattern_children_work(nodes, children, b2),
        decreases children.len(),
    {
        if children.len() > 0 {
            assert forall|i: int| 0 <= i < children.drop_last().len() implies children.drop_last()[i] < b1 && children.drop_last()[i] < b2 by {
                assert(children.drop_last()[i] == children[i]);
            }
            lemma_pattern_children_work_bound(nodes, children.drop_last(), b1, b2);
        }
    }

    pub(super) proof fn lemma_pattern_match_work_push(nodes: Seq<PatternNode>, work: Seq<(usize, &Value)>, task: (usize, &Value))
        requires task.0 < nodes.len(),
        ensures pattern_match_work(nodes, work.push(task)) == pattern_match_work(nodes, work) + pattern_node_work(nodes, task.0 as nat),
            pattern_node_work(nodes, task.0 as nat) >= 1,
    {
        let ids = pattern_work_ids(work);
        assert(pattern_work_ids(work.push(task)) =~= ids.push(task.0 as nat));
        assert(ids.push(task.0 as nat).drop_last() =~= ids);
    }

    /// A matcher step replaces a node by exactly its children.
    pub(super) proof fn lemma_pattern_match_work_expand(nodes: Seq<PatternNode>, initial: Seq<(usize, &Value)>, task: (usize, &Value),
        after: Seq<(usize, &Value)>, children: Seq<nat>)
        requires task.0 < nodes.len(),
            pattern_node_work(nodes, task.0 as nat) == 1 + pattern_children_work(nodes, children, task.0 as nat),
            forall|i: int| 0 <= i < children.len() ==> children[i] < task.0,
            after.len() == initial.len() + children.len(), after.take(initial.len() as int) == initial,
            forall|i: int| 0 <= i < children.len() ==> after[initial.len() + i].0 as nat == children[i],
        ensures pattern_match_work(nodes, after) < pattern_match_work(nodes, initial.push(task)),
    {
        let ids = pattern_work_ids(initial);
        assert(pattern_work_ids(after) =~= ids + children) by {
            assert forall|i: int| 0 <= i < initial.len() implies after[i] == initial[i] by {
                assert(after.take(initial.len() as int)[i] == after[i]);
            }
        }
        lemma_pattern_match_work_push(nodes, initial, task);
        lemma_pattern_children_work_append(nodes, ids, children, nodes.len());
        lemma_pattern_children_work_bound(nodes, children, task.0 as nat, nodes.len());
    }

    pub open spec fn source_task_work(task: PendingSourceWork) -> nat {
        match task {
            PendingSourceWork::Regex(d) => data_work(d),
            PendingSourceWork::Test(d) => data_work(d),
            _ => 1,
        }
    }

    pub open spec fn source_work_measure(work: Seq<PendingSourceWork>) -> nat
        decreases work.len(),
    {
        if work.len() == 0 { 0 } else { source_work_measure(work.drop_last()) + source_task_work(work.last()) }
    }

    pub proof fn lemma_source_work_measure_push(work: Seq<PendingSourceWork>, task: PendingSourceWork)
        ensures source_work_measure(work.push(task)) == source_work_measure(work) + source_task_work(task),
            source_task_work(task) >= 1,
    {
        assert(work.push(task).drop_last() =~= work);
    }

    pub proof fn lemma_source_work_measure_append(a: Seq<PendingSourceWork>, b: Seq<PendingSourceWork>)
        ensures source_work_measure(a + b) == source_work_measure(a) + source_work_measure(b),
        decreases b.len(),
    {
        if b.len() > 0 {
            assert((a + b).drop_last() =~= a + b.drop_last());
            lemma_source_work_measure_append(a, b.drop_last());
        } else {
            assert(a + b =~= a);
        }
    }

    pub proof fn lemma_source_jobs_measure(children: Seq<Data>, regex: bool)
        ensures source_work_measure(source_jobs(children, regex)) == data_list_work(children),
        decreases children.len(),
    {
        if children.len() > 0 {
            lemma_source_jobs_prepend(children, regex);
            lemma_source_jobs_measure(children.drop_first(), regex);
            let task = if regex { PendingSourceWork::Regex(children[0]) } else { PendingSourceWork::Test(children[0]) };
            lemma_source_work_measure_push(source_jobs(children.drop_first(), regex), task);
        } else {
            assert(source_jobs(children, regex) =~= Seq::empty());
        }
    }

    /// A decoder step replaces a tagged source by a reduction marker and the payload's children.
    pub(super) proof fn lemma_source_measure_expand(pending: Seq<PendingSourceWork>, incoming: PendingSourceWork, d: Data, tag: Seq<char>,
        payload: Data, marker: PendingSourceWork, children: Seq<Data>, regex: bool)
        requires source_task_work(incoming) == data_work(d), language::tagged_payload(d, tag) == Some(payload),
            source_task_work(marker) == 1, children == seq![payload] || payload == Data::Array(children),
        ensures source_work_measure(pending.push(marker) + source_jobs(children, regex)) < source_work_measure(pending.push(incoming)),
    {
        lemma_tagged_payload_work(d, tag, payload);
        lemma_source_work_measure_push(pending, incoming);
        lemma_source_work_measure_push(pending, marker);
        lemma_source_work_measure_append(pending.push(marker), source_jobs(children, regex));
        lemma_source_jobs_measure(children, regex);
        if payload == Data::Array(children) {
            lemma_data_work_array(children);
        } else {
            assert(children[0] == payload);
            assert(children.drop_first() =~= Seq::<Data>::empty());
            assert(data_list_work(children.drop_first()) == 0);
            assert(data_list_work(children) == data_work(payload));
        }
    }

        }
}
