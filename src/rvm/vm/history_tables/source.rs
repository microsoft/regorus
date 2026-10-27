// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

#[cfg(verus_keep_ghost)]
use super::kernel::verify as model;
use super::{
    error::HistoryError,
    graph::{allocation, ArenaStorage, CanonicalStore, ObservationWorld, RuntimeKernel},
    kernel::*,
    progress::CompiledPair,
};
#[cfg(verus_keep_ghost)]
use crate::verify::history_specs as language;
use crate::{
    languages::history_table::{Event, HistoryStore},
    rvm::program::{
        HistoryField, HistoryHeadSource, HistoryPairSource, HistoryRegexSource, HistoryTermSource,
        HistoryTestSource,
    },
    utils::limits::ExecutionTimer,
    value::{Array, Object},
    Value,
};
use alloc::{
    format,
    string::{String, ToString as _},
    vec::Vec,
};
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use super::normalize::verify as norm;
#[cfg(verus_keep_ghost)]
use crate::verify::history_assumptions::{KernelStoreSpec, StorageSpec};
#[cfg(verus_keep_ghost)]
use verify::*;
impl HistoryPairSource {
    fn tagged<'a>(value: &'a Value, path: &str) -> KernelResult<(&'a str, &'a Value)> {
        let Value::Object(object) = value else {
            return Err(HistoryError::invalid_policy(
                path,
                "expected a tagged object",
            ));
        };
        if object.len() != 1 {
            return Err(HistoryError::invalid_policy(
                path,
                "expected exactly one tag",
            ));
        }
        let Some((Value::String(tag), payload)) = object.iter_sorted().next() else {
            return Err(HistoryError::invalid_policy(path, "tag must be a string"));
        };
        Ok((tag, payload))
    }

    fn array<'a>(value: &'a Value, path: &str) -> KernelResult<&'a Array> {
        match value {
            Value::Array(values) => Ok(values),
            _ => Err(HistoryError::invalid_policy(path, "expected an array")),
        }
    }

    fn marker(value: &Value, path: &str) -> KernelResult<()> {
        if matches!(value, Value::Bool(true)) {
            Ok(())
        } else {
            Err(HistoryError::invalid_policy(path, "marker must be true"))
        }
    }

    fn member<'a>(object: &'a Object, key: &str, path: &str) -> KernelResult<&'a Value> {
        object
            .iter_sorted()
            .find_map(|(candidate, value)| {
                matches!(candidate, Value::String(name) if &**name == key).then_some(value)
            })
            .ok_or_else(|| HistoryError::invalid_policy(path, "missing required member"))
    }

    fn string<'a>(value: &'a Value, path: &str) -> KernelResult<&'a str> {
        match value {
            Value::String(value) => Ok(value),
            _ => Err(HistoryError::invalid_policy(
                path,
                "identity constant must be a string",
            )),
        }
    }

    fn push<T>(values: &mut Vec<T>, value: T) -> KernelResult<()> {
        allocation(values.try_reserve(1))?;
        values.push(value);
        Ok(())
    }

    fn node<T>(values: &mut Vec<T>, value: T) -> KernelResult<u32> {
        let id = u32::try_from(values.len()).map_err(|_| HistoryError::GraphLimit {
            limit: MAX_GRAPH_BYTES,
        })?;
        HistoryPairSource::push(values, value)?;
        Ok(id)
    }

    #[allow(
        clippy::shadow_unrelated,
        reason = "Nested parser tags retain the existing pattern-matching structure"
    )]
    #[allow(
        clippy::semicolon_if_nothing_returned,
        reason = "Preserve the existing match-arm mutation style"
    )]
    fn parse_head<'a>(
        request: &'a Value,
        timer: &mut ExecutionTimer,
        world: &mut ObservationWorld,
    ) -> KernelResult<([HistoryHeadSource; 3], [Option<&'a str>; 3])> {
        let mut head = [
            HistoryHeadSource::Any,
            HistoryHeadSource::Any,
            HistoryHeadSource::Any,
        ];
        let mut names = [None; 3];
        let (tag, payload) = HistoryPairSource::tagged(request, "$.request")?;
        if tag == "any" {
            HistoryPairSource::marker(payload, "$.request")?;
            return Ok((head, names));
        }
        if tag != "object" {
            return Err(HistoryError::invalid_policy(
                "$.request",
                "request must be any or object",
            ));
        }
        let Value::Object(fields) = payload else {
            return Err(HistoryError::invalid_policy(
                "$.request.object",
                "expected an object",
            ));
        };
        for (key, value) in fields.iter_sorted() {
            world.checkpoint(timer)?;
            let coordinate = HistoryField::parse(
                HistoryPairSource::string(key, "$.request.object")?,
                "$.request.object",
            )?;
            let index = coordinate.index();
            let (tag, payload) = HistoryPairSource::tagged(value, "$.request.object")?;
            let slot = head
                .get_mut(index)
                .ok_or_else(|| HistoryError::invariant("invalid head field"))?;
            match tag {
                "any" => HistoryPairSource::marker(payload, "$.request.object")?,
                "value" => {
                    *slot = HistoryHeadSource::Constant(
                        HistoryPairSource::string(payload, "$.request.object")?.to_string(),
                    )
                }
                "var" => {
                    let name = HistoryPairSource::string(payload, "$.request.object")?;
                    if name.is_empty() {
                        return Err(HistoryError::invalid_policy(
                            "$.request.object",
                            "variable name must not be empty",
                        ));
                    }
                    if names.iter().flatten().any(|other| *other == name) {
                        return Err(HistoryError::invalid_policy(
                            "$.request.object",
                            "variable name reused across domains",
                        ));
                    }
                    *names
                        .get_mut(index)
                        .ok_or_else(|| HistoryError::invariant("invalid binding field"))? =
                        Some(name);
                    *slot = HistoryHeadSource::Bind;
                }
                _ => {
                    return Err(HistoryError::invalid_policy(
                        "$.request.object",
                        "field must be any, value or var",
                    ))
                }
            }
        }
        Ok((head, names))
    }
}

impl HistoryField {
    fn parse(name: &str, path: &str) -> KernelResult<Self> {
        match name {
            "principal" => Ok(HistoryField::Principal),
            "action" => Ok(HistoryField::Action),
            "resource" => Ok(HistoryField::Resource),
            _ => Err(HistoryError::invalid_policy(
                path,
                "expected principal, action or resource",
            )),
        }
    }
}

impl HistoryTermSource {
    fn parse(
        value: &Value,
        coordinate: HistoryField,
        names: &[Option<&str>; 3],
        at: &str,
    ) -> KernelResult<Self> {
        let (tag, payload) = HistoryPairSource::tagged(value, at)?;
        match tag {
            "value" => Ok(HistoryTermSource::Constant(
                HistoryPairSource::string(payload, at)?.to_string(),
            )),
            "var" => {
                let name = HistoryPairSource::string(payload, at)?;
                if name.is_empty() {
                    return Err(HistoryError::invalid_policy(
                        at,
                        "variable name must not be empty",
                    ));
                }
                let declared = names
                    .iter()
                    .position(|candidate| *candidate == Some(name))
                    .ok_or_else(|| HistoryError::UnboundVariable {
                        name: name.to_string(),
                    })?;
                if declared != coordinate.index() {
                    return Err(HistoryError::invalid_policy(
                        at,
                        "variable belongs to another identity domain",
                    ));
                }
                Ok(HistoryTermSource::Variable(coordinate))
            }
            _ => Err(HistoryError::invalid_policy(at, "unknown term tag")),
        }
    }
}

enum SourceWork<'a> {
    Regex(&'a Value, String),
    Test(&'a Value, String),
    RegexMany { tag: &'a str, start: usize },
    RegexOne(&'a str),
    TestMany { and: bool, start: usize },
    LiftTest,
}

impl HistoryPairSource {
    /// Decode cold JSON into flat postorder tables, without constructing a graph.
    pub(crate) fn parse(
        request: &Value,
        history: &Value,
        timer: &mut ExecutionTimer,
        world: &mut ObservationWorld,
    ) -> KernelResult<Self> {
        world.checkpoint(timer)?;
        let (head, names) = HistoryPairSource::parse_head(request, timer, world)?;
        let mut source = HistoryPairSource {
            head,
            tests: Vec::new(),
            regexes: Vec::new(),
            root: 0,
        };
        let mut work = Vec::new();
        let mut regexes = Vec::new();
        let mut tests = Vec::new();
        HistoryPairSource::push(
            &mut work,
            SourceWork::Regex(history, "$.history".to_string()),
        )?;
        // Finish frames run after their children, producing flat postorder tables.
        while let Some(task) = work.pop() {
            world.checkpoint(timer)?;
            match task {
                SourceWork::Regex(value, at) => {
                    let (tag, payload) = HistoryPairSource::tagged(value, &at)?;
                    match tag {
                        "empty" | "all" | "epsilon" => {
                            HistoryPairSource::marker(payload, &at)?;
                            let leaf = match tag {
                                "empty" => HistoryRegexSource::Empty,
                                "all" => HistoryRegexSource::All,
                                _ => HistoryRegexSource::Epsilon,
                            };
                            HistoryPairSource::push(
                                &mut regexes,
                                HistoryPairSource::node(&mut source.regexes, leaf)?,
                            )?;
                        }
                        "test" => {
                            HistoryPairSource::push(&mut work, SourceWork::LiftTest)?;
                            HistoryPairSource::push(
                                &mut work,
                                SourceWork::Test(payload, format!("{at}.test")),
                            )?;
                        }
                        "star" | "not" => {
                            HistoryPairSource::push(&mut work, SourceWork::RegexOne(tag))?;
                            HistoryPairSource::push(
                                &mut work,
                                SourceWork::Regex(payload, format!("{at}.{tag}")),
                            )?;
                        }
                        "concat" | "union" | "intersect" => {
                            let children = HistoryPairSource::array(payload, &at)?;
                            HistoryPairSource::push(
                                &mut work,
                                SourceWork::RegexMany {
                                    tag,
                                    start: regexes.len(),
                                },
                            )?;
                            for (index, child) in children.iter().enumerate().rev() {
                                world.checkpoint(timer)?;
                                HistoryPairSource::push(
                                    &mut work,
                                    SourceWork::Regex(child, format!("{at}.{tag}[{index}]")),
                                )?;
                            }
                        }
                        _ => {
                            return Err(HistoryError::invalid_policy(
                                &at,
                                "unknown history regex tag",
                            ))
                        }
                    }
                }
                SourceWork::Test(value, at) => {
                    if let Value::Bool(value) = value {
                        HistoryPairSource::push(
                            &mut tests,
                            HistoryPairSource::node(
                                &mut source.tests,
                                HistoryTestSource::Bool(*value),
                            )?,
                        )?;
                        continue;
                    }
                    let (tag, payload) = HistoryPairSource::tagged(value, &at)?;
                    match tag {
                        "and" | "or" => {
                            let children = HistoryPairSource::array(payload, &at)?;
                            HistoryPairSource::push(
                                &mut work,
                                SourceWork::TestMany {
                                    and: tag == "and",
                                    start: tests.len(),
                                },
                            )?;
                            for (index, child) in children.iter().enumerate().rev() {
                                world.checkpoint(timer)?;
                                HistoryPairSource::push(
                                    &mut work,
                                    SourceWork::Test(child, format!("{at}.{tag}[{index}]")),
                                )?;
                            }
                        }
                        "eq" | "neq" => {
                            let Value::Object(fields) = payload else {
                                return Err(HistoryError::invalid_policy(
                                    &at,
                                    "comparison payload must be an object",
                                ));
                            };
                            if fields.len() != 2 {
                                return Err(HistoryError::invalid_policy(
                                    &at,
                                    "comparison requires exactly path and term",
                                ));
                            }
                            let path = HistoryPairSource::array(
                                HistoryPairSource::member(fields, "path", &at)?,
                                &at,
                            )?;
                            if path.len() != 1 {
                                return Err(HistoryError::invalid_policy(
                                    &at,
                                    "comparison path must contain exactly one typed field",
                                ));
                            }
                            let name = path.first().ok_or_else(|| {
                                HistoryError::invalid_policy(&at, "missing comparison path")
                            })?;
                            let coordinate =
                                HistoryField::parse(HistoryPairSource::string(name, &at)?, &at)?;
                            let term = HistoryTermSource::parse(
                                HistoryPairSource::member(fields, "term", &at)?,
                                coordinate,
                                &names,
                                &at,
                            )?;
                            HistoryPairSource::push(
                                &mut tests,
                                HistoryPairSource::node(
                                    &mut source.tests,
                                    HistoryTestSource::Atom {
                                        field: coordinate,
                                        term,
                                        positive: tag == "eq",
                                    },
                                )?,
                            )?;
                        }
                        _ => return Err(HistoryError::invalid_policy(&at, "unknown test tag")),
                    }
                }
                SourceWork::RegexMany { tag, start } => {
                    let children = HistoryPairSource::take_children(&mut regexes, start)?;
                    let value = match tag {
                        "concat" => HistoryRegexSource::Concat(children),
                        "union" => HistoryRegexSource::Union(children),
                        _ => HistoryRegexSource::Intersect(children),
                    };
                    HistoryPairSource::push(
                        &mut regexes,
                        HistoryPairSource::node(&mut source.regexes, value)?,
                    )?;
                }
                SourceWork::RegexOne(tag) => {
                    let child = regexes
                        .pop()
                        .ok_or_else(|| HistoryError::invariant("missing regex operand"))?;
                    let value = if tag == "star" {
                        HistoryRegexSource::Star(child)
                    } else {
                        HistoryRegexSource::Complement(child)
                    };
                    HistoryPairSource::push(
                        &mut regexes,
                        HistoryPairSource::node(&mut source.regexes, value)?,
                    )?;
                }
                SourceWork::TestMany { and, start } => {
                    let children = HistoryPairSource::take_children(&mut tests, start)?;
                    let value = if and {
                        HistoryTestSource::And(children)
                    } else {
                        HistoryTestSource::Or(children)
                    };
                    HistoryPairSource::push(
                        &mut tests,
                        HistoryPairSource::node(&mut source.tests, value)?,
                    )?;
                }
                SourceWork::LiftTest => {
                    let child = tests
                        .pop()
                        .ok_or_else(|| HistoryError::invariant("missing test operand"))?;
                    HistoryPairSource::push(
                        &mut regexes,
                        HistoryPairSource::node(
                            &mut source.regexes,
                            HistoryRegexSource::Test(child),
                        )?,
                    )?;
                }
            }
        }
        if regexes.len() != 1 || !tests.is_empty() {
            return Err(HistoryError::invariant("invalid source result stack"));
        }
        source.root = regexes
            .pop()
            .ok_or_else(|| HistoryError::invariant("missing source root"))?;
        world.checkpoint(timer)?;
        Ok(source)
    }

    fn take_children(values: &mut Vec<u32>, start: usize) -> KernelResult<Vec<u32>> {
        let slice = values
            .get(start..)
            .ok_or_else(|| HistoryError::invariant("invalid source child stack"))?;
        let children = Self::copy_ids(slice)?;
        values.truncate(start);
        Ok(children)
    }

    fn copy_ids(ids: &[u32]) -> KernelResult<Vec<u32>> {
        let mut copied = Vec::new();
        allocation(copied.try_reserve_exact(ids.len()))?;
        copied.extend_from_slice(ids);
        Ok(copied)
    }
}

#[verus_verify]
#[verus_verify(external_derive)]
#[derive(Copy, Clone, Debug)]
pub(crate) enum NumericHead {
    Any,
    Constant(u64),
    Bind,
}

#[verus_verify]
#[verus_verify(external_derive)]
#[derive(Clone, Debug)]
pub(crate) enum NumericTest {
    Bool(bool),
    Atom {
        field: HistoryField,
        term: Term,
        positive: bool,
    },
    And(Vec<u32>),
    Or(Vec<u32>),
}

#[verus_verify]
#[verus_verify(external_derive)]
#[derive(Clone, Debug)]
pub(crate) struct NumericPair {
    pub(crate) head: [NumericHead; 3],
    pub(crate) tests: Vec<NumericTest>,
    pub(crate) regexes: Vec<HistoryRegexSource>,
    pub(crate) root: u32,
}

impl NumericHead {
    #[allow(
        clippy::missing_const_for_fn,
        reason = "Keep the existing operation and its Verus contract unchanged"
    )]
    #[verus_verify]
    #[verus_spec(result => ensures match result {
        Some(binding) => language::head_field_match(self@, value as nat, binding as nat),
        None => !exists|binding: nat| language::head_field_match(self@, value as nat, binding),
    })]
    fn bind(self, value: u64) -> Option<u64> {
        match self {
            NumericHead::Any => Some(0),
            NumericHead::Constant(expected) if value == expected => Some(0),
            NumericHead::Constant(_) => None,
            NumericHead::Bind => Some(value),
        }
    }
}

impl HistoryField {
    fn intern(self, store: &HistoryStore, path: &str) -> KernelResult<u64> {
        match self {
            HistoryField::Principal => Ok(store.intern_principal(path)?.get()),
            HistoryField::Action => Ok(store.intern_action(path)?.get()),
            HistoryField::Resource => Ok(store.intern_resource(path)?.get()),
        }
    }
}

// The impl annotation marks associated functions; cold lowering remains outside verification.
#[verus_verify]
impl NumericPair {
    #[verus_verify]
    #[verus_spec(result => ensures match result {
            Some(bindings) => language::head_match(head_view(*self), request@, bindings@),
            None => !exists|theta: language::Subst| language::head_match(head_view(*self), request@, theta),
        })]
    pub(crate) fn bindings(&self, request: &Event) -> Option<Bindings> {
        let p = self.head[0].bind(request.principal.get())?;
        let a = self.head[1].bind(request.action.get())?;
        let r = self.head[2].bind(request.resource.get())?;
        Some(Bindings([p, a, r]))
    }

    #[allow(
        clippy::shadow_unrelated,
        reason = "Term fields retain the existing source-to-kernel matching structure"
    )]
    #[verus_verify(external)]
    pub(crate) fn lower(source: &HistoryPairSource, store: &HistoryStore) -> KernelResult<Self> {
        // Direct and deserialized programs must validate before allocating identities.
        source
            .validate()
            .map_err(|_| HistoryError::invalid_policy("$", "invalid portable history source"))?;
        let mut head = [NumericHead::Any; 3];
        for ((value, numeric), field) in source.head.iter().zip(head.iter_mut()).zip([
            HistoryField::Principal,
            HistoryField::Action,
            HistoryField::Resource,
        ]) {
            *numeric = match value {
                HistoryHeadSource::Any => NumericHead::Any,
                HistoryHeadSource::Bind => NumericHead::Bind,
                HistoryHeadSource::Constant(path) => {
                    NumericHead::Constant(field.intern(store, path)?)
                }
            };
        }
        let mut tests = Vec::new();
        allocation(tests.try_reserve_exact(source.tests.len()))?;
        for test in &source.tests {
            tests.push(match test {
                HistoryTestSource::Bool(value) => NumericTest::Bool(*value),
                HistoryTestSource::Atom {
                    field,
                    term,
                    positive,
                } => NumericTest::Atom {
                    field: *field,
                    term: match term {
                        HistoryTermSource::Constant(path) => {
                            Term::Constant(field.intern(store, path)?)
                        }
                        HistoryTermSource::Variable(field) => Term::Variable(*field),
                    },
                    positive: *positive,
                },
                HistoryTestSource::And(children) => {
                    NumericTest::And(HistoryPairSource::copy_ids(children)?)
                }
                HistoryTestSource::Or(children) => {
                    NumericTest::Or(HistoryPairSource::copy_ids(children)?)
                }
            });
        }
        let mut regexes = Vec::new();
        allocation(regexes.try_reserve_exact(source.regexes.len()))?;
        for regex in &source.regexes {
            regexes.push(match regex {
                HistoryRegexSource::Concat(children) => {
                    HistoryRegexSource::Concat(HistoryPairSource::copy_ids(children)?)
                }
                HistoryRegexSource::Union(children) => {
                    HistoryRegexSource::Union(HistoryPairSource::copy_ids(children)?)
                }
                HistoryRegexSource::Intersect(children) => {
                    HistoryRegexSource::Intersect(HistoryPairSource::copy_ids(children)?)
                }
                other => other.clone(),
            });
        }
        Ok(NumericPair {
            head,
            tests,
            regexes,
            root: source.root,
        })
    }

    #[allow(
        clippy::option_if_let_else,
        reason = "Explicit matches preserve the Verus proof structure"
    )]
    #[verus_verify]
    #[verus_spec(result => ensures result matches Ok(value)
        ==> (id as nat) < values@.len() && value == values@[id as int])]
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
    #[verus_spec(result => ensures result matches Ok(found) ==> {
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
    /// Build a fresh graph from immutable numeric source, including after exhaustion.
    #[allow(
        clippy::shadow_unrelated,
        reason = "Separate lowering loops retain their proof-local index bindings"
    )]
    #[verus_verify]
    #[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
    #[cfg_attr(verus_keep_ghost, verifier::rlimit(30))]
    #[verus_spec(result => ensures result matches Ok(pair) ==> {
        super::progress::verify::pair_wf(pair)
        && forall|theta: language::Subst, word: Seq<language::EventView>| language::event_wf(theta)
            ==> model::regex_lang(pair.store.graph(), theta, pair.root@, word)
                == source_regex(*self, self.root as nat, theta, word)
    })]
    pub(crate) fn compile(
        &self,
        timer: &mut ExecutionTimer,
        world: &mut ObservationWorld,
    ) -> KernelResult<CompiledPair> {
        world.checkpoint(timer)?;
        let mut store = CanonicalStore::new(ArenaStorage::new()?, world)?;
        let mut tests = Vec::new();
        let mut regexes = Vec::new();
        allocation(world.try_reserve_vec_exact(&mut tests, self.tests.len()))?;
        allocation(world.try_reserve_vec_exact(&mut regexes, self.regexes.len()))?;
        {
            let mut kernel = RuntimeKernel {
                store: &mut store,
                timer,
                world,
            };
            proof_decl! { let ghost restoration = kernel.restoration(); }
            let mut index = 0;
            #[cfg_attr(verus_keep_ghost, verus_spec(
                invariant index <= self.tests@.len(), tests@.len() == index,
                    kernel.valid_store(), model::graph_wf(kernel.graph()),
                    kernel.restoration() == restoration,
                    test_maps(kernel.graph(), *self, tests@),
                    regex_maps(kernel.graph(), *self, regexes@), regexes@.len() == 0,
                decreases self.tests@.len() - index,
            ))]
            while index < self.tests.len() {
                kernel.checkpoint()?;
                let test = match self.tests.get(index) {
                    Some(test) => test,
                    None => return Err(HistoryError::invariant("missing numeric test node")),
                };
                proof_decl! { let ghost before = kernel.graph(); }
                proof_decl! { let ghost mut selected_ids = Seq::<TestId>::empty(); }
                proof! { assert(*test == self.tests@[index as int]); }
                let id = match test {
                    NumericTest::Bool(value) => {
                        if *value {
                            kernel.constants().test_true
                        } else {
                            kernel.constants().test_false
                        }
                    }
                    NumericTest::Atom {
                        field,
                        term,
                        positive,
                    } => kernel.intern_test(TestView::Atom {
                        primitive: Primitive::Eq {
                            field: *field,
                            term: *term,
                        },
                        positive: *positive,
                    })?,
                    NumericTest::And(children) => {
                        let selected = Self::references(&tests, children, kernel.world)?;
                        proof! {
                            selected_ids = selected@;
                            selected_tests_valid(kernel.graph(), *self, tests@, children@, selected@);
                        }
                        TestId::connective(&mut kernel, &selected, true)?
                    }
                    NumericTest::Or(children) => {
                        let selected = Self::references(&tests, children, kernel.world)?;
                        proof! {
                            selected_ids = selected@;
                            selected_tests_valid(kernel.graph(), *self, tests@, children@, selected@);
                        }
                        TestId::connective(&mut kernel, &selected, false)?
                    }
                };
                proof! {
                    maps_extend(before, kernel.graph(), *self, tests@, regexes@);
                    assert(test_correct(kernel.graph(), *self, index as nat, id)) by {
                        reveal_with_fuel(source_test, 1);
                        model::lemma_graph_wf_elim(kernel.graph());
                        assert forall|theta: language::Subst, event: language::EventView|
                            language::event_wf(theta) implies
                            norm::test_truth(kernel.graph(), theta, id@, event)
                                == source_test(*self, index as nat, theta, event) by {
                            match test {
                                NumericTest::Bool(_) | NumericTest::Atom { .. } => {
                                    norm::test_lemma_truth(kernel.graph(), theta, id@, event);
                                }
                                NumericTest::And(children) => {
                                    test_connective_transfer(kernel.graph(), *self, tests@,
                                        children@, selected_ids, theta, event, true);
                                }
                                NumericTest::Or(children) => {
                                    test_connective_transfer(kernel.graph(), *self, tests@,
                                        children@, selected_ids, theta, event, false);
                                }
                            }
                        }
                    }
                    test_push(kernel.graph(), *self, tests@, id);
                }
                tests.push(id);
                index = index.saturating_add(1);
            }
            let mut index = 0;
            #[cfg_attr(verus_keep_ghost, verus_spec(
                invariant index <= self.regexes@.len(), regexes@.len() == index,
                    kernel.valid_store(), model::graph_wf(kernel.graph()),
                    kernel.restoration() == restoration,
                    test_maps(kernel.graph(), *self, tests@), tests@.len() == self.tests@.len(),
                    regex_maps(kernel.graph(), *self, regexes@),
                decreases self.regexes@.len() - index,
            ))]
            while index < self.regexes.len() {
                kernel.checkpoint()?;
                let regex = match self.regexes.get(index) {
                    Some(regex) => regex,
                    None => return Err(HistoryError::invariant("missing numeric regex node")),
                };
                proof_decl! { let ghost before = kernel.graph(); }
                proof_decl! { let ghost mut selected_ids = Seq::<RegexId>::empty(); }
                proof! { assert(*regex == self.regexes@[index as int]); }
                let id = match regex {
                    HistoryRegexSource::Empty => kernel.constants().empty,
                    HistoryRegexSource::All => kernel.constants().all,
                    HistoryRegexSource::Epsilon => kernel.constants().epsilon,
                    HistoryRegexSource::Test(test) => {
                        RegexId::from_test(&mut kernel, Self::lookup(&tests, *test)?)?
                    }
                    HistoryRegexSource::Concat(children) => {
                        let selected = Self::references(&regexes, children, kernel.world)?;
                        proof! {
                            selected_ids = selected@;
                            selected_regexes_valid(kernel.graph(), *self, regexes@, children@, selected@);
                        }
                        RegexId::concat(&mut kernel, &selected)?
                    }
                    HistoryRegexSource::Union(children) => {
                        let selected = Self::references(&regexes, children, kernel.world)?;
                        proof! {
                            selected_ids = selected@;
                            selected_regexes_valid(kernel.graph(), *self, regexes@, children@, selected@);
                        }
                        RegexId::set(&mut kernel, &selected, false)?
                    }
                    HistoryRegexSource::Intersect(children) => {
                        let selected = Self::references(&regexes, children, kernel.world)?;
                        proof! {
                            selected_ids = selected@;
                            selected_regexes_valid(kernel.graph(), *self, regexes@, children@, selected@);
                        }
                        RegexId::set(&mut kernel, &selected, true)?
                    }
                    HistoryRegexSource::Star(child) => {
                        Self::lookup(&regexes, *child)?.star(&mut kernel)?
                    }
                    HistoryRegexSource::Complement(child) => {
                        Self::lookup(&regexes, *child)?.not(&mut kernel)?
                    }
                };
                proof! {
                    maps_extend(before, kernel.graph(), *self, tests@, regexes@);
                    assert(regex_correct(kernel.graph(), *self, index as nat, id)) by {
                        reveal_with_fuel(source_regex, 1);
                        norm::regex_constants(kernel.graph());
                        assert forall|theta: language::Subst, word: Seq<language::EventView>|
                            language::event_wf(theta) implies
                            model::regex_lang(kernel.graph(), theta, id@, word)
                                == source_regex(*self, index as nat, theta, word) by {
                            match regex {
                                HistoryRegexSource::Test(test) => {
                                    assert((*test as nat) < tests@.len());
                                    assert(test_correct(kernel.graph(), *self, *test as nat,
                                        tests@[*test as int]));
                                    assert(model::regex_lang(kernel.graph(), theta, id@, word)
                                        == source_regex(*self, index as nat, theta, word));
                                }
                                HistoryRegexSource::Concat(children) => {
                                    assert(selected_ids =~= Seq::new(children@.len(),
                                        |i: int| regexes@[children@[i] as int]));
                                    regex_concat_transfer(kernel.graph(), *self, regexes@, children@,
                                        index as nat, theta, word);
                                    assert(model::regex_lang(kernel.graph(), theta, id@, word)
                                        == source_regex(*self, index as nat, theta, word));
                                }
                                HistoryRegexSource::Star(child) => {
                                    regex_star_transfer(kernel.graph(), *self, regexes@,
                                        *child as nat, theta, word);
                                    assert(model::regex_lang(kernel.graph(), theta, id@, word)
                                        == source_regex(*self, index as nat, theta, word));
                                }
                                HistoryRegexSource::Union(children) => {
                                    regex_set_transfer(kernel.graph(), *self, regexes@,
                                        children@, selected_ids, theta, word, false);
                                    assert(model::regex_lang(kernel.graph(), theta, id@, word)
                                        == source_regex(*self, index as nat, theta, word));
                                }
                                HistoryRegexSource::Intersect(children) => {
                                    regex_set_transfer(kernel.graph(), *self, regexes@,
                                        children@, selected_ids, theta, word, true);
                                    assert(model::regex_lang(kernel.graph(), theta, id@, word)
                                        == source_regex(*self, index as nat, theta, word));
                                }
                                HistoryRegexSource::Complement(child) => {
                                    assert((*child as nat) < regexes@.len());
                                    assert(regex_correct(kernel.graph(), *self, *child as nat,
                                        regexes@[*child as int]));
                                    assert(self.regexes@[index as int] == HistoryRegexSource::Complement(*child));
                                    assert(source_regex(*self, index as nat, theta, word)
                                        == ((*child as nat) < index && !source_regex(*self, *child as nat, theta, word)));
                                    assert(model::regex_lang(kernel.graph(), theta, id@, word)
                                        == !model::regex_lang(kernel.graph(), theta, regexes@[*child as int]@, word));
                                    assert(model::regex_lang(kernel.graph(), theta, id@, word)
                                        == source_regex(*self, index as nat, theta, word));
                                }
                                HistoryRegexSource::Empty | HistoryRegexSource::All | HistoryRegexSource::Epsilon => {
                                    assert(model::regex_lang(kernel.graph(), theta, id@, word)
                                        == source_regex(*self, index as nat, theta, word));
                                }
                            }
                        }
                    }
                    regex_push(kernel.graph(), *self, regexes@, id);
                }
                regexes.push(id);
                index = index.saturating_add(1);
            }
            proof! {
                assert(kernel.valid_store());
                assert(model::graph_wf(kernel.graph()));
                assert(regex_maps(kernel.graph(), *self, regexes@));
            }
        }
        proof! {
            assert(store.valid_store());
            assert(model::graph_wf(store.graph()));
            assert(regex_maps(store.graph(), *self, regexes@));
        }
        let root = Self::lookup(&regexes, self.root)?;
        world.checkpoint(timer)?;
        proof! {
            assert(model::graph_wf(store.graph()));
            assert(regex_correct(store.graph(), *self, self.root as nat, root));
        }
        Ok(CompiledPair::new(store, root))
    }
}

impl Primitive {
    /// The hot boundary performs only fixed-coordinate u64 equality and a checkpoint.
    // Every binding index addresses one of the three fixed coordinates.
    #[allow(
        clippy::indexing_slicing,
        reason = "Binding indices address the three fixed coordinates"
    )]
    #[allow(
        clippy::shadow_unrelated,
        reason = "Term fields mirror the matched Verus model variants"
    )]
    #[verus_verify]
    #[verus_spec(result => ensures result matches Ok(answer)
        ==> answer == model::primitive_holds(bindings@, self@, event@))]
    pub(crate) fn classify(
        self,
        event: &Event,
        bindings: &Bindings,
        timer: &mut ExecutionTimer,
        world: &mut ObservationWorld,
    ) -> KernelResult<bool> {
        world.checkpoint(timer)?;
        let Primitive::Eq { field, term } = self;
        let left = match field {
            HistoryField::Principal => event.principal.get(),
            HistoryField::Action => event.action.get(),
            HistoryField::Resource => event.resource.get(),
        };
        // Variables read the fixed request substitution, not another history-event coordinate.
        let right = match term {
            Term::Constant(value) => value,
            Term::Variable(field) => match field {
                HistoryField::Principal => bindings.0[0],
                HistoryField::Action => bindings.0[1],
                HistoryField::Resource => bindings.0[2],
            },
        };
        Ok(left == right)
    }
}

#[cfg(verus_keep_ghost)]
pub(crate) mod verify {
    use super::*;
    use crate::verify::history_specs::{EventView, Subst};
    verus! {
    impl View for NumericHead {
        type V = language::HeadField;
        open(crate) spec fn view(&self) -> language::HeadField {
            match self {
                NumericHead::Any => language::HeadField::Any,
                NumericHead::Constant(value) => language::HeadField::Constant(*value as nat),
                NumericHead::Bind => language::HeadField::Bind,
            }
        }
    }

    pub(crate) open(crate) spec fn head_view(template: NumericPair) -> language::Head {
        language::Head {
            principal: template.head[0]@,
            action: template.head[1]@,
            resource: template.head[2]@,
        }
    }

    /// Independent interpretation of a cold numeric test table. The index guard
    /// makes this total even for malformed templates; executable lookup rejects
    /// those references rather than treating this default as a verdict.
    pub(crate) open(crate) spec fn source_test(template: NumericPair, index: nat, theta: Subst, event: EventView) -> bool
        decreases index,
    {
        if index >= template.tests@.len() { false }
        else { match template.tests@[index as int] {
            NumericTest::Bool(value) => value,
            NumericTest::Atom { field, term, positive } =>
                model::primitive_holds(theta, model::Primitive::Eq(field, term@), event) == positive,
            NumericTest::And(children) => forall|i: int| 0 <= i < children@.len()
                ==> children@[i] < index && source_test(template, children@[i] as nat, theta, event),
            NumericTest::Or(children) => exists|i: int| 0 <= i < children@.len()
                && children@[i] < index && source_test(template, children@[i] as nat, theta, event),
        }}
    }

    /// Independent regex language over the template's postorder nodes.
    pub(crate) open(crate) spec fn source_regex(template: NumericPair, index: nat, theta: Subst, word: Seq<EventView>) -> bool
        decreases index,
    {
        if index >= template.regexes@.len() { false }
        else { match template.regexes@[index as int] {
            HistoryRegexSource::Empty => false,
            HistoryRegexSource::All => true,
            HistoryRegexSource::Epsilon => word.len() == 0,
            HistoryRegexSource::Test(test) => word.len() == 1 && source_test(template, test as nat, theta, word[0]),
            HistoryRegexSource::Union(children) => exists|i: int| 0 <= i < children@.len()
                && children@[i] < index && source_regex(template, children@[i] as nat, theta, word),
            HistoryRegexSource::Intersect(children) => forall|i: int| 0 <= i < children@.len()
                ==> children@[i] < index && source_regex(template, children@[i] as nat, theta, word),
            HistoryRegexSource::Concat(children) => exists|parts: Seq<Seq<EventView>>|
                parts.len() == children@.len() && parts.flatten() == word
                && forall|i: int| 0 <= i < children@.len()
                    ==> children@[i] < index && source_regex(template, children@[i] as nat, theta, parts[i]),
            HistoryRegexSource::Star(child) => child < index && exists|parts: Seq<Seq<EventView>>|
                parts.flatten() == word && forall|i: int| 0 <= i < parts.len()
                    ==> source_regex(template, child as nat, theta, parts[i]),
            HistoryRegexSource::Complement(child) => child < index && !source_regex(template, child as nat, theta, word),
        }}
    }

    pub(crate) open(crate) spec fn test_correct(g: model::Graph, template: NumericPair, index: nat, id: TestId) -> bool {
        id@ < g.tests.len() && forall|theta: Subst, event: EventView| language::event_wf(theta)
            ==> norm::test_truth(g, theta, id@, event) == source_test(template, index, theta, event)
    }

    pub(crate) open(crate) spec fn regex_correct(g: model::Graph, template: NumericPair, index: nat, id: RegexId) -> bool {
        id@ < g.regexes.len() && forall|theta: Subst, word: Seq<EventView>| language::event_wf(theta)
            ==> model::regex_lang(g, theta, id@, word) == source_regex(template, index, theta, word)
    }

    pub(crate) open(crate) spec fn test_maps(g: model::Graph, template: NumericPair, ids: Seq<TestId>) -> bool {
        ids.len() <= template.tests@.len()
        && forall|i: int| 0 <= i < ids.len() ==> test_correct(g, template, i as nat, ids[i])
    }

    pub(crate) open(crate) spec fn regex_maps(g: model::Graph, template: NumericPair, ids: Seq<RegexId>) -> bool {
        ids.len() <= template.regexes@.len()
        && forall|i: int| 0 <= i < ids.len() ==> regex_correct(g, template, i as nat, ids[i])
    }

    pub(crate) proof fn maps_extend(before: model::Graph, after: model::Graph,
        template: NumericPair, tests: Seq<TestId>, regexes: Seq<RegexId>)
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

    pub(crate) proof fn test_push(g: model::Graph, template: NumericPair, tests: Seq<TestId>, id: TestId)
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

    pub(crate) proof fn regex_push(g: model::Graph, template: NumericPair, regexes: Seq<RegexId>, id: RegexId)
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

    pub(crate) proof fn selected_tests_valid(g: model::Graph, template: NumericPair,
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

    pub(crate) proof fn selected_regexes_valid(g: model::Graph, template: NumericPair,
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

    pub(crate) proof fn test_connective_transfer(g: model::Graph, template: NumericPair,
        ids: Seq<TestId>, children: Seq<u32>, selected: Seq<TestId>,
        theta: Subst, event: EventView, and: bool)
        requires test_maps(g, template, ids), language::event_wf(theta),
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
        if and {
            if norm::test_combo(g, theta, selected, event, and) {
                assert forall|i: int| 0 <= i < children.len() implies
                    children[i] < ids.len() && source_test(template, children[i] as nat, theta, event) by {
                    assert(model::test_holds(theta, model::lift_test(g, selected[i]@), event));
                }
            }
            if forall|i: int| 0 <= i < children.len()
                ==> children[i] < ids.len() && source_test(template, children[i] as nat, theta, event) {
                assert forall|i: int| 0 <= i < selected.len() implies
                    model::test_holds(theta, model::lift_test(g, selected[i]@), event) by {
                    assert(children[i] < ids.len() && source_test(template, children[i] as nat, theta, event));
                }
            }
        } else {
            if norm::test_combo(g, theta, selected, event, and) {
                let i = choose|i: int| 0 <= i < selected.len()
                    && model::test_holds(theta, model::lift_test(g, selected[i]@), event);
                assert(children[i] < ids.len() && source_test(template, children[i] as nat, theta, event));
            }
            if exists|i: int| 0 <= i < children.len()
                && children[i] < ids.len() && source_test(template, children[i] as nat, theta, event) {
                let i = choose|i: int| 0 <= i < children.len()
                    && children[i] < ids.len() && source_test(template, children[i] as nat, theta, event);
                assert(model::test_holds(theta, model::lift_test(g, selected[i]@), event));
            }
        }
    }

    pub(crate) proof fn regex_set_transfer(g: model::Graph, template: NumericPair,
        ids: Seq<RegexId>, children: Seq<u32>, selected: Seq<RegexId>,
        theta: Subst, word: Seq<EventView>, intersect: bool)
        requires regex_maps(g, template, ids), language::event_wf(theta),
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
        if intersect {
            if norm::regex_combo(g, theta, selected, word, intersect) {
                assert forall|i: int| 0 <= i < children.len() implies
                    children[i] < ids.len() && source_regex(template, children[i] as nat, theta, word) by {
                    assert(model::regex_lang(g, theta, selected[i]@, word));
                }
            }
            if forall|i: int| 0 <= i < children.len()
                ==> children[i] < ids.len() && source_regex(template, children[i] as nat, theta, word) {
                assert forall|i: int| 0 <= i < selected.len() implies
                    model::regex_lang(g, theta, selected[i]@, word) by {
                    assert(children[i] < ids.len() && source_regex(template, children[i] as nat, theta, word));
                }
            }
        } else {
            if norm::regex_combo(g, theta, selected, word, intersect) {
                let i = choose|i: int| 0 <= i < selected.len()
                    && model::regex_lang(g, theta, selected[i]@, word);
                assert(children[i] < ids.len() && source_regex(template, children[i] as nat, theta, word));
            }
            if exists|i: int| 0 <= i < children.len()
                && children[i] < ids.len() && source_regex(template, children[i] as nat, theta, word) {
                let i = choose|i: int| 0 <= i < children.len()
                    && children[i] < ids.len() && source_regex(template, children[i] as nat, theta, word);
                assert(model::regex_lang(g, theta, selected[i]@, word));
            }
        }
    }

    pub(crate) proof fn regex_concat_transfer(g: model::Graph, template: NumericPair,
        ids: Seq<RegexId>, children: Seq<u32>, index: nat, theta: Subst, word: Seq<EventView>)
        requires regex_maps(g, template, ids), ids.len() == index, language::event_wf(theta),
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
            language::lang(model::gsem(theta), lifted[i], piece)
                == source_regex(template, children[i] as nat, theta, piece) by {
            assert(regex_correct(g, template, children[i] as nat, ids[children[i] as int]));
        }
        if norm::concat_combo(g, theta, selected, word) {
            let parts = choose|parts: Seq<Seq<EventView>>| parts.len() == lifted.len() && word == parts.flatten()
                && forall|i: int| 0 <= i < lifted.len()
                    ==> language::lang(model::gsem(theta), lifted[i], parts[i]);
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
                language::lang(model::gsem(theta), lifted[i], parts[i]) by {}
            assert(norm::concat_combo(g, theta, selected, word));
        }
    }

    pub(crate) proof fn regex_star_transfer(g: model::Graph, template: NumericPair,
        ids: Seq<RegexId>, child: nat, theta: Subst, word: Seq<EventView>)
        requires regex_maps(g, template, ids), child < ids.len(), language::event_wf(theta),
        ensures language::lang(model::gsem(theta), language::Regex::Star(
            alloc::boxed::Box::new(model::lift_regex(g, ids[child as int]@))), word)
            == (exists|parts: Seq<Seq<EventView>>| parts.flatten() == word
                && forall|i: int| 0 <= i < parts.len() ==> source_regex(template, child, theta, parts[i])),
    {
        let regex = model::lift_regex(g, ids[child as int]@);
        assert(regex_correct(g, template, child, ids[child as int]));
        if language::lang(model::gsem(theta), language::Regex::Star(alloc::boxed::Box::new(regex)), word) {
            let parts = choose|parts: Seq<Seq<EventView>>| word == parts.flatten()
                && forall|i: int| 0 <= i < parts.len() ==> language::lang(model::gsem(theta), regex, parts[i]);
            assert forall|i: int| 0 <= i < parts.len() implies source_regex(template, child, theta, parts[i]) by {}
            assert(exists|parts: Seq<Seq<EventView>>| parts.flatten() == word
                && forall|i: int| 0 <= i < parts.len() ==> source_regex(template, child, theta, parts[i]));
        }
        if exists|parts: Seq<Seq<EventView>>| parts.flatten() == word
            && forall|i: int| 0 <= i < parts.len() ==> source_regex(template, child, theta, parts[i]) {
            let parts = choose|parts: Seq<Seq<EventView>>| parts.flatten() == word
                && forall|i: int| 0 <= i < parts.len() ==> source_regex(template, child, theta, parts[i]);
            assert forall|i: int| 0 <= i < parts.len() implies language::lang(model::gsem(theta), regex, parts[i]) by {}
            assert(language::lang(model::gsem(theta), language::Regex::Star(alloc::boxed::Box::new(regex)), word));
        }
    }
    }
}
