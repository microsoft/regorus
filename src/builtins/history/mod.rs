// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

// Verus checks contract visibility against item visibility, so kernel items keep `pub(crate)`;
// verified matches use reference patterns throughout the proofs.
#![allow(clippy::redundant_pub_crate, clippy::pattern_type_mismatch)]

pub(crate) mod error;
pub(crate) mod graph;
pub(crate) mod kernel;
pub(crate) mod normalize;
pub(crate) mod progress;
pub(crate) mod source;
pub(crate) mod symbolic;

pub(crate) mod work {
    pub(crate) type WorkVec<T> = smallvec::SmallVec<[T; 4]>;
}

#[cfg(feature = "cache")]
use alloc::vec::Vec;

use crate::utils::limits::ExecutionTimer;
use crate::value::Array;
#[cfg(verus_keep_ghost)]
use crate::verify::{
    history_specs as language,
    value_specs::{history_view, value_view},
};
use crate::{Rc, Value};
pub(crate) use error::HistoryError;
pub(crate) use graph::ObservationWorld;
#[cfg(verus_keep_ghost)]
use progress::verify as progress_model;
#[cfg(verus_keep_ghost)]
use verify::*;
use vstd::prelude::*;

#[cfg(feature = "cache")]
#[verus_verify]
const PAIR_CACHE_CAPACITY: usize = 16;

#[cfg(feature = "cache")]
#[verus_verify]
#[verus_verify(external_derive)]
#[derive(Debug)]
struct RetainedPair {
    policy: Value,
    pair: progress::CompiledPair,
}

/// Performance state belongs to one evaluator; cloned/new evaluators start empty.
#[verus_verify]
#[verus_verify(external_derive)]
#[derive(Debug)]
pub(crate) struct HistoryMatchState {
    #[cfg(feature = "cache")]
    pairs: Vec<RetainedPair>,
    #[cfg(test)]
    pub(crate) compile_attempts: usize,
    #[cfg(test)]
    pub(crate) graph_retries: usize,
}

// Verus does not model implicit destructor calls; cleanup itself is verified below.
#[verus_verify(external)]
impl Drop for HistoryMatchState {
    fn drop(&mut self) {
        self.release();
    }
}

// The empty-state invariant needs a verified constructor body.
#[allow(clippy::derivable_impls)]
#[verus_verify]
impl Default for HistoryMatchState {
    #[verus_spec(result => ensures result.state_wf())]
    fn default() -> Self {
        Self {
            #[cfg(feature = "cache")]
            pairs: Vec::new(),
            #[cfg(test)]
            compile_attempts: 0,
            #[cfg(test)]
            graph_retries: 0,
        }
    }
}

#[verus_verify]
impl HistoryMatchState {
    #[allow(clippy::unused_self)]
    #[verus_spec(ensures final(self).state_wf())]
    pub(crate) fn release(&mut self) {
        #[cfg(feature = "cache")]
        {
            #[cfg_attr(verus_keep_ghost, verus_spec(
                ensures self.pairs@.len() == 0,
                decreases self.pairs@.len(),
            ))]
            while let Some(entry) = self.pairs.pop() {
                entry.pair.release();
            }
        }
    }

    #[allow(clippy::unused_self)] // Without cache, production calls retain no state.
    #[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
    #[verus_spec(result =>
        requires old(self).state_wf(),
        ensures final(self).state_wf(),
            result matches Ok(answer) ==> answer == language::policy_lang(
                value_view(*policy), value_view(*request), history_view(*history)),
            result matches Ok(answer) ==> forall|head: language::Head, tail: language::Regex<language::SrcTest>|
                #[trigger] language::decodes_policy(value_view(*policy), head, tail)
                    ==> answer == language::pair_lang(head, tail, value_view(*request), history_view(*history)),
    )]
    pub(crate) fn evaluate(
        &mut self,
        policy: &Value,
        history: &Rc<Array>,
        request: &Value,
        timer: &mut ExecutionTimer,
        world: &mut ObservationWorld,
    ) -> core::result::Result<bool, HistoryError> {
        #[cfg(feature = "cache")]
        {
            // ponytail: at most 16 exact policy comparisons; replace the linear
            // move-to-front LRU only if profiling shows this ceiling matters.
            let mut found: Option<usize> = None;
            let mut failure = None;
            let mut index = 0;
            #[cfg_attr(verus_keep_ghost, verus_spec(
                invariant self.state_wf(), index <= self.pairs@.len(),
                    found matches Some(i) ==> i < self.pairs@.len()
                        && value_view(self.pairs@[i as int].policy) == value_view(*policy),
                decreases self.pairs@.len() - index,
            ))]
            while index < self.pairs.len() {
                let entry = self
                    .pairs
                    .get(index)
                    .ok_or_else(|| graph::invariant("invalid retained pair index"))?;
                kernel::loop_try!(graph::checkpoint(timer, world), failure);
                let equal = policy == &entry.policy;
                kernel::loop_try!(graph::checkpoint(timer, world), failure);
                if equal {
                    found = Some(index);
                    break;
                }
                index = index.saturating_add(1);
            }
            if let Some(error) = failure {
                return Err(error);
            }
            if let Some(index) = found {
                proof_decl! {
                    let ghost before = self.pairs@;
                    let ghost selected = before[index as int];
                    let ghost (head, tail) = choose|head: language::Head, tail: language::Regex<language::SrcTest>|
                        language::decodes_policy(value_view(selected.policy), head, tail)
                            && progress_model::pair_represents(selected.pair, head, tail);
                    progress_model::lemma_pair_represents_wf(selected.pair, head, tail);
                }
                let pairs = self.pairs.as_mut_slice();
                let entry = pairs
                    .get_mut(index)
                    .ok_or_else(|| graph::invariant("invalid retained pair index"))?;
                proof! { assert(*entry == selected); }
                let result = entry.pair.evaluate(history, request, timer, world);
                proof! {
                    assert(language::decodes_policy(value_view(self.pairs@[index as int].policy), head, tail));
                    assert(progress_model::pair_represents(self.pairs@[index as int].pair, head, tail));
                    assert(retained_pair_wf(self.pairs@[index as int]));
                    assert forall|j: int| 0 <= j < self.pairs@.len()
                        implies retained_pair_wf(self.pairs@[j]) by {
                        if j != index { assert(self.pairs@[j] == before[j]); }
                    }
                    assert(language::decodes_policy(value_view(*policy), head, tail));
                    language::lemma_policy_lang_every_decoding(value_view(*policy),
                        value_view(*request), history_view(*history));
                }
                match result {
                    Ok(answer) => {
                        proof_decl! { let ghost prior_rotation = self.pairs@; }
                        let pairs = self.pairs.as_mut_slice();
                        pairs
                            .get_mut(..=index)
                            .ok_or_else(|| graph::invariant("invalid retained pair prefix"))?
                            .rotate_right(1);
                        proof! {
                            assert forall|j: int| 0 <= j < self.pairs@.len()
                                implies retained_pair_wf(self.pairs@[j]) by {
                                if j == 0 { assert(self.pairs@[j] == prior_rotation[index as int]); }
                                else if j <= index { assert(self.pairs@[j] == prior_rotation[j - 1]); }
                                else { assert(self.pairs@[j] == prior_rotation[j]); }
                            }
                        }
                        return Ok(answer);
                    }
                    Err(HistoryError::GraphLimit { .. }) => {
                        // The retained graph may contain unrelated exploration.
                        // Release every old ID before the single cold retry below.
                        self.pairs.remove(index).pair.release();
                        proof! { assert(self.state_wf()); }
                        #[cfg(test)]
                        {
                            self.graph_retries = self.graph_retries.saturating_add(1);
                        }
                    }
                    Err(error) => return Err(error),
                }
            }
        }
        #[cfg(test)]
        {
            self.compile_attempts = self.compile_attempts.saturating_add(1);
        }
        let mut pair = source::compile_pair(policy, timer, world)?;
        proof_decl! {
            let ghost (head, tail) = choose|head: language::Head, tail: language::Regex<language::SrcTest>|
                language::decodes_policy(value_view(*policy), head, tail)
                    && progress_model::pair_represents(pair, head, tail);
        }
        let answer = match pair.evaluate(history, request, timer, world) {
            Ok(answer) => answer,
            Err(error) => {
                pair.release();
                return Err(error);
            }
        };
        proof! {
            assert(language::decodes_policy(value_view(*policy), head, tail));
            language::lemma_policy_lang_every_decoding(value_view(*policy),
                value_view(*request), history_view(*history));
        }
        #[cfg(feature = "cache")]
        {
            if self.pairs.len() < PAIR_CACHE_CAPACITY {
                if let Err(error) = graph::allocation(world.try_reserve_vec(&mut self.pairs, 1)) {
                    pair.release();
                    return Err(error);
                }
            }
            if let Err(error) = graph::checkpoint(timer, world) {
                pair.release();
                return Err(error);
            }
            if self.pairs.len() == PAIR_CACHE_CAPACITY {
                if let Some(entry) = self.pairs.pop() {
                    entry.pair.release();
                }
            }
            proof_decl! { let ghost prior_publication = self.pairs@; }
            self.pairs.insert(
                0,
                RetainedPair {
                    policy: policy.clone(),
                    pair,
                },
            );
            proof! {
                assert(language::decodes_policy(value_view(self.pairs@[0].policy), head, tail));
                assert(progress_model::pair_represents(self.pairs@[0].pair, head, tail));
                assert(retained_pair_wf(self.pairs@[0]));
                assert forall|j: int| 0 <= j < self.pairs@.len()
                    implies retained_pair_wf(self.pairs@[j]) by {
                    if j > 0 { assert(self.pairs@[j] == prior_publication[j - 1]); }
                }
            }
        }
        #[cfg(not(feature = "cache"))]
        pair.release();
        Ok(answer)
    }
}

pub(crate) fn register(m: &mut super::BuiltinsMap<&'static str, super::BuiltinFcn>) {
    m.insert("history.match", (super::history_match, 3));
}

#[cfg(test)]
mod tests;

#[cfg(verus_keep_ghost)]
pub(crate) mod verify {
    use super::*;
    verus! {
        #[cfg(feature = "cache")]
        pub(super) open spec fn retained_pair_wf(entry: RetainedPair) -> bool {
            exists|head: language::Head, tail: language::Regex<language::SrcTest>|
                language::decodes_policy(value_view(entry.policy), head, tail)
                    && progress_model::pair_represents(entry.pair, head, tail)
        }

        impl HistoryMatchState {
            pub open(super) spec fn state_wf(&self) -> bool {
                #[cfg(feature = "cache")]
                { forall|i: int| 0 <= i < self.pairs@.len() ==> retained_pair_wf(#[trigger] self.pairs@[i]) }
                #[cfg(not(feature = "cache"))]
                { true }
            }
        }
    }
}

#[cfg(test)]
#[allow(clippy::unreachable)]
mod pair_cache_tests {
    use super::*;
    #[cfg(feature = "cache")]
    use alloc::vec;
    use serde_json::json;

    fn value(source: serde_json::Value) -> Value {
        Value::from(source)
    }

    fn history(events: serde_json::Value) -> Rc<Array> {
        match value(events) {
            Value::Array(events) => events,
            _ => unreachable!("array fixture"),
        }
    }

    fn policy(request: usize) -> Value {
        value(json!({"request":{"value":request},"history":{"epsilon":true}}))
    }

    fn evaluate(
        state: &mut HistoryMatchState,
        policy: &Value,
        history: &Rc<Array>,
        request: &Value,
    ) -> Result<bool, HistoryError> {
        let mut world = ObservationWorld;
        state.evaluate(
            policy,
            history,
            request,
            &mut ExecutionTimer::new(None),
            &mut world,
        )
    }

    #[cfg(feature = "cache")]
    #[test]
    fn exact_policy_equality_and_move_to_front_eviction() {
        let mut state = HistoryMatchState::default();
        let empty = history(json!([]));
        assert!(evaluate(&mut state, &policy(0), &empty, &Value::from(0)).unwrap());
        // Independently decoded equal Values hit; pointer identity is not authority.
        assert!(evaluate(&mut state, &policy(0), &empty, &Value::from(0)).unwrap());
        assert_eq!(state.compile_attempts, 1);
        for index in 1..PAIR_CACHE_CAPACITY {
            assert!(evaluate(&mut state, &policy(index), &empty, &Value::from(index)).unwrap());
        }
        assert!(evaluate(&mut state, &policy(0), &empty, &Value::from(0)).unwrap());
        assert!(evaluate(
            &mut state,
            &policy(PAIR_CACHE_CAPACITY),
            &empty,
            &Value::from(PAIR_CACHE_CAPACITY)
        )
        .unwrap());
        assert_eq!(state.pairs.len(), PAIR_CACHE_CAPACITY);
        assert!(state.pairs.iter().any(|entry| entry.policy == policy(0)));
        assert!(!state.pairs.iter().any(|entry| entry.policy == policy(1)));
        assert_eq!(
            state.compile_attempts,
            PAIR_CACHE_CAPACITY.saturating_add(1)
        );
        assert!(evaluate(&mut state, &policy(1), &empty, &Value::from(1)).unwrap());
        assert_eq!(
            state.compile_attempts,
            PAIR_CACHE_CAPACITY.saturating_add(2)
        );
        assert_eq!(
            state.pairs.first().map(|entry| &entry.policy),
            Some(&policy(1))
        );

        // Equal normalized languages do not make distinct source policies keys.
        let equivalent = value(json!({"request":{"value":1},"history":{"concat":[]}}));
        assert!(evaluate(&mut state, &equivalent, &empty, &Value::from(1)).unwrap());
        assert_eq!(
            state.compile_attempts,
            PAIR_CACHE_CAPACITY.saturating_add(3)
        );
        assert!(state.pairs.iter().any(|entry| entry.policy == policy(1)));
        assert!(state.pairs.iter().any(|entry| entry.policy == equivalent));
    }

    #[cfg(not(feature = "cache"))]
    #[test]
    fn disabled_cache_compiles_every_call() {
        let mut state = HistoryMatchState::default();
        let empty = history(json!([]));
        for _ in 0..2 {
            assert!(evaluate(&mut state, &policy(1), &empty, &Value::from(1)).unwrap());
        }
        assert_eq!(state.compile_attempts, 2);
        assert_eq!(state.graph_retries, 0);
    }

    #[cfg(feature = "cache")]
    #[test]
    fn retained_graph_limit_evicts_and_replays_once_from_fresh_ids() {
        let p = value(
            json!({"request":{"var":"v"},"history":{"star":{"test":{"eq":{"path":["x"],"term":{"var":"v"}}}}}}),
        );
        let mut state = HistoryMatchState::default();
        let empty = history(json!([]));
        assert!(evaluate(&mut state, &policy(7), &empty, &Value::from(7)).unwrap());
        assert!(evaluate(&mut state, &p, &empty, &Value::from(1)).unwrap());
        let retained = &mut state.pairs.first_mut().expect("admitted pair").pair;
        // Model a graph whose prior exploration has used the exact payload cap.
        retained.store.set_charged_bytes(kernel::MAX_GRAPH_BYTES);
        retained.work.events = 999;
        let events = history(json!([{"x":1}]));
        assert!(evaluate(&mut state, &p, &events, &Value::from(1)).unwrap());
        assert_eq!(state.compile_attempts, 3);
        assert_eq!(state.graph_retries, 1);
        assert_eq!(state.pairs.len(), 2);
        let fresh = &state.pairs.first().expect("freshly admitted pair").pair;
        assert!(fresh.store.bytes < kernel::MAX_GRAPH_BYTES);
        assert_eq!(fresh.work.events, 1);
        assert!(fresh.work.derivative_misses > 0);
        assert!(state.pairs.iter().any(|entry| entry.policy == policy(7)));
    }

    #[cfg(feature = "cache")]
    #[test]
    fn cold_graph_limit_is_not_retried_and_failed_retry_is_not_admitted() {
        let factors = vec![json!({"test":true}); 256];
        let p = value(json!({"request":{"any":true},"history":{"concat":factors}}));
        let empty = history(json!([]));
        let events = history(json!(vec![serde_json::Value::Null; 256]));
        let mut retained = HistoryMatchState::default();
        assert!(!evaluate(&mut retained, &p, &empty, &Value::Null).unwrap());
        assert!(matches!(
            evaluate(&mut retained, &p, &events, &Value::Null),
            Err(HistoryError::GraphLimit { .. })
        ));
        assert_eq!(retained.compile_attempts, 2);
        assert_eq!(retained.graph_retries, 1);
        assert!(retained.pairs.is_empty());
        let mut cold = HistoryMatchState::default();
        assert!(matches!(
            evaluate(&mut cold, &p, &events, &Value::Null),
            Err(HistoryError::GraphLimit { .. })
        ));
        assert_eq!(cold.compile_attempts, 1);
        assert_eq!(cold.graph_retries, 0);
        assert!(cold.pairs.is_empty());
    }

    #[cfg(feature = "cache")]
    #[test]
    fn non_graph_failures_do_not_retry_or_admit_failed_cold_pairs() {
        let p = value(
            json!({"request":{"var":"v"},"history":{"test":{"eq":{"path":["x"],"term":{"var":"v"}}}}}),
        );
        let mut state = HistoryMatchState::default();
        let empty = history(json!([]));
        assert!(!evaluate(&mut state, &p, &empty, &Value::from(1)).unwrap());
        state
            .pairs
            .first_mut()
            .expect("admitted pair")
            .pair
            .symbols
            .paths
            .clear();
        assert!(matches!(
            evaluate(&mut state, &p, &history(json!([{"x":1}])), &Value::from(1)),
            Err(HistoryError::Invariant { .. })
        ));
        assert_eq!(state.compile_attempts, 1);
        assert_eq!(state.graph_retries, 0);
        assert_eq!(state.pairs.len(), 1);
        let malformed = value(json!({"request":{"any":true},"history":{"unknown":true}}));
        assert!(matches!(
            evaluate(&mut state, &malformed, &empty, &Value::Null),
            Err(HistoryError::InvalidPolicy { .. })
        ));
        let unbound = value(
            json!({"request":{"any":true},"history":{"test":{"eq":{"path":[],"term":{"var":"missing"}}}}}),
        );
        assert!(matches!(
            evaluate(&mut state, &unbound, &empty, &Value::Null),
            Err(HistoryError::UnboundVariable { .. })
        ));
        assert_eq!(state.compile_attempts, 3);
        assert_eq!(state.graph_retries, 0);
        assert_eq!(state.pairs.len(), 1);
    }
}

#[cfg(all(test, feature = "cache"))]
#[allow(clippy::unreachable)]
#[test]
fn retained_policy_lookup_uses_active_timer_without_retry() {
    use crate::tests::interpreter::timer_test_support::{configure_time_source, reset_time_source};
    use crate::utils::limits::{acquire_limits_test_lock, ExecutionTimerConfig, LimitError};
    use core::{num::NonZeroU32, time::Duration};
    let _guard = acquire_limits_test_lock();
    configure_time_source(None);
    let policy =
        Value::from_json_str(r#"{"request":{"any":true},"history":{"all":true}}"#).unwrap();
    let history = match Value::new_array() {
        Value::Array(history) => history,
        _ => unreachable!("array fixture"),
    };
    let mut state = HistoryMatchState::default();
    let mut world = ObservationWorld;
    assert!(state
        .evaluate(
            &policy,
            &history,
            &Value::Null,
            &mut ExecutionTimer::new(None),
            &mut world,
        )
        .unwrap());
    reset_time_source();
    let mut timer = ExecutionTimer::new(Some(ExecutionTimerConfig {
        limit: Duration::from_millis(1),
        check_interval: NonZeroU32::MIN,
    }));
    timer.start(world.now().expect("configured test clock"));
    assert!(matches!(
        state.evaluate(&policy, &history, &Value::Null, &mut timer, &mut world),
        Err(HistoryError::Limit(LimitError::TimeLimitExceeded { .. }))
    ));
    assert_eq!(state.compile_attempts, 1);
    assert_eq!(state.graph_retries, 0);
    assert_eq!(state.pairs.len(), 1);
    reset_time_source();
}
