// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Native clock, timer and configured-memory observations for the shared history engine.

use crate::languages::history_table::limits::RegorusLimits;
use crate::utils::limits::{
    check_memory_limit_if_needed, enforce_memory_limit, monotonic_now, ExecutionTimer,
    ExecutionTimerConfig, LimitError,
};
use alloc::sync::Arc;
use core::time::Duration;
use history_semantics::runtime::{verify as runtime, BatchCursor, RuleRuntime};
use history_store::history::StoredHistory;
use history_store::store::HistoryStore as CoreHistoryStore;
use junco_core::{
    error::HistoryError, flat::FlatPair, kernel::Bindings, observation::ObservationWorld,
};
use vstd::prelude::*;

verus! {

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExExecutionTimer(ExecutionTimer);

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExExecutionTimerConfig(ExecutionTimerConfig);

pub assume_specification[ ExecutionTimer::config ](timer: &ExecutionTimer) -> Option<ExecutionTimerConfig>;

pub assume_specification[ ExecutionTimer::accumulate ](
    timer: &mut ExecutionTimer, work_units: u32,
) -> bool;

pub assume_specification[ ExecutionTimer::check_now ](
    timer: &mut ExecutionTimer, now: Duration,
) -> Result<(), LimitError>;

pub assume_specification[ check_memory_limit_if_needed ]() -> Result<(), LimitError>;
pub assume_specification[ enforce_memory_limit ]() -> Result<(), LimitError>;
pub assume_specification[ monotonic_now ]() -> Option<Duration>;

// Instantiate the shared verified bodies with the real host budget adapter.
pub fn construct_with_host_limits(
    store: &Arc<CoreHistoryStore>, template: &FlatPair<u64>, precompile: bool,
    timer: &mut ExecutionTimer, world: &mut ObservationWorld,
) -> (result: Result<RuleRuntime, HistoryError>)
    ensures runtime::constructor_result(result, *store, *template),
        result matches Ok(engine) ==> runtime::runtime_wf(engine) && engine.spec_store() == *store,
{
    let mut limits = RegorusLimits { timer };
    let result = RuleRuntime::new(store, template, precompile, &mut limits, world);
    proof {
        if let Ok(engine) = &result {
            runtime::lemma_constructor_runtime_wf(*engine, *store, *template);
        }
    }
    result
}

// The cache key is the locked record's own immutable ID, never a caller-supplied index.
pub fn resume_with_host_provenance(
    engine: &mut RuleRuntime, bindings: &Bindings,
    stored: &StoredHistory, target_len: usize,
) -> (cursor: BatchCursor)
    requires runtime::resume_requires(*old(engine), *bindings, *stored, target_len),
    ensures runtime::resume_ensures(*old(engine), *final(engine), cursor,
        *bindings, *stored, target_len),
        runtime::advance_requires(*final(engine), cursor, *bindings, *stored),
        final(engine).spec_store() == old(engine).spec_store(),
{
    let ghost before = *engine;
    let cursor = engine.resume_cursor(bindings, stored, target_len);
    proof {
        runtime::lemma_resume_can_advance(before, *engine, cursor, *bindings, *stored, target_len);
    }
    cursor
}

pub fn advance_with_host_limits(
    engine: &mut RuleRuntime, cursor: &mut BatchCursor,
    bindings: &Bindings, stored: &StoredHistory,
    target_len: usize, batch_size: usize,
    timer: &mut ExecutionTimer, world: &mut ObservationWorld,
) -> (result: Result<Option<bool>, HistoryError>)
    requires runtime::advance_requires(*old(engine), *old(cursor), *bindings, *stored),
    ensures runtime::advance_ensures(*old(engine), *final(engine), *old(cursor), *final(cursor),
        *bindings, *stored, target_len, batch_size, result),
        runtime::runtime_wf(*final(engine)),
        runtime::runtime_frame(*old(engine), *final(engine)),
        final(engine).spec_store() == old(engine).spec_store(),
        result is Err ==> runtime::cursor_consumed(*final(cursor)) == runtime::cursor_consumed(*old(cursor))
            && runtime::cursor_cache_unchanged(*old(engine), *final(engine)),
        result matches Ok(None) ==> runtime::cursor_consumed(*final(cursor)) < target_len,
        result matches Ok(Some(_)) ==> runtime::cursor_consumed(*final(cursor)) == target_len,
{
    let mut limits = RegorusLimits { timer };
    let ghost before = *engine;
    let ghost start = *cursor;
    let result = engine.advance_cursor(cursor, bindings, stored, target_len, batch_size, &mut limits, world);
    proof {
        runtime::lemma_advance_result_facts(before, *engine, start, *cursor,
            *bindings, *stored, target_len, batch_size, result);
    }
    result
}

}
