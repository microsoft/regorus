// Copyright (c) Microsoft Corporation. All rights reserved.
// Licensed under the MIT License.

//! Numeric committed histories with failure-atomic mutation.
//! Truncation is a no-op at or beyond length, otherwise consumes one revision
//! or fails unchanged at exhaustion.

use crate::store::{Event, allocation};
use alloc::vec::Vec;
use junco_core::errors::HistoryError;
use junco_core::limits::Limits;
use junco_core::observation::ObservationWorld;

#[derive(Debug)]
pub struct StoredHistory {
    pub(crate) events: Vec<Event>,
    pub(crate) revision: u64,
    pub(crate) id: usize,
}

impl StoredHistory {
    pub fn as_slice(&self) -> &[Event] {
        &self.events
    }

    /// Return the number of encoded events without exposing mutable storage.
    pub fn len(&self) -> usize {
        self.events.len()
    }

    /// Return whether the encoded history is empty without exposing storage.
    pub fn is_empty(&self) -> bool {
        self.events.is_empty()
    }

    /// Return the revision invalidating decisions after a shortening transaction.
    pub const fn revision(&self) -> u64 {
        self.revision
    }

    /// Return the immutable process-wide key that names this record in cursor caches.
    pub const fn id(&self) -> usize {
        self.id
    }

    pub(crate) const fn new(id: usize) -> Self {
        Self {
            events: Vec::new(),
            revision: 0,
            id,
        }
    }

    pub(crate) fn append_events<L: Limits>(
        &mut self,
        events: &[Event],
        limits: &mut L,
        world: &mut ObservationWorld,
    ) -> Result<(), HistoryError> {
        let previous = self.events.len();
        allocation(world.try_reserve_vec(&mut self.events, events.len()))?;
        limits.enforce_memory()?;
        self.events.extend_from_slice(events);
        if let Err(error) = limits.enforce_memory() {
            self.events.truncate(previous);
            return Err(error.into());
        }
        Ok(())
    }

    pub(crate) fn truncate_events(&mut self, len: usize) -> Result<(), HistoryError> {
        if len < self.events.len() {
            let revision = self
                .revision
                .checked_add(1)
                .ok_or(HistoryError::RevisionExhausted)?;
            self.events.truncate(len);
            self.revision = revision;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    #![allow(clippy::unwrap_used)]

    use super::*;
    use crate::store::HistoryStore;
    use alloc::collections::BTreeSet;
    use junco_core::limits::{LimitError, Unmetered};
    use junco_core::observation::fail_reservations_after;

    struct FailMemory {
        observations: usize,
        fail_at: usize,
    }

    impl Limits for FailMemory {
        fn checkpoint(&mut self) -> Result<(), LimitError> {
            Ok(())
        }
        fn publication_checkpoint(&mut self) -> Result<(), LimitError> {
            Ok(())
        }
        fn enforce_memory(&mut self) -> Result<(), LimitError> {
            self.observations = self.observations.saturating_add(1);
            if self.observations == self.fail_at {
                Err(LimitError::MemoryLimitExceeded { usage: 1, limit: 0 })
            } else {
                Ok(())
            }
        }
    }

    fn fresh_key() -> usize {
        HistoryStore::new(3).allocate_history_after(0).unwrap()
    }

    fn event() -> Event {
        let store = HistoryStore::new(3);
        let mut slots = [0; 3];
        for (index, bytes) in [b"alice".as_slice(), b"edit".as_slice(), b"doc".as_slice()]
            .into_iter()
            .enumerate()
        {
            slots[index] = store
                .intern(
                    history_syntax::Component::new(index),
                    bytes,
                    &mut Unmetered,
                    &mut ObservationWorld,
                )
                .unwrap();
        }
        Event::from_encoded(&slots)
    }

    #[test]
    fn append_memory_failures_preserve_sequence_and_revision() {
        let event = event();
        let mut stored = StoredHistory::new(fresh_key());
        stored
            .append_events(&[event], &mut Unmetered, &mut ObservationWorld)
            .unwrap();
        for fail_at in [1, 2] {
            let mut limits = FailMemory {
                observations: 0,
                fail_at,
            };
            assert!(matches!(
                stored.append_events(&[event, event], &mut limits, &mut ObservationWorld),
                Err(HistoryError::Limit(_))
            ));
            assert_eq!(stored.events, [event]);
            assert_eq!(stored.len(), 1);
            assert_eq!(stored.revision(), 0);
        }
        stored
            .append_events(&[event], &mut Unmetered, &mut ObservationWorld)
            .unwrap();
        assert_eq!(stored.events, [event, event]);
        assert_eq!(stored.revision(), 0);
    }

    #[test]
    fn truncate_revision_exhaustion_fails_before_mutation() {
        let event = event();
        let mut stored = StoredHistory::new(fresh_key());
        stored
            .append_events(&[event, event], &mut Unmetered, &mut ObservationWorld)
            .unwrap();
        stored.revision = u64::MAX;
        assert!(matches!(
            stored.truncate_events(1),
            Err(HistoryError::RevisionExhausted)
        ));
        assert_eq!(stored.events, [event, event]);
        assert_eq!(stored.revision(), u64::MAX);
        stored.truncate_events(2).unwrap();
        stored.truncate_events(3).unwrap();
        assert_eq!(stored.events, [event, event]);
        assert_eq!(stored.revision(), u64::MAX);
    }

    #[test]
    fn only_real_shortening_advances_the_revision() {
        let store = HistoryStore::new(3);
        let event = event();
        let history = store
            .new_history(&mut Unmetered, &mut ObservationWorld)
            .unwrap();
        let record = store.history_record(&history).unwrap();
        store
            .append(
                &history,
                &[event, event],
                &mut Unmetered,
                &mut ObservationWorld,
            )
            .unwrap();
        store.truncate(&history, 2).unwrap();
        store.truncate(&history, 5).unwrap();
        assert_eq!(record.read().revision(), 0);
        store.truncate(&history, 1).unwrap();
        assert_eq!(record.read().revision(), 1);
        assert_eq!(record.read().as_slice(), [event]);
        store
            .append(&history, &[event], &mut Unmetered, &mut ObservationWorld)
            .unwrap();
        assert_eq!(record.read().revision(), 1);
        store.truncate(&history, 0).unwrap();
        assert_eq!(record.read().revision(), 2);
        assert!(record.read().is_empty());
    }

    #[test]
    fn append_reservation_failures_preserve_sequence_and_revision() {
        let store = HistoryStore::new(3);
        let event = event();
        let history = store
            .new_history(&mut Unmetered, &mut ObservationWorld)
            .unwrap();
        store
            .append(&history, &[event], &mut Unmetered, &mut ObservationWorld)
            .unwrap();
        {
            let _failure = fail_reservations_after(0);
            assert!(matches!(
                store.append(&history, &[event], &mut Unmetered, &mut ObservationWorld),
                Err(HistoryError::AllocationFailed)
            ));
        }
        let record = store.history_record(&history).unwrap();
        assert_eq!(record.read().as_slice(), [event]);
        assert_eq!(record.read().revision(), 0);
        store
            .append(&history, &[event], &mut Unmetered, &mut ObservationWorld)
            .unwrap();
        assert_eq!(record.read().as_slice(), [event, event]);
    }

    #[test]
    fn store_append_memory_failures_preserve_sequence() {
        let store = HistoryStore::new(3);
        let event = event();
        let history = store
            .new_history(&mut Unmetered, &mut ObservationWorld)
            .unwrap();
        store
            .append(&history, &[event], &mut Unmetered, &mut ObservationWorld)
            .unwrap();
        for fail_at in [1, 2] {
            let mut limits = FailMemory {
                observations: 0,
                fail_at,
            };
            assert!(matches!(
                store.append(&history, &[event], &mut limits, &mut ObservationWorld),
                Err(HistoryError::Limit(_))
            ));
            assert_eq!(store.len(&history).unwrap(), 1);
        }
        assert_eq!(store.history_record(&history).unwrap().read().revision(), 0);
    }

    #[test]
    fn history_keys_do_not_alias_across_event_arities() {
        let mut keys = BTreeSet::new();
        for arity in 1..=history_syntax::MAX_ARITY {
            let store = HistoryStore::new(arity);
            let history = store
                .new_history(&mut Unmetered, &mut ObservationWorld)
                .unwrap();
            assert!(keys.insert(history.index()));
        }
    }
}
