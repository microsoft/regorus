// Copyright (c) Microsoft Corporation. All rights reserved.
// Licensed under the MIT License.
use crate::graph::verify::{graph_weight, regex_weight, test_weight, transition_weight};
use junco_core::kernel::verify::Graph;
use junco_core::kernel::*;
use junco_core::observation::ObservationWorld;
use vstd::prelude::*;
verus! {
#[verifier::external_trait_specification]
#[verifier::external_trait_extension(StorageSpec via StorageSpecImpl)]
pub trait ExStorage {
    type ExternalTraitSpecificationFor: crate::graph::Storage;

    spec fn graph(&self) -> Graph;
    /// Bytes each backing arena can hold (0 for growable storage).
    spec fn capacity(&self) -> int;
    /// `graph_weight(graph) - bytes actually resident`; never decreases on a successful push.
    spec fn slack(&self) -> int;

    fn test(&self, id: TestId) -> (r: KernelResult<TestView<'_>>)
        ensures r matches Ok(v) ==> id@ < self.graph().tests.len()
            && v@ == self.graph().tests[id@ as int],
            r matches Err(error) ==> !(error is ArenaExhausted);
    fn regex(&self, id: RegexId) -> (r: KernelResult<RegexView<'_>>)
        ensures r matches Ok(v) ==> id@ < self.graph().regexes.len()
            && v@ == self.graph().regexes[id@ as int],
            r matches Err(error) ==> !(error is ArenaExhausted);
    fn transition(&self, id: TransitionId) -> (r: KernelResult<TransitionView<'_>>)
        ensures r matches Ok(v) ==> id@ < self.graph().transitions.len()
            && v@ == self.graph().transitions[id@ as int],
            r matches Err(error) ==> !(error is ArenaExhausted);

    fn find_test(&self, view: TestView<'_>) -> (r: KernelResult<Option<TestId>>)
        ensures r matches Ok(Some(id)) ==> id@ < self.graph().tests.len()
            && self.graph().tests[id@ as int] == view@,
            r matches Ok(None) ==> !self.graph().tests.contains(view@),
            r matches Err(error) ==> !(error is ArenaExhausted);
    fn find_regex(&self, view: RegexView<'_>) -> (r: KernelResult<Option<RegexId>>)
        ensures r matches Ok(Some(id)) ==> id@ < self.graph().regexes.len()
            && self.graph().regexes[id@ as int] == view@,
            r matches Ok(None) ==> !self.graph().regexes.contains(view@),
            r matches Err(error) ==> !(error is ArenaExhausted);
    fn find_transition(&self, view: TransitionView<'_>) -> (r: KernelResult<Option<TransitionId>>)
        ensures r matches Ok(Some(id)) ==> id@ < self.graph().transitions.len()
            && self.graph().transitions[id@ as int] == view@,
            r matches Ok(None) ==> !self.graph().transitions.contains(view@),
            r matches Err(error) ==> !(error is ArenaExhausted);

    fn push_test(&mut self, view: TestView<'_>, world: &mut ObservationWorld)
        -> (r: KernelResult<TestId>)
        requires !old(self).graph().tests.contains(view@),
        ensures
            final(self).graph().constants == old(self).graph().constants,
            final(self).graph().regexes == old(self).graph().regexes,
            final(self).graph().transitions == old(self).graph().transitions,
            r is Err ==> final(self).graph() == old(self).graph(),
            r matches Ok(id) ==> id@ == old(self).graph().tests.len()
                && final(self).graph().tests == old(self).graph().tests.push(view@),
            final(self).capacity() == old(self).capacity(),
            r is Ok ==> final(self).slack() >= old(self).slack(),
            r matches Err(error) ==> error is ArenaExhausted ==>
                graph_weight(old(self).graph()) + test_weight(view@) - old(self).slack()
                    > old(self).capacity();
    fn push_regex(&mut self, view: RegexView<'_>, world: &mut ObservationWorld)
        -> (r: KernelResult<RegexId>)
        requires !old(self).graph().regexes.contains(view@),
        ensures
            final(self).graph().constants == old(self).graph().constants,
            final(self).graph().tests == old(self).graph().tests,
            final(self).graph().transitions == old(self).graph().transitions,
            r is Err ==> final(self).graph() == old(self).graph(),
            r matches Ok(id) ==> id@ == old(self).graph().regexes.len()
                && final(self).graph().regexes == old(self).graph().regexes.push(view@),
            final(self).capacity() == old(self).capacity(),
            r is Ok ==> final(self).slack() >= old(self).slack(),
            r matches Err(error) ==> error is ArenaExhausted ==>
                graph_weight(old(self).graph()) + regex_weight(view@) - old(self).slack()
                    > old(self).capacity();
    fn push_transition(&mut self, view: TransitionView<'_>, world: &mut ObservationWorld)
        -> (r: KernelResult<TransitionId>)
        requires !old(self).graph().transitions.contains(view@),
        ensures
            final(self).graph().constants == old(self).graph().constants,
            final(self).graph().tests == old(self).graph().tests,
            final(self).graph().regexes == old(self).graph().regexes,
            r is Err ==> final(self).graph() == old(self).graph(),
            r matches Ok(id) ==> id@ == old(self).graph().transitions.len()
                && final(self).graph().transitions == old(self).graph().transitions.push(view@),
            final(self).capacity() == old(self).capacity(),
            r is Ok ==> final(self).slack() >= old(self).slack(),
            r matches Err(error) ==> error is ArenaExhausted ==>
                graph_weight(old(self).graph()) + transition_weight(view@) - old(self).slack()
                    > old(self).capacity();
}

}
