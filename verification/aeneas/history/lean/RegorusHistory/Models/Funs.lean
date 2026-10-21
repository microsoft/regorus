-- Copyright (c) Microsoft Corporation. All rights reserved.
-- Licensed under the MIT License.
module
public import RegorusHistory.Models.Types

@[expose] public section

namespace RegorusHistory.Models

open Aeneas.Std

/-- Decode only the requested operation with exactly the recorded arguments.
    A mismatch is not a native allocation error. -/
def decode : (request : Request) → Observation → Option (Reply request)
  | .now, .clock value => some value
  | .newHasher, .hasher seed => some seed
  | .reserveVec additional exact, .reserveVec recorded recordedExact outcome =>
      if additional = recorded ∧ exact = recordedExact then some outcome else none
  | .reserveWords additional, .reserveWords recorded outcome =>
      if additional = recorded then some outcome else none
  | .reserveFingerprints additional, .reserveFingerprints recorded outcome =>
      if additional = recorded then some outcome else none
  | .allocValue, .allocValue outcome => some outcome
  | .allocSlice length, .allocSlice recorded outcome =>
      if length = recorded then some outcome else none
  | _, _ => none

@[simp] theorem decode_record (request : Request) (reply : Reply request) :
    decode request (recordReply request reply) = some reply := by
  cases request <;> simp [decode, recordReply]

theorem decode_some_iff (request : Request) (observation : Observation)
    (reply : Reply request) :
    decode request observation = some reply ↔ observation = recordReply request reply := by
  constructor
  · intro decoded
    cases request <;> cases observation <;> simp only [decode] at decoded
    all_goals try contradiction
    all_goals try (split at decoded <;> try contradiction)
    all_goals (cases decoded; simp_all [recordReply])
  · rintro rfl
    exact decode_record request reply

@[simp] theorem recordReply_inj (request : Request) (first second : Reply request) :
    recordReply request first = recordReply request second ↔ first = second := by
  constructor
  · intro equality
    have decoded := congrArg (decode request) equality
    simpa using decoded
  · exact congrArg (recordReply request)

/-- Operation tags and arguments, without inspecting any native payload. -/
def observedRequest : Observation → Request
  | .clock _ => .now
  | .hasher _ => .newHasher
  | .reserveVec additional exact _ => .reserveVec additional exact
  | .reserveWords additional _ => .reserveWords additional
  | .reserveFingerprints additional _ => .reserveFingerprints additional
  | .allocValue _ => .allocValue
  | .allocSlice length _ => .allocSlice length

@[simp] theorem observedRequest_record (request : Request) (reply : Reply request) :
    observedRequest (recordReply request reply) = request := by
  cases request <;> rfl

/-- Wrong tags, amounts, exactness, and slice lengths are precisely decode failure. -/
theorem decode_none_iff (request : Request) (observation : Observation) :
    decode request observation = none ↔ observedRequest observation ≠ request := by
  constructor
  · intro mismatch equality
    cases request <;> cases observation <;>
      simp_all [observedRequest, decode]
  · intro mismatch
    cases decoded : decode request observation with
    | none => rfl
    | some reply =>
      have recorded := (decode_some_iff request observation reply).mp decoded
      exact False.elim (mismatch (recorded ▸ observedRequest_record request reply))

/-- Consume precisely one matching observation. Exhaustion and mismatch are
    outer Aeneas `undef`; every native outcome, including Err, consumes the head. -/
def consume (request : Request) (world : World) : Result (Observed (Reply request)) :=
  match world with
  | [] => .fail .undef
  | observation :: suffix =>
      match decode request observation with
      | none => .fail .undef
      | some reply => .ok ⟨reply, suffix⟩

@[simp] theorem consume_record (request : Request) (reply : Reply request) (suffix : World) :
    consume request (recordReply request reply :: suffix) = .ok ⟨reply, suffix⟩ := by
  simp [consume]

/-- Successful replay determines both the exact tagged head and the remaining tail. -/
theorem consume_ok_iff (request : Request) (world : World) (out : Observed (Reply request)) :
    consume request world = .ok out ↔ world = recordReply request out.value :: out.world := by
  cases out with
  | mk reply suffix =>
    cases world with
    | nil => simp [consume]
    | cons observation rest =>
      cases h : decode request observation with
      | none =>
          simp only [consume, h, fail_not_ok, false_iff]
          intro equality
          cases equality
          simp at h
      | some value =>
          have recorded := (decode_some_iff request observation value).mp h
          subst observation
          simp [consume, Observed.mk.injEq]

/-- One leaf consumes exactly one observation, a stronger fact than suffix progress. -/
theorem consume_exactTraceProgress {request : Request} {world : World}
    {out : Observed (Reply request)} (returned : consume request world = .ok out) :
    world = [recordReply request out.value] ++ out.world :=
  (consume_ok_iff request world out).mp returned

theorem consume_traceProgress {request : Request} {world : World}
    {out : Observed (Reply request)} (returned : consume request world = .ok out) :
    TraceProgress world out.world :=
  ⟨[recordReply request out.value], consume_exactTraceProgress returned⟩

theorem consume_frame {request : Request} {world : World}
    {out : Observed (Reply request)} (returned : consume request world = .ok out)
    (future : World) :
    consume request (world ++ future) = .ok ⟨out.value, out.world ++ future⟩ := by
  rw [(consume_ok_iff request world out).mp returned]
  exact consume_record request out.value (out.world ++ future)

@[simp] theorem consume_exhausted (request : Request) :
    consume request [] = .fail .undef := rfl

theorem consume_mismatch (request : Request) (observation : Observation)
    (suffix : World) (mismatch : decode request observation = none) :
    consume request (observation :: suffix) = .fail .undef := by
  simp [consume, mismatch]

theorem consume_wrongRequest (request : Request) (observation : Observation)
    (suffix : World) (mismatch : observedRequest observation ≠ request) :
    consume request (observation :: suffix) = .fail .undef :=
  consume_mismatch request observation suffix ((decode_none_iff request observation).mpr mismatch)

/-- A content-only result map; it never creates, resets, or rolls back World.
    These logical signatures are not claims about an ungenerated foreign ABI. -/
def observe {α : Type} (request : Request) (f : Reply request → α) (world : World) :
    Result (Observed α) := do
  let observed ← consume request world
  .ok ⟨f observed.value, observed.world⟩

@[simp] theorem observe_record {α : Type} (request : Request) (f : Reply request → α)
    (reply : Reply request) (suffix : World) :
    observe request f (recordReply request reply :: suffix) = .ok ⟨f reply, suffix⟩ := by
  simp [observe]

theorem observe_ok_iff {α : Type} (request : Request) (f : Reply request → α)
    (world : World) (out : Observed α) :
    observe request f world = .ok out ↔
      ∃ reply, world = recordReply request reply :: out.world ∧ out.value = f reply := by
  cases world with
  | nil => simp [observe, consume]
  | cons observation suffix =>
    cases h : decode request observation with
    | none =>
      simp only [observe, consume, h, bind_fail, fail_not_ok, false_iff]
      rintro ⟨reply, equality, _⟩
      cases equality
      simp at h
    | some reply =>
      have recorded := (decode_some_iff request observation reply).mp h
      subst observation
      cases out
      simp [Observed.mk.injEq, eq_comm, and_comm]

theorem observe_traceProgress {α : Type} {request : Request} {f : Reply request → α}
    {world : World} {out : Observed α} (returned : observe request f world = .ok out) :
    TraceProgress world out.world := by
  obtain ⟨reply, recorded, _⟩ := (observe_ok_iff request f world out).mp returned
  exact ⟨[recordReply request reply], recorded⟩

theorem observe_frame {α : Type} {request : Request} {f : Reply request → α}
    {world : World} {out : Observed α} (returned : observe request f world = .ok out)
    (future : World) :
    observe request f (world ++ future) = .ok ⟨out.value, out.world ++ future⟩ := by
  obtain ⟨reply, recorded, value⟩ := (observe_ok_iff request f world out).mp returned
  rw [recorded, List.cons_append, value]
  exact observe_record request f reply (out.world ++ future)

@[simp] theorem observe_exhausted {α : Type} (request : Request) (f : Reply request → α) :
    observe request f [] = .fail .undef := by
  simp [observe]

theorem observe_wrongRequest {α : Type} (request : Request) (f : Reply request → α)
    (observation : Observation) (suffix : World)
    (mismatch : observedRequest observation ≠ request) :
    observe request f (observation :: suffix) = .fail .undef := by
  simp [observe, consume_wrongRequest request observation suffix mismatch]

/-- Every successful logical leaf, whether its payload is Rust Ok or Err,
    consumes exactly one observation and permits any uninspected future suffix. -/
theorem observe_return {α : Type} {request : Request} {f : Reply request → α}
    {world : World} {out : Observed α} (returned : observe request f world = .ok out) :
    TraceProgress world out.world ∧
      (∃ reply, world = recordReply request reply :: out.world ∧ out.value = f reply) ∧
      (∀ future, observe request f (world ++ future) =
        .ok ⟨out.value, out.world ++ future⟩) :=
  ⟨observe_traceProgress returned, (observe_ok_iff request f world out).mp returned,
    observe_frame returned⟩

/-- Logical clock result, with no fixed clock value or monotonicity invented. -/
def now (world : World) : Result (Observed (Option ClockReading)) :=
  observe .now id world

/-- The returned seed is the retained immutable builder, not a fresh seed per lookup. -/
def newHasher (world : World) : Result (Observed HasherSeed) :=
  observe .newHasher id world

/-- Reservation returns `(native status, unchanged semantic contents)`.
    Contents describe only elements/entries: no capacity or layout is represented,
    and in particular no unchanged-capacity guarantee is made on failure. -/
def tryReserveVec {α : Type} (contents : α) (additional : Nat) (world : World) :
    Result (Observed (core.result.Result Unit VecReserveError × α)) :=
  observe (.reserveVec additional false) (fun outcome => (outcome.toRust (), contents)) world

def tryReserveExactVec {α : Type} (contents : α) (additional : Nat) (world : World) :
    Result (Observed (core.result.Result Unit VecReserveError × α)) :=
  observe (.reserveVec additional true) (fun outcome => (outcome.toRust (), contents)) world

def tryReserveWords {α : Type} (contents : α) (additional : Nat) (world : World) :
    Result (Observed (core.result.Result Unit WordsReserveError × α)) :=
  observe (.reserveWords additional) (fun outcome => (outcome.toRust (), contents)) world

def tryReserveFingerprints {α : Type} (contents : α) (additional : Nat) (world : World) :
    Result (Observed (core.result.Result Unit FingerprintsReserveError × α)) :=
  observe (.reserveFingerprints additional) (fun outcome => (outcome.toRust (), contents)) world

/-- Successful allocation exposes exactly the supplied immutable semantic value;
    failure retains its native payload, with the consumed World in either case. -/
def tryAllocValue {α : Type} (value : α) (world : World) :
    Result (Observed (core.result.Result α ArenaAllocError)) :=
  observe .allocValue (fun outcome => outcome.toRust value) world

/-- Slice allocation also checks the exact semantic slice length. -/
def tryAllocSlice {α : Type} (values : List α) (world : World) :
    Result (Observed (core.result.Result (List α) ArenaAllocError)) :=
  observe (.allocSlice values.length) (fun outcome => outcome.toRust values) world

@[simp] theorem now_record (value : Option ClockReading) (suffix : World) :
    now (.clock value :: suffix) = .ok ⟨value, suffix⟩ :=
  observe_record .now id value suffix

@[simp] theorem newHasher_record (seed : HasherSeed) (suffix : World) :
    newHasher (.hasher seed :: suffix) = .ok ⟨seed, suffix⟩ :=
  observe_record .newHasher id seed suffix

@[simp] theorem tryReserveVec_record {α : Type} (contents : α) (additional : Nat)
    (outcome : NativeOutcome VecReserveError) (suffix : World) :
    tryReserveVec contents additional (.reserveVec additional false outcome :: suffix) =
      .ok ⟨(outcome.toRust (), contents), suffix⟩ :=
  observe_record (.reserveVec additional false) _ outcome suffix

@[simp] theorem tryReserveExactVec_record {α : Type} (contents : α) (additional : Nat)
    (outcome : NativeOutcome VecReserveError) (suffix : World) :
    tryReserveExactVec contents additional (.reserveVec additional true outcome :: suffix) =
      .ok ⟨(outcome.toRust (), contents), suffix⟩ :=
  observe_record (.reserveVec additional true) _ outcome suffix

@[simp] theorem tryReserveWords_record {α : Type} (contents : α) (additional : Nat)
    (outcome : NativeOutcome WordsReserveError) (suffix : World) :
    tryReserveWords contents additional (.reserveWords additional outcome :: suffix) =
      .ok ⟨(outcome.toRust (), contents), suffix⟩ :=
  observe_record (.reserveWords additional) _ outcome suffix

@[simp] theorem tryReserveFingerprints_record {α : Type} (contents : α) (additional : Nat)
    (outcome : NativeOutcome FingerprintsReserveError) (suffix : World) :
    tryReserveFingerprints contents additional (.reserveFingerprints additional outcome :: suffix) =
      .ok ⟨(outcome.toRust (), contents), suffix⟩ :=
  observe_record (.reserveFingerprints additional) _ outcome suffix

@[simp] theorem tryAllocValue_record {α : Type} (value : α)
    (outcome : NativeOutcome ArenaAllocError) (suffix : World) :
    tryAllocValue value (.allocValue outcome :: suffix) =
      .ok ⟨outcome.toRust value, suffix⟩ :=
  observe_record .allocValue _ outcome suffix

@[simp] theorem tryAllocSlice_record {α : Type} (values : List α)
    (outcome : NativeOutcome ArenaAllocError) (suffix : World) :
    tryAllocSlice values (.allocSlice values.length outcome :: suffix) =
      .ok ⟨outcome.toRust values, suffix⟩ :=
  observe_record (.allocSlice values.length) _ outcome suffix

theorem now_ok_iff (world : World) (out : Observed (Option ClockReading)) :
    now world = .ok out ↔ world = .clock out.value :: out.world := by
  constructor
  · intro returned
    obtain ⟨reply, recorded, value⟩ := (observe_ok_iff .now id world out).mp returned
    rw [value]
    exact recorded
  · intro recorded
    rw [recorded]
    exact now_record out.value out.world

theorem newHasher_ok_iff (world : World) (out : Observed HasherSeed) :
    newHasher world = .ok out ↔ world = .hasher out.value :: out.world := by
  constructor
  · intro returned
    obtain ⟨reply, recorded, value⟩ := (observe_ok_iff .newHasher id world out).mp returned
    rw [value]
    exact recorded
  · intro recorded
    rw [recorded]
    exact newHasher_record out.value out.world

theorem tryReserveVec_ok_iff {α : Type} (contents : α) (additional : Nat)
    (world : World) (out : Observed (core.result.Result Unit VecReserveError × α)) :
    tryReserveVec contents additional world = .ok out ↔
      ∃ outcome, world = .reserveVec additional false outcome :: out.world ∧
        out.value = (outcome.toRust (), contents) :=
  observe_ok_iff (.reserveVec additional false) _ world out

theorem tryReserveExactVec_ok_iff {α : Type} (contents : α) (additional : Nat)
    (world : World) (out : Observed (core.result.Result Unit VecReserveError × α)) :
    tryReserveExactVec contents additional world = .ok out ↔
      ∃ outcome, world = .reserveVec additional true outcome :: out.world ∧
        out.value = (outcome.toRust (), contents) :=
  observe_ok_iff (.reserveVec additional true) _ world out

theorem tryReserveWords_ok_iff {α : Type} (contents : α) (additional : Nat)
    (world : World) (out : Observed (core.result.Result Unit WordsReserveError × α)) :
    tryReserveWords contents additional world = .ok out ↔
      ∃ outcome, world = .reserveWords additional outcome :: out.world ∧
        out.value = (outcome.toRust (), contents) :=
  observe_ok_iff (.reserveWords additional) _ world out

theorem tryReserveFingerprints_ok_iff {α : Type} (contents : α) (additional : Nat)
    (world : World) (out : Observed (core.result.Result Unit FingerprintsReserveError × α)) :
    tryReserveFingerprints contents additional world = .ok out ↔
      ∃ outcome, world = .reserveFingerprints additional outcome :: out.world ∧
        out.value = (outcome.toRust (), contents) :=
  observe_ok_iff (.reserveFingerprints additional) _ world out

theorem tryAllocValue_ok_iff {α : Type} (value : α) (world : World)
    (out : Observed (core.result.Result α ArenaAllocError)) :
    tryAllocValue value world = .ok out ↔
      ∃ outcome, world = .allocValue outcome :: out.world ∧ out.value = outcome.toRust value :=
  observe_ok_iff .allocValue _ world out

theorem tryAllocSlice_ok_iff {α : Type} (values : List α) (world : World)
    (out : Observed (core.result.Result (List α) ArenaAllocError)) :
    tryAllocSlice values world = .ok out ↔
      ∃ outcome, world = .allocSlice values.length outcome :: out.world ∧
        out.value = outcome.toRust values :=
  observe_ok_iff (.allocSlice values.length) _ world out

/-- The native error payload is retained exactly; no returned Err rewinds World. -/
theorem tryReserveVec_error_iff {α : Type} (contents retained : α) (additional : Nat)
    (failure : VecReserveError) (world suffix : World) :
    tryReserveVec contents additional world = .ok ⟨(.Err failure, retained), suffix⟩ ↔
      world = .reserveVec additional false (.error failure) :: suffix ∧ retained = contents := by
  rw [tryReserveVec_ok_iff]
  constructor
  · rintro ⟨outcome, recorded, value⟩
    cases outcome <;> simp_all [NativeOutcome.toRust]
  · rintro ⟨recorded, rfl⟩
    exact ⟨.error failure, recorded, rfl⟩

theorem tryReserveExactVec_error_iff {α : Type} (contents retained : α) (additional : Nat)
    (failure : VecReserveError) (world suffix : World) :
    tryReserveExactVec contents additional world = .ok ⟨(.Err failure, retained), suffix⟩ ↔
      world = .reserveVec additional true (.error failure) :: suffix ∧ retained = contents := by
  rw [tryReserveExactVec_ok_iff]
  constructor
  · rintro ⟨outcome, recorded, value⟩
    cases outcome <;> simp_all [NativeOutcome.toRust]
  · rintro ⟨recorded, rfl⟩
    exact ⟨.error failure, recorded, rfl⟩

theorem tryReserveWords_error_iff {α : Type} (contents retained : α) (additional : Nat)
    (failure : WordsReserveError) (world suffix : World) :
    tryReserveWords contents additional world = .ok ⟨(.Err failure, retained), suffix⟩ ↔
      world = .reserveWords additional (.error failure) :: suffix ∧ retained = contents := by
  rw [tryReserveWords_ok_iff]
  constructor
  · rintro ⟨outcome, recorded, value⟩
    cases outcome <;> simp_all [NativeOutcome.toRust]
  · rintro ⟨recorded, rfl⟩
    exact ⟨.error failure, recorded, rfl⟩

theorem tryReserveFingerprints_error_iff {α : Type} (contents retained : α) (additional : Nat)
    (failure : FingerprintsReserveError) (world suffix : World) :
    tryReserveFingerprints contents additional world = .ok ⟨(.Err failure, retained), suffix⟩ ↔
      world = .reserveFingerprints additional (.error failure) :: suffix ∧ retained = contents := by
  rw [tryReserveFingerprints_ok_iff]
  constructor
  · rintro ⟨outcome, recorded, value⟩
    cases outcome <;> simp_all [NativeOutcome.toRust]
  · rintro ⟨recorded, rfl⟩
    exact ⟨.error failure, recorded, rfl⟩

theorem tryAllocValue_error_iff {α : Type} (value : α) (failure : ArenaAllocError)
    (world suffix : World) :
    tryAllocValue value world = .ok ⟨.Err failure, suffix⟩ ↔
      world = .allocValue (.error failure) :: suffix := by
  rw [tryAllocValue_ok_iff]
  constructor
  · rintro ⟨outcome, recorded, value⟩
    cases outcome <;> simp_all [NativeOutcome.toRust]
  · intro recorded
    exact ⟨.error failure, recorded, rfl⟩

theorem tryAllocSlice_error_iff {α : Type} (values : List α) (failure : ArenaAllocError)
    (world suffix : World) :
    tryAllocSlice values world = .ok ⟨.Err failure, suffix⟩ ↔
      world = .allocSlice values.length (.error failure) :: suffix := by
  rw [tryAllocSlice_ok_iff]
  constructor
  · rintro ⟨outcome, recorded, value⟩
    cases outcome <;> simp_all [NativeOutcome.toRust]
  · intro recorded
    exact ⟨.error failure, recorded, rfl⟩

/-- Both native reservation statuses preserve precisely the semantic contents. -/
theorem tryReserveVec_preserves {α : Type} (contents : α) (additional : Nat)
    {world : World} {out : Observed (core.result.Result Unit VecReserveError × α)}
    (returned : tryReserveVec contents additional world = .ok out) :
    out.value.2 = contents ∧ TraceProgress world out.world := by
  obtain ⟨outcome, recorded, value⟩ := (tryReserveVec_ok_iff contents additional world out).mp returned
  exact ⟨congrArg Prod.snd value, ⟨[.reserveVec additional false outcome], recorded⟩⟩

theorem tryReserveExactVec_preserves {α : Type} (contents : α) (additional : Nat)
    {world : World} {out : Observed (core.result.Result Unit VecReserveError × α)}
    (returned : tryReserveExactVec contents additional world = .ok out) :
    out.value.2 = contents ∧ TraceProgress world out.world := by
  obtain ⟨outcome, recorded, value⟩ := (tryReserveExactVec_ok_iff contents additional world out).mp returned
  exact ⟨congrArg Prod.snd value, ⟨[.reserveVec additional true outcome], recorded⟩⟩

theorem tryReserveWords_preserves {α : Type} (contents : α) (additional : Nat)
    {world : World} {out : Observed (core.result.Result Unit WordsReserveError × α)}
    (returned : tryReserveWords contents additional world = .ok out) :
    out.value.2 = contents ∧ TraceProgress world out.world := by
  obtain ⟨outcome, recorded, value⟩ := (tryReserveWords_ok_iff contents additional world out).mp returned
  exact ⟨congrArg Prod.snd value, ⟨[.reserveWords additional outcome], recorded⟩⟩

theorem tryReserveFingerprints_preserves {α : Type} (contents : α) (additional : Nat)
    {world : World} {out : Observed (core.result.Result Unit FingerprintsReserveError × α)}
    (returned : tryReserveFingerprints contents additional world = .ok out) :
    out.value.2 = contents ∧ TraceProgress world out.world := by
  obtain ⟨outcome, recorded, value⟩ :=
    (tryReserveFingerprints_ok_iff contents additional world out).mp returned
  exact ⟨congrArg Prod.snd value, ⟨[.reserveFingerprints additional outcome], recorded⟩⟩

theorem tryAllocValue_success_iff {α : Type} (value returned : α) (world suffix : World) :
    tryAllocValue value world = .ok ⟨.Ok returned, suffix⟩ ↔
      world = .allocValue .success :: suffix ∧ returned = value := by
  rw [tryAllocValue_ok_iff]
  constructor
  · rintro ⟨outcome, recorded, value⟩
    cases outcome <;> simp_all [NativeOutcome.toRust]
  · rintro ⟨recorded, rfl⟩
    exact ⟨.success, recorded, rfl⟩

theorem tryAllocSlice_success_iff {α : Type} (values returned : List α) (world suffix : World) :
    tryAllocSlice values world = .ok ⟨.Ok returned, suffix⟩ ↔
      world = .allocSlice values.length .success :: suffix ∧ returned = values := by
  rw [tryAllocSlice_ok_iff]
  constructor
  · rintro ⟨outcome, recorded, value⟩
    cases outcome <;> simp_all [NativeOutcome.toRust]
  · rintro ⟨recorded, rfl⟩
    exact ⟨.success, recorded, rfl⟩

/-- A wrong native operation or any wrong observed argument produces an outer
    failure for every leaf, never a fabricated Rust Err payload. -/
theorem consume_otherRequest (request recorded : Request) (reply : Reply recorded)
    (suffix : World) (mismatch : recorded ≠ request) :
    consume request (recordReply recorded reply :: suffix) = .fail .undef := by
  apply consume_wrongRequest
  simpa using mismatch

theorem consume_wrongVecAmount (additional recorded : Nat) (exact : Bool)
    (outcome : NativeOutcome VecReserveError) (suffix : World) (mismatch : recorded ≠ additional) :
    consume (.reserveVec additional exact) (.reserveVec recorded exact outcome :: suffix) =
      .fail .undef := by
  apply consume_wrongRequest
  simpa [observedRequest] using mismatch

theorem consume_wrongVecExactness (additional : Nat) (exact recorded : Bool)
    (outcome : NativeOutcome VecReserveError) (suffix : World) (mismatch : recorded ≠ exact) :
    consume (.reserveVec additional exact) (.reserveVec additional recorded outcome :: suffix) =
      .fail .undef := by
  apply consume_wrongRequest
  simpa [observedRequest] using mismatch

theorem tryAllocSlice_wrongLength {α : Type} (values : List α) (recorded : Nat)
    (outcome : NativeOutcome ArenaAllocError) (suffix : World)
    (mismatch : recorded ≠ values.length) :
    tryAllocSlice values (.allocSlice recorded outcome :: suffix) = .fail .undef := by
  apply observe_wrongRequest
  simpa [observedRequest] using mismatch

end RegorusHistory.Models
