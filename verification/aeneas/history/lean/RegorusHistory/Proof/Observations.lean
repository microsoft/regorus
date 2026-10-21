-- Copyright (c) Microsoft Corporation. All rights reserved.
-- Licensed under the MIT License.
module
public import RegorusHistory.Models.Types
public import RegorusHistory.Models.Funs

@[expose] public section

namespace RegorusHistory.Proof.Observations

open Aeneas.Std Aeneas.Data.Coinductive RegorusHistory.Models

/-- Observation requests and Aeneas's existing outer failure effect. -/
abbrev ObservationEffect : Effect where
  I := Request ⊕ RustEffect.Input
  O
    | .inl request => Reply request
    | .inr effect => RustEffect.Output effect

abbrev Interaction (α : Type u) := ITree ObservationEffect α

/-- One native call; returned Rust errors are ordinary typed replies. -/
def observe (request : Request) : Interaction (Reply request) :=
  .vis (.inl request) .ret

/-- Outer failure has no reply and is not a returned Rust error. -/
def failure (error : Error) : Interaction α :=
  .vis (.inr (.fail error)) PEmpty.elim

/-- Finite ordered native interaction evidence, independent of replay or World.
    Native-leaf representation contracts must supply the actual replies: this
    relation does not assert that arbitrary reply choices are physically realizable.
    There is deliberately no return constructor for outer failure or divergence. -/
inductive NativeReturned : Interaction α → List Observation → α → Prop where
  | ret (value : α) : NativeReturned (.ret value) [] value
  | observe (request : Request) (continuation : Reply request → Interaction α)
      (reply : Reply request) {trace : List Observation} {value : α}
      (rest : NativeReturned (continuation reply) trace value) :
      NativeReturned (.vis (.inl request) continuation)
        (recordReply request reply :: trace) value

/-- Replay consumes the updated World returned by each leaf, including inner Err.
    It neither adds fuel nor assumes termination of an interaction tree. -/
def replay (next : (request : Request) → World → Result (Observed (Reply request)))
    (interaction : Interaction α) (world : World) : Result (Observed α) :=
  match interaction.unfold with
  | .ret value => .ok ⟨value, world⟩
  | .div => .div
  | .vis (.inl request) continuation =>
      Aeneas.Std.bind (next request world) fun observed =>
        replay next (continuation observed.value) observed.world
  | .vis (.inr (.fail error)) _ => .fail error
partial_fixpoint

@[simp] theorem replay_ret (next) (value : α) (world : World) :
    replay next (.ret value) world = .ok ⟨value, world⟩ := by
  rw [replay]
  simp

@[simp] theorem replay_div (next) (world : World) :
    replay (α := α) next .div world = .div := by
  rw [replay]
  simp

@[simp] theorem replay_failure (next) (error : Error) (world : World) :
    replay (α := α) next (failure error) world = .fail error := by
  rw [replay]
  simp only [failure, unfold_vis]

theorem replay_observe (next) (request : Request)
    (continuation : Reply request → Interaction α) (world : World) :
    replay next (.vis (.inl request) continuation) world =
      Aeneas.Std.bind (next request world) (fun observed =>
        replay next (continuation observed.value) observed.world) := by
  rw [replay]
  rw [unfold_vis]

/-- Forward induction on actual finite returns constructs the exact trace.
    The leaf law is a theorem parameter, discharged by the concrete leaf model.
    The output is unrestricted: semantic state, timer, and inner Rust Err payloads
    can all be retained in α without being interpreted as Boolean false. -/
theorem trace_replay_adequate
    (next : (request : Request) → World → Result (Observed (Reply request)))
    (leaf : ∀ request reply suffix,
      next request (recordReply request reply :: suffix) = .ok ⟨reply, suffix⟩)
    {interaction : Interaction α} {trace : List Observation} {value : α}
    (returned : NativeReturned interaction trace value) (futureSuffix : World) :
    replay next interaction (trace ++ futureSuffix) = .ok ⟨value, futureSuffix⟩ := by
  induction returned with
  | ret value => simp
  | observe request continuation reply rest ih =>
      rw [List.cons_append, replay_observe, leaf, Aeneas.Std.bind_ok]
      exact ih

/-- Return evidence composes with the existing ITree bind, in native call order. -/
theorem NativeReturned.bind
    {first : Interaction α} {firstTrace : List Observation} {intermediate : α}
    (returnedFirst : NativeReturned first firstTrace intermediate)
    {continuation : α → Interaction β} {secondTrace : List Observation} {value : β}
    (returnedSecond : NativeReturned (continuation intermediate) secondTrace value) :
    NativeReturned (ITree.bind first continuation) (firstTrace ++ secondTrace) value := by
  induction returnedFirst with
  | ret intermediate => simpa using returnedSecond
  | observe request k reply rest ih =>
      rw [ITree.bind, unfold_vis]
      exact NativeReturned.observe request
        (fun answer => ITree.bind (k answer) continuation) reply (ih returnedSecond)

/-- A finite first return can be extended by any continuation, even one that
    diverges or fails. Only the first call's recorded observations are consumed. -/
theorem replay_bind_return
    (next : (request : Request) → World → Result (Observed (Reply request)))
    (leaf : ∀ request reply suffix,
      next request (recordReply request reply :: suffix) = .ok ⟨reply, suffix⟩)
    {first : Interaction α} {firstTrace : List Observation} {intermediate : α}
    (returnedFirst : NativeReturned first firstTrace intermediate)
    (continuation : α → Interaction β) (futureSuffix : World) :
    replay next (ITree.bind first continuation) (firstTrace ++ futureSuffix) =
      replay next (continuation intermediate) futureSuffix := by
  induction returnedFirst with
  | ret intermediate => simp
  | observe request k reply rest ih =>
      rw [ITree.bind, unfold_vis, List.cons_append, replay_observe, leaf,
        Aeneas.Std.bind_ok]
      exact ih

/-- A returned invocation consumes precisely its recorded prefix, never its future. -/
theorem trace_replay_progress
    (next : (request : Request) → World → Result (Observed (Reply request)))
    (leaf : ∀ request reply suffix,
      next request (recordReply request reply :: suffix) = .ok ⟨reply, suffix⟩)
    {interaction : Interaction α} {trace : List Observation} {value : α}
    (returned : NativeReturned interaction trace value) (futureSuffix : World) :
    replay next interaction (trace ++ futureSuffix) = .ok ⟨value, futureSuffix⟩ ∧
      TraceProgress (trace ++ futureSuffix) futureSuffix :=
  ⟨trace_replay_adequate next leaf returned futureSuffix, ⟨trace, rfl⟩⟩

/-- Sequential native returns replay constructively with their concatenated trace. -/
theorem trace_replay_bind_adequate
    (next : (request : Request) → World → Result (Observed (Reply request)))
    (leaf : ∀ request reply suffix,
      next request (recordReply request reply :: suffix) = .ok ⟨reply, suffix⟩)
    {first : Interaction α} {firstTrace : List Observation} {intermediate : α}
    (returnedFirst : NativeReturned first firstTrace intermediate)
    {continuation : α → Interaction β} {secondTrace : List Observation} {value : β}
    (returnedSecond : NativeReturned (continuation intermediate) secondTrace value)
    (futureSuffix : World) :
    replay next (ITree.bind first continuation) (firstTrace ++ secondTrace ++ futureSuffix) =
      .ok ⟨value, futureSuffix⟩ ∧
      TraceProgress (firstTrace ++ secondTrace ++ futureSuffix) futureSuffix :=
  trace_replay_progress next leaf (returnedFirst.bind returnedSecond) futureSuffix

/-- A single observed leaf supplies a one-element witness with the same ZST erasure. -/
theorem observe_replay_adequate
    (next : (request : Request) → World → Result (Observed (Reply request)))
    (leaf : ∀ request reply suffix,
      next request (recordReply request reply :: suffix) = .ok ⟨reply, suffix⟩)
    (request : Request) (reply : Reply request) (futureSuffix : World) :
    replay next (observe request) (recordReply request reply :: futureSuffix) =
      .ok ⟨reply, futureSuffix⟩ ∧
      TraceProgress (recordReply request reply :: futureSuffix) futureSuffix ∧
      eraseWorld (recordReply request reply :: futureSuffix) = eraseWorld futureSuffix := by
  have returned := NativeReturned.observe request ITree.ret reply (NativeReturned.ret reply)
  exact ⟨trace_replay_adequate next leaf returned futureSuffix,
    ⟨[recordReply request reply], rfl⟩, rfl⟩

/-- The concrete trace model discharges the leaf premise; no observation law is
    assumed by this specialization. Generated matcher bodies are linked separately. -/
theorem model_trace_replay_adequate
    {interaction : Interaction α} {trace : List Observation} {value : α}
    (returned : NativeReturned interaction trace value) (futureSuffix : World) :
    replay RegorusHistory.Models.consume interaction (trace ++ futureSuffix) =
      .ok ⟨value, futureSuffix⟩ ∧ TraceProgress (trace ++ futureSuffix) futureSuffix :=
  trace_replay_progress RegorusHistory.Models.consume consume_record returned futureSuffix

end RegorusHistory.Proof.Observations
