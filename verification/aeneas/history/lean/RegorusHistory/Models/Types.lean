-- Copyright (c) Microsoft Corporation. All rights reserved.
-- Licensed under the MIT License.
module
public import Aeneas

@[expose] public section

namespace RegorusHistory.Models

open Aeneas.Std

/-- The normalized native duration carried by a clock observation. -/
structure ClockReading where
  secs : U64
  nanos : U32
  normalized : nanos.val < 1000000000

/-- Opaque native error payloads are nominal: their Rust layouts need not agree.
    The token retains identity; no capacity/layout claim follows from it. -/
structure VecReserveError where
  token : Nat

structure WordsReserveError where
  token : Nat

structure FingerprintsReserveError where
  token : Nat

structure ArenaAllocError where
  token : Nat

/-- An immutable captured builder seed, retained by clone and every hash call. -/
structure HasherSeed where
  token : Nat

/-- A returned native allocation result, not an outer Aeneas failure. -/
inductive NativeOutcome (ε : Type) where
  | success
  | error (value : ε)

def NativeOutcome.toRust {α ε : Type} (outcome : NativeOutcome ε) (value : α) :
    core.result.Result α ε :=
  match outcome with
  | .success => .Ok value
  | .error failure => .Err failure

/-- Exactly the eight native adapter operations; vector exactness is explicit. -/
inductive Request where
  | now
  | newHasher
  | reserveVec (additional : Nat) (exact : Bool)
  | reserveWords (additional : Nat)
  | reserveFingerprints (additional : Nat)
  | allocValue
  | allocSlice (length : Nat)
  deriving DecidableEq

def Reply : Request → Type
  | .now => Option ClockReading
  | .newHasher => HasherSeed
  | .reserveVec _ _ => NativeOutcome VecReserveError
  | .reserveWords _ => NativeOutcome WordsReserveError
  | .reserveFingerprints _ => NativeOutcome FingerprintsReserveError
  | .allocValue | .allocSlice _ => NativeOutcome ArenaAllocError

/-- Recorded native outcomes, including the arguments that must match on replay. -/
inductive Observation where
  | clock (value : Option ClockReading)
  | hasher (seed : HasherSeed)
  | reserveVec (additional : Nat) (exact : Bool) (outcome : NativeOutcome VecReserveError)
  | reserveWords (additional : Nat) (outcome : NativeOutcome WordsReserveError)
  | reserveFingerprints (additional : Nat) (outcome : NativeOutcome FingerprintsReserveError)
  | allocValue (outcome : NativeOutcome ArenaAllocError)
  | allocSlice (length : Nat) (outcome : NativeOutcome ArenaAllocError)

/-- Logical state only. Every remaining trace erases to the same native ZST. -/
abbrev World := List Observation

def eraseWorld (_ : World) : Unit := ()

@[simp] theorem eraseWorld_eq (first second : World) : eraseWorld first = eraseWorld second := rfl

/-- One recorded observation for a typed native return. -/
def recordReply : (request : Request) → Reply request → Observation
  | .now, value => .clock value
  | .newHasher, seed => .hasher seed
  | .reserveVec additional exact, outcome => .reserveVec additional exact outcome
  | .reserveWords additional, outcome => .reserveWords additional outcome
  | .reserveFingerprints additional, outcome => .reserveFingerprints additional outcome
  | .allocValue, outcome => .allocValue outcome
  | .allocSlice length, outcome => .allocSlice length outcome

/-- Semantic state is carried by the value; World advances even on inner Rust Err. -/
structure Observed (α : Type u) where
  value : α
  world : World

def TraceProgress (before after : World) : Prop :=
  ∃ consumed, before = consumed ++ after

@[refl] theorem TraceProgress.refl (world : World) : TraceProgress world world := ⟨[], rfl⟩

theorem TraceProgress.trans {first second third : World}
    (h₁ : TraceProgress first second) (h₂ : TraceProgress second third) :
    TraceProgress first third := by
  rcases h₁ with ⟨prefix₁, rfl⟩
  rcases h₂ with ⟨prefix₂, rfl⟩
  exact ⟨prefix₁ ++ prefix₂, by simp only [List.append_assoc]⟩

end RegorusHistory.Models
