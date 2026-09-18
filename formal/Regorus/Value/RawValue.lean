/-
Copyright (c) Microsoft Corporation.
Licensed under the MIT License.
-/

import Regorus.Value.RawNumber

/-!
# Representation-level values

`RawValue` mirrors the eight constructors of Rust's `Value`.  Sets and objects
are intentionally represented by lists here: uniqueness, sorting, and key
normalization are representation invariants imposed by a later refinement.

The mutually recursive node counts expose the decrease that is hidden by the
nested `List RawValue` occurrences.  They are suitable termination measures
for representation-sensitive recursive functions and proofs.
-/

namespace Regorus

inductive RawValue where
  | Null
  | Bool (b : Bool)
  | Number (n : RawNumber)
  | String (s : String)
  | Array (a : List RawValue)
  | Set (s : List RawValue)
  | Object (o : List (RawValue × RawValue))
  | Undefined
  deriving Repr

namespace RawValue

mutual
  /-- Number of `RawValue` nodes, including the root. -/
  @[simp] def nodeCount : RawValue → Nat
    | .Null | .Bool _ | .Number _ | .String _ | .Undefined => 1
    | .Array xs | .Set xs => listNodeCount xs + 1
    | .Object xs => objectNodeCount xs + 1

  /-- Aggregate node count of a raw array or set payload. -/
  @[simp] def listNodeCount : List RawValue → Nat
    | [] => 0
    | x :: xs => nodeCount x + listNodeCount xs + 1

  /-- Aggregate node count of raw object key/value pairs. -/
  @[simp] def objectNodeCount : List (RawValue × RawValue) → Nat
    | [] => 0
    | (k, v) :: xs => nodeCount k + nodeCount v + objectNodeCount xs + 1
end

/-- The standard well-founded relation induced by `nodeCount`. -/
def Smaller (x y : RawValue) : Prop :=
  nodeCount x < nodeCount y

theorem smaller_wellFounded : WellFounded Smaller :=
  Nat.lt_wfRel.wf.onFun

@[simp] theorem nodeCount_pos (v : RawValue) : 0 < nodeCount v := by
  cases v <;> simp

theorem head_lt_list (x : RawValue) (xs : List RawValue) :
    nodeCount x < listNodeCount (x :: xs) := by
  simp
  omega

theorem key_lt_object (k v : RawValue) (xs : List (RawValue × RawValue)) :
    nodeCount k < objectNodeCount ((k, v) :: xs) := by
  simp
  omega

theorem value_lt_object (k v : RawValue) (xs : List (RawValue × RawValue)) :
    nodeCount v < objectNodeCount ((k, v) :: xs) := by
  simp
  omega

theorem nodeCount_lt_list_of_mem {v : RawValue} {xs : List RawValue}
    (h : v ∈ xs) : nodeCount v ≤ listNodeCount xs := by
  induction xs with
  | nil => simp at h
  | cons x xs ih =>
      simp only [List.mem_cons] at h
      rcases h with rfl | h
      · simp
        omega
      · have := ih h
        simp
        omega

theorem nodeCount_lt_array_of_mem {v : RawValue} {xs : List RawValue}
    (h : v ∈ xs) : nodeCount v < nodeCount (.Array xs) := by
  simp only [nodeCount]
  exact Nat.lt_succ_of_le (nodeCount_lt_list_of_mem h)

theorem nodeCount_lt_set_of_mem {v : RawValue} {xs : List RawValue}
    (h : v ∈ xs) : nodeCount v < nodeCount (.Set xs) := by
  simp only [nodeCount]
  exact Nat.lt_succ_of_le (nodeCount_lt_list_of_mem h)

end RawValue

end Regorus
