/-
Copyright (c) Microsoft Corporation.
Licensed under the MIT License.
-/

import Batteries.Classes.Order
import Mathlib.Data.String.Basic
import Regorus.Value.RegoNumber

/-!
# Mathematical Regorus values

This is the finite, exact value domain used for semantic proofs.  Set and
object payload lists represent unordered mathematical sets and maps.  They are
canonicalized at the construction boundary (see `Regorus.Value.Canonical`);
the stored sort order is a choice function for a permutation-equivalence
class, not part of semantic identity.  This is established by
`canonicalizeSet_perm` and `canonicalizeObject_perm` (the latter on inputs
with unique keys, because last-write-wins intentionally distinguishes
conflicting duplicate-key orders).  Consequently `beq` and `compareValue`,
although structural on the payload lists, are representation-independent for
values built with `mkSet` and `mkObject`.

Lean's automatic equality derivation cannot recurse through the nested
`List Value` occurrences.  Equality and comparison are consequently defined
as explicit mutually recursive programs.  Their termination is witnessed by
`nodeCount`, and equality is proved extensionally correct below.
-/

namespace Regorus

inductive Value where
  | Null
  | Bool (b : Bool)
  | Number (n : RegoNumber)
  | String (s : String)
  | Array (a : List Value)
  | Set (s : List Value)
  | Object (o : List (Value × Value))
  | Undefined
  deriving Repr

namespace Value

mutual
  /-- Number of value and list-cell nodes in a value. -/
  @[simp] def nodeCount : Value → Nat
    | .Null | .Bool _ | .Number _ | .String _ | .Undefined => 1
    | .Array xs | .Set xs => listNodeCount xs + 1
    | .Object xs => objectNodeCount xs + 1

  @[simp] def listNodeCount : List Value → Nat
    | [] => 0
    | x :: xs => nodeCount x + listNodeCount xs + 1

  @[simp] def objectNodeCount : List (Value × Value) → Nat
    | [] => 0
    | (k, v) :: xs => nodeCount k + nodeCount v + objectNodeCount xs + 1
end

@[simp] theorem nodeCount_pos (v : Value) : 0 < nodeCount v := by
  cases v <;> simp

def Smaller (x y : Value) : Prop :=
  nodeCount x < nodeCount y

theorem smaller_wellFounded : WellFounded Smaller :=
  Nat.lt_wfRel.wf.onFun

mutual
  /-- Structural Boolean equality for values. -/
  def beq : Value → Value → _root_.Bool
    | .Null, .Null | .Undefined, .Undefined => true
    | .Bool x, .Bool y => x == y
    | .Number x, .Number y => x == y
    | .String x, .String y => x == y
    | .Array xs, .Array ys | .Set xs, .Set ys => listBeq xs ys
    | .Object xs, .Object ys => objectBeq xs ys
    | _, _ => false

  def listBeq : List Value → List Value → _root_.Bool
    | [], [] => true
    | x :: xs, y :: ys => beq x y && listBeq xs ys
    | _, _ => false

  def objectBeq : List (Value × Value) → List (Value × Value) → _root_.Bool
    | [], [] => true
    | (kx, vx) :: xs, (ky, vy) :: ys =>
        beq kx ky && beq vx vy && objectBeq xs ys
    | _, _ => false
end

mutual
  theorem beq_eq_true_iff (x y : Value) : beq x y = true ↔ x = y := by
    cases x <;> cases y <;> simp [beq] <;>
      first | exact listBeq_eq_true_iff _ _ | exact objectBeq_eq_true_iff _ _
  termination_by nodeCount x + nodeCount y

  theorem listBeq_eq_true_iff (xs ys : List Value) :
      listBeq xs ys = true ↔ xs = ys := by
    cases xs with
    | nil => cases ys <;> simp [listBeq]
    | cons x xs =>
        cases ys with
        | nil => simp [listBeq]
        | cons y ys =>
            simp [listBeq, beq_eq_true_iff x y, listBeq_eq_true_iff xs ys]
  termination_by listNodeCount xs + listNodeCount ys

  theorem objectBeq_eq_true_iff
      (xs ys : List (Value × Value)) :
      objectBeq xs ys = true ↔ xs = ys := by
    cases xs with
    | nil => cases ys <;> simp [objectBeq]
    | cons x xs =>
        cases ys with
        | nil => simp [objectBeq]
        | cons y ys =>
            rcases x with ⟨kx, vx⟩
            rcases y with ⟨ky, vy⟩
            simp [objectBeq, beq_eq_true_iff kx ky, beq_eq_true_iff vx vy,
              objectBeq_eq_true_iff xs ys]
  termination_by objectNodeCount xs + objectNodeCount ys
end

instance : BEq Value := ⟨beq⟩

instance : LawfulBEq Value where
  rfl := (beq_eq_true_iff _ _).2 rfl
  eq_of_beq h := (beq_eq_true_iff _ _).1 h

/-- Decidable structural equality, obtained from the terminating Boolean equality. -/
instance : DecidableEq Value := fun x y =>
  decidable_of_iff (beq x y = true) (beq_eq_true_iff x y)

/-- Constructor rank, matching Rust declaration order. -/
def kindRank : Value → Nat
  | .Null => 0
  | .Bool _ => 1
  | .Number _ => 2
  | .String _ => 3
  | .Array _ => 4
  | .Set _ => 5
  | .Object _ => 6
  | .Undefined => 7

mutual
  /-- Rust-compatible heterogeneous comparison. -/
  def compareValue (x y : Value) : Ordering :=
    match x, y with
    | .Null, .Null | .Undefined, .Undefined => .eq
    | .Bool a, .Bool b => compare a b
    | .Number a, .Number b => compare a b
    | .String a, .String b => compare a b
    | .Array xs, .Array ys | .Set xs, .Set ys => compareList xs ys
    | .Object xs, .Object ys => compareObject xs ys
    | a, b => compare a.kindRank b.kindRank

  /-- Lexicographic comparison of array and canonical set payloads. -/
  def compareList : List Value → List Value → Ordering
    | [], [] => .eq
    | [], _ :: _ => .lt
    | _ :: _, [] => .gt
    | x :: xs, y :: ys => (compareValue x y).then (compareList xs ys)

  /-- Lexicographic key-then-value comparison of canonical object payloads. -/
  def compareObject :
      List (Value × Value) → List (Value × Value) → Ordering
    | [], [] => .eq
    | [], _ :: _ => .lt
    | _ :: _, [] => .gt
    | (kx, vx) :: xs, (ky, vy) :: ys =>
        (compareValue kx ky).then
          ((compareValue vx vy).then (compareObject xs ys))
end

instance : Ord Value := ⟨compareValue⟩

@[simp] theorem compare_eq_compareValue (x y : Value) :
    compare x y = compareValue x y := rfl

mutual
  /-- The comparator returns equality exactly for structural equality. -/
  theorem compareValue_eq_eq_iff (x y : Value) :
      compareValue x y = .eq ↔ x = y := by
    cases x <;> cases y <;>
      simp [compareValue, kindRank, compare_eq_iff_eq] <;>
      first
      | exact compareList_eq_eq_iff _ _
      | exact compareObject_eq_eq_iff _ _
  termination_by nodeCount x + nodeCount y

  theorem compareList_eq_eq_iff (xs ys : List Value) :
      compareList xs ys = .eq ↔ xs = ys := by
    cases xs with
    | nil => cases ys <;> simp [compareList]
    | cons x xs =>
        cases ys with
        | nil => simp [compareList]
        | cons y ys =>
            rw [compareList, Ordering.then_eq_eq, compareValue_eq_eq_iff,
              compareList_eq_eq_iff]
            simp
  termination_by listNodeCount xs + listNodeCount ys

  theorem compareObject_eq_eq_iff
      (xs ys : List (Value × Value)) :
      compareObject xs ys = .eq ↔ xs = ys := by
    cases xs with
    | nil => cases ys <;> simp [compareObject]
    | cons x xs =>
        cases ys with
        | nil => simp [compareObject]
        | cons y ys =>
            rcases x with ⟨kx, vx⟩
            rcases y with ⟨ky, vy⟩
            rw [compareObject, Ordering.then_eq_eq, compareValue_eq_eq_iff,
              Ordering.then_eq_eq, compareValue_eq_eq_iff,
              compareObject_eq_eq_iff]
            constructor
            · rintro ⟨hk, hv, ht⟩
              subst ky
              subst vy
              subst ys
              rfl
            · intro h
              have hp : (kx, vx) = (ky, vy) := (List.cons.inj h).1
              have ht : xs = ys := (List.cons.inj h).2
              exact ⟨congrArg Prod.fst hp, congrArg Prod.snd hp, ht⟩
  termination_by objectNodeCount xs + objectNodeCount ys
end

theorem compare_eq_iff_eq (x y : Value) :
    compare x y = .eq ↔ x = y :=
  compareValue_eq_eq_iff x y

mutual
  /-- `compareValue` is oriented: reversing its arguments swaps the result. -/
  theorem compareValue_swap (x y : Value) :
      (compareValue x y).swap = compareValue y x := by
    cases x <;> cases y <;>
      simp [compareValue, kindRank, Ordering.swap_then] <;>
      first
      | rfl
      | exact Batteries.OrientedCmp.symm _ _
      | exact compareList_swap _ _
      | exact compareObject_swap _ _
  termination_by nodeCount x + nodeCount y

  theorem compareList_swap (xs ys : List Value) :
      (compareList xs ys).swap = compareList ys xs := by
    cases xs with
    | nil => cases ys <;> rfl
    | cons x xs =>
        cases ys with
        | nil => rfl
        | cons y ys =>
            simp only [compareList, Ordering.swap_then]
            rw [compareValue_swap, compareList_swap]
  termination_by listNodeCount xs + listNodeCount ys

  theorem compareObject_swap
      (xs ys : List (Value × Value)) :
      (compareObject xs ys).swap = compareObject ys xs := by
    cases xs with
    | nil => cases ys <;> rfl
    | cons x xs =>
        cases ys with
        | nil => rfl
        | cons y ys =>
            rcases x with ⟨kx, vx⟩
            rcases y with ⟨ky, vy⟩
            simp only [compareObject, Ordering.swap_then]
            rw [compareValue_swap, compareValue_swap, compareObject_swap]
  termination_by objectNodeCount xs + objectNodeCount ys
end

theorem compare_of_kindRank_lt {x y : Value}
    (h : x.kindRank < y.kindRank) : compareValue x y = .lt := by
  cases x <;> cases y <;> simp [kindRank, compareValue] at h ⊢ <;> decide

/-- `Undefined` is the final constructor in the heterogeneous order. -/
@[simp] theorem compare_undefined (v : Value) :
    compareValue v .Undefined = if v = .Undefined then .eq else .lt := by
  cases v <;> simp [compareValue, kindRank] <;> decide

@[simp] theorem undefined_compare (v : Value) :
    compareValue .Undefined v = if v = .Undefined then .eq else .gt := by
  cases v <;> simp [compareValue, kindRank] <;> decide

theorem compare_lt_undefined {v : Value} (h : v ≠ .Undefined) :
    compareValue v .Undefined = .lt := by
  rw [compare_undefined, if_neg h]

end Value

end Regorus
