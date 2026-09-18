/-
Copyright (c) Microsoft Corporation.
Licensed under the MIT License.
-/

import Mathlib.Data.Multiset.Sort
import Regorus.Value.Value

/-!
# Canonical unordered collections

`Value.Set` and `Value.Object` store lists only as canonical representations
of unordered mathematical collections.  Set inputs are deduplicated and
sorted.  Object inputs use the same policy as repeated Rust `BTreeMap::insert`
calls: the last value supplied for a key wins, after which entries are sorted
by key (with the value comparison serving only as an unreachable tie-breaker
between distinct retained keys).
-/

namespace Regorus.Value

private theorem compareValue_eq_of_not_gt_not_gt {x y : Value}
    (hxy : compareValue x y ≠ .gt) (hyx : compareValue y x ≠ .gt) :
    compareValue x y = .eq := by
  cases h : compareValue x y with
  | lt =>
      have hs := compareValue_swap x y
      rw [h] at hs
      exact False.elim (hyx (by simpa using hs.symm))
  | eq => rfl
  | gt => exact False.elim (hxy h)

private theorem kindRank_le_of_compareValue_ne_gt {x y : Value}
    (h : compareValue x y ≠ .gt) : x.kindRank ≤ y.kindRank := by
  cases x <;> cases y <;>
    simp [compareValue, kindRank, LinearOrder.compare_eq_compareOfLessAndEq,
      compareOfLessAndEq] at h ⊢

private theorem then_ne_gt_iff (a b : Ordering) :
    a.then b ≠ .gt ↔ a ≠ .gt ∧ (a = .eq → b ≠ .gt) := by
  cases a <;> cases b <;> decide

private theorem compareValue_null :
    compareValue .Null .Null = .eq := rfl

private theorem compareValue_bool (x y : _root_.Bool) :
    compareValue (.Bool x) (.Bool y) = compare x y := rfl

private theorem compareValue_number (x y : RegoNumber) :
    compareValue (.Number x) (.Number y) = compare x y := rfl

private theorem compareValue_string (x y : _root_.String) :
    compareValue (.String x) (.String y) = compare x y := rfl

private theorem compareValue_array (xs ys : List Value) :
    compareValue (.Array xs) (.Array ys) = compareList xs ys := rfl

private theorem compareValue_set (xs ys : List Value) :
    compareValue (.Set xs) (.Set ys) = compareList xs ys := rfl

private theorem compareValue_object (xs ys : List (Value × Value)) :
    compareValue (.Object xs) (.Object ys) = compareObject xs ys := rfl

private theorem compareValue_undefined :
    compareValue .Undefined .Undefined = .eq := rfl

private theorem compareList_nil_left (ys : List Value) :
    compareList [] ys = if ys = [] then .eq else .lt := by
  cases ys <;> rfl

private theorem compareList_cons_nil (x : Value) (xs : List Value) :
    compareList (x :: xs) [] = .gt := rfl

private theorem compareList_cons_cons (x y : Value) (xs ys : List Value) :
    compareList (x :: xs) (y :: ys) =
      (compareValue x y).then (compareList xs ys) := rfl

private theorem compareObject_nil_left (ys : List (Value × Value)) :
    compareObject [] ys = if ys = [] then .eq else .lt := by
  cases ys <;> rfl

private theorem compareObject_cons_nil
    (x : Value × Value) (xs : List (Value × Value)) :
    compareObject (x :: xs) [] = .gt := by
  rcases x with ⟨k, v⟩
  rfl

private theorem compareObject_cons_cons
    (x y : Value × Value) (xs ys : List (Value × Value)) :
    compareObject (x :: xs) (y :: ys) =
      (compareValue x.1 y.1).then
        ((compareValue x.2 y.2).then (compareObject xs ys)) := by
  rcases x with ⟨kx, vx⟩
  rcases y with ⟨ky, vy⟩
  rfl

mutual
  private theorem compareValue_le_trans (x y z : Value)
      (hxy : compareValue x y ≠ .gt)
      (hyz : compareValue y z ≠ .gt) :
      compareValue x z ≠ .gt := by
    have hrxy := kindRank_le_of_compareValue_ne_gt hxy
    have hryz := kindRank_le_of_compareValue_ne_gt hyz
    by_cases hr : x.kindRank < z.kindRank
    · rw [compare_of_kindRank_lt hr]
      decide
    have hrxyEq : x.kindRank = y.kindRank := by omega
    have hryzEq : y.kindRank = z.kindRank := by omega
    cases x <;> cases y <;> cases z <;>
      simp [kindRank] at hrxyEq hryzEq <;>
      simp only [compareValue_null, compareValue_bool, compareValue_number,
        compareValue_string, compareValue_array, compareValue_set,
        compareValue_object, compareValue_undefined] at hxy hyz ⊢ <;>
      first
      | decide
      | exact Batteries.TransCmp.le_trans (cmp := compare) hxy hyz
      | exact compareList_le_trans _ _ _ hxy hyz
      | exact compareObject_le_trans _ _ _ hxy hyz
  termination_by sizeOf x + sizeOf y + sizeOf z
  decreasing_by
    all_goals subst_vars
    all_goals simp_wf
    all_goals omega

  private theorem compareObject_le_trans :
      ∀ (xs ys zs : List (Value × Value)),
        compareObject xs ys ≠ .gt →
        compareObject ys zs ≠ .gt →
        compareObject xs zs ≠ .gt
    | [], _, zs, _, _ => by cases zs <;> simp [compareObject_nil_left]
    | x :: xs, [], _, hxy, _ => by
        exact False.elim (hxy (compareObject_cons_nil x xs))
    | _, y :: ys, [], _, hyz => by
        exact False.elim (hyz (compareObject_cons_nil y ys))
    | x :: xs, y :: ys, z :: zs, hxy, hyz => by
        simp only [compareObject_cons_cons] at hxy hyz ⊢
        rw [then_ne_gt_iff] at hxy hyz ⊢
        simp only [then_ne_gt_iff] at hxy hyz ⊢
        refine
          ⟨compareValue_le_trans x.1 y.1 z.1 hxy.1 hyz.1, ?_⟩
        intro hkxz
        have hkxzEq : x.1 = z.1 :=
          (compareValue_eq_eq_iff x.1 z.1).1 hkxz
        have hyx : compareValue y.1 x.1 ≠ .gt := by
          simpa [hkxzEq] using hyz.1
        have hkxy : compareValue x.1 y.1 = .eq :=
          compareValue_eq_of_not_gt_not_gt hxy.1 hyx
        have hkxyEq : x.1 = y.1 :=
          (compareValue_eq_eq_iff x.1 y.1).1 hkxy
        have hkyzEq : y.1 = z.1 := hkxyEq.symm.trans hkxzEq
        have hxy' := hxy.2 ((compareValue_eq_eq_iff x.1 y.1).2 hkxyEq)
        have hyz' := hyz.2 ((compareValue_eq_eq_iff y.1 z.1).2 hkyzEq)
        refine
          ⟨compareValue_le_trans x.2 y.2 z.2 hxy'.1 hyz'.1, ?_⟩
        intro hvxz
        have hvxzEq : x.2 = z.2 :=
          (compareValue_eq_eq_iff x.2 z.2).1 hvxz
        have hyvx : compareValue y.2 x.2 ≠ .gt := by
          simpa [hvxzEq] using hyz'.1
        have hvxy : compareValue x.2 y.2 = .eq :=
          compareValue_eq_of_not_gt_not_gt hxy'.1 hyvx
        have hvxyEq : x.2 = y.2 :=
          (compareValue_eq_eq_iff x.2 y.2).1 hvxy
        have hvyzEq : y.2 = z.2 := hvxyEq.symm.trans hvxzEq
        exact compareObject_le_trans xs ys zs
          (hxy'.2 ((compareValue_eq_eq_iff x.2 y.2).2 hvxyEq))
          (hyz'.2 ((compareValue_eq_eq_iff y.2 z.2).2 hvyzEq))
  termination_by xs ys zs => sizeOf xs + sizeOf ys + sizeOf zs
  decreasing_by
    all_goals rcases x with ⟨kx, vx⟩
    all_goals rcases y with ⟨ky, vy⟩
    all_goals rcases z with ⟨kz, vz⟩
    all_goals simp_wf
    all_goals omega

  private theorem compareList_le_trans (xs ys zs : List Value)
      (hxy : compareList xs ys ≠ .gt)
      (hyz : compareList ys zs ≠ .gt) :
      compareList xs zs ≠ .gt := by
    cases xs with
    | nil => cases zs <;> simp [compareList_nil_left]
    | cons x xs =>
        cases ys with
        | nil => exact False.elim (hxy (compareList_cons_nil x xs))
        | cons y ys =>
            cases zs with
            | nil => exact False.elim (hyz (compareList_cons_nil y ys))
            | cons z zs =>
                simp only [compareList_cons_cons] at hxy hyz ⊢
                rw [then_ne_gt_iff] at hxy hyz ⊢
                refine ⟨compareValue_le_trans x y z hxy.1 hyz.1, ?_⟩
                intro hxz
                have hxzEq : x = z :=
                  (compareValue_eq_eq_iff x z).1 hxz
                subst z
                have hxyEq : compareValue x y = .eq :=
                  compareValue_eq_of_not_gt_not_gt hxy.1 hyz.1
                have hxyValue : x = y :=
                  (compareValue_eq_eq_iff x y).1 hxyEq
                subst y
                exact compareList_le_trans xs ys zs
                  (hxy.2 ((compareValue_eq_eq_iff x x).2 rfl))
                  (hyz.2 ((compareValue_eq_eq_iff x x).2 rfl))
  termination_by sizeOf xs + sizeOf ys + sizeOf zs
  decreasing_by
    all_goals subst_vars
    all_goals simp_wf
    all_goals omega
end

private instance : Batteries.TransCmp compareValue where
  symm := compareValue_swap
  le_trans := compareValue_le_trans _ _ _

/-- The non-strict order induced by the Rust-compatible value comparator. -/
def canonicalLE (x y : Value) : Prop :=
  compareValue x y ≠ .gt

private instance : DecidableRel canonicalLE := fun x y =>
  inferInstanceAs (Decidable (compareValue x y ≠ .gt))

private instance : IsTrans Value canonicalLE where
  trans _ _ _ := compareValue_le_trans _ _ _

private instance : IsAntisymm Value canonicalLE where
  antisymm x y hxy hyx :=
    (compareValue_eq_eq_iff x y).1
      (compareValue_eq_of_not_gt_not_gt hxy hyx)

private instance : IsTotal Value canonicalLE where
  total x y := by
    cases h : compareValue x y with
    | lt => exact Or.inl (by simp [canonicalLE, h])
    | eq => exact Or.inl (by simp [canonicalLE, h])
    | gt =>
        apply Or.inr
        simp only [canonicalLE]
        intro hyx
        have hs := compareValue_swap x y
        rw [h] at hs
        have hyxlt : compareValue y x = .lt := by simpa using hs.symm
        exact Ordering.noConfusion (hyxlt.symm.trans hyx)

/--
Canonical representation of an unordered set: discard multiplicity, then
sort by `compareValue`.
-/
def canonicalizeSet (xs : List Value) : List Value :=
  Multiset.sort canonicalLE (Multiset.dedup (xs : Multiset Value))

theorem canonicalizeSet_perm {xs ys : List Value} (h : xs.Perm ys) :
    canonicalizeSet xs = canonicalizeSet ys := by
  apply congrArg (Multiset.sort canonicalLE)
  apply congrArg Multiset.dedup
  exact Multiset.coe_eq_coe.mpr h

@[simp] theorem mem_canonicalizeSet {v : Value} {xs : List Value} :
    v ∈ canonicalizeSet xs ↔ v ∈ xs := by
  simp [canonicalizeSet]

theorem canonicalizeSet_sorted (xs : List Value) :
    (canonicalizeSet xs).Sorted canonicalLE :=
  Multiset.sort_sorted canonicalLE _

theorem canonicalizeSet_nodup (xs : List Value) :
    (canonicalizeSet xs).Nodup := by
  have hp : (canonicalizeSet xs).Perm xs.dedup := by
    simpa [canonicalizeSet, Multiset.coe_dedup] using
      List.mergeSort_perm xs.dedup
        (fun x y => decide (canonicalLE x y))
  exact hp.nodup_iff.mpr (List.nodup_dedup xs)

@[simp] theorem canonicalizeSet_idempotent (xs : List Value) :
    canonicalizeSet (canonicalizeSet xs) = canonicalizeSet xs := by
  apply List.eq_of_perm_of_sorted (r := canonicalLE)
  · change
      (Multiset.sort canonicalLE
        (Multiset.dedup (canonicalizeSet xs : Multiset Value))).Perm
        (canonicalizeSet xs)
    apply Multiset.coe_eq_coe.mp
    rw [Multiset.sort_eq]
    have hn : (canonicalizeSet xs : Multiset Value).Nodup :=
      canonicalizeSet_nodup xs
    rw [Multiset.dedup_eq_self.mpr hn]
  · exact canonicalizeSet_sorted _
  · exact canonicalizeSet_sorted _

/-- Construct a semantic set from elements in arbitrary input order. -/
def mkSet (xs : List Value) : Value :=
  .Set (canonicalizeSet xs)

theorem mkSet_perm {xs ys : List Value} (h : xs.Perm ys) :
    mkSet xs = mkSet ys := by
  rw [mkSet, mkSet, canonicalizeSet_perm h]

/-- Key-first, value-second comparison of object entries. -/
def compareEntry (x y : Value × Value) : Ordering :=
  (compareValue x.1 y.1).then (compareValue x.2 y.2)

private theorem compareEntry_swap (x y : Value × Value) :
    (compareEntry x y).swap = compareEntry y x := by
  simp [compareEntry, Ordering.swap_then, compareValue_swap]

private theorem compareEntry_eq_eq_iff (x y : Value × Value) :
    compareEntry x y = .eq ↔ x = y := by
  rcases x with ⟨kx, vx⟩
  rcases y with ⟨ky, vy⟩
  simp [compareEntry, Ordering.then_eq_eq, compareValue_eq_eq_iff,
    Prod.ext_iff]

private theorem compareEntry_le_trans (x y z : Value × Value)
    (hxy : compareEntry x y ≠ .gt)
    (hyz : compareEntry y z ≠ .gt) :
    compareEntry x z ≠ .gt := by
  simp only [compareEntry] at hxy hyz ⊢
  rw [then_ne_gt_iff] at hxy hyz ⊢
  refine ⟨compareValue_le_trans x.1 y.1 z.1 hxy.1 hyz.1, ?_⟩
  intro hxz
  have hxzEq : x.1 = z.1 := (compareValue_eq_eq_iff _ _).1 hxz
  have hyx : compareValue y.1 x.1 ≠ .gt := by
    simpa [hxzEq] using hyz.1
  have hxyEq := compareValue_eq_of_not_gt_not_gt hxy.1 hyx
  have hkxy : x.1 = y.1 := (compareValue_eq_eq_iff _ _).1 hxyEq
  have hkyz : y.1 = z.1 := hkxy.symm.trans hxzEq
  exact compareValue_le_trans x.2 y.2 z.2
    (hxy.2 ((compareValue_eq_eq_iff _ _).2 hkxy))
    (hyz.2 ((compareValue_eq_eq_iff _ _).2 hkyz))

private instance : Batteries.TransCmp compareEntry where
  symm := compareEntry_swap
  le_trans := compareEntry_le_trans _ _ _

/-- The non-strict key-first order used for canonical object entries. -/
def entryLE (x y : Value × Value) : Prop :=
  compareEntry x y ≠ .gt

private instance : DecidableRel entryLE := fun x y =>
  inferInstanceAs (Decidable (compareEntry x y ≠ .gt))

private instance : IsTrans (Value × Value) entryLE where
  trans _ _ _ := compareEntry_le_trans _ _ _

private instance : IsAntisymm (Value × Value) entryLE where
  antisymm x y hxy hyx := by
    apply (compareEntry_eq_eq_iff x y).1
    cases h : compareEntry x y with
    | lt =>
        have hs := compareEntry_swap x y
        rw [h] at hs
        exact False.elim (hyx (by simpa using hs.symm))
    | eq => rfl
    | gt => exact False.elim (hxy h)

private instance : IsTotal (Value × Value) entryLE where
  total x y := by
    cases h : compareEntry x y with
    | lt => exact Or.inl (by simp [entryLE, h])
    | eq => exact Or.inl (by simp [entryLE, h])
    | gt =>
        apply Or.inr
        simp only [entryLE]
        intro hyx
        have hs := compareEntry_swap x y
        rw [h] at hs
        have hyxlt : compareEntry y x = .lt := by simpa using hs.symm
        exact Ordering.noConfusion (hyxlt.symm.trans hyx)

/--
Remove duplicate object keys from right to left.  Thus the final occurrence of
each key is retained, exactly matching repeated `BTreeMap::insert` operations.
-/
def deduplicateObjectLast : List (Value × Value) → List (Value × Value)
  | [] => []
  | x :: xs =>
      let tail := deduplicateObjectLast xs
      if x.1 ∈ tail.map Prod.fst then tail else x :: tail

theorem deduplicateObjectLast_eq_self {xs : List (Value × Value)}
    (h : (xs.map Prod.fst).Nodup) :
    deduplicateObjectLast xs = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      have h' := List.nodup_cons.mp h
      simp [deduplicateObjectLast, ih h'.2, h'.1]

/--
Canonical representation of an object. Duplicate keys use last-write-wins;
the retained entries are sorted by key, then by value as a vacuous tie-break.
-/
def canonicalizeObject (xs : List (Value × Value)) : List (Value × Value) :=
  Multiset.sort entryLE (deduplicateObjectLast xs : Multiset (Value × Value))

theorem canonicalizeObject_perm {xs ys : List (Value × Value)}
    (hkeys : (xs.map Prod.fst).Nodup) (h : xs.Perm ys) :
    canonicalizeObject xs = canonicalizeObject ys := by
  have hkeys' : (ys.map Prod.fst).Nodup :=
    (h.map Prod.fst).nodup_iff.mp hkeys
  simp only [canonicalizeObject, deduplicateObjectLast_eq_self hkeys,
    deduplicateObjectLast_eq_self hkeys']
  apply congrArg (Multiset.sort entryLE)
  exact Multiset.coe_eq_coe.mpr h

theorem canonicalizeObject_sorted (xs : List (Value × Value)) :
    (canonicalizeObject xs).Sorted entryLE :=
  Multiset.sort_sorted entryLE _

theorem canonicalizeObject_sortedByKey (xs : List (Value × Value)) :
    (canonicalizeObject xs).Sorted
      (fun x y => compareValue x.1 y.1 ≠ .gt) := by
  apply (canonicalizeObject_sorted xs).imp
  intro x y h
  exact (then_ne_gt_iff _ _).1 h |>.1

/-- Construct a semantic object from entries in arbitrary input order. -/
def mkObject (xs : List (Value × Value)) : Value :=
  .Object (canonicalizeObject xs)

theorem mkObject_perm {xs ys : List (Value × Value)}
    (hkeys : (xs.map Prod.fst).Nodup) (h : xs.Perm ys) :
    mkObject xs = mkObject ys := by
  rw [mkObject, mkObject, canonicalizeObject_perm hkeys h]

end Regorus.Value
