/-
Copyright (c) Microsoft Corporation.
Licensed under the MIT License.
-/

import Regorus.Value.Truth

/-!
# Bottom-free source values

`SourceValue` has no `Undefined` constructor.  More strongly, recursive
containers can contain only other `SourceValue`s, so bottom cannot be hidden
inside an array, set, object key, or object value.
-/

namespace Regorus

inductive SourceValue where
  | Null
  | Bool (b : Bool)
  | Number (n : RegoNumber)
  | String (s : String)
  | Array (a : List SourceValue)
  | Set (s : List SourceValue)
  | Object (o : List (SourceValue × SourceValue))
  deriving Repr

namespace SourceValue

mutual
  /-- Total embedding of the bottom-free source domain into semantic values. -/
  def embed : SourceValue → Value
    | .Null => .Null
    | .Bool b => .Bool b
    | .Number n => .Number n
    | .String s => .String s
    | .Array xs => .Array (embedList xs)
    | .Set xs => .Set (embedList xs)
    | .Object xs => .Object (embedObject xs)

  def embedList : List SourceValue → List Value
    | [] => []
    | x :: xs => embed x :: embedList xs

  def embedObject :
      List (SourceValue × SourceValue) → List (Value × Value)
    | [] => []
    | (k, v) :: xs => (embed k, embed v) :: embedObject xs
end

instance : Coe SourceValue Value := ⟨embed⟩

end SourceValue

namespace Value

mutual
  /-- No occurrence of `Undefined`, including recursively in containers. -/
  def BottomFree : Value → Prop
    | .Undefined => False
    | .Array xs | .Set xs => ListBottomFree xs
    | .Object xs => ObjectBottomFree xs
    | _ => True

  def ListBottomFree : List Value → Prop
    | [] => True
    | x :: xs => BottomFree x ∧ ListBottomFree xs

  def ObjectBottomFree : List (Value × Value) → Prop
    | [] => True
    | (k, v) :: xs =>
        BottomFree k ∧ BottomFree v ∧ ObjectBottomFree xs
end

theorem BottomFree.ne_undefined {v : Value} (h : BottomFree v) :
    v ≠ .Undefined := by
  intro hv
  subst v
  exact h

end Value

namespace SourceValue

mutual
  theorem embed_bottomFree (s : SourceValue) :
      Value.BottomFree s.embed := by
    cases s with
    | Null => trivial
    | Bool _ => trivial
    | Number _ => trivial
    | String _ => trivial
    | Array xs => exact embedList_bottomFree xs
    | Set xs => exact embedList_bottomFree xs
    | Object xs => exact embedObject_bottomFree xs
  termination_by sizeOf s

  theorem embedList_bottomFree (xs : List SourceValue) :
      Value.ListBottomFree (embedList xs) := by
    cases xs with
    | nil => simp [embedList, Value.ListBottomFree]
    | cons x xs =>
        exact ⟨embed_bottomFree x, embedList_bottomFree xs⟩
  termination_by sizeOf xs

  theorem embedObject_bottomFree
      (xs : List (SourceValue × SourceValue)) :
      Value.ObjectBottomFree (embedObject xs) := by
    cases xs with
    | nil => simp [embedObject, Value.ObjectBottomFree]
    | cons x xs =>
        rcases x with ⟨k, v⟩
        exact ⟨embed_bottomFree k, embed_bottomFree v,
          embedObject_bottomFree xs⟩
  termination_by sizeOf xs
end

/-- Every source value embeds to a defined (non-bottom) semantic value. -/
@[simp] theorem embed_ne_undefined (s : SourceValue) :
    s.embed ≠ Value.Undefined :=
  (embed_bottomFree s).ne_undefined

@[simp] theorem guardNotUndefined_embed (s : SourceValue) :
    guardNotUndefined s.embed = true :=
  (guardNotUndefined_spec s.embed).2 (embed_ne_undefined s)

end SourceValue

end Regorus
