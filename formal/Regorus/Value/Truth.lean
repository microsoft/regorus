/-
Copyright (c) Microsoft Corporation.
Licensed under the MIT License.
-/

import Regorus.Value.Value

/-!
# Rego truth and bottom propagation

Regorus does not identify `Undefined` with Boolean false.  They agree at a
condition guard, but differ at guards that test definedness and remain distinct
values throughout evaluation.  The definitions below mirror the RVM `Not` and
`Guard` instruction cases.
-/

namespace Regorus

/-- Rego/RVM truthiness: only `false` and bottom are not truthy. -/
def isTruthy : Value → _root_.Bool
  | .Bool false | .Undefined => false
  | _ => true

/-- RVM logical negation, including its asymmetric treatment of bottom. -/
def notRvm : Value → Value
  | .Undefined | .Bool false => .Bool true
  | _ => .Bool false

/-- Condition guard: reject exactly bottom and Boolean false. -/
def guardCondition : Value → _root_.Bool
  | .Undefined | .Bool false => false
  | _ => true

/-- Definedness guard: reject bottom, but accept every ordinary value. -/
def guardNotUndefined : Value → _root_.Bool
  | .Undefined => false
  | _ => true

/-- Strict binary bottom lifting used by ordinary two-argument operations. -/
def lift₂ (f : Value → Value → Value) : Value → Value → Value
  | .Undefined, _ | _, .Undefined => .Undefined
  | x, y => f x y

@[simp] theorem isTruthy_false : isTruthy (.Bool false) = false := rfl
@[simp] theorem isTruthy_true : isTruthy (.Bool true) = true := rfl
@[simp] theorem isTruthy_undefined : isTruthy .Undefined = false := rfl

theorem isTruthy_eq_false_iff (v : Value) :
    isTruthy v = false ↔ v = .Bool false ∨ v = .Undefined := by
  cases v <;> simp [isTruthy]
  case Bool b => cases b <;> simp [isTruthy]

theorem isTruthy_eq_true_iff (v : Value) :
    isTruthy v = true ↔ v ≠ .Bool false ∧ v ≠ .Undefined := by
  cases v <;> simp [isTruthy]
  case Bool b => cases b <;> simp [isTruthy]

@[simp] theorem guardCondition_eq_isTruthy (v : Value) :
    guardCondition v = isTruthy v := by
  cases v <;> try rfl
  case Bool b => cases b <;> rfl

theorem guardCondition_spec (v : Value) :
    guardCondition v = true ↔ v ≠ .Undefined ∧ v ≠ .Bool false := by
  rw [guardCondition_eq_isTruthy, isTruthy_eq_true_iff]
  tauto

theorem guardNotUndefined_spec (v : Value) :
    guardNotUndefined v = true ↔ v ≠ .Undefined := by
  cases v <;> simp [guardNotUndefined]

theorem guardNotUndefined_eq_false_iff (v : Value) :
    guardNotUndefined v = false ↔ v = .Undefined := by
  cases v <;> simp [guardNotUndefined]

theorem guardCondition_implies_defined {v : Value}
    (h : guardCondition v = true) : guardNotUndefined v = true := by
  have hv := (guardCondition_spec v).1 h
  exact (guardNotUndefined_spec v).2 hv.1

@[simp] theorem notRvm_eq_boolean_not (v : Value) :
    notRvm v = .Bool (!isTruthy v) := by
  cases v <;> try rfl
  case Bool b => cases b <;> rfl

theorem notRvm_true_iff (v : Value) :
    notRvm v = .Bool true ↔ v = .Undefined ∨ v = .Bool false := by
  cases v <;> simp [notRvm]
  case Bool b => cases b <;> simp [notRvm]

theorem notRvm_false_iff (v : Value) :
    notRvm v = .Bool false ↔ v ≠ .Undefined ∧ v ≠ .Bool false := by
  rw [notRvm_eq_boolean_not]
  cases v <;> simp [isTruthy]
  case Bool b => cases b <;> simp [isTruthy]

@[simp] theorem isTruthy_notRvm (v : Value) :
    isTruthy (notRvm v) = !isTruthy v := by
  rw [notRvm_eq_boolean_not]
  cases isTruthy v <;> rfl

/-- Negating twice Booleanizes a value rather than recovering a non-Boolean operand. -/
@[simp] theorem notRvm_twice (v : Value) :
    notRvm (notRvm v) = .Bool (isTruthy v) := by
  cases v <;> try rfl
  case Bool b => cases b <;> rfl

@[simp] theorem lift₂_left_bottom (f : Value → Value → Value) (v : Value) :
    lift₂ f .Undefined v = .Undefined := by
  cases v <;> rfl

@[simp] theorem lift₂_right_bottom (f : Value → Value → Value) (v : Value) :
    lift₂ f v .Undefined = .Undefined := by
  cases v <;> rfl

theorem lift₂_of_defined (f : Value → Value → Value) {x y : Value}
    (hx : x ≠ .Undefined) (hy : y ≠ .Undefined) :
    lift₂ f x y = f x y := by
  cases x <;> cases y <;> simp_all [lift₂]

theorem lift₂_eq_undefined_iff (f : Value → Value → Value) (x y : Value) :
    lift₂ f x y = .Undefined ↔
      x = .Undefined ∨ y = .Undefined ∨ f x y = .Undefined := by
  cases x <;> cases y <;> simp [lift₂]

theorem lift₂_defined (f : Value → Value → Value) {x y : Value}
    (hx : x ≠ .Undefined) (hy : y ≠ .Undefined)
    (hf : f x y ≠ .Undefined) :
    lift₂ f x y ≠ .Undefined := by
  rw [lift₂_of_defined f hx hy]
  exact hf

theorem lift₂_comm (f : Value → Value → Value)
    (hcomm : ∀ x y, f x y = f y x) (x y : Value) :
    lift₂ f x y = lift₂ f y x := by
  cases x <;> cases y <;> simp [lift₂, hcomm]

end Regorus
