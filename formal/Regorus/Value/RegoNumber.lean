/-
Copyright (c) Microsoft Corporation.
Licensed under the MIT License.
-/

import Regorus.Value.RawNumber

/-!
# Mathematical Regorus numbers

`RegoNumber` is the representation-independent number domain used for proofs.
Every finite IEEE-754 value embeds as its exact dyadic rational, while NaNs and
infinities have no image.  Unlike `RawNumber`, this type has ordinary
mathematical equality and a lawful linear order.
-/

namespace Regorus

/-- An exact, finite mathematical number. -/
structure RegoNumber where
  val : Rat
  deriving DecidableEq

namespace RegoNumber

instance : Repr RegoNumber where
  reprPrec n p := reprPrec n.val p

instance : LinearOrder RegoNumber :=
  LinearOrder.lift' RegoNumber.val <| by
    intro a b h
    cases a
    cases b
    simp_all

instance : Add RegoNumber := ⟨fun a b => ⟨a.val + b.val⟩⟩
instance : Sub RegoNumber := ⟨fun a b => ⟨a.val - b.val⟩⟩
instance : Mul RegoNumber := ⟨fun a b => ⟨a.val * b.val⟩⟩
instance : Neg RegoNumber := ⟨fun a => ⟨-a.val⟩⟩
instance (n : Nat) : OfNat RegoNumber n := ⟨⟨n⟩⟩

/-- Embed a mathematical integer. -/
def ofInt (i : Int) : RegoNumber :=
  ⟨(i : Rat)⟩

/-- Construct an exact rational, rejecting a zero denominator. -/
def ofFraction? (numerator denominator : Int) : Option RegoNumber :=
  if denominator = 0 then none else some ⟨Rat.divInt numerator denominator⟩

/-- Strict division.  Rego reports division by zero rather than assigning it a value. -/
def div? (a b : RegoNumber) : Option RegoNumber :=
  if b.val = 0 then none else some ⟨a.val / b.val⟩

/-- An exact integer projection. -/
def toInt? (n : RegoNumber) : Option Int :=
  if n.val.den = 1 then some n.val.num else none

def isInteger (n : RegoNumber) : Bool :=
  decide (n.val.den = 1)

/-- Forget the representation of a finite raw number. -/
def ofRaw? (n : RawNumber) : Option RegoNumber :=
  n.toRat?.map RegoNumber.mk

/-- A canonical raw integer when possible; otherwise the nearest binary64 value. -/
def toRaw (n : RegoNumber) : RawNumber :=
  match n.toInt? with
  | some i => RawNumber.normalizeInt i
  | none => .Float (F64Bits.fromRat n.val)

@[simp] theorem val_ofInt (i : Int) : (ofInt i).val = (i : Rat) := rfl

@[simp] theorem val_add (a b : RegoNumber) : (a + b).val = a.val + b.val := rfl

@[simp] theorem val_sub (a b : RegoNumber) : (a - b).val = a.val - b.val := rfl

@[simp] theorem val_mul (a b : RegoNumber) : (a * b).val = a.val * b.val := rfl

@[simp] theorem val_neg (a : RegoNumber) : (-a).val = -a.val := rfl

@[simp] theorem ofRaw_normalizeInt (i : Int) :
    ofRaw? (RawNumber.normalizeInt i) = some (ofInt i) := by
  simp [ofRaw?, ofInt]

@[simp] theorem div?_eq_none_iff (a b : RegoNumber) :
    div? a b = none ↔ b.val = 0 := by
  simp [div?]

@[simp] theorem ofRaw?_eq_none_iff (n : RawNumber) :
    ofRaw? n = none ↔ n.toRat? = none := by
  simp [ofRaw?]

theorem le_iff_val_le (a b : RegoNumber) : a ≤ b ↔ a.val ≤ b.val :=
  Iff.rfl

theorem lt_iff_val_lt (a b : RegoNumber) : a < b ↔ a.val < b.val :=
  Iff.rfl

end RegoNumber

end Regorus
