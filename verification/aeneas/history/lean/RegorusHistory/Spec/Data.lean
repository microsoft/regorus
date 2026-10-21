/-
Copyright (c) Microsoft Corporation. All rights reserved.
Licensed under the MIT License.
-/
module

public import Mathlib.Algebra.Order.Ring.Rat
public import Mathlib.Tactic.NormNum

/-!
# Concrete semantic values

This domain is independent of generated Rust code. Finite numbers are exact
rationals and signed zeros coincide. NaNs keep their sign and payload, matching
`NumberView::cmp_values` in `src/verify/number_specs.rs`.
`DataWF` selects canonical, recursively well-formed collection representations;
there is no JSON, finite-number, or safe-integer restriction.
-/

@[expose] public section

namespace RegorusHistory.Spec

inductive Numeric where
  | negInf
  | finite (value : ℚ)
  | posInf
  | nan (negative : Bool) (payload : Nat)
  deriving DecidableEq

inductive Data where
  | null
  | bool (value : Bool)
  | number (value : Numeric)
  | string (value : String)
  | array (values : List Data)
  | set (values : List Data)
  | object (entries : List (Data × Data))
  | undefined

noncomputable instance : DecidableEq Data := Classical.decEq Data

/-- Signed payload order within a NaN class, as `NumberView::cmp_values` scales it. -/
def nanPayloadCompare (negative : Bool) (a b : Nat) : Ordering :=
  if negative then compare b a else compare a b

/-- Negative NaNs sit below `negInf`, positive NaNs above `posInf`. -/
def numericCompare : Numeric → Numeric → Ordering
  | .nan true a, .nan true b => nanPayloadCompare true a b
  | .nan true _, _ => .lt
  | _, .nan true _ => .gt
  | .negInf, .negInf => .eq
  | .negInf, _ => .lt
  | _, .negInf => .gt
  | .finite a, .finite b => if a < b then .lt else if a = b then .eq else .gt
  | .finite _, _ => .lt
  | _, .finite _ => .gt
  | .posInf, .posInf => .eq
  | .posInf, _ => .lt
  | _, .posInf => .gt
  | .nan _ a, .nan _ b => nanPayloadCompare false a b

/-- The declaration order of `Value` in `src/value/mod.rs`. -/
def Data.rank : Data → Nat
  | .null => 0
  | .bool _ => 1
  | .number _ => 2
  | .string _ => 3
  | .array _ => 4
  | .set _ => 5
  | .object _ => 6
  | .undefined => 7

mutual
  /-- Rust variant order, then lexicographic payload order. -/
  def dataCompare : Data → Data → Ordering
    | .null, .null => .eq
    | .bool a, .bool b => compare a b
    | .number a, .number b => numericCompare a b
    | .string a, .string b => compare a b
    | .array a, .array b => dataListCompare a b
    | .set a, .set b => dataListCompare a b
    | .object a, .object b => dataEntriesCompare a b
    | .undefined, .undefined => .eq
    | a, b => compare a.rank b.rank
  termination_by a b => sizeOf a + sizeOf b

  /-- Lexicographic list order; a proper prefix is smaller. -/
  def dataListCompare : List Data → List Data → Ordering
    | [], [] => .eq
    | [], _ :: _ => .lt
    | _ :: _, [] => .gt
    | a :: as, b :: bs =>
        match dataCompare a b with
        | .eq => dataListCompare as bs
        | result => result
  termination_by a b => sizeOf a + sizeOf b

  /-- Objects compare key/value pairs, with the key compared first. -/
  def dataEntriesCompare : List (Data × Data) → List (Data × Data) → Ordering
    | [], [] => .eq
    | [], _ :: _ => .lt
    | _ :: _, [] => .gt
    | (ka, va) :: as, (kb, vb) :: bs =>
        match dataCompare ka kb with
        | .eq =>
            match dataCompare va vb with
            | .eq => dataEntriesCompare as bs
            | result => result
        | result => result
  termination_by a b => sizeOf a + sizeOf b
end

mutual
  /-- Recursive canonical shape; strict collection order also enforces uniqueness. -/
  def DataWF : Data → Prop
    | .array values => dataListWF values
    | .set values =>
        dataListWF values ∧ values.Pairwise (fun a b => dataCompare a b = .lt)
    | .object entries =>
        dataEntriesWF entries ∧ entries.Pairwise (fun a b => dataCompare a.1 b.1 = .lt)
    | _ => True
  termination_by value => sizeOf value

  def dataListWF : List Data → Prop
    | [] => True
    | value :: rest => DataWF value ∧ dataListWF rest
  termination_by values => sizeOf values

  def dataEntriesWF : List (Data × Data) → Prop
    | [] => True
    | (key, value) :: rest => DataWF key ∧ DataWF value ∧ dataEntriesWF rest
  termination_by entries => sizeOf entries
end

/-- Exact unsigned dyadic magnitude, with a normal's implicit leading bit. -/
def binary64Magnitude (rawExponent fraction : Nat) : ℚ :=
  if rawExponent = 0 then
    (fraction : ℚ) / (2 : ℚ) ^ 1074
  else if rawExponent ≤ 1075 then
    ((2 ^ 52 + fraction : Nat) : ℚ) / (2 : ℚ) ^ (1075 - rawExponent)
  else
    (((2 ^ 52 + fraction) * 2 ^ (rawExponent - 1075) : Nat) : ℚ)

/-- Decode all 64 bits without host floating-point arithmetic.

Normals denote ±(2^52 + fraction) * 2^(rawExponent-1075);
subnormals denote ±fraction * 2^-1074.
-/
def numericOfBinary64 (bits : BitVec 64) : Numeric :=
  let raw := bits.toNat / 2 ^ 52 % 2048
  let fraction := bits.toNat % 2 ^ 52
  let negative := bits.toNat / 2 ^ 63 = 1
  if raw = 2047 then
    if fraction = 0 then (if negative then .negInf else .posInf) else .nan negative fraction
  else
    let magnitude := binary64Magnitude raw fraction
    .finite (if negative then -magnitude else magnitude)

/-- A NaN keeps its sign bit and payload. -/
theorem numericOfBinary64_nan {bits : BitVec 64}
    (exponent : bits.toNat / 2 ^ 52 % 2048 = 2047)
    (payload : bits.toNat % 2 ^ 52 ≠ 0) :
    numericOfBinary64 bits = .nan (bits.toNat / 2 ^ 63 = 1) (bits.toNat % 2 ^ 52) := by
  simp only [numericOfBinary64]
  rw [ite_eq_left exponent, ite_eq_right payload]

/-- Outside the special exponent, the lift is precisely the signed dyadic. -/
theorem numericOfBinary64_finite {bits : BitVec 64}
    (exponent : bits.toNat / 2 ^ 52 % 2048 ≠ 2047) :
    numericOfBinary64 bits = .finite
      (if bits.toNat / 2 ^ 63 = 1 then
        -binary64Magnitude (bits.toNat / 2 ^ 52 % 2048) (bits.toNat % 2 ^ 52)
      else binary64Magnitude (bits.toNat / 2 ^ 52 % 2048) (bits.toNat % 2 ^ 52)) := by
  simp only [numericOfBinary64]
  rw [ite_eq_right exponent]

/-- Only the visited value, not all its descendants, must be defined. -/
def Data.isDefined (value : Data) : Prop := value ≠ .undefined

/-- Return a defined value unchanged; an opaque collection may contain Undefined. -/
def definedData : Data → Option Data
  | .undefined => none
  | value => some value

/-- One independent path step. Object keys may be arbitrary semantic values. -/
noncomputable def selectMember : Data → Data → Option Data
  | .object entries, key =>
      (entries.find? (fun entry => decide (entry.1 = key))).map Prod.snd
  | .set values, key => values.find? (fun value => decide (value = key))
  | .array values, .number (.finite index) =>
      if 0 ≤ index ∧ index.den = 1 then values[index.num.toNat]? else none
  | _, _ => none

/-- Every visited Undefined, missing key, or unsupported traversal is absent.
The empty path selects precisely a defined root. -/
noncomputable def selectData : Data → List Data → Option Data
  | value, [] => definedData value
  | value, key :: path => (selectMember value key).bind (fun next => selectData next path)

@[simp] theorem numericCompare_refl (value : Numeric) : numericCompare value value = .eq := by
  cases value with
  | nan negative payload => cases negative <;> simp [numericCompare, nanPayloadCompare]
  | _ => simp [numericCompare]

/-- Equal semantic numbers cannot be distinguished by ordering. -/
theorem numericCompare_congr {a b c d : Numeric} (hab : a = b) (hcd : c = d) :
    numericCompare a c = numericCompare b d := by
  cases hab
  cases hcd
  rfl

/-- Semantic equality, not a concrete numeric representation, determines order. -/
theorem dataCompare_congr {a b c d : Data} (hab : a = b) (hcd : c = d) :
    dataCompare a c = dataCompare b d := by
  cases hab
  cases hcd
  rfl

/-- All path operations respect equality of canonical semantic values and keys. -/
theorem selectData_congr {a b : Data} {p q : List Data} (hab : a = b) (hpq : p = q) :
    selectData a p = selectData b q := by
  cases hab
  cases hpq
  rfl

@[simp] theorem selectData_nil (value : Data) : selectData value [] = definedData value := rfl

@[simp] theorem selectData_undefined (path : List Data) :
    selectData .undefined path = none := by
  cases path <;> rfl

/-- Selecting a collection does not recursively reject Undefined in its payload. -/
theorem selectData_nil_of_defined {value : Data} (h : value ≠ .undefined) :
    selectData value [] = some value := by
  cases value <;> simp_all [selectData, definedData]

/-- Successful path selection always ends at a defined value. -/
theorem selectData_some_defined {root value : Data} {path : List Data}
    (selected : selectData root path = some value) : value ≠ .undefined := by
  induction path generalizing root with
  | nil =>
      intro h
      subst value
      cases root <;> cases selected
  | cons key path ih =>
      cases h : selectMember root key with
      | none => simp [selectData, h] at selected
      | some next =>
          exact ih (by simpa [selectData, h] using selected)

/-! Exact decoding boundaries and path-selection checks, checked with this module. -/

example : numericOfBinary64 (BitVec.ofNat 64 0) = .finite 0 := by
  norm_num [numericOfBinary64, binary64Magnitude]

example : numericOfBinary64 (BitVec.ofNat 64 0x8000000000000000) =
    numericOfBinary64 (BitVec.ofNat 64 0) := by
  norm_num [numericOfBinary64, binary64Magnitude]

example : numericOfBinary64 (BitVec.ofNat 64 0x3ff0000000000000) = .finite 1 := by
  norm_num [numericOfBinary64, binary64Magnitude]

example : numericOfBinary64 (BitVec.ofNat 64 0x4340000000000000) =
    .finite (9007199254740992 : ℚ) := by
  norm_num [numericOfBinary64, binary64Magnitude]

example : numericOfBinary64 (BitVec.ofNat 64 0x4340000000000002) =
    .finite (9007199254740996 : ℚ) := by
  norm_num [numericOfBinary64, binary64Magnitude]

example : numericOfBinary64 (BitVec.ofNat 64 0x7ff0000000000000) = .posInf := by decide

example : numericOfBinary64 (BitVec.ofNat 64 0xfff0000000000000) = .negInf := by decide

example : numericOfBinary64 (BitVec.ofNat 64 0x7ff0000000000001) ≠
    numericOfBinary64 (BitVec.ofNat 64 0xfff0000000000001) := by decide

example : numericOfBinary64 (BitVec.ofNat 64 0x7ff8000000000000) ≠
    numericOfBinary64 (BitVec.ofNat 64 0x7ff8000000000001) := by decide

example : numericCompare (numericOfBinary64 (BitVec.ofNat 64 0xfff8000000000000)) .negInf = .lt := by
  decide

example : numericCompare .posInf (numericOfBinary64 (BitVec.ofNat 64 0x7ff8000000000000)) = .lt := by
  decide

example : numericOfBinary64 (BitVec.ofNat 64 1) =
    .finite ((1 : ℚ) / (2 : ℚ) ^ 1074) := rfl

example : numericOfBinary64 (BitVec.ofNat 64 0x0010000000000000) =
    .finite (((2 ^ 52 : Nat) : ℚ) / (2 : ℚ) ^ 1074) := rfl

example : selectData (.array [.undefined]) [] = some (.array [.undefined]) := rfl

example : selectData (.array [.undefined]) [.number (.finite 0)] = none := by
  norm_num [selectData, selectMember, definedData]

theorem selectData_array_nonintegral (values : List Data) (index : ℚ)
    (fractional : index.den ≠ 1) :
    selectData (.array values) [.number (.finite index)] = none := by
  simp [selectData, selectMember, fractional]

example : selectData (.object [(.array [.null], .bool true)]) [.array [.null]] =
    some (.bool true) := by simp [selectData, selectMember, definedData]

example : selectData (.set [.null, .bool true]) [.bool true] = some (.bool true) := by
  simp [selectData, selectMember, definedData]

end RegorusHistory.Spec
