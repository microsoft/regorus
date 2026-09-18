/-
Copyright (c) Microsoft Corporation.
Licensed under the MIT License.
-/

import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.BitVec
import Mathlib.Tactic.NormNum

/-!
# Raw Regorus numbers

This module models the representation-sensitive `Number` implementation in
`src/number.rs`.  `F64Bits` stores the complete IEEE-754 binary64 bit pattern;
in particular, signed zeroes and all NaN payloads remain distinguishable.

`RawNumber.rustEq` and `RawNumber.rustCompare` deliberately model the Rust
implementation rather than Lean equality.  Consequently `rustCompare` maps an
unordered NaN comparison to `Ordering.eq`, while `rustEq` remains false.  No
lawful order instance is therefore attached to `RawNumber`.
-/

namespace Regorus

/-- A signed 64-bit integer, represented intrinsically by its mathematical value. -/
structure Int64 where
  val : Int
  isValid : -(2 ^ 63 : Int) ≤ val ∧ val < (2 ^ 63 : Int)

namespace Int64

instance : DecidableEq Int64 := fun x y =>
  decidable_of_iff (x.val = y.val) <| by
    constructor
    · intro h
      cases x
      cases y
      simp_all
    · exact congrArg Int64.val

instance : Repr Int64 where
  reprPrec i _ := repr i.val

/-- The mathematical value represented by an `Int64`. -/
@[coe] def toInt (i : Int64) : Int := i.val

instance : Coe Int64 Int := ⟨toInt⟩

/-- Checked construction, corresponding to `i64::try_from`. -/
def ofInt? (i : Int) : Option Int64 :=
  if h : -(2 ^ 63 : Int) ≤ i ∧ i < (2 ^ 63 : Int) then
    some ⟨i, h⟩
  else
    none

/-- Zero in the signed 64-bit representation. -/
def zero : Int64 :=
  ⟨0, by decide⟩

@[simp] theorem toInt_zero : (zero : Int) = 0 := rfl

instance : LinearOrder Int64 :=
  LinearOrder.lift' Int64.val <| by
    intro a b h
    cases a
    cases b
    simp_all

end Int64

/-- A bit-exact IEEE-754 binary64 value. -/
structure F64Bits where
  bits : UInt64
  deriving DecidableEq, Repr

namespace F64Bits

def significandWidth : Nat := 52
def exponentWidth : Nat := 11
def exponentBias : Nat := 1023
def maxExponentField : Nat := 2047
def signWeight : Nat := 2 ^ 63
def exponentWeight : Nat := 2 ^ significandWidth
def significandLimit : Nat := 2 ^ significandWidth
def precisionLimit : Nat := 2 ^ 53

/-- Construct a bit pattern from sign, exponent, and fraction fields.
Inputs are masked to their respective field widths. -/
def ofFields (negative : Bool) (exponent fraction : Nat) : F64Bits :=
  ⟨UInt64.ofNat
    ((if negative then signWeight else 0) +
      (exponent % (2 ^ exponentWidth)) * exponentWeight +
      fraction % significandLimit)⟩

/-- The sign bit (`true` means negative). -/
def sign (f : F64Bits) : Bool :=
  decide (signWeight ≤ f.bits.toNat)

/-- The eleven raw exponent bits. -/
def exponent (f : F64Bits) : Nat :=
  (f.bits.toNat / exponentWeight) % (2 ^ exponentWidth)

/-- The 52 raw trailing-significand bits. -/
def fraction (f : F64Bits) : Nat :=
  f.bits.toNat % significandLimit

def positiveZero : F64Bits := ofFields false 0 0
def negativeZero : F64Bits := ofFields true 0 0
def positiveInfinity : F64Bits := ofFields false maxExponentField 0
def negativeInfinity : F64Bits := ofFields true maxExponentField 0
def quietNaN : F64Bits := ofFields false maxExponentField (2 ^ 51)

/-- Exact semantic classification of a binary64 bit pattern. -/
inductive Decoded where
  /-- Finite mathematical value; `negativeZero` records the sign when `value = 0`. -/
  | finite (value : Rat) (negativeZero : Bool)
  | infinity (negative : Bool)
  | nan
  deriving DecidableEq, Repr

/-- An exact rational power of two. -/
def twoPowRat : Int → Rat
  | .ofNat n => (2 ^ n : Nat)
  | .negSucc n => 1 / (2 ^ (n + 1) : Nat)

/-- Decode a binary64 pattern without passing through a host floating-point value. -/
def decode (f : F64Bits) : Decoded :=
  let e := f.exponent
  let m := f.fraction
  let neg := f.sign
  if e = maxExponentField then
    if m = 0 then .infinity neg else .nan
  else
    let significand := if e = 0 then m else significandLimit + m
    let scale : Int :=
      if e = 0 then -1074 else Int.ofNat e - 1075
    let magnitude : Rat := (significand : Rat) * twoPowRat scale
    let value := if neg then -magnitude else magnitude
    .finite value (neg && significand = 0)

def isNaN (f : F64Bits) : Bool :=
  match f.decode with
  | .nan => true
  | _ => false

def isFinite (f : F64Bits) : Bool :=
  match f.decode with
  | .finite _ _ => true
  | _ => false

def isZero (f : F64Bits) : Bool :=
  match f.decode with
  | .finite q _ => decide (q = 0)
  | _ => false

/-- IEEE equality: NaNs compare unequal and signed zeroes compare equal. -/
def ieeeEq (a b : F64Bits) : Bool :=
  match a.decode, b.decode with
  | .nan, _ | _, .nan => false
  | .infinity sa, .infinity sb => decide (sa = sb)
  | .finite x _, .finite y _ => decide (x = y)
  | _, _ => false

/-- IEEE partial comparison, with `none` for every comparison involving NaN. -/
def partialCompare (a b : F64Bits) : Option Ordering :=
  match a.decode, b.decode with
  | .nan, _ | _, .nan => none
  | .infinity true, .infinity true
  | .infinity false, .infinity false => some .eq
  | .infinity true, _ | _, .infinity false => some .lt
  | .infinity false, _ | _, .infinity true => some .gt
  | .finite x _, .finite y _ => some (compare x y)

/-- Round `n / d` to an integer, using round-to-nearest, ties-to-even. -/
private def roundDivEven (n d : Nat) : Nat :=
  if d = 0 then
    0
  else
    let q := n / d
    let r := n % d
    if 2 * r < d then
      q
    else if d < 2 * r then
      q + 1
    else if q % 2 = 0 then
      q
    else
      q + 1

/-- Decide whether `n / d < 2^e`, without approximate arithmetic. -/
private def ratioLtPowTwo (n d : Nat) : Int → Bool
  | .ofNat e => decide (n < d * 2 ^ e)
  | .negSucc e => decide (n * 2 ^ (e + 1) < d)

/-- `⌊log₂ (n / d)⌋` for positive `n` and `d`. -/
private def floorLogTwoRatio (n d : Nat) : Int :=
  let candidate := Int.ofNat n.log2 - Int.ofNat d.log2
  if ratioLtPowTwo n d candidate then candidate - 1 else candidate

/-- Round `(n / d) * 2^shift` to the nearest-even natural number. -/
private def roundScaled (n d : Nat) : Int → Nat
  | .ofNat shift => roundDivEven (n * 2 ^ shift) d
  | .negSucc shift => roundDivEven n (d * 2 ^ (shift + 1))

/-- Encode a positive rational magnitude with the requested sign. -/
private def encodeMagnitude (negative : Bool) (n d : Nat) : F64Bits :=
  if n = 0 then
    ofFields negative 0 0
  else
    let e := floorLogTwoRatio n d
    if e < -1022 then
      let m := roundScaled n d 1074
      if m = 0 then
        ofFields negative 0 0
      else if significandLimit ≤ m then
        ofFields negative 1 0
      else
        ofFields negative 0 m
    else
      let rounded := roundScaled n d (52 - e)
      let carry := rounded = precisionLimit
      let e' := if carry then e + 1 else e
      let significand := if carry then significandLimit else rounded
      if 1023 < e' then
        ofFields negative maxExponentField 0
      else
        ofFields negative (e' + 1023).toNat (significand - significandLimit)

/-- Correctly round an exact rational to binary64 (nearest, ties-to-even). -/
def fromRat (q : Rat) (negativeZero : Bool := false) : F64Bits :=
  if q = 0 then
    ofFields negativeZero 0 0
  else
    encodeMagnitude (q < 0) q.num.natAbs q.den

def fromInt (i : Int) : F64Bits :=
  fromRat (i : Rat)

/-- Toggle the IEEE sign bit, including for NaNs and signed zeroes. -/
def negate (f : F64Bits) : F64Bits :=
  ofFields (!f.sign) f.exponent f.fraction

private def finiteSign (q : Rat) (negativeZero : Bool) : Bool :=
  if q = 0 then negativeZero else q < 0

/-- IEEE-754 addition, specified through exact rationals and nearest-even rounding. -/
def add (a b : F64Bits) : F64Bits :=
  match a.decode, b.decode with
  | .nan, _ | _, .nan => quietNaN
  | .infinity sa, .infinity sb =>
      if sa = sb then ofFields sa maxExponentField 0 else quietNaN
  | .infinity sa, _ | _, .infinity sa => ofFields sa maxExponentField 0
  | .finite x zx, .finite y zy =>
      let q := x + y
      fromRat q (q = 0 && zx && zy)

def sub (a b : F64Bits) : F64Bits :=
  add a b.negate

/-- IEEE-754 multiplication, specified through exact rationals and nearest-even rounding. -/
def mul (a b : F64Bits) : F64Bits :=
  match a.decode, b.decode with
  | .nan, _ | _, .nan => quietNaN
  | .infinity sa, .infinity sb =>
      ofFields (xor sa sb) maxExponentField 0
  | .infinity sa, .finite q z | .finite q z, .infinity sa =>
      if q = 0 then quietNaN
      else ofFields (xor sa (finiteSign q z)) maxExponentField 0
  | .finite x zx, .finite y zy =>
      let negative := xor (finiteSign x zx) (finiteSign y zy)
      fromRat (x * y) (x * y = 0 && negative)

/-- IEEE-754 division.  `RawNumber.div` rejects zero divisors before using this operation. -/
def div (a b : F64Bits) : F64Bits :=
  match a.decode, b.decode with
  | .nan, _ | _, .nan => quietNaN
  | .infinity _, .infinity _ => quietNaN
  | .infinity sa, .finite y zy =>
      if y = 0 then quietNaN
      else ofFields (xor sa (finiteSign y zy)) maxExponentField 0
  | .finite x zx, .infinity sb =>
      ofFields (xor (finiteSign x zx) sb) 0 0
  | .finite x zx, .finite y zy =>
      let negative := xor (finiteSign x zx) (finiteSign y zy)
      if y = 0 then
        if x = 0 then quietNaN else ofFields negative maxExponentField 0
      else
        fromRat (x / y) (x = 0 && negative)

/-- Rust's `float_to_small_bigint`: exact, finite integral floats in `[-2^53, 2^53]`. -/
def toSmallInt? (f : F64Bits) : Option Int :=
  match f.decode with
  | .finite q _ =>
      if q.den = 1 ∧ q.num.natAbs ≤ precisionLimit then some q.num else none
  | _ => none

@[simp] theorem decode_positiveZero : positiveZero.decode = .finite 0 false := by
  change decode ⟨UInt64.ofNat 0⟩ = .finite 0 false
  simp only [decode, exponent, fraction, sign]
  rw [show (UInt64.ofNat 0).toNat = 0 from
    UInt64.toNat_ofNat_of_lt (by norm_num)]
  norm_num [exponentWeight, significandWidth, exponentWidth,
    maxExponentField, significandLimit, signWeight, twoPowRat]

@[simp] theorem decode_negativeZero : negativeZero.decode = .finite 0 true := by
  change decode ⟨UInt64.ofNat 9223372036854775808⟩ = .finite 0 true
  simp only [decode, exponent, fraction, sign]
  rw [show (UInt64.ofNat 9223372036854775808).toNat =
      9223372036854775808 from UInt64.toNat_ofNat_of_lt (by norm_num)]
  norm_num [exponentWeight, significandWidth, exponentWidth,
    maxExponentField, significandLimit, signWeight, twoPowRat]

@[simp] theorem decode_positiveInfinity :
    positiveInfinity.decode = .infinity false := by
  decide

@[simp] theorem decode_negativeInfinity :
    negativeInfinity.decode = .infinity true := by
  decide

@[simp] theorem decode_quietNaN : quietNaN.decode = .nan := by
  decide

end F64Bits

/-- The four representation variants of Rust's `Number`. -/
inductive RawNumber where
  | UInt (u : UInt64)
  | Int (i : Int64)
  | BigInt (b : Int)
  | Float (f : F64Bits)
  deriving DecidableEq, Repr

namespace RawNumber

def safeInteger : Nat := 2 ^ 53
def maxUInt64 : ℤ := Int.ofNat (UInt64.size - 1)

/-- Canonicalize an integer exactly as `Number::from_bigint_owned`. -/
def normalizeInt (i : ℤ) : RawNumber :=
  if i = 0 then
    .Int Int64.zero
  else if 0 < i ∧ i ≤ maxUInt64 then
    .UInt (UInt64.ofNat i.toNat)
  else
    match Int64.ofInt? i with
    | some j => .Int j
    | none => .BigInt i

/-- Exact integer conversion used by equality, ordering, modulo, and bit operations. -/
def toExactInt? : RawNumber → Option ℤ
  | .UInt u => some (Int.ofNat u.toNat)
  | .Int i => some i.val
  | .BigInt i => some i
  | .Float f => f.toSmallInt?

/-- Exact rational value, undefined for infinities and NaNs. -/
def toRat? : RawNumber → Option Rat
  | .UInt u => some (Int.ofNat u.toNat : Rat)
  | .Int i => some (i.val : Rat)
  | .BigInt i => some (i : Rat)
  | .Float f =>
      match f.decode with
      | .finite q _ => some q
      | _ => none

/-- Rust's lossy conversion used whenever a floating-point operand participates. -/
def toF64Lossy : RawNumber → F64Bits
  | .UInt u => F64Bits.fromInt (Int.ofNat u.toNat)
  | .Int i => F64Bits.fromInt i.val
  | .BigInt i => F64Bits.fromInt i
  | .Float f => f

def isFloat : RawNumber → Bool
  | .Float _ => true
  | _ => false

def isZero : RawNumber → Bool
  | .UInt u => decide (u.toNat = 0)
  | .Int i => decide (i.val = 0)
  | .BigInt i => decide (i = 0)
  | .Float f => f.isZero

/-- Normalize a float to an integer exactly when Rust's `normalize_float` does. -/
def normalizeFloat (f : F64Bits) : RawNumber :=
  match f.toSmallInt? with
  | some i => normalizeInt i
  | none => .Float f

/-- Representation-insensitive equality implemented by `Number::eq`. -/
def rustEq (a b : RawNumber) : Bool :=
  match a.toExactInt?, b.toExactInt? with
  | some x, some y => decide (x = y)
  | _, _ => F64Bits.ieeeEq a.toF64Lossy b.toF64Lossy

/-- Total comparator implemented by `Number::cmp`; unordered NaNs map to equality. -/
def rustCompare (a b : RawNumber) : Ordering :=
  match a.toExactInt?, b.toExactInt? with
  | some x, some y => compare x y
  | _, _ => (F64Bits.partialCompare a.toF64Lossy b.toF64Lossy).getD .eq

inductive Error where
  | divisionByZero
  | moduloOnFloatingPoint
  deriving DecidableEq, Repr

def add (a b : RawNumber) : RawNumber :=
  if a.isFloat || b.isFloat then
    normalizeFloat (F64Bits.add a.toF64Lossy b.toF64Lossy)
  else
    match a.toExactInt?, b.toExactInt? with
    | some x, some y => normalizeInt (x + y)
    | _, _ => .Float F64Bits.quietNaN

def sub (a b : RawNumber) : RawNumber :=
  if a.isFloat || b.isFloat then
    normalizeFloat (F64Bits.sub a.toF64Lossy b.toF64Lossy)
  else
    match a.toExactInt?, b.toExactInt? with
    | some x, some y => normalizeInt (x - y)
    | _, _ => .Float F64Bits.quietNaN

def mul (a b : RawNumber) : RawNumber :=
  if a.isFloat || b.isFloat then
    normalizeFloat (F64Bits.mul a.toF64Lossy b.toF64Lossy)
  else
    match a.toExactInt?, b.toExactInt? with
    | some x, some y => normalizeInt (x * y)
    | _, _ => .Float F64Bits.quietNaN

/-- Division follows `Number::divide`: exact integral quotients stay integral. -/
def div (a b : RawNumber) : Except Error RawNumber :=
  if b.isZero then
    .error .divisionByZero
  else if a.isFloat || b.isFloat then
    .ok (.Float (F64Bits.div a.toF64Lossy b.toF64Lossy))
  else
    match a.toExactInt?, b.toExactInt? with
    | some x, some y =>
        if y ∣ x then
          .ok (normalizeInt (x / y))
        else
          .ok (.Float (F64Bits.div a.toF64Lossy b.toF64Lossy))
    | _, _ => .ok (.Float F64Bits.quietNaN)

/-- Rust remainder (quotient truncated toward zero). -/
def rustRem (a b : ℤ) : ℤ :=
  a - a.tdiv b * b

/-- Modulo accepts integers and only the small integral floats accepted by Rust. -/
def modulo (a b : RawNumber) : Except Error RawNumber :=
  match a.toExactInt?, b.toExactInt? with
  | some x, some y =>
      if y = 0 then
        .error .divisionByZero
      else
        .ok (normalizeInt (rustRem x y))
  | _, _ => .error .moduloOnFloatingPoint

/-- Strict conversion corresponding to `Number::as_u64`. -/
def asUInt64? (n : RawNumber) : Option UInt64 :=
  n.toExactInt?.bind fun i =>
    if 0 ≤ i ∧ i ≤ maxUInt64 then some (UInt64.ofNat i.toNat) else none

/-- Strict conversion corresponding to `Number::as_i64`. -/
def asInt64? (n : RawNumber) : Option Int64 :=
  n.toExactInt?.bind Int64.ofInt?

/-- Strict conversion corresponding to `Number::as_f64`. -/
def asF64? : RawNumber → Option F64Bits
  | .Float f => if f.isFinite then some f else none
  | .UInt u =>
      if u.toNat ≤ safeInteger then some (F64Bits.fromInt (Int.ofNat u.toNat)) else none
  | .Int i =>
      if i.val.natAbs ≤ safeInteger then some (F64Bits.fromInt i.val) else none
  | .BigInt i =>
      if i.natAbs < safeInteger then some (F64Bits.fromInt i) else none

@[simp] theorem toExactInt_normalizeInt (i : ℤ) :
    (normalizeInt i).toExactInt? = some i := by
  simp only [normalizeInt]
  split
  · rename_i h
    subst i
    simp [toExactInt?, Int64.zero]
  · split
    · rename_i h
      simp only [toExactInt?]
      have hnonneg : 0 ≤ i := h.1.le
      have hcast : Int.ofNat i.toNat = i := Int.toNat_of_nonneg hnonneg
      have hi' : i.toNat ≤ UInt64.size - 1 := by
        apply Int.ofNat_le.mp
        simpa [hcast, maxUInt64] using h.2
      have hi : i.toNat < UInt64.size := by
        omega
      rw [UInt64.toNat_ofNat_of_lt hi, hcast]
    · cases h : Int64.ofInt? i with
      | none => simp [toExactInt?, h]
      | some j =>
          simp only [toExactInt?, h, Option.some.injEq]
          simp only [Int64.ofInt?] at h
          split at h
          · have hj := Option.some.inj h
            exact (congrArg Int64.val hj).symm
          · contradiction

@[simp] theorem toRat_normalizeInt (i : ℤ) :
    (normalizeInt i).toRat? = some (i : Rat) := by
  simp only [normalizeInt]
  split
  · rename_i h
    subst i
    simp [toRat?, Int64.zero]
  · split
    · rename_i h
      simp only [toRat?]
      have hnonneg : 0 ≤ i := h.1.le
      have hcast : Int.ofNat i.toNat = i := Int.toNat_of_nonneg hnonneg
      have hi' : i.toNat ≤ UInt64.size - 1 := by
        apply Int.ofNat_le.mp
        simpa [hcast, maxUInt64] using h.2
      have hi : i.toNat < UInt64.size := by
        omega
      rw [UInt64.toNat_ofNat_of_lt hi, hcast]
    · cases h : Int64.ofInt? i with
      | none => simp [toRat?, h]
      | some j =>
          simp only [toRat?, h, Option.some.injEq]
          simp only [Int64.ofInt?] at h
          split at h
          · have hj := Option.some.inj h
            exact (congrArg (fun z : Int64 => (z.val : Rat)) hj).symm
          · contradiction

@[simp] theorem add_integer_semantics
    {a b : RawNumber} {x y : ℤ}
    (ha : a.isFloat = false) (hb : b.isFloat = false)
    (hax : a.toExactInt? = some x) (hby : b.toExactInt? = some y) :
    (add a b).toExactInt? = some (x + y) := by
  simp [add, ha, hb, hax, hby]

@[simp] theorem rustEq_self_of_not_nan (n : RawNumber)
    (h : F64Bits.isNaN n.toF64Lossy = false) :
    rustEq n n = true := by
  simp only [rustEq]
  cases hi : n.toExactInt? with
  | some i => simp
  | none =>
      simp only [hi]
      cases hd : n.toF64Lossy.decode with
      | nan => simp [F64Bits.isNaN, hd] at h
      | infinity s => simp [F64Bits.ieeeEq, hd]
      | finite q z => simp [F64Bits.ieeeEq, hd]

end RawNumber

end Regorus
