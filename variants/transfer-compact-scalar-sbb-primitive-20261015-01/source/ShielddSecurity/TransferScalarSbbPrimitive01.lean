import ShielddSecurity.TransferScalarAdcShift01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferScalarSbbPrimitive01
open TransferScalarSerializationRange01 (radix64)
open TransferScalarAdcShift01 (sourceSplit128)
/-! Source-shaped util.rs SBB for reachable input borrow masks (zero/all ones).
The widening, wrapping subtraction, fixed high shift/casts yield the low limb
and exactly the next zero/all-ones borrow mask. Small constant-width arithmetic
lemmas isolate this primitive; no wide limb walk or runtime certification.
Rust primitive/trace and whole sub/add-back/byte layout remain interfaces. -/
def borrowMask (borrow : Bool) : UInt64 := if borrow then 0xffff_ffff_ffff_ffff else 0
def borrowBit (borrow : Bool) : Nat := if borrow then 1 else 0
def sbb128 (a b : UInt64) (borrow : Bool) : BitVec 128 :=
  BitVec.ofNat 128 a.toNat - (BitVec.ofNat 128 b.toNat + BitVec.ofNat 128 ((borrowMask borrow >>> 63).toNat))
def sbb64 (a b : UInt64) (borrow : Bool) : UInt64 × UInt64 := sourceSplit128 (sbb128 a b borrow)

theorem reachable_borrow_mask_high_bit_is_exact_boolean (borrow : Bool) :
    (borrowMask borrow >>> 63).toNat = borrowBit borrow := by
  cases borrow <;> decide

theorem widened_source_sbb_has_exact_wrapping_integer_form (a b : UInt64) (borrow : Bool) :
    (sbb128 a b borrow).toNat = ((2 ^ 128 - (b.toNat + borrowBit borrow)) + a.toNat) % 2 ^ 128 := by
  have bitBound : borrowBit borrow ≤ 1 := by cases borrow <;> decide
  have bitWide : borrowBit borrow < 2 ^ 128 := Nat.lt_of_le_of_lt bitBound (by decide)
  have aWide : a.toNat < 2 ^ 128 := Nat.lt_of_lt_of_le a.toNat_lt (by decide)
  have bWide : b.toNat < 2 ^ 128 := Nat.lt_of_lt_of_le b.toNat_lt (by decide)
  have sumWide : b.toNat + borrowBit borrow < 2 ^ 128 :=
    Nat.lt_of_le_of_lt (Nat.add_le_add (Nat.le_sub_one_of_lt b.toNat_lt) bitBound) (by decide)
  simp only [sbb128, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat,
    reachable_borrow_mask_high_bit_is_exact_boolean, Nat.mod_eq_of_lt aWide, Nat.mod_eq_of_lt bWide,
    Nat.mod_eq_of_lt bitWide, Nat.mod_eq_of_lt sumWide]

theorem nonunderflowing_sbb_returns_small_difference (a b : UInt64) (borrow : Bool)
    (enough : b.toNat + borrowBit borrow ≤ a.toNat) :
    (sbb128 a b borrow).toNat = a.toNat - (b.toNat + borrowBit borrow) := by
  rw [widened_source_sbb_has_exact_wrapping_integer_form]
  have aBound := a.toNat_lt
  have bBound := b.toNat_lt
  have bitBound : borrowBit borrow ≤ 1 := by cases borrow <;> decide
  omega

theorem underflowing_sbb_returns_exact_wrapped_difference (a b : UInt64) (borrow : Bool)
    (underflow : a.toNat < b.toNat + borrowBit borrow) :
    (sbb128 a b borrow).toNat = (2 ^ 128 - (b.toNat + borrowBit borrow)) + a.toNat := by
  rw [widened_source_sbb_has_exact_wrapping_integer_form]
  have aBound := a.toNat_lt
  have bBound := b.toNat_lt
  have bitBound : borrowBit borrow ≤ 1 := by cases borrow <;> decide
  omega

theorem source_sbb_low_word_and_next_borrow_mask_are_exact (a b : UInt64) (borrow : Bool) :
    (sbb64 a b borrow).2 = (if a.toNat < b.toNat + borrowBit borrow then borrowMask true else borrowMask false) ∧
    (sbb64 a b borrow).1.toNat + b.toNat + borrowBit borrow =
      a.toNat + radix64 * (if a.toNat < b.toNat + borrowBit borrow then 1 else 0) := by
  have aBound := a.toNat_lt
  have bBound := b.toNat_lt
  have bitBound : borrowBit borrow ≤ 1 := by cases borrow <;> decide
  unfold sbb64
  rw [TransferScalarAdcShift01.fixed_high_shift_and_cast_equals_radix_quotient_pair]
  unfold TransferScalarWordPrimitives01.split128
  by_cases underflow : a.toNat < b.toNat + borrowBit borrow
  · rw [if_pos underflow, underflowing_sbb_returns_exact_wrapped_difference a b borrow underflow]
    constructor
    · apply UInt64.toNat_inj.1
      change (((2 ^ 128 - (b.toNat + borrowBit borrow)) + a.toNat) / radix64) % 2 ^ 64 = 2 ^ 64 - 1
      unfold radix64
      omega
    · rw [if_pos underflow]
      change (((2 ^ 128 - (b.toNat + borrowBit borrow)) + a.toNat) % 2 ^ 64) + b.toNat + borrowBit borrow = a.toNat + radix64 * 1
      unfold radix64
      omega
  · have enough : b.toNat + borrowBit borrow ≤ a.toNat := Nat.le_of_not_gt underflow
    rw [if_neg underflow, nonunderflowing_sbb_returns_small_difference a b borrow enough]
    constructor
    · apply UInt64.toNat_inj.1
      change ((a.toNat - (b.toNat + borrowBit borrow)) / radix64) % 2 ^ 64 = 0
      unfold radix64
      omega
    · rw [if_neg underflow]
      change (a.toNat - (b.toNat + borrowBit borrow)) % 2 ^ 64 + b.toNat + borrowBit borrow = a.toNat + radix64 * 0
      unfold radix64
      omega

set_option pp.all true in
#check @borrowMask
#print axioms borrowMask
set_option pp.all true in
#check @borrowBit
#print axioms borrowBit
set_option pp.all true in
#check @sbb128
#print axioms sbb128
set_option pp.all true in
#check @sbb64
#print axioms sbb64
set_option pp.all true in
#check @reachable_borrow_mask_high_bit_is_exact_boolean
#print axioms reachable_borrow_mask_high_bit_is_exact_boolean
set_option pp.all true in
#check @widened_source_sbb_has_exact_wrapping_integer_form
#print axioms widened_source_sbb_has_exact_wrapping_integer_form
set_option pp.all true in
#check @nonunderflowing_sbb_returns_small_difference
#print axioms nonunderflowing_sbb_returns_small_difference
set_option pp.all true in
#check @underflowing_sbb_returns_exact_wrapped_difference
#print axioms underflowing_sbb_returns_exact_wrapped_difference
set_option pp.all true in
#check @source_sbb_low_word_and_next_borrow_mask_are_exact
#print axioms source_sbb_low_word_and_next_borrow_mask_are_exact
end ShielddSecurity.TransferScalarSbbPrimitive01
