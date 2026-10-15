import ShielddSecurity.TransferBlstArmInverseSignedProductSum01
import ShielddSecurity.TransferBlstArmInverseNorm01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseRowSumDecode01
open TransferScalarSerializationRange01 (radix64)
open TransferScalarWordPrimitives01 (packWords)
open TransferBlstArmInverseSignedProductSum01 (sourceSignedProductSum)
open TransferBlstArmInverseSignedProductDecode01 (sourceSignedRadixDecode)
attribute [local irreducible] sourceSignedProductSum sourceSignedRadixDecode

/-! A 31-step factor row has ample signed output headroom. Its row norm,
instead of an assumed decoded sum, supplies both factor and sum bounds.
Negative-factor nonzero input origins and compiled execution remain open. -/

theorem every_factor_in_a_31_step_bounded_row_fits_the_entire_signed64_range
    (f g : Int) (row : f.natAbs + g.natAbs ≤ 2 ^ 31) :
    (-9223372036854775808 ≤ f ∧ f < 9223372036854775808) ∧
      (-9223372036854775808 ≤ g ∧ g < 9223372036854775808) := by
  have rowCast : (f.natAbs : Int) + (g.natAbs : Int) ≤ 2147483648 := by exact_mod_cast row
  have fUpper := Int.le_natAbs (a := f)
  have fLower := Int.le_natAbs (a := -f)
  have gUpper := Int.le_natAbs (a := g)
  have gLower := Int.le_natAbs (a := -g)
  rw [Int.natAbs_neg] at fLower gLower
  have fNonnegative := Int.natCast_nonneg f.natAbs
  have gNonnegative := Int.natCast_nonneg g.natAbs
  omega

theorem every_equal_width_unsigned_input_and_31_step_row_sum_fits_the_full_signed_output
    (left right : List UInt64) (f g : Int) (same : left.length = right.length)
    (row : f.natAbs + g.natAbs ≤ 2 ^ 31) :
    ((packWords left : Int) * f + (packWords right : Int) * g).natAbs <
      radix64 ^ left.length * 9223372036854775808 := by
  have leftBound := Nat.le_of_lt (TransferScalarWordPrimitives01.packed_u64_vector_is_below_radix_power left)
  have rightBound := Nat.le_of_lt (TransferScalarWordPrimitives01.packed_u64_vector_is_below_radix_power right)
  rw [←same] at rightBound
  have bounded := TransferBlstArmInverseNorm01.bounded_signed_inputs_and_factor_row_derive_the_actual_linear_combination_bound
    (packWords left : Int) (packWords right : Int) f g (radix64 ^ left.length) (2 ^ 31)
    (by simpa only [Int.natAbs_natCast] using leftBound)
    (by simpa only [Int.natAbs_natCast] using rightBound) row
  have positive : 0 < radix64 ^ left.length := Nat.pow_pos (by decide : 0 < radix64)
  have room := Nat.mul_lt_mul_of_pos_left (by decide : 2 ^ 31 < 9223372036854775808) positive
  exact Nat.lt_of_le_of_lt bounded room

theorem original_two_signed_products_and_carry_sum_derive_the_entire_31_step_row_integer
    (left right : List UInt64) (f g : Int) (same : left.length = right.length)
    (row : f.natAbs + g.natAbs ≤ 2 ^ 31)
    (leftNonzero : f < 0 → 0 < packWords left) (rightNonzero : g < 0 → 0 < packWords right) :
    sourceSignedRadixDecode ((radix64 ^ left.length * 9223372036854775808 : Nat) : Int)
      (packWords (sourceSignedProductSum left right f g).1 : Int) =
        (packWords left : Int) * f + (packWords right : Int) * g := by
  let half := radix64 ^ left.length * 9223372036854775808
  have capacity : ((radix64 ^ (left.length + 1) : Nat) : Int) = 2 * (half : Int) := by
    have cast := congrArg (fun value : Nat => (value : Int))
      (TransferBlstArmInverseSignedProductDecode01.the_extra_output_word_capacity_is_exactly_twice_the_entire_signed_half_capacity left.length)
    dsimp only at cast
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using cast
  have absolute := every_equal_width_unsigned_input_and_31_step_row_sum_fits_the_full_signed_output left right f g same row
  have absoluteCast : (((((packWords left : Int) * f + (packWords right : Int) * g).natAbs) : Nat) : Int) < (half : Int) := by exact_mod_cast absolute
  have valueUpper := Int.le_natAbs (a := (packWords left : Int) * f + (packWords right : Int) * g)
  have valueLower := Int.le_natAbs (a := -((packWords left : Int) * f + (packWords right : Int) * g))
  rw [Int.natAbs_neg] at valueLower
  have signedLower : -(half : Int) ≤ (packWords left : Int) * f + (packWords right : Int) * g := by omega
  have signedUpper : (packWords left : Int) * f + (packWords right : Int) * g < (half : Int) := by omega
  have unsignedBound := TransferScalarWordPrimitives01.packed_u64_vector_is_below_radix_power (sourceSignedProductSum left right f g).1
  rw [TransferBlstArmInverseSignedProductSum01.equal_input_widths_derive_the_full_extra_word_sum_width left right f g same] at unsignedBound
  have unsignedSmall : (packWords (sourceSignedProductSum left right f g).1 : Int) < ((radix64 ^ (left.length + 1) : Nat) : Int) := by exact_mod_cast unsignedBound
  rw [capacity] at unsignedSmall
  have factors := every_factor_in_a_31_step_bounded_row_fits_the_entire_signed64_range f g row
  have residue := TransferBlstArmInverseSignedProductSum01.original_two_signed_products_and_word_sum_derive_the_full_linear_combination_residue
    left right f g same factors.1.1 factors.1.2 factors.2.1 factors.2.2 leftNonzero rightNonzero
  rw [capacity] at residue
  exact TransferBlstArmInverseSignedProductDecode01.exact_residue_and_both_entire_ranges_derive_the_full_signed_integer
    (half : Int) (packWords (sourceSignedProductSum left right f g).1 : Int)
    ((packWords left : Int) * f + (packWords right : Int) * g)
    (Int.natCast_nonneg _) unsignedSmall signedLower signedUpper residue

set_option pp.all true in
#check @every_factor_in_a_31_step_bounded_row_fits_the_entire_signed64_range
#print axioms every_factor_in_a_31_step_bounded_row_fits_the_entire_signed64_range
set_option pp.all true in
#check @every_equal_width_unsigned_input_and_31_step_row_sum_fits_the_full_signed_output
#print axioms every_equal_width_unsigned_input_and_31_step_row_sum_fits_the_full_signed_output
set_option pp.all true in
#check @original_two_signed_products_and_carry_sum_derive_the_entire_31_step_row_integer
#print axioms original_two_signed_products_and_carry_sum_derive_the_entire_31_step_row_integer
end ShielddSecurity.TransferBlstArmInverseRowSumDecode01
