import ShielddSecurity.TransferBlstArmInverseSignedWordPrepare01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseSignedTopOperand01
open TransferScalarSerializationRange01 (radix64)
open TransferBlstArmInverseSignedWord01 (sourceSignedWordCode)
open TransferBlstArmInverseSignMask01 (sourceFactorSignMask)
open TransferBlstArmInverseFactorMagnitude01 (sourceFactorMagnitudeWord)
attribute [local irreducible] sourceSignedWordCode sourceFactorSignMask sourceFactorMagnitudeWord

/-! Original AND/NEG high-word operand, derived from the actual coded factor
sign and magnitude. This supplies an operand origin to the separately proved
offset carry equation, not a compiled instruction or signed-product theorem. -/

def sourceFactorProductTopOffset (factorWord : UInt64) : UInt64 :=
  -(sourceFactorSignMask factorWord &&& sourceFactorMagnitudeWord factorWord)

theorem every_actual_negated_word_plus_the_original_has_the_complete_zero_or_one_radix_sum
    (word : UInt64) : (-word).toNat + word.toNat = if word.toNat = 0 then 0 else radix64 := by
  have bounded : word.toNat < radix64 := word.toNat_lt
  rw [UInt64.toNat_neg]
  change (radix64 - word.toNat) % radix64 + word.toNat = if word.toNat = 0 then 0 else radix64
  by_cases zero : word.toNat = 0
  · simp only [zero, Nat.sub_zero, Nat.mod_self, Nat.zero_add, ite_true]
  · have differenceBound : radix64 - word.toNat < radix64 := by omega
    rw [Nat.mod_eq_of_lt differenceBound, if_neg zero]
    exact Nat.sub_add_cancel (Nat.le_of_lt bounded)

theorem every_original_coded_factor_derives_its_exact_and_neg_top_offset_word
    (factor : Int) (lower : -9223372036854775808 ≤ factor) (upper : factor < 9223372036854775808) :
    sourceFactorProductTopOffset (sourceSignedWordCode factor) =
      if factor < 0 then -sourceFactorMagnitudeWord (sourceSignedWordCode factor) else 0 := by
  have mask := TransferBlstArmInverseSignedWordPrepare01.the_original_coded_factor_derives_its_entire_source_preparation_mask factor lower upper
  unfold sourceFactorProductTopOffset
  rw [mask]
  by_cases negative : factor < 0
  · simp only [if_pos negative, UInt64.neg_one_and]
  · have zeroNegation : -(0 : UInt64) = 0 := by decide
    simp only [if_neg negative, UInt64.zero_and, zeroNegation]

theorem every_original_coded_factor_derives_the_entire_integer_top_offset_operand
    (factor : Int) (lower : -9223372036854775808 ≤ factor) (upper : factor < 9223372036854775808) :
    ((sourceFactorProductTopOffset (sourceSignedWordCode factor)).toNat : Int) =
      if factor < 0 then (radix64 : Int) - (factor.natAbs : Int) else 0 := by
  rw [every_original_coded_factor_derives_its_exact_and_neg_top_offset_word factor lower upper]
  by_cases negative : factor < 0
  · simp only [if_pos negative]
    let magnitude := sourceFactorMagnitudeWord (sourceSignedWordCode factor)
    have magnitudeValue : magnitude.toNat = factor.natAbs :=
      TransferBlstArmInverseFactorMagnitude01.original_coded_signed_factor_asr_xor_subtract_recovers_integer_magnitude factor lower upper
    have signed := Int.eq_neg_natAbs_of_nonpos (Int.le_of_lt negative)
    have absolutePositive : 0 < factor.natAbs := by omega
    have magnitudeNonzero : magnitude.toNat ≠ 0 := by rw [magnitudeValue]; omega
    have entire := every_actual_negated_word_plus_the_original_has_the_complete_zero_or_one_radix_sum magnitude
    rw [if_neg magnitudeNonzero] at entire
    have cast := congrArg (fun value : Nat => (value : Int)) entire
    simp only [Nat.cast_add] at cast
    rw [magnitudeValue] at cast
    dsimp only [magnitude] at cast
    omega
  · simp only [if_neg negative, UInt64.toNat_zero, Nat.cast_zero]

set_option pp.all true in
#check @sourceFactorProductTopOffset
#print axioms sourceFactorProductTopOffset
set_option pp.all true in
#check @every_actual_negated_word_plus_the_original_has_the_complete_zero_or_one_radix_sum
#print axioms every_actual_negated_word_plus_the_original_has_the_complete_zero_or_one_radix_sum
set_option pp.all true in
#check @every_original_coded_factor_derives_its_exact_and_neg_top_offset_word
#print axioms every_original_coded_factor_derives_its_exact_and_neg_top_offset_word
set_option pp.all true in
#check @every_original_coded_factor_derives_the_entire_integer_top_offset_operand
#print axioms every_original_coded_factor_derives_the_entire_integer_top_offset_operand
end ShielddSecurity.TransferBlstArmInverseSignedTopOperand01
