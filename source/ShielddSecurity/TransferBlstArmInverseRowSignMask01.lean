import ShielddSecurity.TransferBlstArmInverseOriginalRowMagnitude01
import ShielddSecurity.TransferBlstArmInverseShiftAbsolute01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseRowSignMask01
open TransferScalarSerializationRange01 (radix64)
open TransferScalarWordPrimitives01 (packWords)
open TransferBlstArmInverseExtrChain01 (sourceExtractChain)
open TransferBlstArmInverseSignMask01 (sourceFactorSignMask)
open TransferBlstArmInverseSignedProductDecode01 (sourceSignedRadixDecode)
open TransferBlstArmInverseOriginalRowWords01 (sourceOriginalFactorRow sourceOriginalRowWordSum)
open TransferBlstArmInverseOriginalRowMagnitude01 (sourceOriginalRowQuotient)
attribute [local irreducible] sourceExtractChain sourceFactorSignMask sourceSignedRadixDecode
  sourceOriginalFactorRow sourceOriginalRowWordSum sourceOriginalRowQuotient

/-! The retained top-word mask is the actual source row quotient sign,
including zero. This supplies the external mask for both word absolute
correction and coefficient EOR/SUB correction. Compiled execution stays open. -/

theorem full_source_signed_decode_derives_the_exact_retained_top_quotient_sign_mask
    (words : List UInt64) (count shift : Nat) (value : Int)
    (width : words.length = count + 1)
    (decoded : sourceSignedRadixDecode ((radix64 ^ count * 9223372036854775808 : Nat) : Int)
      (packWords words : Int) = value) :
    sourceFactorSignMask (sourceExtractChain shift words).2 =
      if value / ((2 ^ shift : Nat) : Int) < 0 then (-1 : UInt64) else 0 := by
  have nonempty : words ≠ [] := by
    intro empty
    rw [empty, List.length_nil] at width
    omega
  have mask := TransferBlstArmInverseTopWordSign01.every_nonempty_source_word_input_derives_its_entire_retained_top_sign_mask
    shift words nonempty
  rw [width, Nat.add_sub_cancel, decoded] at mask
  have divisorPositive : (0 : Int) < ((2 ^ shift : Nat) : Int) := by exact_mod_cast (Nat.two_pow_pos shift)
  have sign := TransferBlstArmInverseShiftAbsolute01.positive_integer_division_preserves_the_exact_negativity_test
    value ((2 ^ shift : Nat) : Int) divisorPositive
  simpa only [sign] using mask

theorem original_row_word_sum_retained_top_asr_derives_the_exact_original_quotient_sign_mask
    (second : Bool) (a b : TransferBlstArmInverseWindowSelect01.SourceFourWords)
    (oddB : b.w0.toNat % 2 = 1) :
    sourceFactorSignMask (sourceExtractChain 31 (sourceOriginalRowWordSum second a b).1).2 =
      if sourceOriginalRowQuotient 31 second a b < 0 then (-1 : UInt64) else 0 := by
  have width := TransferBlstArmInverseRowWordOperation01.every_original_source_row_word_sum_retains_exactly_five_words second a b
  have decoded := TransferBlstArmInverseRowWordOperation01.original_window_factor_rows_and_source_word_products_derive_the_entire_signed_row_numerator
    second a b oddB
  unfold sourceOriginalRowQuotient
  exact full_source_signed_decode_derives_the_exact_retained_top_quotient_sign_mask
    (sourceOriginalRowWordSum second a b).1 4 31
    ((TransferBlstArmInverseWindowSelect01.sourcePackedFourWords a : Int) * (sourceOriginalFactorRow 31 second a b).1 +
      (TransferBlstArmInverseWindowSelect01.sourcePackedFourWords b : Int) * (sourceOriginalFactorRow 31 second a b).2)
    width decoded

set_option pp.all true in
#check @full_source_signed_decode_derives_the_exact_retained_top_quotient_sign_mask
#print axioms full_source_signed_decode_derives_the_exact_retained_top_quotient_sign_mask
set_option pp.all true in
#check @original_row_word_sum_retained_top_asr_derives_the_exact_original_quotient_sign_mask
#print axioms original_row_word_sum_retained_top_asr_derives_the_exact_original_quotient_sign_mask
end ShielddSecurity.TransferBlstArmInverseRowSignMask01
