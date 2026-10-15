import ShielddSecurity.TransferBlstArmInversePackedWalk01
import ShielddSecurity.TransferBlstArmInverseDebiasWord01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInversePackedFactorWords01
open TransferBlstArmInverseSignedWord01 (sourceSignedWordCode sourceSignedWordMeaning)
open TransferBlstArmInversePackedWalk01 (FactorWord PackedState sourcePackedWalk sourcePackedInitial)
open TransferBlstArmInversePack01 (sourceDecodeLow sourceDecodeHigh)
open TransferBlstArmInverseFactors01 (SourceFactors sourceFactorWalk sourceFactorInitial)
open TransferBlstArmInverseDebiasWord01 (sourceLowFactorWord sourceHighFactorWord)
attribute [local irreducible] sourceSignedWordCode sourcePackedWalk sourceFactorWalk

/-! Exact source modulo64 packed registers, converted to UInt64 then passed
through the original UBFX32/bias-subtract operations, produce all four
entire integer factor codes. This is source arithmetic correspondence;
actual UInt64 loop-control execution and compiled ISA/ABI remain open. -/

local instance wordModulusNonzero : NeZero (18446744073709551616 : Nat) := ⟨by decide⟩

theorem every_entire_signed_word_decode_codes_back_to_the_original_word (word : UInt64) :
    sourceSignedWordCode (sourceSignedWordMeaning word) = word := by
  have code := TransferBlstArmInverseSignedWord01.original_signed64_word_code_has_the_entire_integer_modulo_residue (sourceSignedWordMeaning word)
  have bounded : (word.toNat : Int) < 18446744073709551616 := by exact_mod_cast word.toNat_lt
  have residue : sourceSignedWordMeaning word % 18446744073709551616 = (word.toNat : Int) := by
    by_cases sign : 9223372036854775808 ≤ word.toNat
    · rw [sourceSignedWordMeaning, if_pos sign, Int.sub_emod_right,
        Int.emod_eq_of_lt (Int.natCast_nonneg _) bounded]
    · rw [sourceSignedWordMeaning, if_neg sign,
        Int.emod_eq_of_lt (Int.natCast_nonneg _) bounded]
  rw [residue] at code
  apply UInt64.toNat_inj.mp
  exact_mod_cast code

attribute [local irreducible] sourceSignedWordMeaning

theorem an_entire_signed_word_decode_equality_derives_the_exact_integer_word_code
    (word : UInt64) (value : Int) (decoded : sourceSignedWordMeaning word = value) :
    word = sourceSignedWordCode value := by
  exact (every_entire_signed_word_decode_codes_back_to_the_original_word word).symm.trans
    (congrArg sourceSignedWordCode decoded)

def sourcePackedRegisterWord (word : FactorWord) : UInt64 := UInt64.ofNat word.val

theorem the_entire_source_packed_register_is_preserved_by_its_uint64_conversion
    (word : FactorWord) : (sourcePackedRegisterWord word).toNat = word.val := by
  have bounded : word.val < UInt64.size := ZMod.val_lt word
  exact UInt64.toNat_ofNat_of_lt' bounded

def sourcePackedFactorRegisterWords (packed : PackedState) : UInt64 × UInt64 × UInt64 × UInt64 :=
  (sourceLowFactorWord (sourcePackedRegisterWord packed.2.2.1),
   sourceHighFactorWord (sourcePackedRegisterWord packed.2.2.1),
   sourceLowFactorWord (sourcePackedRegisterWord packed.2.2.2),
   sourceHighFactorWord (sourcePackedRegisterWord packed.2.2.2))

attribute [local irreducible] sourcePackedRegisterWord sourcePackedFactorRegisterWords

theorem exact_biased_slot_decoders_derive_all_four_complete_factor_word_codes
    (factors : SourceFactors) (packed : PackedState)
    (decoded : sourceDecodeLow (packed.2.2.1.val : Int) = factors.f0 ∧
      sourceDecodeHigh (packed.2.2.1.val : Int) = factors.g0 ∧
      sourceDecodeLow (packed.2.2.2.val : Int) = factors.f1 ∧
      sourceDecodeHigh (packed.2.2.2.val : Int) = factors.g1) :
    sourcePackedFactorRegisterWords packed =
      (sourceSignedWordCode factors.f0, sourceSignedWordCode factors.g0,
       sourceSignedWordCode factors.f1, sourceSignedWordCode factors.g1) := by
  have lowFirst := TransferBlstArmInverseDebiasWord01.original_low32_extraction_and_word_subtraction_recovers_the_integer_slot_decoder (sourcePackedRegisterWord packed.2.2.1)
  have highFirst := TransferBlstArmInverseDebiasWord01.original_high32_extraction_and_word_subtraction_recovers_the_integer_slot_decoder (sourcePackedRegisterWord packed.2.2.1)
  have lowLast := TransferBlstArmInverseDebiasWord01.original_low32_extraction_and_word_subtraction_recovers_the_integer_slot_decoder (sourcePackedRegisterWord packed.2.2.2)
  have highLast := TransferBlstArmInverseDebiasWord01.original_high32_extraction_and_word_subtraction_recovers_the_integer_slot_decoder (sourcePackedRegisterWord packed.2.2.2)
  rw [the_entire_source_packed_register_is_preserved_by_its_uint64_conversion] at lowFirst highFirst lowLast highLast
  unfold sourcePackedFactorRegisterWords
  rw [an_entire_signed_word_decode_equality_derives_the_exact_integer_word_code _ _ (lowFirst.trans decoded.1),
    an_entire_signed_word_decode_equality_derives_the_exact_integer_word_code _ _ (highFirst.trans decoded.2.1),
    an_entire_signed_word_decode_equality_derives_the_exact_integer_word_code _ _ (lowLast.trans decoded.2.2.1),
    an_entire_signed_word_decode_equality_derives_the_exact_integer_word_code _ _ (highLast.trans decoded.2.2.2)]

theorem original_modulo64_packed_walk_and_ubfx_bias_subtraction_derive_all_four_entire_factor_codes
    (a b : Nat) :
    sourcePackedFactorRegisterWords (sourcePackedWalk 31 (sourcePackedInitial a b)) =
      (sourceSignedWordCode (sourceFactorWalk 31 (sourceFactorInitial a b)).f0,
       sourceSignedWordCode (sourceFactorWalk 31 (sourceFactorInitial a b)).g0,
       sourceSignedWordCode (sourceFactorWalk 31 (sourceFactorInitial a b)).f1,
       sourceSignedWordCode (sourceFactorWalk 31 (sourceFactorInitial a b)).g1) := by
  have decoded := TransferBlstArmInversePackedWalk01.original_initialized_31_packed_walk_decodes_all_four_actual_factor_coefficients a b
  exact exact_biased_slot_decoders_derive_all_four_complete_factor_word_codes
    (sourceFactorWalk 31 (sourceFactorInitial a b)) (sourcePackedWalk 31 (sourcePackedInitial a b)) decoded

set_option pp.all true in
#check @wordModulusNonzero
#print axioms wordModulusNonzero
set_option pp.all true in
#check @every_entire_signed_word_decode_codes_back_to_the_original_word
#print axioms every_entire_signed_word_decode_codes_back_to_the_original_word
set_option pp.all true in
#check @an_entire_signed_word_decode_equality_derives_the_exact_integer_word_code
#print axioms an_entire_signed_word_decode_equality_derives_the_exact_integer_word_code
set_option pp.all true in
#check @sourcePackedRegisterWord
#print axioms sourcePackedRegisterWord
set_option pp.all true in
#check @the_entire_source_packed_register_is_preserved_by_its_uint64_conversion
#print axioms the_entire_source_packed_register_is_preserved_by_its_uint64_conversion
set_option pp.all true in
#check @sourcePackedFactorRegisterWords
#print axioms sourcePackedFactorRegisterWords
set_option pp.all true in
#check @exact_biased_slot_decoders_derive_all_four_complete_factor_word_codes
#print axioms exact_biased_slot_decoders_derive_all_four_complete_factor_word_codes
set_option pp.all true in
#check @original_modulo64_packed_walk_and_ubfx_bias_subtraction_derive_all_four_entire_factor_codes
#print axioms original_modulo64_packed_walk_and_ubfx_bias_subtraction_derive_all_four_entire_factor_codes
end ShielddSecurity.TransferBlstArmInversePackedFactorWords01
