import ShielddSecurity.TransferBlstArmInverseFactorMagnitude01
import ShielddSecurity.TransferBlstArmInversePack01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseDebiasWord01
open TransferBlstArmInverseSignedWord01 (sourceSignedWordCode sourceSignedWordMeaning)

/-! Source word semantics of UBFX followed by subtraction of 0x7fffffff.
The low/high extraction is explicit unsigned32 arithmetic. Actual packed
register provenance, compiled instructions and full inverse remain open. -/

def sourceDebiasedFactorSlot (slot : Nat) : UInt64 := UInt64.ofNat slot - 2147483647

theorem original_unsigned32_slot_word_subtraction_is_the_exact_signed_factor_code
    (slot : Nat) (bounded : slot < 4294967296) :
    sourceDebiasedFactorSlot slot=sourceSignedWordCode ((slot:Int)-2147483647) := by
  apply UInt64.toNat_inj.mp
  have wordBound : slot < UInt64.size := by change slot < 18446744073709551616; omega
  have radix : (2:Nat)^64=18446744073709551616 := by decide +kernel
  have bias : (2147483647:UInt64).toNat=2147483647 := by decide
  have raw : (sourceDebiasedFactorSlot slot).toNat=(18446744073709551616-2147483647+slot)%18446744073709551616 := by
    simpa only [sourceDebiasedFactorSlot, UInt64.toNat_ofNat_of_lt' wordBound, bias, radix] using
      (UInt64.toNat_sub (UInt64.ofNat slot) (2147483647:UInt64))
  have code := TransferBlstArmInverseSignedWord01.original_signed64_word_code_has_the_entire_integer_modulo_residue ((slot:Int)-2147483647)
  have period := Int.add_emod_right ((slot:Int)-2147483647) 18446744073709551616
  have castmod := Int.natCast_emod (18446744073709551616-2147483647+slot) 18446744073709551616
  omega

theorem original_unsigned32_slot_word_subtraction_decodes_the_entire_integer_factor
    (slot : Nat) (bounded : slot < 4294967296) :
    sourceSignedWordMeaning (sourceDebiasedFactorSlot slot)=(slot:Int)-2147483647 := by
  rw [original_unsigned32_slot_word_subtraction_is_the_exact_signed_factor_code slot bounded]
  exact TransferBlstArmInverseSignedWord01.original_signed64_code_and_threshold_decode_recover_the_entire_factor_value
    ((slot:Int)-2147483647) (by omega) (by omega)

def sourceLowFactorWord (word : UInt64) : UInt64 :=
  sourceDebiasedFactorSlot (word.toNat%4294967296)

def sourceHighFactorWord (word : UInt64) : UInt64 :=
  sourceDebiasedFactorSlot (word.toNat/4294967296)

theorem original_low32_extraction_and_word_subtraction_recovers_the_integer_slot_decoder
    (word : UInt64) :
    sourceSignedWordMeaning (sourceLowFactorWord word)=
      TransferBlstArmInversePack01.sourceDecodeLow (word.toNat:Int) := by
  simpa only [sourceLowFactorWord, TransferBlstArmInversePack01.sourceDecodeLow, Int.natCast_emod] using
    (original_unsigned32_slot_word_subtraction_decodes_the_entire_integer_factor _ (Nat.mod_lt _ (by decide)))

theorem original_high32_extraction_and_word_subtraction_recovers_the_integer_slot_decoder
    (word : UInt64) :
    sourceSignedWordMeaning (sourceHighFactorWord word)=
      TransferBlstArmInversePack01.sourceDecodeHigh (word.toNat:Int) := by
  have range := word.toNat_lt
  change word.toNat < 18446744073709551616 at range
  have slotBound : word.toNat/4294967296 < 4294967296 := by omega
  simpa only [sourceHighFactorWord, TransferBlstArmInversePack01.sourceDecodeHigh, Int.natCast_ediv] using
    (original_unsigned32_slot_word_subtraction_decodes_the_entire_integer_factor _ slotBound)

set_option pp.all true in
#check @sourceDebiasedFactorSlot
#print axioms sourceDebiasedFactorSlot
set_option pp.all true in
#check @original_unsigned32_slot_word_subtraction_is_the_exact_signed_factor_code
#print axioms original_unsigned32_slot_word_subtraction_is_the_exact_signed_factor_code
set_option pp.all true in
#check @original_unsigned32_slot_word_subtraction_decodes_the_entire_integer_factor
#print axioms original_unsigned32_slot_word_subtraction_decodes_the_entire_integer_factor
set_option pp.all true in
#check @sourceLowFactorWord
#print axioms sourceLowFactorWord
set_option pp.all true in
#check @sourceHighFactorWord
#print axioms sourceHighFactorWord
set_option pp.all true in
#check @original_low32_extraction_and_word_subtraction_recovers_the_integer_slot_decoder
#print axioms original_low32_extraction_and_word_subtraction_recovers_the_integer_slot_decoder
set_option pp.all true in
#check @original_high32_extraction_and_word_subtraction_recovers_the_integer_slot_decoder
#print axioms original_high32_extraction_and_word_subtraction_recovers_the_integer_slot_decoder
end ShielddSecurity.TransferBlstArmInverseDebiasWord01
