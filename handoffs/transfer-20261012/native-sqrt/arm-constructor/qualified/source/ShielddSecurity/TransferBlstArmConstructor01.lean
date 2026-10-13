import ShielddSecurity.TransferBlstArmCiosWalk01
import ShielddSecurity.TransferScalarR2Payload01
import ShielddSecurity.TransferBlstArmCaller01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmConstructor01
open TransferCanonicalWordEquality01 (CanonicalScalar)
open TransferScalarSerializationRange01 (radix64)
open TransferScalarWordPrimitives01 (packWords)
open TransferScalarMontgomeryValue01 (radixInverse montgomeryValue)
open TransferBoundedNativeCodec01 (nullifierModulus)
open TransferBlstArmCiosWalk01
open TransferBlstArmNormalized01 (sourceBlstFrWordMeaning)
attribute [local irreducible] sourceCiosProduct sourceCiosWalk sourceCiosFinalWords montgomeryValue
  TransferBlstArmCaller01.sourceAsSlice

/-- Exact locked consts.c BLS12_381_rRR words supplied as left operand by
exports.c blst_fr_from_uint64 on the 64-bit limb route. Native selection,
pointer/ABI and compiler correspondence remain separate. -/
def sourceBlstR2Operand : CanonicalScalar :=
  ⟨#v[0xc999e990f3f29c6d,0x2b6cedcb87925c23,0x05d314967254398f,0x0748d9d99f59ff11],by decide⟩

theorem locked_blst_rRR_words_are_exactly_the_qualified_sdk_r2_words :
    sourceBlstR2Operand.words = TransferScalarR2Payload01.sourceR2 := rfl

theorem locked_blst_rRR_original_field_value_is_the_single_montgomery_radix :
    montgomeryValue sourceBlstR2Operand.words = radix64^4%nullifierModulus := by
  rw [locked_blst_rRR_words_are_exactly_the_qualified_sdk_r2_words,montgomeryValue]
  exact TransferScalarR2Payload01.pinned_R2_words_have_exact_value_range_and_inverse_relation.2.2

theorem two_plain_modular_radix_factors_cancel_on_every_raw_integer
    (modulus radix inverse raw : Nat) (cancellation : (radix*inverse)%modulus=1) :
    ((radix%modulus)*(inverse*raw%modulus))%modulus=raw%modulus := by
  rw [Nat.mod_mul_mod,Nat.mul_mod_mod,← Nat.mul_assoc,Nat.mul_mod,cancellation,
    Nat.one_mul,Nat.mod_mod]

def sourceFrFromLimbs (raw : Vector UInt64 4) : CanonicalScalar :=
  sourceCiosProduct sourceBlstR2Operand raw

theorem original_locked_constructor_derives_the_original_four_limb_integer_field_value
    (raw : Vector UInt64 4) :
    montgomeryValue (sourceFrFromLimbs raw).words = packWords raw.toList%nullifierModulus := by
  have relation := actual_original_four_block_product_and_final_selector_derive_the_montgomery_contract sourceBlstR2Operand raw
  have numericRaw := TransferScalarFieldValues01.canonical_montgomery_word_contract_derives_exact_field_product
    (packWords sourceBlstR2Operand.words.toList) (packWords raw.toList)
    (packWords (sourceFrFromLimbs raw).words.toList) (sourceFrFromLimbs raw).canonical relation
  have numeric : montgomeryValue (sourceFrFromLimbs raw).words =
      (montgomeryValue sourceBlstR2Operand.words*montgomeryValue raw)%nullifierModulus := by
    simpa only [montgomeryValue] using numericRaw
  rw [locked_blst_rRR_original_field_value_is_the_single_montgomery_radix] at numeric
  have rawMeaning : montgomeryValue raw = radixInverse*packWords raw.toList%nullifierModulus := by
    rw [montgomeryValue]
  rw [rawMeaning] at numeric
  have cancellation : (radix64^4*radixInverse)%nullifierModulus=1 := by
    rw [Nat.mul_comm]
    exact TransferScalarMontgomeryValue01.source_four_word_radix_inverse_is_exact
  exact numeric.trans (two_plain_modular_radix_factors_cancel_on_every_raw_integer
    nullifierModulus (radix64^4) radixInverse (packWords raw.toList) cancellation)

theorem original_locked_constructor_word_meaning_is_the_original_input_field_cast
    (raw : Vector UInt64 4) :
    sourceBlstFrWordMeaning (sourceFrFromLimbs raw).words = (packWords raw.toList : ZMod nullifierModulus) := by
  rw [sourceBlstFrWordMeaning,original_locked_constructor_derives_the_original_four_limb_integer_field_value,
    ZMod.natCast_mod]

theorem original_locked_constructor_and_original_as_slice_caller_derive_every_original_input_field_byte
    (raw : Vector UInt64 4) (scalarPrior outputPrior : Vector UInt8 32)
    (scratch : Vector UInt64 4) (index : Fin 32) :
    (TransferBlstArmCaller01.sourceAsSlice ((sourceFrFromLimbs raw).words,scalarPrior,outputPrior) scratch).2.2[index.val] =
      TransferCommonwareMapBytes01.canonicalBEByte (packWords raw.toList : ZMod nullifierModulus) index := by
  have caller := TransferBlstArmCaller01.caller_as_slice_derives_every_original_input_field_byte
    ((sourceFrFromLimbs raw).words,scalarPrior,outputPrior) scratch index
  rw [original_locked_constructor_word_meaning_is_the_original_input_field_cast] at caller
  exact caller
set_option pp.all true in
#check @sourceBlstR2Operand
#print axioms sourceBlstR2Operand
set_option pp.all true in
#check @locked_blst_rRR_words_are_exactly_the_qualified_sdk_r2_words
#print axioms locked_blst_rRR_words_are_exactly_the_qualified_sdk_r2_words
set_option pp.all true in
#check @locked_blst_rRR_original_field_value_is_the_single_montgomery_radix
#print axioms locked_blst_rRR_original_field_value_is_the_single_montgomery_radix
set_option pp.all true in
#check @two_plain_modular_radix_factors_cancel_on_every_raw_integer
#print axioms two_plain_modular_radix_factors_cancel_on_every_raw_integer
set_option pp.all true in
#check @sourceFrFromLimbs
#print axioms sourceFrFromLimbs
set_option pp.all true in
#check @original_locked_constructor_derives_the_original_four_limb_integer_field_value
#print axioms original_locked_constructor_derives_the_original_four_limb_integer_field_value
set_option pp.all true in
#check @original_locked_constructor_word_meaning_is_the_original_input_field_cast
#print axioms original_locked_constructor_word_meaning_is_the_original_input_field_cast
set_option pp.all true in
#check @original_locked_constructor_and_original_as_slice_caller_derive_every_original_input_field_byte
#print axioms original_locked_constructor_and_original_as_slice_caller_derive_every_original_input_field_byte
end ShielddSecurity.TransferBlstArmConstructor01
