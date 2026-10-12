import ShielddSecurity.TransferScalarInvertChain01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferScalarPublicConstants01
open TransferCanonicalWordEquality01 (CanonicalScalar)
open TransferScalarWordPrimitives01 (packWords)
open TransferScalarLittleEndianBytes01 (decodeLE serializerBytes)
open TransferScalarMontgomeryValue01 (montgomeryValue)
open TransferBoundedNativeCodec01 (nullifierModulus)
/-! Public PrimeField constants use the exact cached source four-word
Montgomery literals. Their canonical raw bounds and serialization follow
without an operand premise. Only the closed integer values stated below
are certified; root orders/DELTA exponent and native compiler/caller
correspondence remain separate. Private MODULUS/raw temporaries are not
claimed canonical and remain governed by the arithmetic operation proofs. -/

inductive PublicConstant where
  | twoInverse
  | generator
  | rootOfUnity
  | rootOfUnityInverse
  | delta

def sourceConstantWords : PublicConstant → Vector UInt64 4
  | .twoInverse => #v[0x00000000ffffffff, 0xac425bfd0001a401, 0xccc627f7f65e27fa, 0x0c1258acd66282b7]
  | .generator => #v[0x0000000efffffff1, 0x17e363d300189c0f, 0xff9c57876f8457b0, 0x351332208fc5a8c4]
  | .rootOfUnity => #v[0xb9b58d8c5f0e466a, 0x5b1b4c801819d7ec, 0x0af53ae352a31e64, 0x5bf3adda19e9b27b]
  | .rootOfUnityInverse => #v[0x4256481adcf3219a, 0x45f37b7f96b6cad3, 0xf9c3f1d75f7a3b27, 0x2d2fc049658afd43]
  | .delta => #v[0x70e310d3d146f96a, 0x4b64c08919e299e6, 0x51e114186a8b970d, 0x6185d06627c067cb]

theorem every_source_public_constant_has_derived_canonical_raw_words (constant : PublicConstant) :
    packWords (sourceConstantWords constant).toList < nullifierModulus := by
  cases constant <;> decide

def sourceConstant (constant : PublicConstant) : CanonicalScalar :=
  ⟨sourceConstantWords constant, every_source_public_constant_has_derived_canonical_raw_words constant⟩

theorem every_source_public_constant_has_exact_canonical_32_byte_montgomery_key (constant : PublicConstant) :
    (serializerBytes (sourceConstant constant).words.toList).length = 32 ∧
      decodeLE (serializerBytes (sourceConstant constant).words.toList) < nullifierModulus ∧
      decodeLE (serializerBytes (sourceConstant constant).words.toList) = montgomeryValue (sourceConstant constant).words := by
  exact TransferCheckedWordAcceptedInput01.every_original_typed_field_has_exact_32_byte_canonical_serialized_key (sourceConstant constant)

theorem source_public_two_inverse_generator_and_root_inverse_have_exact_integer_values :
    montgomeryValue (sourceConstantWords .twoInverse) = (nullifierModulus + 1) / 2 ∧
      montgomeryValue (sourceConstantWords .generator) = 7 ∧
      (montgomeryValue (sourceConstantWords .rootOfUnity) * montgomeryValue (sourceConstantWords .rootOfUnityInverse)) %
        nullifierModulus = 1 := by decide

set_option pp.all true in
#check @PublicConstant
#print axioms PublicConstant
set_option pp.all true in
#check @sourceConstantWords
#print axioms sourceConstantWords
set_option pp.all true in
#check @every_source_public_constant_has_derived_canonical_raw_words
#print axioms every_source_public_constant_has_derived_canonical_raw_words
set_option pp.all true in
#check @sourceConstant
#print axioms sourceConstant
set_option pp.all true in
#check @every_source_public_constant_has_exact_canonical_32_byte_montgomery_key
#print axioms every_source_public_constant_has_exact_canonical_32_byte_montgomery_key
set_option pp.all true in
#check @source_public_two_inverse_generator_and_root_inverse_have_exact_integer_values
#print axioms source_public_two_inverse_generator_and_root_inverse_have_exact_integer_values
end ShielddSecurity.TransferScalarPublicConstants01
