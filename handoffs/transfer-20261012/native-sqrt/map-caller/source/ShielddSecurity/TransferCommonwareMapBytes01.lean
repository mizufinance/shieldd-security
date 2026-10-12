import ShielddSecurity.TransferCommonwareMapRoots01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferCommonwareMapBytes01
open TransferBoundedNativeCodec01 (nullifierModulus)
open TransferCanonicalWordEquality01 (CanonicalScalar)
open TransferScalarLittleEndianBytes01 (serializerBytes decodeLE scalarKey)
open TransferScalarMontgomeryValue01 (montgomeryValue)
open TransferSqrtProducerField01
open TransferCommonwareMapRoots01
local instance scalarPrimeFact : Fact (Nat.Prime nullifierModulus) :=
  ⟨TransferScalarInverseCorrectness01.exact_source_scalar_modulus_is_prime⟩
local instance scalarNonzero : NeZero nullifierModulus := ⟨by decide⟩

theorem exact_source_field_representative_is_the_montgomery_value (value : CanonicalScalar) :
    (sourceFieldValue value).val = montgomeryValue value.words := by
  have canonical : montgomeryValue value.words < nullifierModulus := by
    rw [← TransferScalarMontgomeryValue01.fixed_four_word_typed_serializer_has_exact_canonical_montgomery_value]
    exact TransferScalarLittleEndianBytes01.fixed_four_word_source_scalar_projection_is_canonical value.words
  unfold sourceFieldValue
  rw [ZMod.val_natCast,Nat.mod_eq_of_lt canonical]

def sourceSdkLowBit (value : CanonicalScalar) : UInt8 :=
  (serializerBytes value.words.toList).headD 0 &&& 1

theorem actual_sdk_source_serializer_mask_derives_the_canonical_field_parity (value : CanonicalScalar) :
    (sourceSdkLowBit value).toNat = (sourceFieldValue value).val % 2 := by
  have width := TransferScalarLittleEndianBytes01.source_scalar_serialization_has_exact_32_byte_width
    value.words.toList Vector.length_toList
  have mathematical : decodeLE (serializerBytes value.words.toList) = montgomeryValue value.words :=
    TransferScalarMontgomeryValue01.fixed_four_word_typed_serializer_has_exact_canonical_montgomery_value value.words
  cases observed : serializerBytes value.words.toList with
  | nil => simp only [observed,List.length_nil] at width; omega
  | cons byte rest =>
    have head := TransferScalarByteEquality01.typed_little_endian_head_is_exact_numeric_remainder byte rest
    rw [← observed,mathematical] at head
    rw [sourceSdkLowBit,observed,List.headD_cons,UInt8.toNat_and]
    change byte.toNat &&& 1 = _
    rw [Nat.and_one_is_mod,← head,exact_source_field_representative_is_the_montgomery_value]
    exact Nat.mod_mod_of_dvd _ (by decide : 2 ∣ 256)

/-- Canonical big-endian writer model; native blst encoder/FFI origin is a
separate source binding. The last byte and AND operation are derived here. -/
def canonicalBEByte (value : ZMod nullifierModulus) (index : Fin 32) : UInt8 :=
  UInt8.ofNat (value.val / 256^(31-index.val) % 256)

def sourceCommonwareLowBit (value : ZMod nullifierModulus) : UInt8 :=
  canonicalBEByte value ⟨31,by decide⟩ &&& 1

theorem canonical_commonware_be_byte31_mask_derives_the_field_parity (value : ZMod nullifierModulus) :
    (sourceCommonwareLowBit value).toNat = value.val % 2 := by
  simp only [sourceCommonwareLowBit,canonicalBEByte,Nat.sub_self,pow_zero,Nat.div_one]
  rw [UInt8.toNat_and]
  change ((value.val % 256) % 256) &&& 1 = _
  rw [Nat.mod_mod,Nat.and_one_is_mod]
  exact Nat.mod_mod_of_dvd _ (by decide : 2 ∣ 256)

def encodedSdkNormalize (choice : Bool) (value : CanonicalScalar) : ZMod nullifierModulus :=
  if decide ((sourceSdkLowBit value).toNat=1) != choice then -sourceFieldValue value else sourceFieldValue value

def encodedCommonwareNormalize (choice : Bool) (value : ZMod nullifierModulus) : ZMod nullifierModulus :=
  if decide ((sourceCommonwareLowBit value).toNat=1) != choice then -value else value

theorem actual_sdk_source_byte_sign_branch_is_the_canonical_normalizer (choice : Bool) (value : CanonicalScalar) :
    encodedSdkNormalize choice value = normalizeRoot choice (sourceFieldValue value) := by
  unfold encodedSdkNormalize
  rw [actual_sdk_source_serializer_mask_derives_the_canonical_field_parity]
  have parity : (sourceFieldValue value).val % 2=0 ∨ (sourceFieldValue value).val % 2=1 := by
    have bound := Nat.mod_lt (sourceFieldValue value).val (by decide : 0 < 2)
    omega
  rcases parity with even | odd
  · cases choice <;> simp [normalizeRoot,even]
  · cases choice <;> simp [normalizeRoot,odd]

theorem canonical_commonware_be_byte_sign_branch_is_the_canonical_normalizer
    (choice : Bool) (value : ZMod nullifierModulus) : encodedCommonwareNormalize choice value = normalizeRoot choice value := by
  unfold encodedCommonwareNormalize
  rw [canonical_commonware_be_byte31_mask_derives_the_field_parity]
  have parity : value.val % 2=0 ∨ value.val % 2=1 := by
    have bound := Nat.mod_lt value.val (by decide : 0 < 2)
    omega
  rcases parity with even | odd
  · cases choice <;> simp [normalizeRoot,even]
  · cases choice <;> simp [normalizeRoot,odd]

set_option pp.all true in
#check @scalarPrimeFact
#print axioms scalarPrimeFact
set_option pp.all true in
#check @scalarNonzero
#print axioms scalarNonzero
set_option pp.all true in
#check @exact_source_field_representative_is_the_montgomery_value
#print axioms exact_source_field_representative_is_the_montgomery_value
set_option pp.all true in
#check @sourceSdkLowBit
#print axioms sourceSdkLowBit
set_option pp.all true in
#check @actual_sdk_source_serializer_mask_derives_the_canonical_field_parity
#print axioms actual_sdk_source_serializer_mask_derives_the_canonical_field_parity
set_option pp.all true in
#check @canonicalBEByte
#print axioms canonicalBEByte
set_option pp.all true in
#check @sourceCommonwareLowBit
#print axioms sourceCommonwareLowBit
set_option pp.all true in
#check @canonical_commonware_be_byte31_mask_derives_the_field_parity
#print axioms canonical_commonware_be_byte31_mask_derives_the_field_parity
set_option pp.all true in
#check @encodedSdkNormalize
#print axioms encodedSdkNormalize
set_option pp.all true in
#check @encodedCommonwareNormalize
#print axioms encodedCommonwareNormalize
set_option pp.all true in
#check @actual_sdk_source_byte_sign_branch_is_the_canonical_normalizer
#print axioms actual_sdk_source_byte_sign_branch_is_the_canonical_normalizer
set_option pp.all true in
#check @canonical_commonware_be_byte_sign_branch_is_the_canonical_normalizer
#print axioms canonical_commonware_be_byte_sign_branch_is_the_canonical_normalizer
end ShielddSecurity.TransferCommonwareMapBytes01
