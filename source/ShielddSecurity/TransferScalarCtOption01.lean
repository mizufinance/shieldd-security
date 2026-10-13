import ShielddSecurity.TransferNullifierFieldDomain01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferScalarCtOption01
open TransferScalarCanonicalDecoder01 (byteDecoderPayload sourceDecodeOption)
open TransferScalarChoiceBit01 (sourceCanonicalChoiceByte)
open TransferScalarLittleEndianBytes01 (decodeLE scalarKey)
open TransferScalarMontgomeryValue01 (montgomeryValue)
open TransferScalarWordPrimitives01 (packWords)
open TransferBoundedNativeCodec01 (nullifierModulus)
/-! Exact locked subtle source success projection: CtOption::new retains
both payload and Choice byte; is_some and unwrap_u8 project stored fields;
From<CtOption<T>> returns Some(value) exactly for byte1. No byte-validity
assumption is needed for conversion itself. The actual modeled Scalar byte
constructor derives its bit invariant and canonical R2 payload on every
input, including refused input. This records stored payload as well as the
returned Option. Rust compiler/volatile barrier/layout/ABI/native caller
origins/eager-computation side effects/timing/full Transfer remain open. -/

structure SourceCtOption (α : Type) where
  value : α
  isSomeByte : UInt8

def sourceCtOptionNew {α : Type} (value : α) (byte : UInt8) : SourceCtOption α :=
  ⟨value, byte⟩

def sourceCtOptionIntoOption {α : Type} (source : SourceCtOption α) : Option α :=
  if source.isSomeByte = 1 then some source.value else none

theorem exact_source_ct_option_constructor_retains_payload_and_byte_on_every_input
    {α : Type} (value : α) (byte : UInt8) :
    (sourceCtOptionNew value byte).value = value ∧
      (sourceCtOptionNew value byte).isSomeByte = byte := by
  exact ⟨rfl, rfl⟩

theorem exact_source_ct_option_conversion_returns_some_iff_stored_byte_one_and_exact_payload
    {α : Type} (source : SourceCtOption α) (value : α) :
    sourceCtOptionIntoOption source = some value ↔ source.isSomeByte = 1 ∧ source.value = value := by
  by_cases yes : source.isSomeByte = 1
  · rw [sourceCtOptionIntoOption, if_pos yes]
    simp only [Option.some.injEq, yes, true_and]
  · rw [sourceCtOptionIntoOption, if_neg yes]
    simp only [reduceCtorEq, yes, false_and]

def sourceByteDecoderCtOption (bytes : Vector UInt8 32) : SourceCtOption (Vector UInt64 4) :=
  sourceCtOptionNew (byteDecoderPayload bytes) (sourceCanonicalChoiceByte bytes)

theorem exact_source_ct_option_conversion_of_byte_constructor_equals_the_qualified_decoder
    (bytes : Vector UInt8 32) :
    sourceCtOptionIntoOption (sourceByteDecoderCtOption bytes) = sourceDecodeOption bytes := by
  rfl

theorem every_source_byte_constructor_has_a_derived_valid_choice_byte (bytes : Vector UInt8 32) :
    (sourceByteDecoderCtOption bytes).isSomeByte.toNat < 2 := by
  change (sourceCanonicalChoiceByte bytes).toNat < 2
  rw [sourceCanonicalChoiceByte,
    TransferScalarChoiceBit01.source_borrow_choice_byte_is_exact_zero_or_one]
  split <;> decide

theorem stored_source_byte_constructor_payload_is_canonical_with_exact_modular_field_value
    (bytes : Vector UInt8 32) :
    packWords (sourceByteDecoderCtOption bytes).value.toList < nullifierModulus ∧
      montgomeryValue (sourceByteDecoderCtOption bytes).value = decodeLE bytes.toList % nullifierModulus := by
  change packWords (byteDecoderPayload bytes).toList < nullifierModulus ∧
    montgomeryValue (byteDecoderPayload bytes) = decodeLE bytes.toList % nullifierModulus
  have payload := TransferScalarCanonicalDecoder01.source_byte_decoder_payload_has_derived_range_and_serialized_value bytes
  refine ⟨payload.1, ?_⟩
  rw [← TransferScalarMontgomeryValue01.fixed_four_word_typed_serializer_has_exact_canonical_montgomery_value]
  exact payload.2

theorem exact_source_ct_option_byte_conversion_accepts_the_entire_canonical_input_domain
    (bytes : Vector UInt8 32) :
    (∃ value, sourceCtOptionIntoOption (sourceByteDecoderCtOption bytes) = some value) ↔
      decodeLE bytes.toList < nullifierModulus := by
  rw [exact_source_ct_option_conversion_of_byte_constructor_equals_the_qualified_decoder]
  exact TransferScalarCanonicalDecoder01.source_decoder_success_projection_accepts_exactly_canonical_bytes bytes

theorem refused_source_ct_option_byte_constructor_still_retains_the_actual_canonical_payload
    (bytes : Vector UInt8 32) (refused : ¬ decodeLE bytes.toList < nullifierModulus) :
    sourceCtOptionIntoOption (sourceByteDecoderCtOption bytes) = none ∧
      (sourceByteDecoderCtOption bytes).value = byteDecoderPayload bytes ∧
      (sourceByteDecoderCtOption bytes).isSomeByte = 0 := by
  have flag := (TransferScalarChoiceBit01.source_canonical_choice_byte_is_zero_iff_parsed_integer_is_noncanonical bytes).mpr refused
  change (if sourceCanonicalChoiceByte bytes = 1 then some (byteDecoderPayload bytes) else none) = none ∧
    byteDecoderPayload bytes = byteDecoderPayload bytes ∧ sourceCanonicalChoiceByte bytes = 0
  rw [flag]
  exact ⟨rfl, rfl, rfl⟩

set_option pp.all true in
#check @SourceCtOption
#print axioms SourceCtOption
set_option pp.all true in
#check @sourceCtOptionNew
#print axioms sourceCtOptionNew
set_option pp.all true in
#check @sourceCtOptionIntoOption
#print axioms sourceCtOptionIntoOption
set_option pp.all true in
#check @exact_source_ct_option_constructor_retains_payload_and_byte_on_every_input
#print axioms exact_source_ct_option_constructor_retains_payload_and_byte_on_every_input
set_option pp.all true in
#check @exact_source_ct_option_conversion_returns_some_iff_stored_byte_one_and_exact_payload
#print axioms exact_source_ct_option_conversion_returns_some_iff_stored_byte_one_and_exact_payload
set_option pp.all true in
#check @sourceByteDecoderCtOption
#print axioms sourceByteDecoderCtOption
set_option pp.all true in
#check @exact_source_ct_option_conversion_of_byte_constructor_equals_the_qualified_decoder
#print axioms exact_source_ct_option_conversion_of_byte_constructor_equals_the_qualified_decoder
set_option pp.all true in
#check @every_source_byte_constructor_has_a_derived_valid_choice_byte
#print axioms every_source_byte_constructor_has_a_derived_valid_choice_byte
set_option pp.all true in
#check @stored_source_byte_constructor_payload_is_canonical_with_exact_modular_field_value
#print axioms stored_source_byte_constructor_payload_is_canonical_with_exact_modular_field_value
set_option pp.all true in
#check @exact_source_ct_option_byte_conversion_accepts_the_entire_canonical_input_domain
#print axioms exact_source_ct_option_byte_conversion_accepts_the_entire_canonical_input_domain
set_option pp.all true in
#check @refused_source_ct_option_byte_constructor_still_retains_the_actual_canonical_payload
#print axioms refused_source_ct_option_byte_constructor_still_retains_the_actual_canonical_payload
end ShielddSecurity.TransferScalarCtOption01
