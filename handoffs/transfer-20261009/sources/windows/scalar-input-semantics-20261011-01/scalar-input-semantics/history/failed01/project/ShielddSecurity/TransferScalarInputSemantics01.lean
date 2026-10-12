import ShielddSecurity.TransferScalarAdditiveField01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferScalarInputSemantics01
open TransferCanonicalWordEquality01 (CanonicalScalar)
open TransferScalarInputFamily01 (ScalarInputProgram sourceInputEval)
open TransferScalarMontgomeryValue01 (montgomeryValue)
open TransferScalarLittleEndianBytes01 (decodeLE)
open TransferScalarWordPrimitives01 (packWords)
open TransferBoundedNativeCodec01 (nullifierModulus)
open TransferScalarAdditiveField01 (sourceCanonicalAdd sourceCanonicalSub sourceCanonicalNeg)
open TransferScalarPowInvariant01 (sourceCanonicalMul)
/-! Independent integer-residue semantics for every represented source input
program. Raw and wide constructors reduce their actual input integer; the
32-byte constructor accepts precisely canonical input. Arithmetic and
constructor failures propagate compositionally. The whole evaluator theorem
uses constructor and source word-operation proofs; no desired output/flag
is supplied as a premise. This is the represented typed source model,
not an exhaustive native caller census or compiler/ABI/Transfer proof. -/

theorem mapped_canonical_option_binary_operation_preserves_derived_field_semantics
    (left right : Option CanonicalScalar) (sourceOp : CanonicalScalar → CanonicalScalar → CanonicalScalar)
    (mathOp : Nat → Nat → Nat)
    (corresponds : ∀ a b, montgomeryValue (sourceOp a b).words = mathOp (montgomeryValue a.words) (montgomeryValue b.words)) :
    (do let a ← left; let b ← right; pure (sourceOp a b)).map (fun scalar => montgomeryValue scalar.words) =
      (do let a ← left.map (fun scalar => montgomeryValue scalar.words)
          let b ← right.map (fun scalar => montgomeryValue scalar.words)
          pure (mathOp a b)) := by
  cases left with
  | none => rfl
  | some a =>
    cases right with
    | none => rfl
    | some b => exact congrArg Option.some (corresponds a b)

theorem mapped_canonical_option_unary_operation_preserves_derived_field_semantics
    (value : Option CanonicalScalar) (sourceOp : CanonicalScalar → CanonicalScalar) (mathOp : Nat → Nat)
    (corresponds : ∀ a, montgomeryValue (sourceOp a).words = mathOp (montgomeryValue a.words)) :
    (do let a ← value; pure (sourceOp a)).map (fun scalar => montgomeryValue scalar.words) =
      (do let a ← value.map (fun scalar => montgomeryValue scalar.words); pure (mathOp a)) := by
  cases value with
  | none => rfl
  | some a => exact congrArg Option.some (corresponds a)

theorem raw_source_input_constructor_has_derived_integer_residue_semantics (words : Vector UInt64 4) :
    (sourceInputEval (.raw words)).map (fun scalar => montgomeryValue scalar.words) =
      some (packWords words.toList % nullifierModulus) := by
  change some (montgomeryValue (TransferScalarR2Payload01.sourceDecoderPayload words)) = _
  apply congrArg Option.some
  rw [← TransferScalarMontgomeryValue01.fixed_four_word_typed_serializer_has_exact_canonical_montgomery_value]
  exact TransferScalarR2Payload01.actual_modeled_decoder_payload_serializer_returns_raw_modulus_value words

theorem wide_source_input_constructor_has_derived_integer_residue_semantics (bytes : Vector UInt8 64) :
    (sourceInputEval (.wide bytes)).map (fun scalar => montgomeryValue scalar.words) =
      some (decodeLE bytes.toList % nullifierModulus) := by
  change some (montgomeryValue (TransferScalarWideByteInput01.sourceFromWideBytes bytes)) = _
  apply congrArg Option.some
  rw [← TransferScalarMontgomeryValue01.fixed_four_word_typed_serializer_has_exact_canonical_montgomery_value]
  exact (TransferScalarWideByteInput01.arbitrary_64_source_bytes_derive_canonical_field_and_exact_modular_key bytes).2.1

theorem canonical_byte_source_input_constructor_has_derived_integer_and_refusal_semantics (bytes : Vector UInt8 32) :
    (sourceInputEval (.bytes bytes)).map (fun scalar => montgomeryValue scalar.words) =
      if decodeLE bytes.toList < nullifierModulus then some (decodeLE bytes.toList) else none := by
  by_cases canonical : decodeLE bytes.toList < nullifierModulus
  · have flag := (TransferScalarChoiceBit01.source_canonical_choice_byte_is_one_iff_parsed_integer_below_modulus bytes).mpr canonical
    rw [sourceInputEval, if_pos flag, if_pos canonical]
    change some (montgomeryValue (TransferScalarCanonicalDecoder01.byteDecoderPayload bytes)) = _
    apply congrArg Option.some
    rw [← TransferScalarMontgomeryValue01.fixed_four_word_typed_serializer_has_exact_canonical_montgomery_value,
      (TransferScalarCanonicalDecoder01.source_byte_decoder_payload_has_derived_range_and_serialized_value bytes).2,
      Nat.mod_eq_of_lt canonical]
  · have flag : TransferScalarChoiceBit01.sourceCanonicalChoiceByte bytes ≠ 1 := by
      intro yes
      exact canonical ((TransferScalarChoiceBit01.source_canonical_choice_byte_is_one_iff_parsed_integer_below_modulus bytes).mp yes)
    rw [sourceInputEval, if_neg flag, if_neg canonical]
    rfl

def mathematicalInputEval : ScalarInputProgram → Option Nat
  | .raw words => some (packWords words.toList % nullifierModulus)
  | .wide bytes => some (decodeLE bytes.toList % nullifierModulus)
  | .bytes bytes => if decodeLE bytes.toList < nullifierModulus then some (decodeLE bytes.toList) else none
  | .add left right => do
    let a ← mathematicalInputEval left
    let b ← mathematicalInputEval right
    pure ((a + b) % nullifierModulus)
  | .sub left right => do
    let a ← mathematicalInputEval left
    let b ← mathematicalInputEval right
    pure ((a + nullifierModulus - b) % nullifierModulus)
  | .mul left right => do
    let a ← mathematicalInputEval left
    let b ← mathematicalInputEval right
    pure ((a * b) % nullifierModulus)
  | .neg value => do
    let a ← mathematicalInputEval value
    pure ((nullifierModulus - a) % nullifierModulus)
  | .double value => do
    let a ← mathematicalInputEval value
    pure ((a + a) % nullifierModulus)

theorem entire_represented_source_input_evaluator_has_exact_independent_mathematical_field_semantics
    (program : ScalarInputProgram) :
    (sourceInputEval program).map (fun scalar => montgomeryValue scalar.words) = mathematicalInputEval program := by
  induction program with
  | raw words => exact raw_source_input_constructor_has_derived_integer_residue_semantics words
  | wide bytes => exact wide_source_input_constructor_has_derived_integer_residue_semantics bytes
  | bytes bytes => exact canonical_byte_source_input_constructor_has_derived_integer_and_refusal_semantics bytes
  | add left right leftIH rightIH =>
    change (do let a ← sourceInputEval left; let b ← sourceInputEval right; pure (sourceCanonicalAdd a b)).map
      (fun scalar => montgomeryValue scalar.words) = _
    rw [mapped_canonical_option_binary_operation_preserves_derived_field_semantics _ _ _ _
      TransferScalarAdditiveField01.actual_source_canonical_add_has_exact_mathematical_field_sum, leftIH, rightIH]
    rfl
  | sub left right leftIH rightIH =>
    change (do let a ← sourceInputEval left; let b ← sourceInputEval right; pure (sourceCanonicalSub a b)).map
      (fun scalar => montgomeryValue scalar.words) = _
    rw [mapped_canonical_option_binary_operation_preserves_derived_field_semantics _ _ _ _
      TransferScalarAdditiveField01.actual_source_canonical_sub_has_exact_mathematical_field_difference, leftIH, rightIH]
    rfl
  | mul left right leftIH rightIH =>
    change (do let a ← sourceInputEval left; let b ← sourceInputEval right; pure (sourceCanonicalMul a b)).map
      (fun scalar => montgomeryValue scalar.words) = _
    rw [mapped_canonical_option_binary_operation_preserves_derived_field_semantics _ _ _ _
      TransferScalarFieldValues01.actual_modeled_canonical_multiply_has_exact_mathematical_field_value, leftIH, rightIH]
    rfl
  | neg value ih =>
    change (do let a ← sourceInputEval value; pure (sourceCanonicalNeg a)).map (fun scalar => montgomeryValue scalar.words) = _
    rw [mapped_canonical_option_unary_operation_preserves_derived_field_semantics _ _ _
      TransferScalarAdditiveField01.actual_source_canonical_negation_has_exact_mathematical_field_value, ih]
    rfl
  | double value ih =>
    change (do let a ← sourceInputEval value; pure (sourceCanonicalAdd a a)).map (fun scalar => montgomeryValue scalar.words) = _
    rw [mapped_canonical_option_unary_operation_preserves_derived_field_semantics _ _ _
      (fun a => TransferScalarAdditiveField01.actual_source_canonical_add_has_exact_mathematical_field_sum a a), ih]
    rfl

set_option pp.all true in
#check @mapped_canonical_option_binary_operation_preserves_derived_field_semantics
#print axioms mapped_canonical_option_binary_operation_preserves_derived_field_semantics
set_option pp.all true in
#check @mapped_canonical_option_unary_operation_preserves_derived_field_semantics
#print axioms mapped_canonical_option_unary_operation_preserves_derived_field_semantics
set_option pp.all true in
#check @raw_source_input_constructor_has_derived_integer_residue_semantics
#print axioms raw_source_input_constructor_has_derived_integer_residue_semantics
set_option pp.all true in
#check @wide_source_input_constructor_has_derived_integer_residue_semantics
#print axioms wide_source_input_constructor_has_derived_integer_residue_semantics
set_option pp.all true in
#check @canonical_byte_source_input_constructor_has_derived_integer_and_refusal_semantics
#print axioms canonical_byte_source_input_constructor_has_derived_integer_and_refusal_semantics
set_option pp.all true in
#check @mathematicalInputEval
#print axioms mathematicalInputEval
set_option pp.all true in
#check @entire_represented_source_input_evaluator_has_exact_independent_mathematical_field_semantics
#print axioms entire_represented_source_input_evaluator_has_exact_independent_mathematical_field_semantics
end ShielddSecurity.TransferScalarInputSemantics01
