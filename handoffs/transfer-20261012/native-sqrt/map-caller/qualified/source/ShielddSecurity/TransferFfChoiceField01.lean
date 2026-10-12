import ShielddSecurity.TransferSqrtProducerField01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferFfChoiceField01
open TransferCanonicalWordEquality01 (CanonicalScalar)
open TransferScalarChoiceMasks01 (SourceChoiceByte sourceChoiceFromBool sourceMaskedScalarSelect valid_source_choice_byte_is_exactly_zero_or_one)
open TransferSqrtLoopPrimitives01
open TransferSqrtProducerField01
/-! Every ff source Choice/operator is interpreted in the exact prime field
and unsigned-index values. No boolean branch or operand equality is supplied
as a premise. Native compiler/private/caller origins remain separate. -/

def sourceBit (choice : SourceChoiceByte) : Bool := decide (choice.byte ≠ 0)

theorem every_valid_source_choice_has_the_exact_boolean_byte (choice : SourceChoiceByte) :
    choice.byte = if sourceBit choice then 1 else 0 := by
  rcases valid_source_choice_byte_is_exactly_zero_or_one choice with zero | one
  · simp [sourceBit, zero]
  · simp [sourceBit, one]

theorem literal_source_bool_choice_has_the_exact_bit (bit : Bool) :
    sourceBit (sourceChoiceFromBool bit) = bit := by cases bit <;> rfl

theorem source_choice_not_has_the_exact_boolean_negation (choice : SourceChoiceByte) :
    sourceBit (sourceNotChoice choice) = !sourceBit choice := by
  rcases valid_source_choice_byte_is_exactly_zero_or_one choice with zero | one
  · simp [sourceBit, sourceNotChoice, TransferScalarConstantEquality01.sourceNotChoiceByte, zero]
  · simp [sourceBit, sourceNotChoice, TransferScalarConstantEquality01.sourceNotChoiceByte, one]

theorem source_choice_and_has_the_exact_boolean_conjunction (a b : SourceChoiceByte) :
    sourceBit (sourceAndChoice a b) = (sourceBit a && sourceBit b) := by
  rcases valid_source_choice_byte_is_exactly_zero_or_one a with zero | one <;>
    rcases valid_source_choice_byte_is_exactly_zero_or_one b with zero' | one'
  · simp [sourceBit, sourceAndChoice, zero, zero']
  · simp [sourceBit, sourceAndChoice, zero, one']
  · simp [sourceBit, sourceAndChoice, one, zero']
  · simp [sourceBit, sourceAndChoice, one, one']

theorem source_scalar_masked_selection_has_the_exact_boolean_field_branch
    (a b : CanonicalScalar) (choice : SourceChoiceByte) :
    sourceFieldValue (sourceMaskedScalarSelect a b choice) =
      if sourceBit choice then sourceFieldValue b else sourceFieldValue a := by
  rw [source_field_masked_selection_has_exact_branch]
  rcases valid_source_choice_byte_is_exactly_zero_or_one choice with zero | one
  · simp [sourceBit, zero]
  · simp [sourceBit, one]

theorem source_u32_masked_selection_has_the_exact_boolean_index_branch
    (a b : UInt32) (choice : SourceChoiceByte) :
    (sourceU32Select a b choice).toNat =
      if sourceBit choice then b.toNat else a.toNat := by
  rw [source_u32_masked_selection_is_exact]
  rcases valid_source_choice_byte_is_exactly_zero_or_one choice with zero | one
  · simp [sourceBit, zero]
  · simp [sourceBit, one]

theorem source_scalar_equality_choice_has_the_exact_field_equality_bit (a b : CanonicalScalar) :
    sourceBit (sourceScalarEqChoice a b) = decide (sourceFieldValue a = sourceFieldValue b) := by
  unfold sourceBit
  rw [source_scalar_choice_equality_is_exact]
  by_cases same : a.words = b.words
  · have mathematical := (source_field_value_equality_is_exact_word_equality a b).mpr same
    simp [same, mathematical]
  · have mathematical : sourceFieldValue a ≠ sourceFieldValue b := fun equal =>
      same ((source_field_value_equality_is_exact_word_equality a b).mp equal)
    simp [same, mathematical]

theorem source_u32_equality_choice_has_the_exact_unsigned_integer_equality_bit (a b : UInt32) :
    sourceBit (sourceU32EqChoice a b) = decide (a.toNat = b.toNat) := by
  change decide (sourceU32CtEqByte a b ≠ 0) = _
  rw [source_u32_ct_equality_is_exact]
  by_cases same : a = b
  · simp [same]
  · have numerical : a.toNat ≠ b.toNat := fun equal => same (UInt32.toNat_inj.mp equal)
    simp [same, numerical]

theorem source_field_one_has_the_exact_mathematical_one :
    sourceFieldValue TransferScalarPowInvariant01.sourceOne = 1 := by
  unfold sourceFieldValue
  rw [TransferScalarPowInvariant01.source_zero_and_one_constants_have_exact_canonical_montgomery_keys.2]
  exact Nat.cast_one

set_option pp.all true in
#check @sourceBit
#print axioms sourceBit
set_option pp.all true in
#check @every_valid_source_choice_has_the_exact_boolean_byte
#print axioms every_valid_source_choice_has_the_exact_boolean_byte
set_option pp.all true in
#check @literal_source_bool_choice_has_the_exact_bit
#print axioms literal_source_bool_choice_has_the_exact_bit
set_option pp.all true in
#check @source_choice_not_has_the_exact_boolean_negation
#print axioms source_choice_not_has_the_exact_boolean_negation
set_option pp.all true in
#check @source_choice_and_has_the_exact_boolean_conjunction
#print axioms source_choice_and_has_the_exact_boolean_conjunction
set_option pp.all true in
#check @source_scalar_masked_selection_has_the_exact_boolean_field_branch
#print axioms source_scalar_masked_selection_has_the_exact_boolean_field_branch
set_option pp.all true in
#check @source_u32_masked_selection_has_the_exact_boolean_index_branch
#print axioms source_u32_masked_selection_has_the_exact_boolean_index_branch
set_option pp.all true in
#check @source_scalar_equality_choice_has_the_exact_field_equality_bit
#print axioms source_scalar_equality_choice_has_the_exact_field_equality_bit
set_option pp.all true in
#check @source_u32_equality_choice_has_the_exact_unsigned_integer_equality_bit
#print axioms source_u32_equality_choice_has_the_exact_unsigned_integer_equality_bit
set_option pp.all true in
#check @source_field_one_has_the_exact_mathematical_one
#print axioms source_field_one_has_the_exact_mathematical_one
end ShielddSecurity.TransferFfChoiceField01
