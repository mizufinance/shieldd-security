import ShielddSecurity.TransferScalarPowInvariant01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferScalarChoiceMasks01
open TransferCanonicalWordEquality01 (CanonicalScalar)
open TransferScalarWordPrimitives01 (packWords)
open TransferBoundedNativeCodec01 (nullifierModulus)
open TransferScalarPowInvariant01
/-! Locked subtle2.6.1 word select/assign uses a XOR (-choice AND (a XOR b)).
Choice's documented byte invariant is explicit, rather than inferred from
its debug-only assertion. The actual modeled power shift/mask cast derives
this invariant. Rust compiler/volatile barrier/caller origin/timing remains
separate; these theorems concern the source-shaped word values. -/

structure SourceChoiceByte where
  byte : UInt8
  valid : byte.toNat < 2

theorem valid_source_choice_byte_is_exactly_zero_or_one (choice : SourceChoiceByte) :
    choice.byte = 0 ∨ choice.byte = 1 := by
  have bounded := choice.valid
  have casesByte : choice.byte.toNat = 0 ∨ choice.byte.toNat = 1 := by omega
  rcases casesByte with zero | one
  · exact Or.inl (UInt8.toNat_inj.mp zero)
  · exact Or.inr (UInt8.toNat_inj.mp one)

def sourceChoiceFromBool (bit : Bool) : SourceChoiceByte :=
  if bit then ⟨1, by decide⟩ else ⟨0, by decide⟩

def sourceChoiceMask (choice : SourceChoiceByte) : UInt64 :=
  -(UInt64.ofNat choice.byte.toNat)

def sourceWordSelect (a b : UInt64) (choice : SourceChoiceByte) : UInt64 :=
  a ^^^ (sourceChoiceMask choice &&& (a ^^^ b))

theorem exact_source_choice_mask_is_zero_or_all_ones (choice : SourceChoiceByte) :
    sourceChoiceMask choice = if choice.byte = 0 then 0 else (-1 : UInt64) := by
  rcases valid_source_choice_byte_is_exactly_zero_or_one choice with zero | one
  · rw [sourceChoiceMask, zero] <;> rfl
  · rw [sourceChoiceMask, one] <;> rfl

theorem exact_source_xor_and_word_selection_equals_the_choice_branch
    (a b : UInt64) (choice : SourceChoiceByte) :
    sourceWordSelect a b choice = if choice.byte = 0 then a else b := by
  rw [sourceWordSelect, exact_source_choice_mask_is_zero_or_all_ones]
  split
  · simp
  · simp [← UInt64.xor_assoc]

def sourceVectorSelect (a b : Vector UInt64 4) (choice : SourceChoiceByte) : Vector UInt64 4 :=
  Vector.zipWith (fun x y => sourceWordSelect x y choice) a b

theorem exact_source_four_word_selection_equals_the_whole_choice_branch
    (a b : Vector UInt64 4) (choice : SourceChoiceByte) :
    sourceVectorSelect a b choice = if choice.byte = 0 then a else b := by
  by_cases zero : choice.byte = 0
  · rw [if_pos zero]
    apply Vector.ext
    intro i bounded
    simp [sourceVectorSelect, exact_source_xor_and_word_selection_equals_the_choice_branch, zero]
  · rw [if_neg zero]
    apply Vector.ext
    intro i bounded
    simp [sourceVectorSelect, exact_source_xor_and_word_selection_equals_the_choice_branch, zero]

def sourceMaskedScalarSelect (a b : CanonicalScalar) (choice : SourceChoiceByte) : CanonicalScalar :=
  ⟨sourceVectorSelect a.words b.words choice, by
    rw [exact_source_four_word_selection_equals_the_whole_choice_branch]
    split
    · exact a.canonical
    · exact b.canonical⟩

theorem canonical_scalar_objects_equal_of_exact_raw_word_equality
    (a b : CanonicalScalar) (same : a.words = b.words) : a = b := by
  cases a
  cases b
  cases same
  rfl

theorem exact_source_masked_scalar_selection_equals_the_whole_canonical_branch
    (a b : CanonicalScalar) (choice : SourceChoiceByte) :
    sourceMaskedScalarSelect a b choice = if choice.byte = 0 then a else b := by
  apply canonical_scalar_objects_equal_of_exact_raw_word_equality
  change sourceVectorSelect a.words b.words choice = (if choice.byte = 0 then a else b).words
  rw [exact_source_four_word_selection_equals_the_whole_choice_branch]
  split <;> rfl

def sourceMaskedConstantTimeStep (self current : CanonicalScalar) (bit : Bool) : CanonicalScalar :=
  let squared := sourceCanonicalSquare current
  let multiplied := sourceCanonicalMul squared self
  sourceMaskedScalarSelect squared multiplied (sourceChoiceFromBool bit)

theorem exact_source_masked_bit_step_equals_the_boolean_power_model
    (self current : CanonicalScalar) (bit : Bool) :
    sourceMaskedConstantTimeStep self current bit = sourceConstantTimeStep self current bit := by
  unfold sourceMaskedConstantTimeStep
  rw [exact_source_masked_scalar_selection_equals_the_whole_canonical_branch]
  cases bit <;> rfl

def sourceMaskedPow (self : CanonicalScalar) (exponent : Vector UInt64 4) : CanonicalScalar :=
  sourcePowLoop (sourceMaskedConstantTimeStep self) exponent

theorem exact_source_word_masked_power_loop_equals_the_boolean_power_model
    (self : CanonicalScalar) (exponent : Vector UInt64 4) :
    sourceMaskedPow self exponent = sourcePow self exponent := by
  have stepSame : sourceMaskedConstantTimeStep self = sourceConstantTimeStep self := by
    funext current bit
    exact exact_source_masked_bit_step_equals_the_boolean_power_model self current bit
  rw [sourceMaskedPow, sourcePow, stepSame]

theorem exact_source_word_masked_power_has_derived_canonical_serialized_field
    (self : CanonicalScalar) (exponent : Vector UInt64 4) :
    (TransferScalarLittleEndianBytes01.serializerBytes (sourceMaskedPow self exponent).words.toList).length = 32 ∧
      TransferScalarLittleEndianBytes01.decodeLE
        (TransferScalarLittleEndianBytes01.serializerBytes (sourceMaskedPow self exponent).words.toList) < nullifierModulus ∧
      TransferScalarLittleEndianBytes01.decodeLE
        (TransferScalarLittleEndianBytes01.serializerBytes (sourceMaskedPow self exponent).words.toList) =
          TransferScalarMontgomeryValue01.montgomeryValue (sourceMaskedPow self exponent).words := by
  exact TransferCheckedWordAcceptedInput01.every_original_typed_field_has_exact_32_byte_canonical_serialized_key _

def sourcePowShiftMaskCastByte (word : UInt64) (index : Nat) : UInt8 :=
  UInt8.ofNat ((word >>> UInt64.ofNat index) &&& 1).toNat

theorem actual_source_power_shift_mask_cast_derives_the_boolean_choice_byte
    (word : UInt64) (index : Nat) :
    sourcePowShiftMaskCastByte word index = (sourceChoiceFromBool (sourcePowBit word index)).byte := by
  let masked := (word >>> UInt64.ofNat index) &&& 1
  have maskedBound : masked.toNat < 2 := by
    simp only [masked, UInt64.toNat_and, UInt64.toNat_one, Nat.and_one_is_mod]
    exact Nat.mod_lt _ (by decide)
  have maskedCases : masked.toNat = 0 ∨ masked.toNat = 1 := by omega
  rcases maskedCases with zero | one
  · have actual : masked = 0 := UInt64.toNat_inj.mp zero
    change UInt8.ofNat masked.toNat = (sourceChoiceFromBool (masked == 1)).byte
    rw [actual] <;> rfl
  · have actual : masked = 1 := UInt64.toNat_inj.mp one
    change UInt8.ofNat masked.toNat = (sourceChoiceFromBool (masked == 1)).byte
    rw [actual] <;> rfl

theorem actual_source_power_choice_byte_has_derived_zero_one_invariant
    (word : UInt64) (index : Nat) : (sourcePowShiftMaskCastByte word index).toNat < 2 := by
  rw [actual_source_power_shift_mask_cast_derives_the_boolean_choice_byte]
  exact (sourceChoiceFromBool (sourcePowBit word index)).valid

set_option pp.all true in
#check @SourceChoiceByte
#print axioms SourceChoiceByte
set_option pp.all true in
#check @valid_source_choice_byte_is_exactly_zero_or_one
#print axioms valid_source_choice_byte_is_exactly_zero_or_one
set_option pp.all true in
#check @sourceChoiceFromBool
#print axioms sourceChoiceFromBool
set_option pp.all true in
#check @sourceChoiceMask
#print axioms sourceChoiceMask
set_option pp.all true in
#check @sourceWordSelect
#print axioms sourceWordSelect
set_option pp.all true in
#check @exact_source_choice_mask_is_zero_or_all_ones
#print axioms exact_source_choice_mask_is_zero_or_all_ones
set_option pp.all true in
#check @exact_source_xor_and_word_selection_equals_the_choice_branch
#print axioms exact_source_xor_and_word_selection_equals_the_choice_branch
set_option pp.all true in
#check @sourceVectorSelect
#print axioms sourceVectorSelect
set_option pp.all true in
#check @exact_source_four_word_selection_equals_the_whole_choice_branch
#print axioms exact_source_four_word_selection_equals_the_whole_choice_branch
set_option pp.all true in
#check @sourceMaskedScalarSelect
#print axioms sourceMaskedScalarSelect
set_option pp.all true in
#check @canonical_scalar_objects_equal_of_exact_raw_word_equality
#print axioms canonical_scalar_objects_equal_of_exact_raw_word_equality
set_option pp.all true in
#check @exact_source_masked_scalar_selection_equals_the_whole_canonical_branch
#print axioms exact_source_masked_scalar_selection_equals_the_whole_canonical_branch
set_option pp.all true in
#check @sourceMaskedConstantTimeStep
#print axioms sourceMaskedConstantTimeStep
set_option pp.all true in
#check @exact_source_masked_bit_step_equals_the_boolean_power_model
#print axioms exact_source_masked_bit_step_equals_the_boolean_power_model
set_option pp.all true in
#check @sourceMaskedPow
#print axioms sourceMaskedPow
set_option pp.all true in
#check @exact_source_word_masked_power_loop_equals_the_boolean_power_model
#print axioms exact_source_word_masked_power_loop_equals_the_boolean_power_model
set_option pp.all true in
#check @exact_source_word_masked_power_has_derived_canonical_serialized_field
#print axioms exact_source_word_masked_power_has_derived_canonical_serialized_field
set_option pp.all true in
#check @sourcePowShiftMaskCastByte
#print axioms sourcePowShiftMaskCastByte
set_option pp.all true in
#check @actual_source_power_shift_mask_cast_derives_the_boolean_choice_byte
#print axioms actual_source_power_shift_mask_cast_derives_the_boolean_choice_byte
set_option pp.all true in
#check @actual_source_power_choice_byte_has_derived_zero_one_invariant
#print axioms actual_source_power_choice_byte_has_derived_zero_one_invariant
end ShielddSecurity.TransferScalarChoiceMasks01
