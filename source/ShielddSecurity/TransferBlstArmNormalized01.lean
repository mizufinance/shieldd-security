import ShielddSecurity.TransferBlstArmReduction01
import ShielddSecurity.TransferBlstByteRoundtrip01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmNormalized01
open TransferScalarSerializationRange01 (radix64 normalize)
open TransferScalarWordPrimitives01 (packWords)
open TransferScalarFourRoundWrapper01 (modulusWords nativeRounds)
open TransferScalarBorrowWalk01 (borrowWalk)
open TransferScalarSbbPrimitive01 (borrowBit)
open TransferScalarMaskedNormalization01 (sourceNormalize)
open TransferBoundedNativeCodec01 (nullifierModulus)
open TransferBlstArmReduction01

/-- Arithmetic borrow/csel interpretation of the locked final four-limb
SUBS/SBCS/CSEL sequence. ISA and pointer/ABI execution remain separate. -/
def sourceArmBorrowSelect (words : List UInt64) : List UInt64 :=
  let difference := borrowWalk false (words.zip modulusWords)
  if difference.2 then words else difference.1

theorem actual_final_borrow_select_retains_the_four_word_width
    (words : List UInt64) (four : words.length=4) : (sourceArmBorrowSelect words).length=4 := by
  have differenceWidth : (borrowWalk false (words.zip modulusWords)).1.length=4 := by
    rw [TransferScalarBorrowWalk01.borrow_walk_retains_limb_count,List.length_zip,four,
      TransferScalarFourRoundWrapper01.modulus_words_have_four_limbs,Nat.min_self]
  unfold sourceArmBorrowSelect
  dsimp only
  split
  · exact four
  · exact differenceWidth

theorem actual_final_borrow_select_derives_exact_single_modulus_normalization
    (words : List UInt64) (four : words.length=4) :
    packWords (sourceArmBorrowSelect words) = normalize nullifierModulus (packWords words) := by
  have modulusWidth := TransferScalarFourRoundWrapper01.modulus_words_have_four_limbs
  have leftProjection : words.length ≤ modulusWords.length := by rw [four,modulusWidth]
  have rightProjection : modulusWords.length ≤ words.length := by rw [four,modulusWidth]
  have equation := TransferScalarBorrowWalk01.borrow_walk_conserves_full_subtraction_equation
    false (words.zip modulusWords)
  rw [List.map_fst_zip leftProjection,List.map_snd_zip rightProjection,
    TransferScalarFourRoundWrapper01.modulus_words_pack_to_actual_nullifier_modulus] at equation
  simp only [borrowBit,Bool.false_eq_true,if_false,Nat.add_zero] at equation
  have underflow := TransferScalarBorrowWalk01.final_borrow_is_exact_input_underflow (words.zip modulusWords)
  rw [List.map_fst_zip leftProjection,List.map_snd_zip rightProjection,
    TransferScalarFourRoundWrapper01.modulus_words_pack_to_actual_nullifier_modulus] at underflow
  unfold sourceArmBorrowSelect
  dsimp only
  cases flag : (borrowWalk false (words.zip modulusWords)).2 with
  | false =>
    have enough : nullifierModulus ≤ packWords words := by
      have absent : ¬ packWords words < nullifierModulus := by
        intro below
        have trueFlag := underflow.mpr below
        rw [flag] at trueFlag
        cases trueFlag
      exact Nat.le_of_not_gt absent
    simp only [Bool.false_eq_true,if_false]
    rw [TransferScalarSerializationRange01.normalize,if_pos enough]
    simp only [flag,Bool.false_eq_true,if_false,Nat.mul_zero,Nat.add_zero] at equation
    omega
  | true =>
    have below : packWords words < nullifierModulus := underflow.mp flag
    rw [if_pos (rfl : true=true),TransferScalarSerializationRange01.normalize,if_neg (Nat.not_le_of_lt below)]

theorem actual_final_borrow_select_derives_the_qualified_normalized_word_vector
    (words : List UInt64) (four : words.length=4) : sourceArmBorrowSelect words = sourceNormalize words := by
  apply TransferCanonicalWordEquality01.equal_width_packed_u64_lists_are_equal
  · rw [actual_final_borrow_select_retains_the_four_word_width words four,
      TransferScalarMaskedNormalization01.source_normalization_retains_four_word_width words four]
  · rw [actual_final_borrow_select_derives_exact_single_modulus_normalization words four,
      TransferScalarMaskedNormalization01.source_sub_and_masked_addback_equal_single_modulus_normalization words four]

def sourceArmFromMontWords (words : List UInt64) : List UInt64 :=
  sourceArmBorrowSelect (sourceArmReductionRounds 4 words)

theorem actual_full_from_mont_source_program_derives_every_qualified_output_word
    (words : List UInt64) (four : words.length=4) :
    sourceArmFromMontWords words = sourceNormalize (nativeRounds 4 words) := by
  rw [sourceArmFromMontWords,symbolic_actual_arm_reduction_rounds_equal_the_qualified_word_recurrence 4 words four]
  exact actual_final_borrow_select_derives_the_qualified_normalized_word_vector _
    (TransferScalarFourRoundWrapper01.native_round_walk_preserves_four_word_width 4 words four)

theorem actual_full_from_mont_source_program_retains_the_four_limb_width
    (words : List UInt64) (four : words.length=4) : (sourceArmFromMontWords words).length=4 := by
  rw [actual_full_from_mont_source_program_derives_every_qualified_output_word words four]
  exact TransferScalarMaskedNormalization01.source_normalization_retains_four_word_width _
    (TransferScalarFourRoundWrapper01.native_round_walk_preserves_four_word_width 4 words four)

theorem actual_full_from_mont_source_program_derives_the_original_montgomery_value
    (words : Vector UInt64 4) :
    packWords (sourceArmFromMontWords words.toList) = TransferScalarMontgomeryValue01.montgomeryValue words := by
  rw [actual_full_from_mont_source_program_derives_every_qualified_output_word words.toList Vector.length_toList]
  calc
    _ = TransferScalarLittleEndianBytes01.decodeLE (TransferScalarLittleEndianBytes01.serializerBytes words.toList) :=
      (TransferScalarLittleEndianBytes01.serialized_word_vector_reconstructs_actual_packed_words _).symm
    _ = _ := TransferScalarMontgomeryValue01.fixed_four_word_typed_serializer_has_exact_canonical_montgomery_value words

def sourceArmFromMontVector (words : Vector UInt64 4) : Vector UInt64 4 :=
  ⟨(sourceArmFromMontWords words.toList).toArray,by
    rw [List.size_toArray,actual_full_from_mont_source_program_retains_the_four_limb_width words.toList Vector.length_toList]⟩

theorem actual_full_from_mont_fixed_vector_is_the_actual_four_output_words
    (words : Vector UInt64 4) :
    (sourceArmFromMontVector words).toList = sourceArmFromMontWords words.toList := by
  simp only [sourceArmFromMontVector,Vector.toList,List.toList_toArray]

def sourceBlstFrWordMeaning (words : Vector UInt64 4) : ZMod nullifierModulus :=
  (TransferScalarMontgomeryValue01.montgomeryValue words : ZMod nullifierModulus)

theorem actual_full_from_mont_output_derives_its_input_representation_field_value
    (words : Vector UInt64 4) :
    packWords (sourceArmFromMontVector words).toList = (sourceBlstFrWordMeaning words).val := by
  have bound : TransferScalarMontgomeryValue01.montgomeryValue words < nullifierModulus := by
    rw [← TransferScalarMontgomeryValue01.fixed_four_word_typed_serializer_has_exact_canonical_montgomery_value]
    exact TransferScalarLittleEndianBytes01.fixed_four_word_source_scalar_projection_is_canonical words
  rw [actual_full_from_mont_fixed_vector_is_the_actual_four_output_words,
    actual_full_from_mont_source_program_derives_the_original_montgomery_value,
    sourceBlstFrWordMeaning,ZMod.val_natCast,Nat.mod_eq_of_lt bound]

theorem actual_full_from_mont_and_complete_encoder_chain_derive_every_input_field_byte
    (words : Vector UInt64 4) (index : Fin 32) :
    TransferBlstByteCaller01.sourceScalarBendianBytes64 (sourceArmFromMontVector words) index =
      TransferCommonwareMapBytes01.canonicalBEByte (sourceBlstFrWordMeaning words) index := by
  exact TransferBlstByteRoundtrip01.actual_le_parser_be_writer_chain_derives_every_canonical_field_byte
    _ _ (actual_full_from_mont_output_derives_its_input_representation_field_value words) index
set_option pp.all true in
#check @sourceArmBorrowSelect
#print axioms sourceArmBorrowSelect
set_option pp.all true in
#check @actual_final_borrow_select_retains_the_four_word_width
#print axioms actual_final_borrow_select_retains_the_four_word_width
set_option pp.all true in
#check @actual_final_borrow_select_derives_exact_single_modulus_normalization
#print axioms actual_final_borrow_select_derives_exact_single_modulus_normalization
set_option pp.all true in
#check @actual_final_borrow_select_derives_the_qualified_normalized_word_vector
#print axioms actual_final_borrow_select_derives_the_qualified_normalized_word_vector
set_option pp.all true in
#check @sourceArmFromMontWords
#print axioms sourceArmFromMontWords
set_option pp.all true in
#check @actual_full_from_mont_source_program_derives_every_qualified_output_word
#print axioms actual_full_from_mont_source_program_derives_every_qualified_output_word
set_option pp.all true in
#check @actual_full_from_mont_source_program_retains_the_four_limb_width
#print axioms actual_full_from_mont_source_program_retains_the_four_limb_width
set_option pp.all true in
#check @actual_full_from_mont_source_program_derives_the_original_montgomery_value
#print axioms actual_full_from_mont_source_program_derives_the_original_montgomery_value
set_option pp.all true in
#check @sourceArmFromMontVector
#print axioms sourceArmFromMontVector
set_option pp.all true in
#check @actual_full_from_mont_fixed_vector_is_the_actual_four_output_words
#print axioms actual_full_from_mont_fixed_vector_is_the_actual_four_output_words
set_option pp.all true in
#check @sourceBlstFrWordMeaning
#print axioms sourceBlstFrWordMeaning
set_option pp.all true in
#check @actual_full_from_mont_output_derives_its_input_representation_field_value
#print axioms actual_full_from_mont_output_derives_its_input_representation_field_value
set_option pp.all true in
#check @actual_full_from_mont_and_complete_encoder_chain_derive_every_input_field_byte
#print axioms actual_full_from_mont_and_complete_encoder_chain_derive_every_input_field_byte
end ShielddSecurity.TransferBlstArmNormalized01
