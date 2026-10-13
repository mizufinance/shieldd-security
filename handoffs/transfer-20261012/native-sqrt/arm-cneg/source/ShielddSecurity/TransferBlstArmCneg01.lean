import ShielddSecurity.TransferBlstArmCaller01
import ShielddSecurity.TransferScalarAdditiveField01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmCneg01
open TransferCanonicalWordEquality01 (CanonicalScalar)
open TransferScalarWordPrimitives01 (packWords)
open TransferScalarBorrowWalk01 (borrowWalk)
open TransferScalarFourRoundWrapper01 (modulusWords)
open TransferScalarCanonicalNeg01 (orWalk)
open TransferScalarSbbPrimitive01 (borrowBit)
open TransferBoundedNativeCodec01 (nullifierModulus)
open TransferBlstArmNormalized01 (sourceBlstFrWordMeaning)
open TransferBlstArmCaller01
attribute [local irreducible] TransferBlstArmNormalized01.sourceArmFromMontVector
  TransferBlstByteCaller01.sourceScalarLEBytes64 TransferBlstByteCaller01.sourceLEParseMemory64
  TransferBlstEncoder01.sourceBEFromLimbs64 sourceAsSlice sourceScalarFromFr sourceBendianFromScalar

/-- Arithmetic transcription of locked ARM cneg: modulus-input borrow chain,
OR nonzero detector, flag AND and CSEL. The OR tree is represented by its
symbolic fold. Actual register/flag/pointer/ABI execution remains separate. -/
def sourceArmCnegWords (flag : Bool) (words : Vector UInt64 4) : List UInt64 :=
  let difference := borrowWalk false (modulusWords.zip words.toList)
  if flag && decide (orWalk 0 words.toList ≠ 0) then difference.1 else words.toList

attribute [local irreducible] sourceArmCnegWords

theorem source_arm_cneg_retains_the_four_limb_width (flag : Bool) (words : Vector UInt64 4) :
    (sourceArmCnegWords flag words).length = 4 := by
  have width : (borrowWalk false (modulusWords.zip words.toList)).1.length = 4 := by
    rw [TransferScalarBorrowWalk01.borrow_walk_retains_limb_count,List.length_zip,
      TransferScalarFourRoundWrapper01.modulus_words_have_four_limbs,Vector.length_toList,Nat.min_self]
  unfold sourceArmCnegWords
  dsimp only
  split
  · exact width
  · exact Vector.length_toList

theorem source_modulus_subtraction_on_canonical_input_has_no_borrow_and_exact_difference
    (scalar : CanonicalScalar) :
    (borrowWalk false (modulusWords.zip scalar.words.toList)).2 = false ∧
      packWords (borrowWalk false (modulusWords.zip scalar.words.toList)).1 =
        nullifierModulus - packWords scalar.words.toList := by
  have leftProjection : modulusWords.length ≤ scalar.words.toList.length := by
    rw [TransferScalarFourRoundWrapper01.modulus_words_have_four_limbs,Vector.length_toList]
  have rightProjection : scalar.words.toList.length ≤ modulusWords.length := by
    rw [TransferScalarFourRoundWrapper01.modulus_words_have_four_limbs,Vector.length_toList]
  have underflow := TransferScalarBorrowWalk01.final_borrow_is_exact_input_underflow
    (modulusWords.zip scalar.words.toList)
  rw [List.map_fst_zip leftProjection,List.map_snd_zip rightProjection,
    TransferScalarFourRoundWrapper01.modulus_words_pack_to_actual_nullifier_modulus] at underflow
  have noBorrow : (borrowWalk false (modulusWords.zip scalar.words.toList)).2 = false := by
    cases flag : (borrowWalk false (modulusWords.zip scalar.words.toList)).2 with
    | false => rfl
    | true => exact False.elim ((Nat.not_lt_of_ge (Nat.le_of_lt scalar.canonical)) (underflow.mp flag))
  have conserved := TransferScalarBorrowWalk01.borrow_walk_conserves_full_subtraction_equation
    false (modulusWords.zip scalar.words.toList)
  rw [List.map_fst_zip leftProjection,List.map_snd_zip rightProjection,
    TransferScalarFourRoundWrapper01.modulus_words_pack_to_actual_nullifier_modulus,noBorrow] at conserved
  simp only [borrowBit,Bool.false_eq_true,if_false,Nat.mul_zero,Nat.add_zero] at conserved
  exact ⟨noBorrow,Nat.eq_sub_of_add_eq conserved⟩

theorem source_arm_cneg_derives_the_canonical_raw_output
    (flag : Bool) (scalar : CanonicalScalar) :
    packWords (sourceArmCnegWords flag scalar.words) =
      if flag then (nullifierModulus - packWords scalar.words.toList) % nullifierModulus
        else packWords scalar.words.toList := by
  cases flag with
  | false => simp only [sourceArmCnegWords,Bool.false_and,Bool.false_eq_true,if_false]
  | true =>
    by_cases zero : packWords scalar.words.toList = 0
    · have detector := (TransferScalarCanonicalNeg01.symbolic_or_zero_detector_is_exact_packed_word_zero
        0 scalar.words.toList).mpr ⟨rfl,zero⟩
      simp [sourceArmCnegWords,detector,zero]
    · have detector : orWalk 0 scalar.words.toList ≠ 0 := by
        intro impossible
        exact zero ((TransferScalarCanonicalNeg01.symbolic_or_zero_detector_is_exact_packed_word_zero
          0 scalar.words.toList).mp impossible).2
      have difference := (source_modulus_subtraction_on_canonical_input_has_no_borrow_and_exact_difference scalar).2
      have below : nullifierModulus - packWords scalar.words.toList < nullifierModulus := by
        have := scalar.canonical
        omega
      have selected : decide (orWalk 0 scalar.words.toList ≠ 0) = true := decide_eq_true detector
      simp only [sourceArmCnegWords,Bool.true_and,if_true]
      rw [if_pos selected,difference,Nat.mod_eq_of_lt below]

theorem source_arm_cneg_derives_output_canonicality (flag : Bool) (scalar : CanonicalScalar) :
    packWords (sourceArmCnegWords flag scalar.words) < nullifierModulus := by
  rw [source_arm_cneg_derives_the_canonical_raw_output]
  cases flag with
  | false => exact scalar.canonical
  | true => exact Nat.mod_lt _ (by decide)

def sourceArmCneg (flag : Bool) (scalar : CanonicalScalar) : CanonicalScalar :=
  TransferScalarProgramInvariant01.certifyResult (sourceArmCnegWords flag scalar.words)
    (source_arm_cneg_retains_the_four_limb_width flag scalar.words)
    (source_arm_cneg_derives_output_canonicality flag scalar)

theorem original_fr_word_meaning_is_the_raw_montgomery_residue (words : Vector UInt64 4) :
    sourceBlstFrWordMeaning words =
      (TransferScalarMontgomeryValue01.radixInverse : ZMod nullifierModulus) *
        (packWords words.toList : ZMod nullifierModulus) := by
  rw [sourceBlstFrWordMeaning,TransferScalarMontgomeryValue01.montgomeryValue,
    ZMod.natCast_mod,Nat.cast_mul]

theorem source_arm_cneg_derives_the_input_field_negation (flag : Bool) (scalar : CanonicalScalar) :
    sourceBlstFrWordMeaning (sourceArmCneg flag scalar).words =
      if flag then -sourceBlstFrWordMeaning scalar.words else sourceBlstFrWordMeaning scalar.words := by
  have output : packWords (sourceArmCneg flag scalar).words.toList =
      packWords (sourceArmCnegWords flag scalar.words) := by
    change packWords (sourceArmCnegWords flag scalar.words).toArray.toList = _
    rw [List.toList_toArray]
  rw [original_fr_word_meaning_is_the_raw_montgomery_residue,output,
    source_arm_cneg_derives_the_canonical_raw_output]
  cases flag with
  | false => exact (original_fr_word_meaning_is_the_raw_montgomery_residue scalar.words).symm
  | true =>
    simp only [if_true]
    rw [ZMod.natCast_mod,Nat.cast_sub (Nat.le_of_lt scalar.canonical),ZMod.natCast_self,
      zero_sub,mul_neg,← original_fr_word_meaning_is_the_raw_montgomery_residue]

/-- Original input words feed both the byte guard and conditional negation.
The canonical raw-input domain is explicit, and output invariants are derived. -/
def sourceCallerCorrectedRoot (choice : Bool) (scalar : CanonicalScalar)
    (scratch : Vector UInt64 4) : CanonicalScalar :=
  let memory : CallerMemory := (scalar.words,Vector.replicate 32 0,Vector.replicate 32 0)
  sourceArmCneg (sourceCallerSignGuard choice memory scratch) scalar

theorem original_caller_byte_guard_and_cneg_derive_the_same_canonical_root
    (choice : Bool) (scalar : CanonicalScalar) (scratch : Vector UInt64 4) :
    sourceBlstFrWordMeaning (sourceCallerCorrectedRoot choice scalar scratch).words =
      TransferCommonwareMapRoots01.normalizeRoot choice (sourceBlstFrWordMeaning scalar.words) := by
  rw [sourceCallerCorrectedRoot,source_arm_cneg_derives_the_input_field_negation]
  exact caller_selected_meaning_derives_the_qualified_root_normalizer choice _ scratch
set_option pp.all true in
#check @sourceArmCnegWords
#print axioms sourceArmCnegWords
set_option pp.all true in
#check @source_arm_cneg_retains_the_four_limb_width
#print axioms source_arm_cneg_retains_the_four_limb_width
set_option pp.all true in
#check @source_modulus_subtraction_on_canonical_input_has_no_borrow_and_exact_difference
#print axioms source_modulus_subtraction_on_canonical_input_has_no_borrow_and_exact_difference
set_option pp.all true in
#check @source_arm_cneg_derives_the_canonical_raw_output
#print axioms source_arm_cneg_derives_the_canonical_raw_output
set_option pp.all true in
#check @source_arm_cneg_derives_output_canonicality
#print axioms source_arm_cneg_derives_output_canonicality
set_option pp.all true in
#check @sourceArmCneg
#print axioms sourceArmCneg
set_option pp.all true in
#check @original_fr_word_meaning_is_the_raw_montgomery_residue
#print axioms original_fr_word_meaning_is_the_raw_montgomery_residue
set_option pp.all true in
#check @source_arm_cneg_derives_the_input_field_negation
#print axioms source_arm_cneg_derives_the_input_field_negation
set_option pp.all true in
#check @sourceCallerCorrectedRoot
#print axioms sourceCallerCorrectedRoot
set_option pp.all true in
#check @original_caller_byte_guard_and_cneg_derive_the_same_canonical_root
#print axioms original_caller_byte_guard_and_cneg_derive_the_same_canonical_root
end ShielddSecurity.TransferBlstArmCneg01
