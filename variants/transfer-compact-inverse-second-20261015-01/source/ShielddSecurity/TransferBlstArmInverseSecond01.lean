import ShielddSecurity.TransferBlstArmInverseFirst01
import ShielddSecurity.TransferBlstArmInverseMask01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseSecond01
open TransferBlstArmInverseFirst01 (WideState sourceWideMeaning sourceWideRaw sourceFourRadix)
open TransferBlstArmInverseSign01 (sourceRx2 sourceWideRadix sourceCorrectionShift sourceSignedFirst sourceSignedCorrection)
open TransferBlstArmInverseMask01 (sourceOperandVector)
open TransferBlstArmAdd01 (sourceArmAddRaw)
open TransferScalarWordPrimitives01 (packWords)
open TransferScalarSerializationRange01 (radix64)

/-! Complete word interpretation of the second inverse high-half adjustment.
Actual operand masks and captured addition carry derive the final wide words;
the extra signed top is discarded only after deriving its cancellation.
Composing the first word correction discharges the middle-range interface.
Coefficient production and native ISA/ABI remain separate. -/

def sourceSecondHigh (s : WideState) : Vector UInt64 4 :=
  ⟨(sourceArmAddRaw s.2.1 (sourceOperandVector s.2.2)).1.toArray,by
    rw [List.size_toArray,TransferBlstArmAdd01.source_arm_add_raw_retains_four_limbs]⟩

def sourceSecondWordCorrection (s : WideState) : WideState := (s.1,sourceSecondHigh s,0)

def sourceSignedSecond (value : Int) : Int :=
  if value<0 then value+sourceCorrectionShift
  else if sourceWideRadix≤value then value-sourceCorrectionShift else value

theorem original_second_high_vector_retains_the_actual_addition_words (s : WideState) :
    (sourceSecondHigh s).toList=(sourceArmAddRaw s.2.1 (sourceOperandVector s.2.2)).1 := by
  simp only [sourceSecondHigh,Vector.toList,List.toList_toArray]

theorem original_second_high_addition_conserves_the_entire_carry_equation (s : WideState) :
    sourceWideMeaning (sourceSecondWordCorrection s)+sourceWideRadix*
      ((sourceArmAddRaw s.2.1 (sourceOperandVector s.2.2)).2.toNat:Int)=
        (sourceWideRaw s:Int)+sourceFourRadix*(packWords (sourceOperandVector s.2.2).toList:Int) := by
  let operand := sourceOperandVector s.2.2
  have leftProjection : s.2.1.toList.length≤operand.toList.length := by rw [Vector.length_toList,Vector.length_toList]
  have rightProjection : operand.toList.length≤s.2.1.toList.length := by rw [Vector.length_toList,Vector.length_toList]
  have conserved := TransferBlstArmCarryChains01.symbolic_actual_add_chain_conserves_the_limb_integer_and_final_flag
    false (s.2.1.toList.zip operand.toList)
  rw [List.map_fst_zip leftProjection,List.map_snd_zip rightProjection,List.length_zip,
    Vector.length_toList,Vector.length_toList,Nat.min_self] at conserved
  change packWords (sourceArmAddRaw s.2.1 operand).1+radix64^4*(sourceArmAddRaw s.2.1 operand).2.toNat=
    packWords s.2.1.toList+packWords operand.toList+0 at conserved
  rw [Nat.add_zero] at conserved
  have interpreted : (packWords (sourceSecondHigh s).toList:Int)+sourceFourRadix*
      ((sourceArmAddRaw s.2.1 operand).2.toNat:Int)=
        (packWords s.2.1.toList:Int)+(packWords operand.toList:Int) := by
    rw [original_second_high_vector_retains_the_actual_addition_words,sourceFourRadix]
    exact_mod_cast conserved
  simp only [sourceWideMeaning,sourceWideRaw,sourceSecondWordCorrection,
    TransferBlstArmInverseFirst01.symbolic_word_append_has_the_entire_radix_weighted_value,
    Vector.length_toList,Nat.cast_add,Nat.cast_mul,mul_zero,add_zero]
  change (packWords s.1.toList:Int)+sourceFourRadix*(packWords (sourceSecondHigh s).toList:Int)+
    sourceWideRadix*((sourceArmAddRaw s.2.1 operand).2.toNat:Int)=
      (packWords s.1.toList:Int)+sourceFourRadix*(packWords s.2.1.toList:Int)+sourceFourRadix*(packWords operand.toList:Int)
  calc
    _ = (packWords s.1.toList:Int)+sourceFourRadix*((packWords (sourceSecondHigh s).toList:Int)+
      sourceFourRadix*((sourceArmAddRaw s.2.1 operand).2.toNat:Int)) := by
        rw [TransferBlstArmInverseFirst01.original_wide_radix_is_the_square_of_the_four_word_radix]
        ring
    _ = _ := by rw [interpreted]; ring

theorem middle_signed_range_derives_the_actual_extra_top_range (s : WideState)
    (lower : -sourceCorrectionShift<sourceWideMeaning s) (upper : sourceWideMeaning s≤sourceWideRadix) :
    -1≤s.2.2 ∧ s.2.2≤1 := by
  have range := TransferBlstArmInverseFirst01.original_two_four_word_halves_derive_the_unsigned_wide_range s
  have shiftBounds := TransferBlstArmInverseSign01.original_correction_shift_is_between_half_and_whole_wide_radix
  have positive : 0<sourceWideRadix := by decide
  constructor
  · by_contra absent
    have topBound : s.2.2≤-2 := by omega
    have productBound := mul_le_mul_of_nonneg_left topBound (le_of_lt positive)
    have two : sourceWideRadix*(-2)=-2*sourceWideRadix := by ring
    rw [two] at productBound
    unfold sourceWideMeaning at lower
    omega
  · by_contra absent
    have topBound : 2≤s.2.2 := by omega
    have productBound := mul_le_mul_of_nonneg_left topBound (le_of_lt positive)
    have two : sourceWideRadix*2=2*sourceWideRadix := by ring
    rw [two] at productBound
    unfold sourceWideMeaning at upper
    omega

theorem original_second_word_adjustment_is_the_qualified_second_integer_adjustment (s : WideState)
    (lower : -sourceCorrectionShift<sourceWideMeaning s) (upper : sourceWideMeaning s≤sourceWideRadix) :
    sourceWideMeaning (sourceSecondWordCorrection s)=sourceSignedSecond (sourceWideMeaning s) := by
  have topBounds := middle_signed_range_derives_the_actual_extra_top_range s lower upper
  have operand := TransferBlstArmInverseMask01.original_second_correction_masks_derive_the_actual_selected_operand_value
    s.2.2 topBounds.1 topBounds.2
  have conserved := original_second_high_addition_conserves_the_entire_carry_equation s
  have rawRange := TransferBlstArmInverseFirst01.original_two_four_word_halves_derive_the_unsigned_wide_range s
  have resultRange := TransferBlstArmInverseFirst01.original_two_four_word_halves_derive_the_unsigned_wide_range
    (sourceSecondWordCorrection s)
  change 0≤sourceWideMeaning (sourceSecondWordCorrection s) ∧
    sourceWideMeaning (sourceSecondWordCorrection s)<sourceWideRadix at resultRange
  have shiftBounds := TransferBlstArmInverseSign01.original_correction_shift_is_between_half_and_whole_wide_radix
  have shift : sourceFourRadix*(packWords sourceRx2.toList:Int)=sourceCorrectionShift := by
    rw [sourceCorrectionShift]
    change sourceFourRadix*(packWords sourceRx2.toList:Int)=(packWords sourceRx2.toList:Int)*sourceFourRadix
    ring
  have alternatives : s.2.2=-1 ∨ s.2.2=0 ∨ s.2.2=1 := by omega
  rcases alternatives with negative | zero | positive
  · have fullNegative := (TransferBlstArmInverseFirst01.original_extra_top_sign_is_the_entire_signed_wide_value_sign s).mp (by omega)
    rw [if_pos (by omega : s.2.2<0)] at operand
    have castOperand := congrArg (fun value : Nat => (value:Int)) operand
    change (packWords (sourceOperandVector s.2.2).toList:Int)=(packWords sourceRx2.toList:Int) at castOperand
    rw [castOperand,shift] at conserved
    have value : sourceWideMeaning s=(sourceWideRaw s:Int)-sourceWideRadix := by
      rw [sourceWideMeaning,negative,mul_neg,mul_one]
      ring
    rw [sourceSignedSecond,if_pos fullNegative,value]
    unfold sourceWideMeaning at lower upper
    rw [negative] at lower upper
    cases carry : (sourceArmAddRaw s.2.1 (sourceOperandVector s.2.2)).2 <;>
      simp [carry] at conserved <;> omega
  · rw [if_neg (by omega : ¬s.2.2<0),if_neg (by omega : ¬0<s.2.2)] at operand
    have castOperand := congrArg (fun value : Nat => (value:Int)) operand
    change (packWords (sourceOperandVector s.2.2).toList:Int)=0 at castOperand
    rw [castOperand,mul_zero,add_zero] at conserved
    have value : sourceWideMeaning s=(sourceWideRaw s:Int) := by rw [sourceWideMeaning,zero,mul_zero,add_zero]
    rw [sourceSignedSecond,value,if_neg (by omega : ¬(sourceWideRaw s:Int)<0),
      if_neg (by omega : ¬sourceWideRadix≤(sourceWideRaw s:Int))]
    cases carry : (sourceArmAddRaw s.2.1 (sourceOperandVector s.2.2)).2 <;>
      simp [carry] at conserved <;> omega
  · rw [if_neg (by omega : ¬s.2.2<0),if_pos (by omega : 0<s.2.2)] at operand
    have fits : packWords sourceRx2.toList≤radix64^4 := by decide
    have castOperand := congrArg (fun value : Nat => (value:Int)) operand
    change (packWords (sourceOperandVector s.2.2).toList:Int)=((radix64^4-packWords sourceRx2.toList:Nat):Int) at castOperand
    rw [Nat.cast_sub fits] at castOperand
    have operandShift : sourceFourRadix*(packWords (sourceOperandVector s.2.2).toList:Int)=
        sourceWideRadix-sourceCorrectionShift := by
      rw [castOperand]
      change sourceFourRadix*(sourceFourRadix-(packWords sourceRx2.toList:Int))=sourceWideRadix-sourceCorrectionShift
      rw [mul_sub,shift,TransferBlstArmInverseFirst01.original_wide_radix_is_the_square_of_the_four_word_radix]
    rw [operandShift] at conserved
    have value : sourceWideMeaning s=sourceWideRadix := by
      unfold sourceWideMeaning at upper ⊢
      rw [positive,mul_one] at upper ⊢
      omega
    have rawZero : (sourceWideRaw s:Int)=0 := by
      unfold sourceWideMeaning at upper
      rw [positive,mul_one] at upper
      omega
    rw [rawZero,zero_add] at conserved
    have nonnegativeRadix : ¬sourceWideRadix<0 := by
      have positiveRadix : 0<sourceWideRadix := by decide
      omega
    rw [sourceSignedSecond,value,if_neg nonnegativeRadix,if_pos (le_refl _)]
    cases carry : (sourceArmAddRaw s.2.1 (sourceOperandVector s.2.2)).2 <;>
      simp [carry] at conserved <;> omega

theorem first_original_word_adjustment_derives_the_required_middle_signed_range (s : WideState)
    (lower : -sourceWideRadix≤sourceWideMeaning s) (upper : sourceWideMeaning s≤sourceWideRadix) :
    -sourceCorrectionShift<sourceWideMeaning (TransferBlstArmInverseFirst01.sourceFirstWordCorrection s) ∧
      sourceWideMeaning (TransferBlstArmInverseFirst01.sourceFirstWordCorrection s)≤sourceWideRadix := by
  rw [TransferBlstArmInverseFirst01.original_first_signed_word_correction_is_the_qualified_signed_integer_correction]
  have bounds := TransferBlstArmInverseSign01.original_correction_shift_is_between_half_and_whole_wide_radix
  unfold sourceSignedFirst
  split <;> constructor <;> omega

theorem original_complete_two_word_adjustments_are_the_qualified_integer_signed_correction (s : WideState)
    (lower : -sourceWideRadix≤sourceWideMeaning s) (upper : sourceWideMeaning s≤sourceWideRadix) :
    sourceWideMeaning (sourceSecondWordCorrection (TransferBlstArmInverseFirst01.sourceFirstWordCorrection s))=
      sourceSignedCorrection (sourceWideMeaning s) := by
  have middle := first_original_word_adjustment_derives_the_required_middle_signed_range s lower upper
  rw [original_second_word_adjustment_is_the_qualified_second_integer_adjustment _ middle.1 middle.2,
    TransferBlstArmInverseFirst01.original_first_signed_word_correction_is_the_qualified_signed_integer_correction]
  rfl

set_option pp.all true in
#check @sourceSecondHigh
#print axioms sourceSecondHigh
set_option pp.all true in
#check @sourceSecondWordCorrection
#print axioms sourceSecondWordCorrection
set_option pp.all true in
#check @sourceSignedSecond
#print axioms sourceSignedSecond
set_option pp.all true in
#check @original_second_high_vector_retains_the_actual_addition_words
#print axioms original_second_high_vector_retains_the_actual_addition_words
set_option pp.all true in
#check @original_second_high_addition_conserves_the_entire_carry_equation
#print axioms original_second_high_addition_conserves_the_entire_carry_equation
set_option pp.all true in
#check @middle_signed_range_derives_the_actual_extra_top_range
#print axioms middle_signed_range_derives_the_actual_extra_top_range
set_option pp.all true in
#check @original_second_word_adjustment_is_the_qualified_second_integer_adjustment
#print axioms original_second_word_adjustment_is_the_qualified_second_integer_adjustment
set_option pp.all true in
#check @first_original_word_adjustment_derives_the_required_middle_signed_range
#print axioms first_original_word_adjustment_derives_the_required_middle_signed_range
set_option pp.all true in
#check @original_complete_two_word_adjustments_are_the_qualified_integer_signed_correction
#print axioms original_complete_two_word_adjustments_are_the_qualified_integer_signed_correction
end ShielddSecurity.TransferBlstArmInverseSecond01
