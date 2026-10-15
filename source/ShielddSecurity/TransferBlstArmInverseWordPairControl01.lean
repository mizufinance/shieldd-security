import ShielddSecurity.TransferBlstArmInverseWordParityMask01
import ShielddSecurity.TransferBlstArmInverseFactors01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseWordPairControl01
open TransferBlstArmInverseWordParityMask01 (sourceParityWordMask)
open TransferBlstArmInverseFactors01 (SourceFactors sourceFactorStep)
attribute [local irreducible] sourceParityWordMask

/-! Source word AND/SUB/CSEL/LSR data control, with no-borrow computed from
the entire unsigned operands, equals the natural even/subtract/swap step.
This is an arithmetic source flag model; actual PSTATE and compiled ISA
execution, memory and ABI remain separate. -/

def sourceNaturalPairControlStep (a b : Nat) : Nat × Nat :=
  if a % 2 = 0 then (a / 2, b)
  else if b ≤ a then ((a - b) / 2, b) else ((b - a) / 2, a)

def sourceWordPairControlStep (a b : UInt64) : UInt64 × UInt64 :=
  let maskedB := b &&& sourceParityWordMask a
  let noBorrow := decide (maskedB.toNat ≤ a.toNat)
  ((if noBorrow then a - maskedB else b - a) >>> 1, if noBorrow then b else a)

theorem no_borrow_source_word_subtraction_has_the_exact_entire_natural_difference
    (left right : UInt64) (noBorrow : right.toNat ≤ left.toNat) :
    (left - right).toNat = left.toNat - right.toNat := by
  exact UInt64.toNat_sub_of_le left right (UInt64.le_iff_toNat_le.mpr noBorrow)

theorem source_lsr_by_one_has_the_exact_entire_natural_half (word : UInt64) :
    (word >>> 1).toNat = word.toNat / 2 := by
  exact TransferBlstArmInverseExtrWord01.original_extr_right_fragment_is_the_entire_low_word_quotient word 1 (by decide)

theorem original_word_mask_subtract_borrow_select_and_shift_derive_the_entire_natural_pair_step
    (a b : UInt64) :
    ((sourceWordPairControlStep a b).1.toNat, (sourceWordPairControlStep a b).2.toNat) =
      sourceNaturalPairControlStep a.toNat b.toNat := by
  have parityBound := Nat.mod_lt a.toNat (by decide : 0 < 2)
  by_cases even : a.toNat % 2 = 0
  · have notOdd : ¬a.toNat % 2 = 1 := by omega
    have mask : sourceParityWordMask a = 0 := by
      rw [TransferBlstArmInverseWordParityMask01.original_one_bit_signed_extraction_derives_the_exact_zero_or_all_ones_parity_mask]
      simp only [if_neg notOdd]
    have program : sourceWordPairControlStep a b = (a >>> 1, b) := by
      simp [sourceWordPairControlStep, mask]
    simp only [program]
    rw [sourceNaturalPairControlStep, if_pos even]
    rw [source_lsr_by_one_has_the_exact_entire_natural_half]
  · have odd : a.toNat % 2 = 1 := by omega
    have mask : sourceParityWordMask a = -1 := by
      rw [TransferBlstArmInverseWordParityMask01.original_one_bit_signed_extraction_derives_the_exact_zero_or_all_ones_parity_mask]
      simp only [if_pos odd]
    by_cases ordered : b.toNat ≤ a.toNat
    · have program : sourceWordPairControlStep a b = ((a - b) >>> 1, b) := by
        simp [sourceWordPairControlStep, mask, ordered]
      simp only [program]
      rw [sourceNaturalPairControlStep, if_neg even, if_pos ordered]
      rw [source_lsr_by_one_has_the_exact_entire_natural_half,
        no_borrow_source_word_subtraction_has_the_exact_entire_natural_difference a b ordered]
    · have reverseOrder : a.toNat ≤ b.toNat := by omega
      have program : sourceWordPairControlStep a b = ((b - a) >>> 1, a) := by
        simp [sourceWordPairControlStep, mask, ordered]
      simp only [program]
      rw [sourceNaturalPairControlStep, if_neg even, if_neg ordered]
      rw [source_lsr_by_one_has_the_exact_entire_natural_half,
        no_borrow_source_word_subtraction_has_the_exact_entire_natural_difference b a reverseOrder]

theorem the_natural_pair_control_step_is_exactly_the_data_part_of_the_original_factor_step
    (state : SourceFactors) : sourceNaturalPairControlStep state.a state.b =
      ((sourceFactorStep state).a, (sourceFactorStep state).b) := by
  by_cases even : state.a % 2 = 0
  · simp only [sourceNaturalPairControlStep, sourceFactorStep, if_pos even]
  · by_cases ordered : state.b ≤ state.a
    · simp only [sourceNaturalPairControlStep, sourceFactorStep, if_neg even, if_pos ordered]
    · simp only [sourceNaturalPairControlStep, sourceFactorStep, if_neg even, if_neg ordered]

theorem every_natural_pair_control_step_never_increases_the_entire_input_maximum
    (a b : Nat) :
    (sourceNaturalPairControlStep a b).1 ≤ max a b ∧ (sourceNaturalPairControlStep a b).2 ≤ max a b := by
  have left := Nat.le_max_left a b
  have right := Nat.le_max_right a b
  by_cases even : a % 2 = 0
  · simp only [sourceNaturalPairControlStep, if_pos even]
    omega
  · by_cases ordered : b ≤ a
    · simp only [sourceNaturalPairControlStep, if_neg even, if_pos ordered]
      omega
    · simp only [sourceNaturalPairControlStep, if_neg even, if_neg ordered]
      omega

set_option pp.all true in
#check @sourceNaturalPairControlStep
#print axioms sourceNaturalPairControlStep
set_option pp.all true in
#check @sourceWordPairControlStep
#print axioms sourceWordPairControlStep
set_option pp.all true in
#check @no_borrow_source_word_subtraction_has_the_exact_entire_natural_difference
#print axioms no_borrow_source_word_subtraction_has_the_exact_entire_natural_difference
set_option pp.all true in
#check @source_lsr_by_one_has_the_exact_entire_natural_half
#print axioms source_lsr_by_one_has_the_exact_entire_natural_half
set_option pp.all true in
#check @original_word_mask_subtract_borrow_select_and_shift_derive_the_entire_natural_pair_step
#print axioms original_word_mask_subtract_borrow_select_and_shift_derive_the_entire_natural_pair_step
set_option pp.all true in
#check @the_natural_pair_control_step_is_exactly_the_data_part_of_the_original_factor_step
#print axioms the_natural_pair_control_step_is_exactly_the_data_part_of_the_original_factor_step
set_option pp.all true in
#check @every_natural_pair_control_step_never_increases_the_entire_input_maximum
#print axioms every_natural_pair_control_step_never_increases_the_entire_input_maximum
end ShielddSecurity.TransferBlstArmInverseWordPairControl01
