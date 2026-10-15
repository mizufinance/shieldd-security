import ShielddSecurity.TransferBlstArmInverseBatchRange01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseBatchZero01
open TransferBlstArmInverseFactors01 (SourceFactors sourceFactorInitial sourceFactorStep sourceFactorWalk)
open TransferBlstArmInverseWindowSelect01 (SourceFourWords sourcePackedFourWords)
open TransferBlstArmInverseWindowInput01 (sourceFourWordWindowWords)
open TransferBlstArmInverseApproxBits01 (sourceApproxLow31)
open TransferBlstArmInverseErrorRows01 (sourceActualFactorQuotients)

/-! A zero first full source operand remains zero after the original batch.
This supports fixed schedules after early termination without a false
strict-decrease premise. Native word execution remains open. -/

theorem a_zero_first_factor_input_keeps_its_first_coefficient_row_unchanged
    (count : Nat) (s : SourceFactors) (zero : s.a = 0) :
    (sourceFactorWalk count s).a = 0 ∧
      (sourceFactorWalk count s).f0 = s.f0 ∧ (sourceFactorWalk count s).g0 = s.g0 := by
  induction count generalizing s with
  | zero => exact ⟨zero, rfl, rfl⟩
  | succ count ih =>
    have even : s.a % 2 = 0 := by rw [zero]
    have nextZero : (sourceFactorStep s).a = 0 := by
      rw [sourceFactorStep, if_pos even]
      exact congrArg (fun x : Nat => x / 2) zero
    have sameF : (sourceFactorStep s).f0 = s.f0 := by rw [sourceFactorStep, if_pos even]
    have sameG : (sourceFactorStep s).g0 = s.g0 := by rw [sourceFactorStep, if_pos even]
    have previous := ih (sourceFactorStep s) nextZero
    exact ⟨previous.1, previous.2.1.trans sameF, previous.2.2.trans sameG⟩

theorem an_original_zero_full_first_input_has_zero_low31_approximation
    (a b : SourceFourWords) (zero : sourcePackedFourWords a = 0) :
    sourceApproxLow31 (sourceFourWordWindowWords a b).1 a.w0 = 0 := by
  have producer := (TransferBlstArmInverseWindowInput01.original_source_window_words_derive_the_high_window_premises_for_both_entire_inputs a b).1
  rw [zero, Nat.zero_div] at producer
  have lowZero : a.w0.toNat = 0 := by
    change a.w0.toNat + TransferScalarSerializationRange01.radix64 *
      TransferScalarWordPrimitives01.packWords [a.w1, a.w2, a.w3] = 0 at zero
    omega
  simp only [sourceApproxLow31, producer, lowZero, Nat.zero_div, Nat.zero_mul, Nat.zero_mod, Nat.zero_add]

theorem an_original_zero_first_full_input_stays_zero_after_the31_step_source_batch
    (a b : SourceFourWords) (zero : sourcePackedFourWords a = 0) :
    (sourceActualFactorQuotients 31
      (sourceApproxLow31 (sourceFourWordWindowWords a b).1 a.w0)
      (sourceApproxLow31 (sourceFourWordWindowWords a b).2 b.w0)
      (sourcePackedFourWords a : Int) (sourcePackedFourWords b : Int)).1 = 0 := by
  have approximateZero := an_original_zero_full_first_input_has_zero_low31_approximation a b zero
  have rows := a_zero_first_factor_input_keeps_its_first_coefficient_row_unchanged 31
    (sourceFactorInitial (sourceApproxLow31 (sourceFourWordWindowWords a b).1 a.w0)
      (sourceApproxLow31 (sourceFourWordWindowWords a b).2 b.w0)) approximateZero
  change ((sourceFactorWalk 31 (sourceFactorInitial
      (sourceApproxLow31 (sourceFourWordWindowWords a b).1 a.w0)
      (sourceApproxLow31 (sourceFourWordWindowWords a b).2 b.w0))).f0 * (sourcePackedFourWords a : Int) +
    (sourceFactorWalk 31 (sourceFactorInitial
      (sourceApproxLow31 (sourceFourWordWindowWords a b).1 a.w0)
      (sourceApproxLow31 (sourceFourWordWindowWords a b).2 b.w0))).g0 * (sourcePackedFourWords b : Int)) / (2 : Int) ^ 31 = 0
  rw [rows.2.1, rows.2.2, zero]
  change (1 * (0 : Int) + 0 * (sourcePackedFourWords b : Int)) / (2 : Int) ^ 31 = 0
  simp only [Int.mul_zero, Int.zero_mul, Int.zero_add, Int.zero_ediv]

set_option pp.all true in
#check @a_zero_first_factor_input_keeps_its_first_coefficient_row_unchanged
#print axioms a_zero_first_factor_input_keeps_its_first_coefficient_row_unchanged
set_option pp.all true in
#check @an_original_zero_full_first_input_has_zero_low31_approximation
#print axioms an_original_zero_full_first_input_has_zero_low31_approximation
set_option pp.all true in
#check @an_original_zero_first_full_input_stays_zero_after_the31_step_source_batch
#print axioms an_original_zero_first_full_input_stays_zero_after_the31_step_source_batch
end ShielddSecurity.TransferBlstArmInverseBatchZero01
