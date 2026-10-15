import ShielddSecurity.TransferBlstArmInverseProducedWordFixup01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseZeroFactorRows01
open TransferBlstArmInverseFactors01 (SourceFactors sourceFactorStep sourceFactorWalk sourceFactorInitial)
open TransferBlstArmInverseWindowSelect01 (SourceFourWords sourcePackedFourWords)
open TransferBlstArmInverseWindowInput01 (sourceFourWordWindowWords)
open TransferBlstArmInverseApproxBits01 (sourceApproxLow31)
open TransferScalarSerializationRange01 (radix64)
open TransferScalarWordPrimitives01 (packWords)

/-! Zero-input invariant needed before interpreting a negative-factor
conditional-negate/multiply sequence. The original recurrence cannot
produce a negative first-column factor from a zero first full input.
No generic native multiplication or ISA execution theorem is claimed. -/

theorem a_zero_first_factor_state_keeps_its_first_row_and_only_doubles_its_second_row
    (count : Nat) (state : SourceFactors) (zero : state.a = 0) :
    (sourceFactorWalk count state).a = 0 ∧
    (sourceFactorWalk count state).b = state.b ∧
    (sourceFactorWalk count state).f0 = state.f0 ∧
    (sourceFactorWalk count state).g0 = state.g0 ∧
    (sourceFactorWalk count state).f1 = (2 : Int) ^ count * state.f1 ∧
    (sourceFactorWalk count state).g1 = (2 : Int) ^ count * state.g1 := by
  induction count generalizing state with
  | zero =>
    refine ⟨zero, rfl, rfl, rfl, ?_, ?_⟩
    · change state.f1 = (2 : Int) ^ 0 * state.f1
      rw [Int.pow_zero, Int.one_mul]
    · change state.g1 = (2 : Int) ^ 0 * state.g1
      rw [Int.pow_zero, Int.one_mul]
  | succ count ih =>
    have step : sourceFactorStep state = ⟨0, state.b, state.f0, state.g0, 2 * state.f1, 2 * state.g1⟩ := by
      simp only [sourceFactorStep, zero, Nat.zero_mod, ite_true, Nat.zero_div]
    have next := ih (state := ⟨0, state.b, state.f0, state.g0, 2 * state.f1, 2 * state.g1⟩) rfl
    rw [sourceFactorWalk, step]
    refine ⟨next.1, next.2.1, next.2.2.1, next.2.2.2.1, ?_, ?_⟩
    · calc
        _ = (2 : Int) ^ count * (2 * state.f1) := next.2.2.2.2.1
        _ = (2 : Int) ^ (count + 1) * state.f1 := by rw [Int.pow_succ]; ring1
    · calc
        _ = (2 : Int) ^ count * (2 * state.g1) := next.2.2.2.2.2
        _ = (2 : Int) ^ (count + 1) * state.g1 := by rw [Int.pow_succ]; ring1

theorem every_original_initialized_zero_first_factor_walk_has_first_column_one_zero
    (count second : Nat) :
    (sourceFactorWalk count (sourceFactorInitial 0 second)).f0 = 1 ∧
      (sourceFactorWalk count (sourceFactorInitial 0 second)).f1 = 0 := by
  have rows := a_zero_first_factor_state_keeps_its_first_row_and_only_doubles_its_second_row
    count (sourceFactorInitial 0 second) rfl
  refine ⟨rows.2.2.1, ?_⟩
  simpa only [sourceFactorInitial, Int.mul_zero] using rows.2.2.2.2.1

theorem an_original_zero_first_full_input_produces_a_zero_first_low31_approximation
    (a b : SourceFourWords) (zero : sourcePackedFourWords a = 0) :
    sourceApproxLow31 (sourceFourWordWindowWords a b).1 a.w0 = 0 := by
  have high := (TransferBlstArmInverseWindowInput01.original_source_window_words_derive_the_high_window_premises_for_both_entire_inputs a b).1
  rw [zero, Nat.zero_div] at high
  have lowBound : a.w0.toNat ≤ sourcePackedFourWords a := by
    change a.w0.toNat ≤ a.w0.toNat + radix64 * packWords [a.w1, a.w2, a.w3]
    exact Nat.le_add_right _ _
  rw [zero] at lowBound
  have lowZero : a.w0.toNat = 0 := Nat.eq_zero_of_le_zero lowBound
  simp only [sourceApproxLow31, high, lowZero, Nat.zero_div, Nat.zero_mul, Nat.zero_mod, Nat.add_zero]

theorem every_original_zero_first_full_input_has_nonnegative_first_column_prefix_factors
    (count : Nat) (a b : SourceFourWords) (zero : sourcePackedFourWords a = 0) :
    let factors := sourceFactorWalk count (sourceFactorInitial
      (sourceApproxLow31 (sourceFourWordWindowWords a b).1 a.w0)
      (sourceApproxLow31 (sourceFourWordWindowWords a b).2 b.w0))
    0 ≤ factors.f0 ∧ 0 ≤ factors.f1 := by
  dsimp only
  rw [an_original_zero_first_full_input_produces_a_zero_first_low31_approximation a b zero]
  have rows := every_original_initialized_zero_first_factor_walk_has_first_column_one_zero count
    (sourceApproxLow31 (sourceFourWordWindowWords a b).2 b.w0)
  rw [rows.1, rows.2]
  constructor <;> omega

theorem any_original_negative_first_column_prefix_factor_requires_a_nonzero_first_full_input
    (count : Nat) (a b : SourceFourWords)
    (negative :
      (sourceFactorWalk count (sourceFactorInitial
        (sourceApproxLow31 (sourceFourWordWindowWords a b).1 a.w0)
        (sourceApproxLow31 (sourceFourWordWindowWords a b).2 b.w0))).f0 < 0 ∨
      (sourceFactorWalk count (sourceFactorInitial
        (sourceApproxLow31 (sourceFourWordWindowWords a b).1 a.w0)
        (sourceApproxLow31 (sourceFourWordWindowWords a b).2 b.w0))).f1 < 0) :
    sourcePackedFourWords a ≠ 0 := by
  intro zero
  have nonnegative := every_original_zero_first_full_input_has_nonnegative_first_column_prefix_factors count a b zero
  dsimp only at nonnegative
  omega

set_option pp.all true in
#check @a_zero_first_factor_state_keeps_its_first_row_and_only_doubles_its_second_row
#print axioms a_zero_first_factor_state_keeps_its_first_row_and_only_doubles_its_second_row
set_option pp.all true in
#check @every_original_initialized_zero_first_factor_walk_has_first_column_one_zero
#print axioms every_original_initialized_zero_first_factor_walk_has_first_column_one_zero
set_option pp.all true in
#check @an_original_zero_first_full_input_produces_a_zero_first_low31_approximation
#print axioms an_original_zero_first_full_input_produces_a_zero_first_low31_approximation
set_option pp.all true in
#check @every_original_zero_first_full_input_has_nonnegative_first_column_prefix_factors
#print axioms every_original_zero_first_full_input_has_nonnegative_first_column_prefix_factors
set_option pp.all true in
#check @any_original_negative_first_column_prefix_factor_requires_a_nonzero_first_full_input
#print axioms any_original_negative_first_column_prefix_factor_requires_a_nonzero_first_full_input
end ShielddSecurity.TransferBlstArmInverseZeroFactorRows01
