import ShielddSecurity.TransferBlstArmInverseSignedExtrQuotient01
import ShielddSecurity.TransferBlstArmInverseRowSumDecode01
import ShielddSecurity.TransferBlstArmInverseZeroFactorRows01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseOriginalRowWords01
open TransferBlstArmInverseWindowSelect01 (SourceFourWords sourcePackedFourWords)
open TransferBlstArmInverseWindowInput01 (sourceFourWordWindowWords)
open TransferBlstArmInverseApproxBits01 (sourceApproxLow31)
open TransferBlstArmInverseFactors01 (sourceFactorWalk sourceFactorInitial)
open TransferBlstArmInverseSignedProductSum01 (sourceSignedProductSum)
attribute [local irreducible] sourceFactorWalk sourceSignedProductSum

/-! Source row selection is proved over arbitrary integer coefficients before
specializing the original symbolic 31-step recurrence. Word-sum correspondence,
packed factor registers and compiled execution remain separate obligations. -/

def sourceSelectFactorRow (second : Bool) (f0 g0 f1 g1 : Int) : Int × Int :=
  if second then (f1, g1) else (f0, g0)

structure SourceRowContract (bound inputA inputB : Nat) (row : Int × Int) : Prop where
  norm : row.1.natAbs + row.2.natAbs ≤ bound
  negativeNonzero : row.1 < 0 → 0 < inputA
  secondPositive : 0 < inputB

theorem generic_row_selection_preserves_both_norms_and_negative_first_input_origin
    (second : Bool) (f0 g0 f1 g1 : Int) (bound inputA inputB : Nat)
    (first : f0.natAbs + g0.natAbs ≤ bound) (last : f1.natAbs + g1.natAbs ≤ bound)
    (nonzeroA : f0 < 0 ∨ f1 < 0 → 0 < inputA) (nonzeroB : 0 < inputB) :
    SourceRowContract bound inputA inputB (sourceSelectFactorRow second f0 g0 f1 g1) := by
  cases second with
  | false => exact ⟨first, (fun negative => nonzeroA (Or.inl negative)), nonzeroB⟩
  | true => exact ⟨last, (fun negative => nonzeroA (Or.inr negative)), nonzeroB⟩

theorem an_abstract_factor_state_supplies_selected_row_norm_and_nonzero_contract
    (second : Bool) (state : TransferBlstArmInverseFactors01.SourceFactors)
    (bound inputA inputB : Nat) (norms : TransferBlstArmInverseNorm01.RowBounds bound state)
    (nonzeroA : state.f0 < 0 ∨ state.f1 < 0 → 0 < inputA) (nonzeroB : 0 < inputB) :
    SourceRowContract bound inputA inputB (sourceSelectFactorRow second state.f0 state.g0 state.f1 state.g1) := by
  exact generic_row_selection_preserves_both_norms_and_negative_first_input_origin second
    state.f0 state.g0 state.f1 state.g1 bound inputA inputB norms.1 norms.2 nonzeroA nonzeroB

theorem an_odd_second_low_word_requires_a_nonzero_entire_second_input
    (b : SourceFourWords) (oddB : b.w0.toNat % 2 = 1) : 0 < sourcePackedFourWords b := by
  have lowBound : b.w0.toNat ≤ sourcePackedFourWords b := by
    change b.w0.toNat ≤ b.w0.toNat + TransferScalarSerializationRange01.radix64 *
      TransferScalarWordPrimitives01.packWords [b.w1, b.w2, b.w3]
    exact Nat.le_add_right _ _
  omega

attribute [local irreducible] sourceSelectFactorRow

def sourceOriginalFactorRow (count : Nat) (second : Bool) (a b : SourceFourWords) : Int × Int :=
  let factors := sourceFactorWalk count (sourceFactorInitial
    (sourceApproxLow31 (sourceFourWordWindowWords a b).1 a.w0)
    (sourceApproxLow31 (sourceFourWordWindowWords a b).2 b.w0))
  sourceSelectFactorRow second factors.f0 factors.g0 factors.f1 factors.g1

attribute [local irreducible] sourceOriginalFactorRow

def sourceOriginalRowWordSum (second : Bool) (a b : SourceFourWords) : List UInt64 × Bool :=
  let row := sourceOriginalFactorRow 31 second a b
  sourceSignedProductSum [a.w0, a.w1, a.w2, a.w3] [b.w0, b.w1, b.w2, b.w3] row.1 row.2

theorem original_window_factor_rows_derive_all_source_product_bounds_and_nonzero_origins
    (count : Nat) (second : Bool) (a b : SourceFourWords) (oddB : b.w0.toNat % 2 = 1) :
    SourceRowContract (2 ^ count) (sourcePackedFourWords a) (sourcePackedFourWords b)
      (sourceOriginalFactorRow count second a b) := by
  let factors := sourceFactorWalk count (sourceFactorInitial
    (sourceApproxLow31 (sourceFourWordWindowWords a b).1 a.w0)
    (sourceApproxLow31 (sourceFourWordWindowWords a b).2 b.w0))
  have norms := TransferBlstArmInverseNorm01.original_initialized_factor_walk_derives_row_sums_at_most_its_radix_power
    count (sourceApproxLow31 (sourceFourWordWindowWords a b).1 a.w0)
    (sourceApproxLow31 (sourceFourWordWindowWords a b).2 b.w0)
  have nonzeroA : factors.f0 < 0 ∨ factors.f1 < 0 → 0 < sourcePackedFourWords a := by
    intro negative
    exact Nat.pos_of_ne_zero
      (TransferBlstArmInverseZeroFactorRows01.any_original_negative_first_column_prefix_factor_requires_a_nonzero_first_full_input count a b negative)
  have selected := an_abstract_factor_state_supplies_selected_row_norm_and_nonzero_contract second factors
    (2 ^ count) (sourcePackedFourWords a) (sourcePackedFourWords b) norms nonzeroA
    (an_odd_second_low_word_requires_a_nonzero_entire_second_input b oddB)
  unfold sourceOriginalFactorRow
  exact selected

set_option pp.all true in
#check @sourceSelectFactorRow
#print axioms sourceSelectFactorRow
set_option pp.all true in
#check @SourceRowContract
#print axioms SourceRowContract
set_option pp.all true in
#check @generic_row_selection_preserves_both_norms_and_negative_first_input_origin
#print axioms generic_row_selection_preserves_both_norms_and_negative_first_input_origin
set_option pp.all true in
#check @an_abstract_factor_state_supplies_selected_row_norm_and_nonzero_contract
#print axioms an_abstract_factor_state_supplies_selected_row_norm_and_nonzero_contract
set_option pp.all true in
#check @an_odd_second_low_word_requires_a_nonzero_entire_second_input
#print axioms an_odd_second_low_word_requires_a_nonzero_entire_second_input
set_option pp.all true in
#check @sourceOriginalFactorRow
#print axioms sourceOriginalFactorRow
set_option pp.all true in
#check @sourceOriginalRowWordSum
#print axioms sourceOriginalRowWordSum
set_option pp.all true in
#check @original_window_factor_rows_derive_all_source_product_bounds_and_nonzero_origins
#print axioms original_window_factor_rows_derive_all_source_product_bounds_and_nonzero_origins
end ShielddSecurity.TransferBlstArmInverseOriginalRowWords01
