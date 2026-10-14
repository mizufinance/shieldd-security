import ShielddSecurity.TransferBlstArmInverseOrderBudget01
import ShielddSecurity.TransferBlstArmInverseWindowError01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseOrderStep01
open TransferBlstArmInverseWindowSelect01 (SourceFourWords sourcePackedFourWords)
open TransferBlstArmInverseWindowInput01 (sourceFourWordWindowWords sourceFourWordWindowShift)
open TransferBlstArmInverseApproxBits01 (sourceApproxLow31)
open TransferBlstArmInverseFactors01 (sourceFactorInitial sourceFactorWalk)
open TransferBlstArmInverseErrorRows01 (sourceActualFactorQuotients)
attribute [local irreducible] sourceFactorWalk sourceActualFactorQuotients

/-! UNRUN pointwise ordering-disagreement application at an original source
prefix. Strict cases distinguish the two modeled comparison outcomes; the
weaker gap premise alone also permits ties. This compares signed row
quotients. To identify an actual first odd comparison, trace alignment,
nonnegative input observations and matching odd parity must be derived.
No first-divergence existence, lasting behavior or bitlength progress claim. -/

def sourceComparisonDisagreement (x y : Int) (p q : Nat) : Prop :=
  (y ≤ x ∧ p < q) ∨ (x < y ∧ q ≤ p)

theorem strict_comparison_disagreement_derives_the_opposing_order_gap_premise
    (x y : Int) (p q : Nat) (disagreement : sourceComparisonDisagreement x y p q) :
    (y ≤ x ∧ p ≤ q) ∨ (x ≤ y ∧ q ≤ p) := by
  rcases disagreement with first | second
  · exact Or.inl ⟨first.1, Nat.le_of_lt first.2⟩
  · exact Or.inr ⟨Int.le_of_lt second.1, second.2⟩

theorem strict_source_prefix_comparison_disagreement_derives_the_entire_signed_gap_bound
    (count : Nat) (a b : SourceFourWords) (bounded : count < 31) (oddB : b.w0.toNat % 2 = 1) :
    let windows := sourceFourWordWindowWords a b
    let shift := sourceFourWordWindowShift a b
    let factors := sourceFactorWalk count (sourceFactorInitial
      (sourceApproxLow31 windows.1 a.w0) (sourceApproxLow31 windows.2 b.w0))
    let actual := sourceActualFactorQuotients count
      (sourceApproxLow31 windows.1 a.w0) (sourceApproxLow31 windows.2 b.w0)
      (sourcePackedFourWords a : Int) (sourcePackedFourWords b : Int)
    sourceComparisonDisagreement actual.1 actual.2 factors.a factors.b →
      (actual.1 - actual.2).natAbs ≤ 2 ^ (shift + 32) := by
  dsimp only
  intro disagreement
  have errors := TransferBlstArmInverseWindowError01.original_source_produced_four_word_windows_derive_both_factor_prefix_error_bounds
    count a b (Nat.le_of_lt bounded) oddB
  exact TransferBlstArmInverseOrderBudget01.either_ordering_mismatch_from_both_low31_prefix_errors_derives_the_entire_gap_bound
    _ _ _ _ (sourceFourWordWindowShift a b) errors.1 errors.2
    (strict_comparison_disagreement_derives_the_opposing_order_gap_premise _ _ _ _ disagreement)

end ShielddSecurity.TransferBlstArmInverseOrderStep01
