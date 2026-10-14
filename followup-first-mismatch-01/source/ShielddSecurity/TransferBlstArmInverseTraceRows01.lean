import ShielddSecurity.TransferBlstArmInverseErrorRows01
import ShielddSecurity.TransferBlstArmInverseOrderStep01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseTraceRows01
open TransferBlstArmInverseFactors01
  (SourceFactors sourceFactorInitial sourceFactorStep sourceFactorWalk)
open TransferBlstArmInverseErrorRows01 (sourceActualFactorQuotients)

/-! UNRUN source-model trace alignment. Earlier branch synchronization derives
row equality, so signed quotients identify the exact natural loop inputs at a
candidate mismatch. Current parity agreement is an explicit remaining premise.
No compiled runtime trace, mismatch existence or post-mismatch progress claim. -/

def sourceFactorControl (s : SourceFactors) : Nat :=
  if s.a % 2 = 0 then 0 else if s.b ≤ s.a then 1 else 2

def sourceSameFactorRows (s t : SourceFactors) : Prop :=
  s.f0 = t.f0 ∧ s.g0 = t.g0 ∧ s.f1 = t.f1 ∧ s.g1 = t.g1

theorem symbolic_factor_walk_successor_is_the_last_factor_step
    (count : Nat) (s : SourceFactors) :
    sourceFactorWalk (count + 1) s = sourceFactorStep (sourceFactorWalk count s) := by
  induction count generalizing s with
  | zero => rfl
  | succ count ih => exact ih (sourceFactorStep s)

theorem equal_factor_rows_and_controls_derive_equal_next_factor_rows
    (s t : SourceFactors) (rows : sourceSameFactorRows s t)
    (controls : sourceFactorControl s = sourceFactorControl t) :
    sourceSameFactorRows (sourceFactorStep s) (sourceFactorStep t) := by
  rcases rows with ⟨f0, g0, f1, g1⟩
  by_cases se : s.a % 2 = 0
  · have te : t.a % 2 = 0 := by
      by_contra ne
      by_cases ordered : t.b ≤ t.a
      · simp only [sourceFactorControl, if_pos se, if_neg ne, if_pos ordered] at controls
        omega
      · simp only [sourceFactorControl, if_pos se, if_neg ne, if_neg ordered] at controls
        omega
    simp only [sourceFactorStep, if_pos se, if_pos te, sourceSameFactorRows]
    exact ⟨f0, g0, congrArg (fun x : Int => 2 * x) f1, congrArg (fun x : Int => 2 * x) g1⟩
  · have te : t.a % 2 ≠ 0 := by
      intro even
      by_cases ordered : s.b ≤ s.a
      · simp only [sourceFactorControl, if_neg se, if_pos even, if_pos ordered] at controls
        omega
      · simp only [sourceFactorControl, if_neg se, if_pos even, if_neg ordered] at controls
        omega
    by_cases so : s.b ≤ s.a
    · have tOrdered : t.b ≤ t.a := by
        by_contra no
        simp only [sourceFactorControl, if_neg se, if_neg te, if_pos so, if_neg no] at controls
        omega
      simp only [sourceFactorStep, if_neg se, if_neg te, if_pos so, if_pos tOrdered, sourceSameFactorRows]
      rw [f0, g0, f1, g1]
      exact ⟨rfl, rfl, rfl, rfl⟩
    · have tNotOrdered : ¬t.b ≤ t.a := by
        intro ordered
        simp only [sourceFactorControl, if_neg se, if_neg te, if_neg so, if_pos ordered] at controls
        omega
      simp only [sourceFactorStep, if_neg se, if_neg te, if_neg so, if_neg tNotOrdered, sourceSameFactorRows]
      rw [f0, g0, f1, g1]
      exact ⟨rfl, rfl, rfl, rfl⟩

theorem synchronized_earlier_prefix_controls_derive_equal_entire_factor_rows
    (count : Nat) (s t : SourceFactors) (initialRows : sourceSameFactorRows s t) :
    (∀ index < count, sourceFactorControl (sourceFactorWalk index s) =
      sourceFactorControl (sourceFactorWalk index t)) →
    sourceSameFactorRows (sourceFactorWalk count s) (sourceFactorWalk count t) := by
  induction count with
  | zero => intro _; exact initialRows
  | succ count ih =>
      intro synchronized
      rw [symbolic_factor_walk_successor_is_the_last_factor_step,
        symbolic_factor_walk_successor_is_the_last_factor_step]
      exact equal_factor_rows_and_controls_derive_equal_next_factor_rows _ _
        (ih (fun index less => synchronized index (Nat.lt_trans less (Nat.lt_succ_self count))))
        (synchronized count (Nat.lt_succ_self count))

theorem synchronized_initialized_prefix_identifies_both_signed_actual_quotients
    (count approxA approxB inputA inputB : Nat) (oddB : inputB % 2 = 1)
    (synchronized : ∀ index < count,
      sourceFactorControl (sourceFactorWalk index (sourceFactorInitial approxA approxB)) =
      sourceFactorControl (sourceFactorWalk index (sourceFactorInitial inputA inputB))) :
    sourceActualFactorQuotients count approxA approxB (inputA : Int) (inputB : Int) =
      (((sourceFactorWalk count (sourceFactorInitial inputA inputB)).a : Int),
       ((sourceFactorWalk count (sourceFactorInitial inputA inputB)).b : Int)) := by
  let approximate := sourceFactorWalk count (sourceFactorInitial approxA approxB)
  let actual := sourceFactorWalk count (sourceFactorInitial inputA inputB)
  have rows : sourceSameFactorRows approximate actual :=
    synchronized_earlier_prefix_controls_derive_equal_entire_factor_rows count _ _
      ⟨rfl, rfl, rfl, rfl⟩ synchronized
  have tracked := TransferBlstArmInverseFactors01.original_initialized_factor_walk_derives_exact_scaled_input_rows
    count inputA inputB oddB
  change ((2 : Int) ^ count) * (actual.a : Int) = actual.f0 * (inputA : Int) + actual.g0 * (inputB : Int) ∧
    ((2 : Int) ^ count) * (actual.b : Int) = actual.f1 * (inputA : Int) + actual.g1 * (inputB : Int) at tracked
  have radixNonzero : (2 : Int) ^ count ≠ 0 := pow_ne_zero _ (by decide)
  change ((approximate.f0 * (inputA : Int) + approximate.g0 * (inputB : Int)) / (2 : Int) ^ count,
    (approximate.f1 * (inputA : Int) + approximate.g1 * (inputB : Int)) / (2 : Int) ^ count) = _
  rcases rows with ⟨f0, g0, f1, g1⟩
  apply Prod.ext
  · change (approximate.f0 * (inputA : Int) + approximate.g0 * (inputB : Int)) / (2 : Int) ^ count = (actual.a : Int)
    rw [f0, g0, ←tracked.1, Int.mul_ediv_cancel_left _ radixNonzero]
  · change (approximate.f1 * (inputA : Int) + approximate.g1 * (inputB : Int)) / (2 : Int) ^ count = (actual.b : Int)
    rw [f1, g1, ←tracked.2, Int.mul_ediv_cancel_left _ radixNonzero]

theorem matched_parity_and_different_controls_derive_strict_signed_comparison_disagreement
    (actual approximate : SourceFactors)
    (parity : actual.a % 2 = approximate.a % 2)
    (mismatch : sourceFactorControl actual ≠ sourceFactorControl approximate) :
    TransferBlstArmInverseOrderStep01.sourceComparisonDisagreement
      (actual.a : Int) (actual.b : Int) approximate.a approximate.b := by
  have actualOdd : actual.a % 2 ≠ 0 := by
    intro even
    have approximateEven : approximate.a % 2 = 0 := parity.symm.trans even
    simp only [sourceFactorControl, if_pos even, if_pos approximateEven] at mismatch
    exact mismatch rfl
  have approximateOdd : approximate.a % 2 ≠ 0 := by omega
  by_cases ordered : actual.b ≤ actual.a
  · have reversed : approximate.a < approximate.b := by
      by_contra no
      have orderApprox : approximate.b ≤ approximate.a := by omega
      simp only [sourceFactorControl, if_neg actualOdd, if_neg approximateOdd,
        if_pos ordered, if_pos orderApprox] at mismatch
      exact mismatch rfl
    exact Or.inl ⟨by omega, reversed⟩
  · have orderApprox : approximate.b ≤ approximate.a := by
      by_contra no
      simp only [sourceFactorControl, if_neg actualOdd, if_neg approximateOdd,
        if_neg ordered, if_neg no] at mismatch
      exact mismatch rfl
    exact Or.inr ⟨by omega, orderApprox⟩

end ShielddSecurity.TransferBlstArmInverseTraceRows01
