import ShielddSecurity.TransferBlstArmInverseFactors01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseProgress01
open TransferBlstArmInverseFactors01
  (SourceFactors sourceFactorStep sourceFactorWalk sourceFactorInitial
   original_factor_step_retains_odd_second_input)

/-! Product decrease and finite termination of the exact logical factor
recurrence. The bound is symbolic in the number of steps. It does not turn
approximate 31-bit batches into exact steps or prove their progress. -/

theorem original_exact_factor_step_halves_the_input_product (s : SourceFactors) :
    2*((sourceFactorStep s).a*(sourceFactorStep s).b)≤s.a*s.b := by
  rw [sourceFactorStep]
  split
  · change 2*((s.a/2)*s.b)≤s.a*s.b
    have half : 2*(s.a/2)≤s.a := by omega
    calc
      _ = (2*(s.a/2))*s.b := by ring
      _ ≤ s.a*s.b := Nat.mul_le_mul_right _ half
  · split
    · change 2*(((s.a-s.b)/2)*s.b)≤s.a*s.b
      have half : 2*((s.a-s.b)/2)≤s.a := by omega
      calc
        _ = (2*((s.a-s.b)/2))*s.b := by ring
        _ ≤ s.a*s.b := Nat.mul_le_mul_right _ half
    · change 2*(((s.b-s.a)/2)*s.a)≤s.a*s.b
      have half : 2*((s.b-s.a)/2)≤s.b := by omega
      calc
        _ = (2*((s.b-s.a)/2))*s.a := by ring
        _ ≤ s.b*s.a := Nat.mul_le_mul_right _ half
        _ = _ := Nat.mul_comm _ _

theorem symbolic_original_exact_factor_walk_derives_scaled_product_decrease
    (count : Nat) (s : SourceFactors) :
    2^count*((sourceFactorWalk count s).a*(sourceFactorWalk count s).b)≤s.a*s.b := by
  induction count generalizing s with
  | zero => simp only [sourceFactorWalk,pow_zero,one_mul,Nat.le_refl]
  | succ count ih =>
      have tail := Nat.mul_le_mul_left 2 (ih (sourceFactorStep s))
      have head := original_exact_factor_step_halves_the_input_product s
      calc
        _ = 2*(2^count*((sourceFactorWalk count (sourceFactorStep s)).a*
            (sourceFactorWalk count (sourceFactorStep s)).b)) := by
          rw [sourceFactorWalk,pow_succ]
          ring
        _ ≤ 2*((sourceFactorStep s).a*(sourceFactorStep s).b) := tail
        _ ≤ s.a*s.b := head

theorem original_exact_factor_walk_retains_odd_second_input
    (count : Nat) (s : SourceFactors) (odd : s.b%2=1) :
    (sourceFactorWalk count s).b%2=1 := by
  induction count generalizing s with
  | zero => exact odd
  | succ count ih =>
      exact ih (sourceFactorStep s) (original_factor_step_retains_odd_second_input s odd)

theorem exact_original_walk_reaches_zero_first_input_from_the_derived_product_bound
    (count : Nat) (s : SourceFactors) (odd : s.b%2=1) (bounded : s.a*s.b<2^count) :
    (sourceFactorWalk count s).a=0 ∧ 0<(sourceFactorWalk count s).b := by
  have decrease := symbolic_original_exact_factor_walk_derives_scaled_product_decrease count s
  have retained := original_exact_factor_walk_retains_odd_second_input count s odd
  have positiveB : 0<(sourceFactorWalk count s).b := by omega
  have productZero : (sourceFactorWalk count s).a*(sourceFactorWalk count s).b=0 := by
    by_contra nonzero
    have atLeastOne : 1≤(sourceFactorWalk count s).a*(sourceFactorWalk count s).b := by omega
    have scale := Nat.mul_le_mul_left (2^count) atLeastOne
    simp only [mul_one] at scale
    omega
  have zeroA := (Nat.mul_eq_zero.mp productZero).resolve_right (Nat.ne_of_gt positiveB)
  exact ⟨zeroA,positiveB⟩

set_option pp.all true in
#check @original_exact_factor_step_halves_the_input_product
#print axioms original_exact_factor_step_halves_the_input_product
set_option pp.all true in
#check @symbolic_original_exact_factor_walk_derives_scaled_product_decrease
#print axioms symbolic_original_exact_factor_walk_derives_scaled_product_decrease
set_option pp.all true in
#check @original_exact_factor_walk_retains_odd_second_input
#print axioms original_exact_factor_walk_retains_odd_second_input
set_option pp.all true in
#check @exact_original_walk_reaches_zero_first_input_from_the_derived_product_bound
#print axioms exact_original_walk_reaches_zero_first_input_from_the_derived_product_bound
end ShielddSecurity.TransferBlstArmInverseProgress01
