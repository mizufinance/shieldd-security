import ShielddSecurity.TransferBlstArmInverseFactors01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseBounds01
open TransferBlstArmInverseFactors01 (SourceFactors sourceFactorInitial sourceFactorStep sourceFactorWalk)

/-! Small symbolic coefficient bounds for the exact inner-loop interpretation.
All intermediate coefficients in the final 47-step walk fit signed 64 bits.
This is an integer bound, not a compiled register or approximate-batch proof. -/

def CoefficientBounds (bound : Int) (s : SourceFactors) : Prop :=
  0≤bound ∧ (-bound≤s.f0 ∧ s.f0≤bound) ∧ (-bound≤s.g0 ∧ s.g0≤bound) ∧
    (-bound≤s.f1 ∧ s.f1≤bound) ∧ (-bound≤s.g1 ∧ s.g1≤bound)

theorem original_factor_step_derives_doubled_coefficient_bounds
    (bound : Int) (s : SourceFactors) (bounded : CoefficientBounds bound s) :
    CoefficientBounds (2*bound) (sourceFactorStep s) := by
  rw [sourceFactorStep]
  split
  · simp only [CoefficientBounds] at bounded ⊢
    rcases bounded with ⟨positive,low0,high0,low1,high1⟩
    repeat' constructor <;> omega
  · split
    · simp only [CoefficientBounds] at bounded ⊢
      rcases bounded with ⟨positive,low0,high0,low1,high1⟩
      repeat' constructor <;> omega
    · simp only [CoefficientBounds] at bounded ⊢
      rcases bounded with ⟨positive,low0,high0,low1,high1⟩
      repeat' constructor <;> omega

theorem symbolic_original_factor_walk_derives_all_coefficient_bounds
    (count : Nat) (bound : Int) (s : SourceFactors) (bounded : CoefficientBounds bound s) :
    CoefficientBounds ((2:Int)^count*bound) (sourceFactorWalk count s) := by
  induction count generalizing bound s with
  | zero => simpa only [pow_zero,one_mul,sourceFactorWalk] using bounded
  | succ count ih =>
      have next := ih (2*bound) (sourceFactorStep s)
        (original_factor_step_derives_doubled_coefficient_bounds bound s bounded)
      have scaled : (2:Int)^count*(2*bound)=(2:Int)^(count+1)*bound := by rw [pow_succ]; ring
      rw [scaled] at next
      exact next

theorem original_initialized_factor_walk_derives_its_power_of_two_coefficient_bounds
    (count a b : Nat) : CoefficientBounds ((2:Int)^count) (sourceFactorWalk count (sourceFactorInitial a b)) := by
  have initial : CoefficientBounds 1 (sourceFactorInitial a b) := by
    norm_num [CoefficientBounds,sourceFactorInitial]
  have derived := symbolic_original_factor_walk_derives_all_coefficient_bounds count 1 (sourceFactorInitial a b) initial
  simpa only [mul_one] using derived

theorem every_original_final_inner_walk_coefficient_fits_the_signed_word
    (count a b : Nat) (bounded : count≤47) :
    let s := sourceFactorWalk count (sourceFactorInitial a b);
    -(2:Int)^63≤s.f0 ∧ s.f0<(2:Int)^63 ∧ -(2:Int)^63≤s.g0 ∧ s.g0<(2:Int)^63 ∧
      -(2:Int)^63≤s.f1 ∧ s.f1<(2:Int)^63 ∧ -(2:Int)^63≤s.g1 ∧ s.g1<(2:Int)^63 := by
  dsimp only
  have derived := original_initialized_factor_walk_derives_its_power_of_two_coefficient_bounds count a b
  have powerBound : (2:Int)^count≤(2:Int)^47 := by
    have natBound := Nat.pow_le_pow_right Nat.zero_lt_two bounded
    exact_mod_cast natBound
  have wordRoom : (2:Int)^47<(2:Int)^63 := by norm_num
  simp only [CoefficientBounds] at derived
  rcases derived with ⟨positive,low0,high0,low1,high1⟩
  repeat' constructor <;> omega

set_option pp.all true in
#check @CoefficientBounds
#print axioms CoefficientBounds
set_option pp.all true in
#check @original_factor_step_derives_doubled_coefficient_bounds
#print axioms original_factor_step_derives_doubled_coefficient_bounds
set_option pp.all true in
#check @symbolic_original_factor_walk_derives_all_coefficient_bounds
#print axioms symbolic_original_factor_walk_derives_all_coefficient_bounds
set_option pp.all true in
#check @original_initialized_factor_walk_derives_its_power_of_two_coefficient_bounds
#print axioms original_initialized_factor_walk_derives_its_power_of_two_coefficient_bounds
set_option pp.all true in
#check @every_original_final_inner_walk_coefficient_fits_the_signed_word
#print axioms every_original_final_inner_walk_coefficient_fits_the_signed_word
end ShielddSecurity.TransferBlstArmInverseBounds01
