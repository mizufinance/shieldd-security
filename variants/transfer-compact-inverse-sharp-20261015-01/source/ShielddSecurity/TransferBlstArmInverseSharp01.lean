import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import ShielddSecurity.TransferBlstArmInverseFactors01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseSharp01
open TransferBlstArmInverseFactors01 (SourceFactors sourceFactorInitial sourceFactorStep sourceFactorWalk)

/-! Asymmetric coefficient bounds for the original biased32 packed factor
encoding. The first row stays strictly between negative and positive 2^count; the second row can
reach +2^count but stays above -2^count. Original initialization and updates
derive the bounds; no chosen coefficient/encoding values are supplied.
Packed instruction correspondence and approximation/batch semantics remain open. -/

def SharpBounds (power : Int) (s : SourceFactors) : Prop :=
  2≤power ∧ (1-power≤s.f0 ∧ s.f0≤power-1) ∧ (1-power≤s.g0 ∧ s.g0≤power-1) ∧
    (2-power≤s.f1 ∧ s.f1≤power) ∧ (2-power≤s.g1 ∧ s.g1≤power)

theorem original_first_factor_step_derives_asymmetric_bounds (a b : Nat) :
    SharpBounds 2 (sourceFactorStep (sourceFactorInitial a b)) := by
  rw [sourceFactorInitial,sourceFactorStep]
  split
  · change 2≤(2:Int) ∧ (1-2≤1 ∧ 1≤2-1) ∧ (1-2≤0 ∧ 0≤2-1) ∧
      (2-2≤2*0 ∧ 2*0≤2) ∧ (2-2≤2*1 ∧ 2*1≤2)
    decide
  · split
    · change 2≤(2:Int) ∧ (1-2≤1-0 ∧ 1-0≤2-1) ∧ (1-2≤0-1 ∧ 0-1≤2-1) ∧
        (2-2≤2*0 ∧ 2*0≤2) ∧ (2-2≤2*1 ∧ 2*1≤2)
      decide
    · change 2≤(2:Int) ∧ (1-2≤0-1 ∧ 0-1≤2-1) ∧ (1-2≤1-0 ∧ 1-0≤2-1) ∧
        (2-2≤2*1 ∧ 2*1≤2) ∧ (2-2≤2*0 ∧ 2*0≤2)
      decide

theorem original_factor_step_preserves_doubled_asymmetric_bounds
    (power : Int) (s : SourceFactors) (bounded : SharpBounds power s) :
    SharpBounds (2*power) (sourceFactorStep s) := by
  rw [sourceFactorStep]
  split
  · simp only [SharpBounds] at bounded ⊢
    rcases bounded with ⟨positive,firstF,firstG,secondF,secondG⟩
    repeat' constructor <;> omega
  · split
    · simp only [SharpBounds] at bounded ⊢
      rcases bounded with ⟨positive,firstF,firstG,secondF,secondG⟩
      repeat' constructor <;> omega
    · simp only [SharpBounds] at bounded ⊢
      rcases bounded with ⟨positive,firstF,firstG,secondF,secondG⟩
      repeat' constructor <;> omega

theorem symbolic_original_factor_walk_preserves_all_asymmetric_bounds
    (count : Nat) (power : Int) (s : SourceFactors) (bounded : SharpBounds power s) :
    SharpBounds ((2:Int)^count*power) (sourceFactorWalk count s) := by
  induction count generalizing power s with
  | zero => simpa only [pow_zero,one_mul,sourceFactorWalk] using bounded
  | succ count ih =>
      have next := ih (2*power) (sourceFactorStep s)
        (original_factor_step_preserves_doubled_asymmetric_bounds power s bounded)
      have scaled : (2:Int)^count*(2*power)=(2:Int)^(count+1)*power := by rw [pow_succ]; ring
      rw [scaled] at next
      exact next

theorem original_initialized_positive_count_walk_derives_asymmetric_bounds
    (count a b : Nat) :
    SharpBounds ((2:Int)^(count+1)) (sourceFactorWalk (count+1) (sourceFactorInitial a b)) := by
  have bounded := symbolic_original_factor_walk_preserves_all_asymmetric_bounds count 2
    (sourceFactorStep (sourceFactorInitial a b)) (original_first_factor_step_derives_asymmetric_bounds a b)
  simpa only [sourceFactorWalk,pow_succ] using bounded

theorem every_original_31_step_factor_coefficient_fits_its_biased_unsigned_slot
    (count a b : Nat) (positive : 1≤count) (bounded : count≤31) :
    let s := sourceFactorWalk count (sourceFactorInitial a b);
    0≤s.f0+2147483647 ∧ s.f0+2147483647<4294967296 ∧
      0≤s.g0+2147483647 ∧ s.g0+2147483647<4294967296 ∧
      0≤s.f1+2147483647 ∧ s.f1+2147483647<4294967296 ∧
      0≤s.g1+2147483647 ∧ s.g1+2147483647<4294967296 := by
  dsimp only
  have previous : count-1+1=count := by omega
  have bounds := original_initialized_positive_count_walk_derives_asymmetric_bounds (count-1) a b
  rw [previous] at bounds
  have natPower := Nat.pow_le_pow_right Nat.zero_lt_two bounded
  have powerBound : (2:Int)^count≤2147483648 := by exact_mod_cast natPower
  simp only [SharpBounds] at bounds
  rcases bounds with ⟨size,firstF,firstG,secondF,secondG⟩
  repeat' constructor <;> omega

set_option pp.all true in
#check @SharpBounds
#print axioms SharpBounds
set_option pp.all true in
#check @original_first_factor_step_derives_asymmetric_bounds
#print axioms original_first_factor_step_derives_asymmetric_bounds
set_option pp.all true in
#check @original_factor_step_preserves_doubled_asymmetric_bounds
#print axioms original_factor_step_preserves_doubled_asymmetric_bounds
set_option pp.all true in
#check @symbolic_original_factor_walk_preserves_all_asymmetric_bounds
#print axioms symbolic_original_factor_walk_preserves_all_asymmetric_bounds
set_option pp.all true in
#check @original_initialized_positive_count_walk_derives_asymmetric_bounds
#print axioms original_initialized_positive_count_walk_derives_asymmetric_bounds
set_option pp.all true in
#check @every_original_31_step_factor_coefficient_fits_its_biased_unsigned_slot
#print axioms every_original_31_step_factor_coefficient_fits_its_biased_unsigned_slot
end ShielddSecurity.TransferBlstArmInverseSharp01
