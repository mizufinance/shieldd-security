import Mathlib.Algebra.Group.Nat.Defs
import ShielddSecurity.TransferBlstArmInverseFactors01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseNorm01
open TransferBlstArmInverseFactors01 (SourceFactors sourceFactorInitial sourceFactorStep sourceFactorWalk)

/-! Row-sum bounds derived from exact factor initialization and updates.
They bound signed u*f+v*g without an extra factor per matrix composition.
Actual packed31 factors, approximation/batch interpretation, coefficient
word multiplication and termination remain separate source obligations. -/

def RowBounds (bound : Nat) (s : SourceFactors) : Prop :=
  s.f0.natAbs+s.g0.natAbs≤bound ∧ s.f1.natAbs+s.g1.natAbs≤bound

theorem subtracting_two_bounded_rows_derives_the_doubled_row_sum_bound
    (a b c d : Int) (bound : Nat) (left : a.natAbs+b.natAbs≤bound) (right : c.natAbs+d.natAbs≤bound) :
    (a-c).natAbs+(b-d).natAbs≤2*bound := by
  have first := Int.natAbs_sub_le a c
  have second := Int.natAbs_sub_le b d
  omega

theorem original_exact_factor_step_derives_doubled_row_sum_bounds
    (bound : Nat) (s : SourceFactors) (bounded : RowBounds bound s) :
    RowBounds (2*bound) (sourceFactorStep s) := by
  have forward := subtracting_two_bounded_rows_derives_the_doubled_row_sum_bound
    s.f0 s.g0 s.f1 s.g1 bound bounded.1 bounded.2
  have reversed := subtracting_two_bounded_rows_derives_the_doubled_row_sum_bound
    s.f1 s.g1 s.f0 s.g0 bound bounded.2 bounded.1
  rw [sourceFactorStep]
  split
  · change s.f0.natAbs+s.g0.natAbs≤2*bound ∧ (2*s.f1).natAbs+(2*s.g1).natAbs≤2*bound
    rw [Int.natAbs_mul,Int.natAbs_mul]
    change s.f0.natAbs+s.g0.natAbs≤2*bound ∧ 2*s.f1.natAbs+2*s.g1.natAbs≤2*bound
    have first := bounded.1
    have second := bounded.2
    constructor <;> omega
  · split
    · change (s.f0-s.f1).natAbs+(s.g0-s.g1).natAbs≤2*bound ∧ (2*s.f1).natAbs+(2*s.g1).natAbs≤2*bound
      rw [Int.natAbs_mul,Int.natAbs_mul]
      change (s.f0-s.f1).natAbs+(s.g0-s.g1).natAbs≤2*bound ∧ 2*s.f1.natAbs+2*s.g1.natAbs≤2*bound
      have second := bounded.2
      exact ⟨forward,by omega⟩
    · change (s.f1-s.f0).natAbs+(s.g1-s.g0).natAbs≤2*bound ∧ (2*s.f0).natAbs+(2*s.g0).natAbs≤2*bound
      rw [Int.natAbs_mul,Int.natAbs_mul]
      change (s.f1-s.f0).natAbs+(s.g1-s.g0).natAbs≤2*bound ∧ 2*s.f0.natAbs+2*s.g0.natAbs≤2*bound
      have first := bounded.1
      exact ⟨reversed,by omega⟩

theorem symbolic_original_factor_walk_derives_its_full_row_sum_bounds
    (count bound : Nat) (s : SourceFactors) (bounded : RowBounds bound s) :
    RowBounds (2^count*bound) (sourceFactorWalk count s) := by
  induction count generalizing bound s with
  | zero => simpa only [pow_zero,one_mul,sourceFactorWalk] using bounded
  | succ count ih =>
      have next := ih (2*bound) (sourceFactorStep s)
        (original_exact_factor_step_derives_doubled_row_sum_bounds bound s bounded)
      have scaled : 2^count*(2*bound)=2^(count+1)*bound := by rw [Nat.pow_succ]; simp only [Nat.mul_assoc]
      rw [scaled] at next
      exact next

theorem original_initialized_factor_walk_derives_row_sums_at_most_its_radix_power
    (count a b : Nat) : RowBounds (2^count) (sourceFactorWalk count (sourceFactorInitial a b)) := by
  have initial : RowBounds 1 (sourceFactorInitial a b) := by
    change 1+0≤1 ∧ 0+1≤1
    decide
  have bounded := symbolic_original_factor_walk_derives_its_full_row_sum_bounds count 1 (sourceFactorInitial a b) initial
  simpa only [mul_one] using bounded

theorem original_simultaneous_factor_sign_correction_preserves_row_sum (a b : Int) :
    (-a).natAbs+(-b).natAbs=a.natAbs+b.natAbs := by rw [Int.natAbs_neg,Int.natAbs_neg]

theorem bounded_signed_inputs_and_factor_row_derive_the_actual_linear_combination_bound
    (u v f g : Int) (inputBound rowBound : Nat)
    (left : u.natAbs ≤ inputBound) (right : v.natAbs ≤ inputBound)
    (row : f.natAbs+g.natAbs≤rowBound) :
    (u*f+v*g).natAbs ≤ inputBound*rowBound := by
  calc
    _ ≤ (u*f).natAbs+(v*g).natAbs := Int.natAbs_add_le _ _
    _ = u.natAbs*f.natAbs+v.natAbs*g.natAbs := by rw [Int.natAbs_mul,Int.natAbs_mul]
    _ ≤ inputBound*f.natAbs+inputBound*g.natAbs :=
      Nat.add_le_add (Nat.mul_le_mul_right _ left) (Nat.mul_le_mul_right _ right)
    _ = inputBound*(f.natAbs+g.natAbs) := by rw [Nat.mul_add]
    _ ≤ inputBound*rowBound := Nat.mul_le_mul_left _ row

set_option pp.all true in
#check @RowBounds
#print axioms RowBounds
set_option pp.all true in
#check @subtracting_two_bounded_rows_derives_the_doubled_row_sum_bound
#print axioms subtracting_two_bounded_rows_derives_the_doubled_row_sum_bound
set_option pp.all true in
#check @original_exact_factor_step_derives_doubled_row_sum_bounds
#print axioms original_exact_factor_step_derives_doubled_row_sum_bounds
set_option pp.all true in
#check @symbolic_original_factor_walk_derives_its_full_row_sum_bounds
#print axioms symbolic_original_factor_walk_derives_its_full_row_sum_bounds
set_option pp.all true in
#check @original_initialized_factor_walk_derives_row_sums_at_most_its_radix_power
#print axioms original_initialized_factor_walk_derives_row_sums_at_most_its_radix_power
set_option pp.all true in
#check @original_simultaneous_factor_sign_correction_preserves_row_sum
#print axioms original_simultaneous_factor_sign_correction_preserves_row_sum
set_option pp.all true in
#check @bounded_signed_inputs_and_factor_row_derive_the_actual_linear_combination_bound
#print axioms bounded_signed_inputs_and_factor_row_derive_the_actual_linear_combination_bound
end ShielddSecurity.TransferBlstArmInverseNorm01
