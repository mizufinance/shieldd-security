import ShielddSecurity.TransferBlstArmInverseProgress01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseExactGcd01
open TransferBlstArmInverseFactors01 (SourceFactors sourceFactorStep sourceFactorWalk)

/-! GCD conservation of the exact source factor recurrence. The endpoint
uses an explicit input-product bound; preceding approximate batch progress
and actual runtime final-state correspondence remain separate obligations. -/

theorem symbolic_exact_halving_retains_gcd_with_an_odd_second_input
    (a b : Nat) (even : a%2=0) (odd : b%2=1) :
    Nat.gcd (a/2) b=Nat.gcd a b := by
  have coprime : Nat.Coprime 2 b := by
    change Nat.gcd 2 b=1
    rw [Nat.gcd_rec, odd, Nat.gcd_one_left]
  have half : 2*(a/2)=a := by omega
  exact (coprime.gcd_mul_left_cancel (a/2)).symm.trans (congrArg (fun n => Nat.gcd n b) half)

theorem original_exact_factor_step_preserves_the_entire_input_gcd
    (s : SourceFactors) (odd : s.b%2=1) :
    Nat.gcd (sourceFactorStep s).a (sourceFactorStep s).b=Nat.gcd s.a s.b := by
  by_cases even : s.a%2=0
  · rw [sourceFactorStep, if_pos even]
    exact symbolic_exact_halving_retains_gcd_with_an_odd_second_input s.a s.b even odd
  · have aOdd : s.a%2=1 := by have bound := Nat.mod_lt s.a (by decide : 0<2); omega
    by_cases ordered : s.b <= s.a
    · rw [sourceFactorStep, if_neg even, if_pos ordered]
      exact (symbolic_exact_halving_retains_gcd_with_an_odd_second_input (s.a-s.b) s.b (by omega) odd).trans
        (Nat.gcd_sub_self_left ordered)
    · rw [sourceFactorStep, if_neg even, if_neg ordered]
      exact (symbolic_exact_halving_retains_gcd_with_an_odd_second_input (s.b-s.a) s.a (by omega) aOdd).trans
        ((Nat.gcd_sub_self_left (by omega : s.a <= s.b)).trans (Nat.gcd_comm s.b s.a))

theorem symbolic_original_exact_factor_walk_preserves_the_entire_input_gcd
    (count : Nat) (s : SourceFactors) (odd : s.b%2=1) :
    Nat.gcd (sourceFactorWalk count s).a (sourceFactorWalk count s).b=Nat.gcd s.a s.b := by
  induction count generalizing s with
  | zero => rfl
  | succ count ih =>
      exact (ih (sourceFactorStep s)
        (TransferBlstArmInverseFactors01.original_factor_step_retains_odd_second_input s odd)).trans
        (original_exact_factor_step_preserves_the_entire_input_gcd s odd)

theorem original_exact_factor_walk_derives_zero_and_the_original_gcd_from_product_progress
    (count : Nat) (s : SourceFactors) (odd : s.b%2=1) (bounded : s.a*s.b < 2^count) :
    (sourceFactorWalk count s).a=0 /\ (sourceFactorWalk count s).b=Nat.gcd s.a s.b := by
  have zero := (TransferBlstArmInverseProgress01.exact_original_walk_reaches_zero_first_input_from_the_derived_product_bound count s odd bounded).1
  have conserved := symbolic_original_exact_factor_walk_preserves_the_entire_input_gcd count s odd
  rw [zero, Nat.gcd_zero_left] at conserved
  exact And.intro zero conserved

set_option pp.all true in
#check @symbolic_exact_halving_retains_gcd_with_an_odd_second_input
#print axioms symbolic_exact_halving_retains_gcd_with_an_odd_second_input
set_option pp.all true in
#check @original_exact_factor_step_preserves_the_entire_input_gcd
#print axioms original_exact_factor_step_preserves_the_entire_input_gcd
set_option pp.all true in
#check @symbolic_original_exact_factor_walk_preserves_the_entire_input_gcd
#print axioms symbolic_original_exact_factor_walk_preserves_the_entire_input_gcd
set_option pp.all true in
#check @original_exact_factor_walk_derives_zero_and_the_original_gcd_from_product_progress
#print axioms original_exact_factor_walk_derives_zero_and_the_original_gcd_from_product_progress
end ShielddSecurity.TransferBlstArmInverseExactGcd01
