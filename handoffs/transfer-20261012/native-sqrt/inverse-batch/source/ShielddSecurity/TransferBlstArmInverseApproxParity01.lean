import ShielddSecurity.TransferBlstArmInverseApproxRows01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseApproxParity01
open TransferBlstArmInverseFactors01 (SourceFactors Tracks sourceFactorStep sourceFactorWalk)
attribute [local irreducible] sourceFactorWalk

/-! The original doubled second factor row is even. Combining that property
with exact low31 input lifts preserves oddness of the entire second quotient.
Actual signed absolute-value word path, high-window progress, coefficient
production and native execution remain separate. -/

theorem original_factor_step_derives_even_second_row_coefficients (s : SourceFactors) :
    (sourceFactorStep s).f1%2=0 ∧ (sourceFactorStep s).g1%2=0 := by
  rw [sourceFactorStep]
  split
  · change (2*s.f1)%2=0 ∧ (2*s.g1)%2=0
    constructor <;> omega
  · split
    · change (2*s.f1)%2=0 ∧ (2*s.g1)%2=0
      constructor <;> omega
    · change (2*s.f0)%2=0 ∧ (2*s.g0)%2=0
      constructor <;> omega

theorem symbolic_factor_walk_retains_even_second_row_coefficients
    (count : Nat) (s : SourceFactors) (even : s.f1%2=0 ∧ s.g1%2=0) :
    (sourceFactorWalk count s).f1%2=0 ∧ (sourceFactorWalk count s).g1%2=0 := by
  induction count generalizing s with
  | zero => simpa only [sourceFactorWalk] using even
  | succ count ih =>
      rw [sourceFactorWalk]
      exact ih (sourceFactorStep s) (original_factor_step_derives_even_second_row_coefficients s)

theorem every_positive_original_factor_walk_derives_even_second_row_coefficients
    (count : Nat) (s : SourceFactors) :
    (sourceFactorWalk (count+1) s).f1%2=0 ∧ (sourceFactorWalk (count+1) s).g1%2=0 := by
  rw [sourceFactorWalk]
  exact symbolic_factor_walk_retains_even_second_row_coefficients count (sourceFactorStep s)
    (original_factor_step_derives_even_second_row_coefficients s)

theorem tracked_second_row_and_exact_input_lifts_derive_the_entire_original_quotient
    (approxA approxB : Nat) (inputA inputB deltaA deltaB : Int) (s : SourceFactors)
    (tracked : Tracks approxA approxB 2147483648 s)
    (left : inputA=(approxA:Int)+2147483648*deltaA)
    (right : inputB=(approxB:Int)+2147483648*deltaB) :
    (s.f1*inputA+s.g1*inputB)/2147483648=(s.b:Int)+s.f1*deltaA+s.g1*deltaB := by
  have whole : s.f1*inputA+s.g1*inputB=
      2147483648*((s.b:Int)+s.f1*deltaA+s.g1*deltaB) := by
    rw [left,right]
    calc
      _ = (s.f1*(approxA:Int)+s.g1*(approxB:Int))+
          2147483648*(s.f1*deltaA+s.g1*deltaB) := by ring
      _ = _ := by rw [← tracked.2]; ring
  rw [whole,Int.mul_ediv_cancel_left _ (by decide : (2147483648:Int)≠0)]

theorem original_even_second_factor_row_and_odd_approximate_input_preserve_full_quotient_oddness
    (approxA approxB : Nat) (inputA inputB deltaA deltaB : Int) (s : SourceFactors)
    (tracked : Tracks approxA approxB 2147483648 s)
    (left : inputA=(approxA:Int)+2147483648*deltaA)
    (right : inputB=(approxB:Int)+2147483648*deltaB)
    (even : s.f1%2=0 ∧ s.g1%2=0) (odd : s.b%2=1) :
    ((s.f1*inputA+s.g1*inputB)/2147483648)%2=1 := by
  rw [tracked_second_row_and_exact_input_lifts_derive_the_entire_original_quotient
    approxA approxB inputA inputB deltaA deltaB s tracked left right]
  have oddInt : (s.b:Int)%2=1 := by
    have cast := congrArg (fun value : Nat => (value:Int)) odd
    simpa only [Int.natCast_emod,Nat.cast_ofNat] using cast
  simp only [Int.add_emod,Int.mul_emod,even.1,even.2,zero_mul,Int.zero_emod,
    add_zero,oddInt]
  decide

set_option pp.all true in
#check @original_factor_step_derives_even_second_row_coefficients
#print axioms original_factor_step_derives_even_second_row_coefficients
set_option pp.all true in
#check @symbolic_factor_walk_retains_even_second_row_coefficients
#print axioms symbolic_factor_walk_retains_even_second_row_coefficients
set_option pp.all true in
#check @every_positive_original_factor_walk_derives_even_second_row_coefficients
#print axioms every_positive_original_factor_walk_derives_even_second_row_coefficients
set_option pp.all true in
#check @tracked_second_row_and_exact_input_lifts_derive_the_entire_original_quotient
#print axioms tracked_second_row_and_exact_input_lifts_derive_the_entire_original_quotient
set_option pp.all true in
#check @original_even_second_factor_row_and_odd_approximate_input_preserve_full_quotient_oddness
#print axioms original_even_second_factor_row_and_odd_approximate_input_preserve_full_quotient_oddness
end ShielddSecurity.TransferBlstArmInverseApproxParity01
