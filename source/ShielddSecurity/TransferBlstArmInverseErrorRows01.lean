import ShielddSecurity.TransferBlstArmInverseNorm01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseErrorRows01
open TransferBlstArmInverseFactors01 (sourceFactorInitial sourceFactorWalk)
attribute [local irreducible] sourceFactorWalk

/-! Propagation of initial integer approximation errors through initialized
factor rows. Quotient outputs are defined from the full row numerators.
Exact row divisibility remains explicit here; the full-input low-bit lift
and prefix divisibility will discharge it in a later composition. No high
window, progress, compiled execution or full inverse claim is inferred. -/

def sourceActualFactorQuotients (count approxA approxB : Nat) (inputA inputB : Int) : Int × Int :=
  let factors := sourceFactorWalk count (sourceFactorInitial approxA approxB)
  ((factors.f0*inputA+factors.g0*inputB)/((2:Int)^count),
   (factors.f1*inputA+factors.g1*inputB)/((2:Int)^count))

theorem symbolic_exact_scaled_row_and_coefficient_norm_preserve_the_input_error_bound
    (count errorBound : Nat) (inputA inputB approxA approxB scale f g actual approx : Int)
    (leftError : (inputA-scale*approxA).natAbs <= errorBound)
    (rightError : (inputB-scale*approxB).natAbs <= errorBound)
    (rowNorm : f.natAbs+g.natAbs <= 2^count)
    (actualRow : ((2:Int)^count)*actual=f*inputA+g*inputB)
    (approxRow : ((2:Int)^count)*approx=f*approxA+g*approxB) :
    (actual-scale*approx).natAbs <= errorBound := by
  have conserved : ((2:Int)^count)*(actual-scale*approx)=
      (inputA-scale*approxA)*f+(inputB-scale*approxB)*g := by
    calc
      _ = ((2:Int)^count)*actual-scale*(((2:Int)^count)*approx) := by ring
      _ = _ := by rw [actualRow,approxRow]; ring
  have bounded := TransferBlstArmInverseNorm01.bounded_signed_inputs_and_factor_row_derive_the_actual_linear_combination_bound
    (inputA-scale*approxA) (inputB-scale*approxB) f g errorBound (2^count) leftError rightError rowNorm
  rw [←conserved, Int.natAbs_mul, Int.natAbs_pow] at bounded
  change 2^count*(actual-scale*approx).natAbs <= errorBound*2^count at bounded
  have reordered : 2^count*(actual-scale*approx).natAbs <= 2^count*errorBound := by
    simpa only [Nat.mul_comm] using bounded
  exact Nat.le_of_mul_le_mul_left reordered (Nat.two_pow_pos count)

theorem original_initialized_factor_quotients_preserve_both_full_input_error_bounds
    (count approxA approxB errorBound : Nat) (inputA inputB scale : Int)
    (oddB : approxB%2=1)
    (leftError : (inputA-scale*(approxA:Int)).natAbs <= errorBound)
    (rightError : (inputB-scale*(approxB:Int)).natAbs <= errorBound)
    (leftDivisible : ((2:Int)^count) ∣
      (sourceFactorWalk count (sourceFactorInitial approxA approxB)).f0*inputA+
      (sourceFactorWalk count (sourceFactorInitial approxA approxB)).g0*inputB)
    (rightDivisible : ((2:Int)^count) ∣
      (sourceFactorWalk count (sourceFactorInitial approxA approxB)).f1*inputA+
      (sourceFactorWalk count (sourceFactorInitial approxA approxB)).g1*inputB) :
    ((sourceActualFactorQuotients count approxA approxB inputA inputB).1-
      scale*((sourceFactorWalk count (sourceFactorInitial approxA approxB)).a:Int)).natAbs <= errorBound /\
    ((sourceActualFactorQuotients count approxA approxB inputA inputB).2-
      scale*((sourceFactorWalk count (sourceFactorInitial approxA approxB)).b:Int)).natAbs <= errorBound := by
  let factors := sourceFactorWalk count (sourceFactorInitial approxA approxB)
  have norms := TransferBlstArmInverseNorm01.original_initialized_factor_walk_derives_row_sums_at_most_its_radix_power count approxA approxB
  have tracked := TransferBlstArmInverseFactors01.original_initialized_factor_walk_derives_exact_scaled_input_rows count approxA approxB oddB
  change factors.f0.natAbs+factors.g0.natAbs <= 2^count /\ factors.f1.natAbs+factors.g1.natAbs <= 2^count at norms
  change ((2:Int)^count)*(factors.a:Int)=factors.f0*(approxA:Int)+factors.g0*(approxB:Int) /\
    ((2:Int)^count)*(factors.b:Int)=factors.f1*(approxA:Int)+factors.g1*(approxB:Int) at tracked
  change ((factors.f0*inputA+factors.g0*inputB)/((2:Int)^count)-scale*(factors.a:Int)).natAbs <= errorBound /\
    ((factors.f1*inputA+factors.g1*inputB)/((2:Int)^count)-scale*(factors.b:Int)).natAbs <= errorBound
  exact And.intro
    (symbolic_exact_scaled_row_and_coefficient_norm_preserve_the_input_error_bound count errorBound
      inputA inputB (approxA:Int) (approxB:Int) scale factors.f0 factors.g0
      ((factors.f0*inputA+factors.g0*inputB)/((2:Int)^count)) (factors.a:Int)
      leftError rightError norms.1 (Int.mul_ediv_cancel_of_dvd leftDivisible) tracked.1)
    (symbolic_exact_scaled_row_and_coefficient_norm_preserve_the_input_error_bound count errorBound
      inputA inputB (approxA:Int) (approxB:Int) scale factors.f1 factors.g1
      ((factors.f1*inputA+factors.g1*inputB)/((2:Int)^count)) (factors.b:Int)
      leftError rightError norms.2 (Int.mul_ediv_cancel_of_dvd rightDivisible) tracked.2)

set_option pp.all true in
#check @sourceActualFactorQuotients
#print axioms sourceActualFactorQuotients
set_option pp.all true in
#check @symbolic_exact_scaled_row_and_coefficient_norm_preserve_the_input_error_bound
#print axioms symbolic_exact_scaled_row_and_coefficient_norm_preserve_the_input_error_bound
set_option pp.all true in
#check @original_initialized_factor_quotients_preserve_both_full_input_error_bounds
#print axioms original_initialized_factor_quotients_preserve_both_full_input_error_bounds
end ShielddSecurity.TransferBlstArmInverseErrorRows01
