import Mathlib.Algebra.Group.Nat.Defs
import ShielddSecurity.TransferBlstArmInverseApproxBits01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseApproxError01
open TransferBlstArmInverseApproxBits01 (sourceApproxLow31)

/-! Initial error of the original low31 replacement, with explicit whole-input
high-window correspondence. Arithmetic guidance: Mahboubi et al., ITP2026,
DOI10.4230/LIPIcs.ITP.2026.9, Lemma27. This handwritten Lean proof does not
import their Rocq/Why3 artifact. Actual CLZ/high-window selection and the
first-divergence progress theorem remain separate obligations. -/

theorem original_high_window_and_low31_replacement_have_the_entire_remainder_equation
    (value shift : Nat) (high low : UInt64)
    (highWindow : high.toNat=value/2^shift) :
    2^shift*sourceApproxLow31 high low+
      (2^shift*(high.toNat%2147483648)+value%(2^shift))=
      value+2^shift*(low.toNat%2147483648) := by
  have highSplit := Nat.mod_add_div high.toNat 2147483648
  have inputSplit : value%(2^shift)+2^shift*high.toNat=value := by
    rw [highWindow]
    exact Nat.mod_add_div value (2^shift)
  rw [sourceApproxLow31]
  calc
    _ = (value%(2^shift)+2^shift*(high.toNat%2147483648+2147483648*(high.toNat/2147483648)))+
      2^shift*(low.toNat%2147483648) := by simp only [Nat.mul_add, Nat.mul_comm, Nat.add_assoc, Nat.add_comm]
    _ = _ := by rw [highSplit,inputSplit]

theorem symbolic_scaled_remainder_pair_is_strictly_below_the_combined_radix
    (scale quotient remainder : Nat)
    (quotientBound : quotient<2147483648) (remainderBound : remainder<scale) :
    scale*quotient+remainder<scale*2147483648 := by
  calc
    _ < scale*quotient+scale := Nat.add_lt_add_left remainderBound _
    _ = scale*(quotient+1) := by simp only [Nat.mul_add] <;> omega
    _ <= scale*2147483648 := Nat.mul_le_mul_left scale (by omega)

theorem symbolic_bounded_remainder_difference_has_strict_integer_magnitude
    (actual expected upperRemainder lowerRemainder budget : Nat)
    (conserved : expected+upperRemainder=actual+lowerRemainder)
    (upperBound : upperRemainder<budget) (lowerBound : lowerRemainder<budget) :
    ((actual:Int)-(expected:Int)).natAbs<budget := by
  by_cases nonnegative : 0 <= (actual:Int)-(expected:Int)
  · have absolute := Int.natAbs_of_nonneg nonnegative
    omega
  · have absolute := Int.eq_neg_natAbs_of_nonpos (by omega : (actual:Int)-(expected:Int) <= 0)
    omega

theorem original_low31_replacement_has_strict_initial_scaled_integer_error
    (value shift : Nat) (high low : UInt64)
    (highWindow : high.toNat=value/2^shift) :
    ((value:Int)-((2^shift*sourceApproxLow31 high low:Nat):Int)).natAbs <
      2^shift*2147483648 := by
  have positive : 0<(2:Nat)^shift := Nat.two_pow_pos shift
  have highBound := Nat.mod_lt high.toNat (by decide : 0<2147483648)
  have lowBound := Nat.mod_lt low.toNat (by decide : 0<2147483648)
  have remainderBound := Nat.mod_lt value positive
  have combined := symbolic_scaled_remainder_pair_is_strictly_below_the_combined_radix
    (2^shift) (high.toNat%2147483648) (value%(2^shift)) highBound remainderBound
  have lowScaled : 2^shift*(low.toNat%2147483648)<2^shift*2147483648 :=
    Nat.mul_lt_mul_of_pos_left lowBound positive
  have equation := original_high_window_and_low31_replacement_have_the_entire_remainder_equation value shift high low highWindow
  exact symbolic_bounded_remainder_difference_has_strict_integer_magnitude
    value (2^shift*sourceApproxLow31 high low)
    (2^shift*(high.toNat%2147483648)+value%(2^shift))
    (2^shift*(low.toNat%2147483648)) (2^shift*2147483648)
    equation combined lowScaled

theorem original_width_normalization_has_the_exact_initial_error_radix
    (width : Nat) (wide : 64 <= width) :
    2^(width-64)*2147483648=2^(width-33) := by
  have scale : (2147483648:Nat)=2^31 := by decide +kernel
  rw [scale,←Nat.pow_add]
  congr 1
  omega

theorem original_common_width_high_window_derives_the_paper_initial_error_bound
    (value width : Nat) (high low : UInt64) (wide : 64 <= width)
    (highWindow : high.toNat=value/2^(width-64)) :
    ((value:Int)-((2^(width-64)*sourceApproxLow31 high low:Nat):Int)).natAbs <
      2^(width-33) := by
  have bounded := original_low31_replacement_has_strict_initial_scaled_integer_error value (width-64) high low highWindow
  rw [original_width_normalization_has_the_exact_initial_error_radix width wide] at bounded
  exact bounded

set_option pp.all true in
#check @original_high_window_and_low31_replacement_have_the_entire_remainder_equation
#print axioms original_high_window_and_low31_replacement_have_the_entire_remainder_equation
set_option pp.all true in
#check @symbolic_scaled_remainder_pair_is_strictly_below_the_combined_radix
#print axioms symbolic_scaled_remainder_pair_is_strictly_below_the_combined_radix
set_option pp.all true in
#check @symbolic_bounded_remainder_difference_has_strict_integer_magnitude
#print axioms symbolic_bounded_remainder_difference_has_strict_integer_magnitude
set_option pp.all true in
#check @original_low31_replacement_has_strict_initial_scaled_integer_error
#print axioms original_low31_replacement_has_strict_initial_scaled_integer_error
set_option pp.all true in
#check @original_width_normalization_has_the_exact_initial_error_radix
#print axioms original_width_normalization_has_the_exact_initial_error_radix
set_option pp.all true in
#check @original_common_width_high_window_derives_the_paper_initial_error_bound
#print axioms original_common_width_high_window_derives_the_paper_initial_error_bound
end ShielddSecurity.TransferBlstArmInverseApproxError01
