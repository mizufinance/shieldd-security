import ShielddSecurity.TransferCommonwareMapRoots01
import Mathlib.Algebra.Ring.Parity
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferCommonwareMapParameters01
open TransferBoundedNativeCodec01 (nullifierModulus)
open TransferCommonwareMapRoots01
open TransferFfEulerCriterion01
local instance scalarPrimeFact : Fact (Nat.Prime nullifierModulus) :=
  ⟨TransferScalarInverseCorrectness01.exact_source_scalar_modulus_is_prime⟩
local instance scalarNonzero : NeZero nullifierModulus := ⟨by decide⟩

def sourceK : ZMod nullifierModulus := -40964
def sourceC1 : ZMod nullifierModulus := 40962 * sourceK⁻¹
def sourceC2 : ZMod nullifierModulus := sourceK⁻¹ * sourceK⁻¹
def sourceDenominator (u : ZMod nullifierModulus) : ZMod nullifierModulus := 1+5*u*u
def sourceFirstX (u : ZMod nullifierModulus) : ZMod nullifierModulus := -sourceC1 * (sourceDenominator u)⁻¹
def sourceFirstCubic (u : ZMod nullifierModulus) : ZMod nullifierModulus :=
  ((sourceFirstX u+sourceC1)*sourceFirstX u+sourceC2)*sourceFirstX u
def sourceDiscriminantNumerator : ZMod nullifierModulus := 40962^2-4

theorem exact_negative_euler_parameter_is_nonsquare (value : ZMod nullifierModulus)
    (negative : value ^ (nullifierModulus/2) = -1) : ¬ IsSquare value := by
  exact every_negative_euler_power_value_is_nonsquare value negative

theorem exact_elligator_negative_inverse_five_is_nonsquare : ¬ IsSquare (-1/5 : ZMod nullifierModulus) := by
  apply exact_negative_euler_parameter_is_nonsquare
  rw [div_pow,(by decide : Even (nullifierModulus/2)).neg_one_pow,
    exact_elligator_five_parameter_has_negative_euler_power]
  simp

theorem actual_elligator_denominator_is_nonzero (u : ZMod nullifierModulus) : sourceDenominator u ≠ 0 := by
  intro zero
  have fiveNonzero : (5 : ZMod nullifierModulus) ≠ 0 := by decide +kernel
  have product : u*u*5 = -1 := by
    unfold sourceDenominator at zero
    calc
      u*u*5 = 5*u*u := by ring
      _ = -1 := eq_neg_of_add_eq_zero_right zero
  have square : u*u = (-1/5 : ZMod nullifierModulus) := (eq_div_iff fiveNonzero).mpr product
  exact exact_elligator_negative_inverse_five_is_nonsquare ⟨u,square.symm⟩

theorem exact_map_coefficients_have_nonzero_k_and_c1 : sourceK ≠ 0 ∧ sourceC1 ≠ 0 := by
  have kNonzero : sourceK ≠ 0 := by decide +kernel
  exact ⟨kNonzero,mul_ne_zero (by decide +kernel : (40962 : ZMod nullifierModulus) ≠ 0) (inv_ne_zero kNonzero)⟩

theorem actual_elligator_first_x_is_nonzero (u : ZMod nullifierModulus) : sourceFirstX u ≠ 0 :=
  mul_ne_zero (neg_ne_zero.mpr exact_map_coefficients_have_nonzero_k_and_c1.2)
    (inv_ne_zero (actual_elligator_denominator_is_nonzero u))

theorem exact_map_coefficient_products_recover_the_source_literals :
    sourceC1*sourceK = 40962 ∧ sourceC2*sourceK*sourceK = 1 := by
  have nonzero := exact_map_coefficients_have_nonzero_k_and_c1.1
  constructor
  · rw [sourceC1,mul_assoc,inv_mul_cancel₀ nonzero,mul_one]
  · calc
      sourceC2*sourceK*sourceK = (sourceK⁻¹*sourceK)*(sourceK⁻¹*sourceK) := by unfold sourceC2; ring
      _ = 1 := by rw [inv_mul_cancel₀ nonzero,one_mul]

theorem exact_discriminant_numerator_has_negative_euler_power :
    sourceDiscriminantNumerator ^ (nullifierModulus/2) = -1 := by
  have literal : sourceDiscriminantNumerator = (1677885440 : ZMod nullifierModulus) := by
    norm_num [sourceDiscriminantNumerator]
  have power : (ModularPower.power nullifierModulus 1677885440 (nullifierModulus/2) : ZMod nullifierModulus) =
      (1677885440 : ZMod nullifierModulus) ^ (nullifierModulus/2) := by
    simpa only [Nat.cast_ofNat] using ModularPower.power_sound nullifierModulus 1677885440 (nullifierModulus/2)
  rw [literal,← power]
  have checked : ModularPower.power nullifierModulus 1677885440 (nullifierModulus/2) = nullifierModulus-1 := by decide +kernel
  rw [checked,Nat.cast_sub (by decide : 1 ≤ nullifierModulus),ZMod.natCast_self,Nat.cast_one,zero_sub]

theorem actual_elligator_first_cubic_is_nonzero (u : ZMod nullifierModulus) : sourceFirstCubic u ≠ 0 := by
  intro zero
  have xNonzero := actual_elligator_first_x_is_nonzero u
  have quadratic : (sourceFirstX u+sourceC1)*sourceFirstX u+sourceC2=0 :=
    (mul_eq_zero.mp zero).resolve_right xNonzero
  have polynomial : ((2*sourceFirstX u+sourceC1)*sourceK)^2 =
      ((sourceC1*sourceK)^2-4*(sourceC2*sourceK*sourceK)) +
        4*sourceK*sourceK*((sourceFirstX u+sourceC1)*sourceFirstX u+sourceC2) := by ring
  rw [exact_map_coefficient_products_recover_the_source_literals.1,
    exact_map_coefficient_products_recover_the_source_literals.2,quadratic,mul_zero,add_zero,mul_one] at polynomial
  exact exact_negative_euler_parameter_is_nonsquare sourceDiscriminantNumerator
    exact_discriminant_numerator_has_negative_euler_power
    ⟨(2*sourceFirstX u+sourceC1)*sourceK,by simpa only [pow_two] using polynomial.symm⟩

set_option pp.all true in
#check @scalarPrimeFact
#print axioms scalarPrimeFact
set_option pp.all true in
#check @scalarNonzero
#print axioms scalarNonzero
set_option pp.all true in
#check @sourceK
#print axioms sourceK
set_option pp.all true in
#check @sourceC1
#print axioms sourceC1
set_option pp.all true in
#check @sourceC2
#print axioms sourceC2
set_option pp.all true in
#check @sourceDenominator
#print axioms sourceDenominator
set_option pp.all true in
#check @sourceFirstX
#print axioms sourceFirstX
set_option pp.all true in
#check @sourceFirstCubic
#print axioms sourceFirstCubic
set_option pp.all true in
#check @sourceDiscriminantNumerator
#print axioms sourceDiscriminantNumerator
set_option pp.all true in
#check @exact_negative_euler_parameter_is_nonsquare
#print axioms exact_negative_euler_parameter_is_nonsquare
set_option pp.all true in
#check @exact_elligator_negative_inverse_five_is_nonsquare
#print axioms exact_elligator_negative_inverse_five_is_nonsquare
set_option pp.all true in
#check @actual_elligator_denominator_is_nonzero
#print axioms actual_elligator_denominator_is_nonzero
set_option pp.all true in
#check @exact_map_coefficients_have_nonzero_k_and_c1
#print axioms exact_map_coefficients_have_nonzero_k_and_c1
set_option pp.all true in
#check @actual_elligator_first_x_is_nonzero
#print axioms actual_elligator_first_x_is_nonzero
set_option pp.all true in
#check @exact_map_coefficient_products_recover_the_source_literals
#print axioms exact_map_coefficient_products_recover_the_source_literals
set_option pp.all true in
#check @exact_discriminant_numerator_has_negative_euler_power
#print axioms exact_discriminant_numerator_has_negative_euler_power
set_option pp.all true in
#check @actual_elligator_first_cubic_is_nonzero
#print axioms actual_elligator_first_cubic_is_nonzero
end ShielddSecurity.TransferCommonwareMapParameters01
