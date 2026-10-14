import ShielddSecurity.ConcreteJubjubField01
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.Ring.Parity
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
namespace ShielddSecurity.BalanceMapParameters699
open ConcreteJubjubField01
-- Mathematical circuit construction parameters. This does not claim native execution.
theorem exact_elligator_five_parameter_has_negative_euler_power :
    (5:F) ^ (Scalar.modulus/2) = -1 := by
  have power : (ModularPower.power Scalar.modulus 5 (Scalar.modulus/2) : F) =
      (5:F) ^ (Scalar.modulus/2) := by
    simpa only [Nat.cast_ofNat] using ModularPower.power_sound Scalar.modulus 5 (Scalar.modulus/2)
  rw [← power]
  have checked : ModularPower.power Scalar.modulus 5 (Scalar.modulus/2) = Scalar.modulus-1 := by decide +kernel
  rw [checked,Nat.cast_sub (by decide : 1 ≤ Scalar.modulus),ZMod.natCast_self,Nat.cast_one,zero_sub]

def sourceK : F := -40964
def sourceC1 : F := 40962 * sourceK⁻¹
def sourceC2 : F := sourceK⁻¹ * sourceK⁻¹
def sourceDenominator (u : F) : F := 1+5*u*u
def sourceFirstX (u : F) : F := -sourceC1 * (sourceDenominator u)⁻¹
def sourceFirstCubic (u : F) : F :=
  ((sourceFirstX u+sourceC1)*sourceFirstX u+sourceC2)*sourceFirstX u
def sourceDiscriminantNumerator : F := 40962^2-4

theorem exact_negative_euler_parameter_is_nonsquare (value : F)
    (negative : value ^ (Scalar.modulus/2) = -1) : ¬ IsSquare value := by
  have nonzero : value ≠ 0 := by
    intro zero
    have bad : (0:F) = -1 := by simpa only [zero,zero_pow (by decide : Scalar.modulus/2 ≠ 0)] using negative
    exact (neg_ne_zero.mpr (one_ne_zero : (1:F) ≠ 0)) bad.symm
  intro square
  have positive : value ^ (Scalar.modulus/2) = 1 := by
    obtain ⟨root,equation⟩ := square
    have rootNonzero : root≠0 := by
      intro zero
      apply nonzero
      simpa only [zero,mul_zero] using equation
    let unit : Fˣ := Units.mk0 root rootNonzero
    have cardinality : Fintype.card Fˣ=Scalar.modulus-1 := by rw [Fintype.card_units,ZMod.card]
    have unitPower : unit^(Scalar.modulus-1)=1 := by rw [← cardinality]; exact pow_card_eq_one
    have projected := congrArg (fun u : Fˣ => (u:F)) unitPower
    have power : root^(Scalar.modulus-1)=1 := by
      simpa only [Units.val_pow_eq_pow_val,Units.val_one,unit,Units.val_mk0] using projected
    rw [equation,← pow_two,← pow_mul,(by decide : 2*(Scalar.modulus/2)=Scalar.modulus-1)]
    exact power
  exact (by decide +kernel : (-1:F) ≠ 1) (negative.symm.trans positive)

theorem exact_elligator_negative_inverse_five_is_nonsquare : ¬ IsSquare (-1/5 : F) := by
  apply exact_negative_euler_parameter_is_nonsquare
  rw [div_pow,(by decide : Even (Scalar.modulus/2)).neg_one_pow,
    exact_elligator_five_parameter_has_negative_euler_power]
  simp

theorem actual_elligator_denominator_is_nonzero (u : F) : sourceDenominator u ≠ 0 := by
  intro zero
  have fiveNonzero : (5 : F) ≠ 0 := by decide +kernel
  have product : u*u*5 = -1 := by
    unfold sourceDenominator at zero
    calc
      u*u*5 = 5*u*u := by ring
      _ = -1 := eq_neg_of_add_eq_zero_right zero
  have square : u*u = (-1/5 : F) := (eq_div_iff fiveNonzero).mpr product
  exact exact_elligator_negative_inverse_five_is_nonsquare ⟨u,square.symm⟩

theorem exact_map_coefficients_have_nonzero_k_and_c1 : sourceK ≠ 0 ∧ sourceC1 ≠ 0 := by
  have kNonzero : sourceK ≠ 0 := by decide +kernel
  exact ⟨kNonzero,mul_ne_zero (by decide +kernel : (40962 : F) ≠ 0) (inv_ne_zero kNonzero)⟩

theorem actual_elligator_first_x_is_nonzero (u : F) : sourceFirstX u ≠ 0 :=
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
    sourceDiscriminantNumerator ^ (Scalar.modulus/2) = -1 := by
  have literal : sourceDiscriminantNumerator = (1677885440 : F) := by
    norm_num [sourceDiscriminantNumerator]
  have power : (ModularPower.power Scalar.modulus 1677885440 (Scalar.modulus/2) : F) =
      (1677885440 : F) ^ (Scalar.modulus/2) := by
    simpa only [Nat.cast_ofNat] using ModularPower.power_sound Scalar.modulus 1677885440 (Scalar.modulus/2)
  rw [literal,← power]
  have checked : ModularPower.power Scalar.modulus 1677885440 (Scalar.modulus/2) = Scalar.modulus-1 := by decide +kernel
  rw [checked,Nat.cast_sub (by decide : 1 ≤ Scalar.modulus),ZMod.natCast_self,Nat.cast_one,zero_sub]

theorem actual_elligator_first_cubic_is_nonzero (u : F) : sourceFirstCubic u ≠ 0 := by
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

end ShielddSecurity.BalanceMapParameters699

set_option pp.all true in
#check @ShielddSecurity.BalanceMapParameters699.exact_elligator_five_parameter_has_negative_euler_power
#print axioms ShielddSecurity.BalanceMapParameters699.exact_elligator_five_parameter_has_negative_euler_power

set_option pp.all true in
#check @ShielddSecurity.BalanceMapParameters699.exact_negative_euler_parameter_is_nonsquare
#print axioms ShielddSecurity.BalanceMapParameters699.exact_negative_euler_parameter_is_nonsquare

set_option pp.all true in
#check @ShielddSecurity.BalanceMapParameters699.exact_elligator_negative_inverse_five_is_nonsquare
#print axioms ShielddSecurity.BalanceMapParameters699.exact_elligator_negative_inverse_five_is_nonsquare

set_option pp.all true in
#check @ShielddSecurity.BalanceMapParameters699.actual_elligator_denominator_is_nonzero
#print axioms ShielddSecurity.BalanceMapParameters699.actual_elligator_denominator_is_nonzero

set_option pp.all true in
#check @ShielddSecurity.BalanceMapParameters699.exact_map_coefficients_have_nonzero_k_and_c1
#print axioms ShielddSecurity.BalanceMapParameters699.exact_map_coefficients_have_nonzero_k_and_c1

set_option pp.all true in
#check @ShielddSecurity.BalanceMapParameters699.actual_elligator_first_x_is_nonzero
#print axioms ShielddSecurity.BalanceMapParameters699.actual_elligator_first_x_is_nonzero

set_option pp.all true in
#check @ShielddSecurity.BalanceMapParameters699.exact_map_coefficient_products_recover_the_source_literals
#print axioms ShielddSecurity.BalanceMapParameters699.exact_map_coefficient_products_recover_the_source_literals

set_option pp.all true in
#check @ShielddSecurity.BalanceMapParameters699.exact_discriminant_numerator_has_negative_euler_power
#print axioms ShielddSecurity.BalanceMapParameters699.exact_discriminant_numerator_has_negative_euler_power

set_option pp.all true in
#check @ShielddSecurity.BalanceMapParameters699.actual_elligator_first_cubic_is_nonzero
#print axioms ShielddSecurity.BalanceMapParameters699.actual_elligator_first_cubic_is_nonzero
