import ShielddSecurity.TransferCommonwareMapCaller01
import ShielddSecurity.TransferJubjubDouble01
import Mathlib.Tactic.FieldSimp
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferJubjubMapCurve01
open TransferBoundedNativeCodec01 (nullifierModulus)
open TransferCommonwareMapParameters01
open TransferCommonwareMapCaller01
local instance scalarPrimeFact : Fact (Nat.Prime nullifierModulus) :=
  ⟨TransferScalarInverseCorrectness01.exact_source_scalar_modulus_is_prime⟩
local instance scalarNonzero : NeZero nullifierModulus := ⟨by decide⟩

attribute [local irreducible] sourceSelectedRoot sourceChoice sourceSelectedX sourceSdkCofactorInput

def sourceCubic (x : ZMod nullifierModulus) : ZMod nullifierModulus :=
  ((x+sourceC1)*x+sourceC2)*x

theorem actual_first_x_derives_the_source_denominator_equation (u : ZMod nullifierModulus) :
    (1+5*u*u)*sourceFirstX u+sourceC1=0 := by
  have nonzero := actual_elligator_denominator_is_nonzero u
  have product : sourceDenominator u*sourceFirstX u = -sourceC1 := by
    unfold sourceFirstX
    calc
      sourceDenominator u*(-sourceC1*(sourceDenominator u)⁻¹) =
          -sourceC1*(sourceDenominator u*(sourceDenominator u)⁻¹) := by ring
      _ = -sourceC1 := by rw [mul_inv_cancel₀ nonzero,mul_one]
  change sourceDenominator u*sourceFirstX u+sourceC1 = 0
  rw [product]
  exact neg_add_cancel sourceC1

theorem actual_alternative_cubic_is_the_source_selected_root_square (u : ZMod nullifierModulus) :
    sourceCubic (-sourceFirstX u-sourceC1) = sourceAlternative u := by
  have zero := actual_first_x_derives_the_source_denominator_equation u
  have identity : sourceCubic (-sourceFirstX u-sourceC1)-sourceAlternative u =
      -(sourceFirstX u*sourceFirstX u+sourceC1*sourceFirstX u+sourceC2)*
        ((1+5*u*u)*sourceFirstX u+sourceC1) := by
    unfold sourceCubic sourceAlternative sourceFirstCubic
    ring
  rw [zero,mul_zero] at identity
  exact sub_eq_zero.mp identity

theorem actual_selected_root_derives_the_selected_cubic_for_every_map_input (u : ZMod nullifierModulus) :
    sourceSelectedRoot u*sourceSelectedRoot u = sourceCubic (sourceSelectedX u) := by
  have square := (actual_map_root_constructor_derives_option_square_and_parity u).2.1
  cases chosen : sourceChoice u with
  | false =>
    rw [chosen] at square
    rw [sourceSelectedX,chosen]
    exact square.trans (actual_alternative_cubic_is_the_source_selected_root_square u).symm
  | true =>
    rw [chosen] at square
    rw [sourceSelectedX,chosen]
    exact square

theorem actual_selected_root_and_x_derive_the_source_montgomery_curve (u : ZMod nullifierModulus) :
    (sourceSelectedRoot u*sourceK)^2*sourceK =
      (sourceSelectedX u*sourceK)^3+40962*(sourceSelectedX u*sourceK)^2+sourceSelectedX u*sourceK := by
  have square := actual_selected_root_derives_the_selected_cubic_for_every_map_input u
  calc
    (sourceSelectedRoot u*sourceK)^2*sourceK =
        sourceCubic (sourceSelectedX u)*sourceK^3 := by
      calc
        _ = (sourceSelectedRoot u*sourceSelectedRoot u)*sourceK^3 := by ring
        _ = _ := by rw [square]
    _ = (sourceSelectedX u*sourceK)^3+
        (sourceC1*sourceK)*(sourceSelectedX u*sourceK)^2+
        (sourceC2*sourceK*sourceK)*(sourceSelectedX u*sourceK) := by unfold sourceCubic; ring
    _ = _ := by rw [exact_map_coefficient_products_recover_the_source_literals.1,
      exact_map_coefficient_products_recover_the_source_literals.2,one_mul]

def sourceD : ZMod nullifierModulus := -(10240 : ZMod nullifierModulus)* (10241 : ZMod nullifierModulus)⁻¹

theorem exact_d_numerator_has_negative_euler_power :
    (10240 : ZMod nullifierModulus)^(nullifierModulus/2) = -1 := by
  have power : (ModularPower.power nullifierModulus 10240 (nullifierModulus/2) : ZMod nullifierModulus) =
      (10240 : ZMod nullifierModulus)^(nullifierModulus/2) := by
    simpa only [Nat.cast_ofNat] using ModularPower.power_sound nullifierModulus 10240 (nullifierModulus/2)
  rw [← power]
  have checked : ModularPower.power nullifierModulus 10240 (nullifierModulus/2) = nullifierModulus-1 := by decide +kernel
  rw [checked,Nat.cast_sub (by decide : 1 ≤ nullifierModulus),ZMod.natCast_self,Nat.cast_one,zero_sub]

theorem exact_d_denominator_has_positive_euler_power :
    (10241 : ZMod nullifierModulus)^(nullifierModulus/2) = 1 := by
  have power : (ModularPower.power nullifierModulus 10241 (nullifierModulus/2) : ZMod nullifierModulus) =
      (10241 : ZMod nullifierModulus)^(nullifierModulus/2) := by
    simpa only [Nat.cast_ofNat] using ModularPower.power_sound nullifierModulus 10241 (nullifierModulus/2)
  rw [← power]
  have checked : ModularPower.power nullifierModulus 10241 (nullifierModulus/2) = 1 := by decide +kernel
  rw [checked,Nat.cast_one]

theorem exact_source_d_is_nonsquare_and_minus_one_is_square :
    ¬ IsSquare sourceD ∧ IsSquare (-1 : ZMod nullifierModulus) := by
  constructor
  · apply TransferFfEulerCriterion01.every_negative_euler_power_value_is_nonsquare
    have literal : sourceD = (-1)*(10240 : ZMod nullifierModulus)*(10241 : ZMod nullifierModulus)⁻¹ := by
      unfold sourceD; ring
    rw [literal,mul_pow,mul_pow,(by decide : Even (nullifierModulus/2)).neg_one_pow,
      exact_d_numerator_has_negative_euler_power,inv_pow,exact_d_denominator_has_positive_euler_power]
    simp
  · apply TransferFfEulerCriterion01.actual_ff_order_progress_derives_a_root_from_positive_euler_power
    exact (by decide : Even (nullifierModulus/2)).neg_one_pow

theorem actual_nonexceptional_rational_coordinates_derive_the_edwards_curve
    (s t : ZMod nullifierModulus) (tNonzero : t ≠ 0) (plusNonzero : s+1 ≠ 0)
    (montgomery : t^2*sourceK = s^3+40962*s^2+s) :
    ((s-1)*(s+1)⁻¹)^2-(s*t⁻¹)^2 =
      1+sourceD*(s*t⁻¹)^2*((s-1)*(s+1)⁻¹)^2 := by
  have cNonzero : (10241 : ZMod nullifierModulus) ≠ 0 := by decide +kernel
  have residual := sub_eq_zero.mpr montgomery
  have identity :
      ((((s-1)*(s+1)⁻¹)^2-(s*t⁻¹)^2)-
        (1+sourceD*(s*t⁻¹)^2*((s-1)*(s+1)⁻¹)^2))*t^2*(s+1)^2*sourceK =
      -4*s*(t^2*sourceK-(s^3+40962*s^2+s)) := by
    unfold sourceD sourceK
    field_simp
    ring
  rw [residual,mul_zero] at identity
  have multiplierNonzero : t^2*(s+1)^2*sourceK ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero 2 tNonzero) (pow_ne_zero 2 plusNonzero))
      exact_map_coefficients_have_nonzero_k_and_c1.1
  apply sub_eq_zero.mp
  apply (mul_eq_zero.mp ?_).resolve_right multiplierNonzero
  convert identity using 1
  ring

theorem actual_rational_map_payload_derives_the_edwards_curve
    (x y : ZMod nullifierModulus)
    (montgomery : (y*sourceK)^2*sourceK = (x*sourceK)^3+40962*(x*sourceK)^2+x*sourceK) :
    let p := sdkRationalInput x y
    p.2^2-p.1^2 = 1+sourceD*p.1^2*p.2^2 := by
  by_cases zero : (x*sourceK+1)*(y*sourceK)=0
  · simp [sdkRationalInput,zero]
  · have nonzero := mul_ne_zero_iff.mp zero
    have row := actual_nonexceptional_rational_coordinates_derive_the_edwards_curve
      (x*sourceK) (y*sourceK) nonzero.2 nonzero.1 montgomery
    have coordinates : sdkRationalInput x y =
        (x*sourceK*(y*sourceK)⁻¹,(x*sourceK-1)*(x*sourceK+1)⁻¹) := by
      unfold sdkRationalInput
      simp only [if_neg zero]
      apply Prod.ext
      · dsimp only
        rw [mul_inv_rev]
        calc
          _ = ((x*sourceK+1)⁻¹*(x*sourceK+1))*
              (x*sourceK*(y*sourceK)⁻¹) := by ring
          _ = _ := by rw [inv_mul_cancel₀ nonzero.1,one_mul]
      · dsimp only
        rw [mul_inv_rev]
        calc
          _ = ((y*sourceK)⁻¹*(y*sourceK))*
              ((x*sourceK-1)*(x*sourceK+1)⁻¹) := by ring
          _ = _ := by rw [inv_mul_cancel₀ nonzero.2,one_mul]
    simpa only [coordinates] using row

theorem actual_sdk_map_cofactor_input_derives_the_edwards_curve_on_every_input
    (u : ZMod nullifierModulus) :
    let p := sourceSdkCofactorInput u
    p.2^2-p.1^2 = 1+sourceD*p.1^2*p.2^2 := by
  unfold sourceSdkCofactorInput
  rw [actual_source_sdk_and_commonware_x_choices_agree]
  exact actual_rational_map_payload_derives_the_edwards_curve _ _
    (actual_selected_root_and_x_derive_the_source_montgomery_curve u)
theorem exact_sdk_d_from_raw_integer_is_the_commonware_rational_coefficient :
    (0x01065fd6d6343eb1+2^64*0x292d7f6d37579d26+
      2^128*0xf5fd9207e6bd7fd4+2^192*0x2a9318e74bfa2b48 : ZMod nullifierModulus) = sourceD := by
  have nonzero : (10241 : ZMod nullifierModulus) ≠ 0 := by decide +kernel
  apply mul_right_cancel₀ nonzero
  rw [sourceD,mul_assoc,inv_mul_cancel₀ nonzero,mul_one]
  decide +kernel

def sourceSdkClearedMap (u : ZMod nullifierModulus) : ZMod nullifierModulus × ZMod nullifierModulus :=
  let p := sourceSdkCofactorInput u
  TransferJubjubDouble01.sourceNormalizedCoordinates
    (TransferJubjubDouble01.sourceProjectiveSteps 3 (p.1,p.2,1))

def sourceCommonwareClearedMap (u : ZMod nullifierModulus) :
    Option (ZMod nullifierModulus × ZMod nullifierModulus) :=
  (sourceCommonwareCofactorInput u).map (TransferJubjubDouble01.sourceAffineSteps sourceD 3)

theorem actual_distinct_source_clearing_callers_derive_the_same_output_on_every_input
    (u : ZMod nullifierModulus) : sourceCommonwareClearedMap u = some (sourceSdkClearedMap u) := by
  rw [sourceCommonwareClearedMap,actual_source_map_callers_derive_the_same_cofactor_input,Option.map_some]
  have triple := TransferJubjubDouble01.actual_three_projective_doubles_match_three_affine_self_adds
    sourceD (sourceSdkCofactorInput u).1 (sourceSdkCofactorInput u).2
    (actual_sdk_map_cofactor_input_derives_the_edwards_curve_on_every_input u)
    exact_source_d_is_nonsquare_and_minus_one_is_square.1
    exact_source_d_is_nonsquare_and_minus_one_is_square.2
  exact congrArg some triple.symm
set_option pp.all true in
#check @scalarPrimeFact
#print axioms scalarPrimeFact
set_option pp.all true in
#check @scalarNonzero
#print axioms scalarNonzero
set_option pp.all true in
#check @sourceCubic
#print axioms sourceCubic
set_option pp.all true in
#check @actual_first_x_derives_the_source_denominator_equation
#print axioms actual_first_x_derives_the_source_denominator_equation
set_option pp.all true in
#check @actual_alternative_cubic_is_the_source_selected_root_square
#print axioms actual_alternative_cubic_is_the_source_selected_root_square
set_option pp.all true in
#check @actual_selected_root_derives_the_selected_cubic_for_every_map_input
#print axioms actual_selected_root_derives_the_selected_cubic_for_every_map_input
set_option pp.all true in
#check @actual_selected_root_and_x_derive_the_source_montgomery_curve
#print axioms actual_selected_root_and_x_derive_the_source_montgomery_curve
set_option pp.all true in
#check @sourceD
#print axioms sourceD
set_option pp.all true in
#check @exact_d_numerator_has_negative_euler_power
#print axioms exact_d_numerator_has_negative_euler_power
set_option pp.all true in
#check @exact_d_denominator_has_positive_euler_power
#print axioms exact_d_denominator_has_positive_euler_power
set_option pp.all true in
#check @exact_source_d_is_nonsquare_and_minus_one_is_square
#print axioms exact_source_d_is_nonsquare_and_minus_one_is_square
set_option pp.all true in
#check @actual_nonexceptional_rational_coordinates_derive_the_edwards_curve
#print axioms actual_nonexceptional_rational_coordinates_derive_the_edwards_curve
set_option pp.all true in
#check @actual_rational_map_payload_derives_the_edwards_curve
#print axioms actual_rational_map_payload_derives_the_edwards_curve
set_option pp.all true in
#check @actual_sdk_map_cofactor_input_derives_the_edwards_curve_on_every_input
#print axioms actual_sdk_map_cofactor_input_derives_the_edwards_curve_on_every_input
set_option pp.all true in
#check @exact_sdk_d_from_raw_integer_is_the_commonware_rational_coefficient
#print axioms exact_sdk_d_from_raw_integer_is_the_commonware_rational_coefficient
set_option pp.all true in
#check @sourceSdkClearedMap
#print axioms sourceSdkClearedMap
set_option pp.all true in
#check @sourceCommonwareClearedMap
#print axioms sourceCommonwareClearedMap
set_option pp.all true in
#check @actual_distinct_source_clearing_callers_derive_the_same_output_on_every_input
#print axioms actual_distinct_source_clearing_callers_derive_the_same_output_on_every_input
end ShielddSecurity.TransferJubjubMapCurve01
