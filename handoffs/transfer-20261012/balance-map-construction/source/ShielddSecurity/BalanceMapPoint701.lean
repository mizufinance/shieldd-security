import ShielddSecurity.BalanceMapRoots700
import ShielddSecurity.BalanceElligatorAlgebra697
import ShielddSecurity.BalanceMapInverse698
import ShielddSecurity.ConcreteCofactorModel01
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.BalanceMapPoint701
open ConcreteJubjubField01 ConcretePointTorsion01 BalanceMapParameters699
attribute [local irreducible] ConcreteCofactorModel01.model

noncomputable def s (u : F) : F :=
  (if BalanceMapRoots700.choice u then sourceFirstX u else -sourceFirstX u-sourceC1)*sourceK
noncomputable def t (u : F) : F := BalanceMapRoots700.selectedRoot u*sourceK
noncomputable def denominator (u : F) : F := (s u+1)*t u
noncomputable def zero (u : F) : F := if denominator u=0 then 1 else 0
noncomputable def preimage (u : F) : Group.Point F :=
  ⟨(denominator u)⁻¹*(s u+1)*s u,(denominator u)⁻¹*t u*(s u-1)+zero u⟩
noncomputable def twice (u : F) : Group.Point F := Group.affineAdd coefficient (preimage u) (preimage u)
noncomputable def four (u : F) : Group.Point F := Group.affineAdd coefficient (twice u) (twice u)
noncomputable def eight (u : F) : Group.Point F := Group.affineAdd coefficient (four u) (four u)

theorem coefficient_scale : coefficient*sourceK=(40962:F)-2 := by
  have cast := congrArg (fun value : Nat => (value:F)) coefficient_integer_equation
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,ZMod.natCast_self,mul_zero] at cast
  change (10241:F)*coefficient+10240=0 at cast
  unfold sourceK
  linear_combination -4*cast

theorem first_equation (u : F) : (1+5*u*u)*sourceFirstX u= -sourceC1 := by
  have nonzero := actual_elligator_denominator_is_nonzero u
  change sourceDenominator u*(-sourceC1*(sourceDenominator u)⁻¹)= -sourceC1
  calc
    _ = -sourceC1*(sourceDenominator u*(sourceDenominator u)⁻¹) := by ring
    _ = -sourceC1 := by rw [mul_inv_cancel₀ nonzero,mul_one]

theorem scaled_cubic (u : F) : sourceK*(t u)^2=(s u)^3+40962*(s u)^2+s u := by
  apply BalanceElligatorAlgebra697.scaled 40962 sourceK sourceC1 sourceC2 _ _
    exact_map_coefficient_products_recover_the_source_literals.1
    exact_map_coefficient_products_recover_the_source_literals.2
  apply BalanceElligatorAlgebra697.selected_square sourceC1 sourceC2 (5*u*u)
    (sourceFirstX u) (BalanceMapRoots700.selectedRoot u) (BalanceMapRoots700.choice u) (first_equation u)
  exact BalanceMapRoots700.selected_square u

theorem preimage_on_curve (u : F) : Group.OnCurve coefficient (preimage u) := by
  have h := BalanceMapInverse698.circuit_curve 40962 sourceK coefficient (s u) (t u)
    coefficient_scale (by norm_num [sourceK]) exact_map_coefficients_have_nonzero_k_and_c1.1 (scaled_cubic u)
  change -((preimage u).x)^2+((preimage u).y)^2=
    1+coefficient*((preimage u).x)^2*((preimage u).y)^2 at h
  unfold Group.OnCurve
  linear_combination h

theorem inverse_constraints (u : F) :
    denominator u*(denominator u)⁻¹=1-zero u ∧ denominator u*zero u=0 ∧ (denominator u)⁻¹*zero u=0 :=
  BalanceMapInverse698.constraints (denominator u)

theorem represented_exists (u : F) : ∃ point : curve.Point,
    ConcreteCofactorModel01.model.coordinates point=eight u ∧ Scalar.order • point=0 :=
  ConcreteCofactorModel01.cofactor_image_annihilated (preimage u) (twice u) (four u) (eight u)
    (preimage_on_curve u) rfl rfl rfl

noncomputable def represented (u : F) : curve.Point := Classical.choose (represented_exists u)

theorem represented_coordinates (u : F) : ConcreteCofactorModel01.model.coordinates (represented u)=eight u :=
  (Classical.choose_spec (represented_exists u)).1

theorem represented_subgroup (u : F) : Scalar.order • represented u=0 :=
  (Classical.choose_spec (represented_exists u)).2
end ShielddSecurity.BalanceMapPoint701

set_option pp.all true in
#check @ShielddSecurity.BalanceMapPoint701.coefficient_scale
#print axioms ShielddSecurity.BalanceMapPoint701.coefficient_scale

set_option pp.all true in
#check @ShielddSecurity.BalanceMapPoint701.first_equation
#print axioms ShielddSecurity.BalanceMapPoint701.first_equation

set_option pp.all true in
#check @ShielddSecurity.BalanceMapPoint701.scaled_cubic
#print axioms ShielddSecurity.BalanceMapPoint701.scaled_cubic

set_option pp.all true in
#check @ShielddSecurity.BalanceMapPoint701.preimage_on_curve
#print axioms ShielddSecurity.BalanceMapPoint701.preimage_on_curve

set_option pp.all true in
#check @ShielddSecurity.BalanceMapPoint701.inverse_constraints
#print axioms ShielddSecurity.BalanceMapPoint701.inverse_constraints

set_option pp.all true in
#check @ShielddSecurity.BalanceMapPoint701.represented_exists
#print axioms ShielddSecurity.BalanceMapPoint701.represented_exists

set_option pp.all true in
#check @ShielddSecurity.BalanceMapPoint701.represented_coordinates
#print axioms ShielddSecurity.BalanceMapPoint701.represented_coordinates

set_option pp.all true in
#check @ShielddSecurity.BalanceMapPoint701.represented_subgroup
#print axioms ShielddSecurity.BalanceMapPoint701.represented_subgroup
