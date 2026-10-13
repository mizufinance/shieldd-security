import ShielddSecurity.TransferCommonwareMapCaller01
import Mathlib.Tactic.FieldSimp
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferJubjubDouble01
variable {F : Type} [Field F]

def sourceProjectiveDouble (u v z : F) : F × F × F :=
  let uu := u*u
  let vv := v*v
  let zz2 := 2*(z*z)
  let uv2 := (u+v)*(u+v)
  let sum := vv+uu
  let difference := vv-uu
  let j := zz2-difference
  ((uv2-sum)*j,sum*difference,difference*j)

def sourceNormalizedCoordinates (p : F × F × F) : F × F :=
  (p.1*(p.2.2)⁻¹,p.2.1*(p.2.2)⁻¹)

def sourceAffineSelfAdd (d x y : F) : F × F :=
  let xx := x*x
  let yy := y*y
  let dt := xx*yy*d
  let plus := 1+dt
  let minus := 1-dt
  let inverse := (plus*minus)⁻¹
  ((x*y+y*x)*minus*inverse,(yy+xx)*plus*inverse)

theorem homogeneous_curve_row_derives_the_actual_doubling_factors
    (d u v z : F) (zNonzero : z ≠ 0)
    (curve : v^2*z^2-u^2*z^2 = z^4+d*u^2*v^2) :
    v^2-u^2 = z^2*(1+d*(u*z⁻¹)^2*(v*z⁻¹)^2) ∧
    2*z^2-(v^2-u^2) = z^2*(1-d*(u*z⁻¹)^2*(v*z⁻¹)^2) := by
  have plus : v^2-u^2 = z^2*(1+d*(u*z⁻¹)^2*(v*z⁻¹)^2) := by
    apply mul_right_cancel₀ (pow_ne_zero 2 zNonzero)
    calc
      (v^2-u^2)*z^2 = z^4+d*u^2*v^2 := by
        calc
          _ = v^2*z^2-u^2*z^2 := by ring
          _ = _ := curve
      _ = (z^2*(1+d*(u*z⁻¹)^2*(v*z⁻¹)^2))*z^2 := by field_simp
  refine ⟨plus,?_⟩
  rw [plus]
  ring

theorem source_projective_double_normalization_is_the_actual_affine_self_add
    (d u v z : F) (zNonzero : z ≠ 0)
    (curve : v^2*z^2-u^2*z^2 = z^4+d*u^2*v^2)
    (plusNonzero : 1+d*(u*z⁻¹)^2*(v*z⁻¹)^2 ≠ 0)
    (minusNonzero : 1-d*(u*z⁻¹)^2*(v*z⁻¹)^2 ≠ 0) :
    sourceNormalizedCoordinates (sourceProjectiveDouble u v z) = sourceAffineSelfAdd d (u*z⁻¹) (v*z⁻¹) := by
  have factors := homogeneous_curve_row_derives_the_actual_doubling_factors d u v z zNonzero curve
  have differenceNonzero : v^2-u^2 ≠ 0 := by
    rw [factors.1]
    exact mul_ne_zero (pow_ne_zero 2 zNonzero) plusNonzero
  have jNonzero : 2*z^2-(v^2-u^2) ≠ 0 := by
    rw [factors.2]
    exact mul_ne_zero (pow_ne_zero 2 zNonzero) minusNonzero
  have denominatorNonzero : (1+(u*z⁻¹)^2*(v*z⁻¹)^2*d)*(1-(u*z⁻¹)^2*(v*z⁻¹)^2*d) ≠ 0 := by
    convert mul_ne_zero plusNonzero minusNonzero using 1
    ring
  have numerator : (u+v)^2-(v^2+u^2) = 2*u*v := by ring
  unfold sourceProjectiveDouble sourceNormalizedCoordinates sourceAffineSelfAdd
  dsimp only
  simp only [← pow_two,numerator]
  apply Prod.ext
  · dsimp only
    rw [factors.2,factors.1]
    field_simp
    ring
  · dsimp only
    rw [factors.2,factors.1]
    field_simp

theorem square_scaled_by_a_nonzero_square_derives_the_coefficient_square
    (d t : F) (nonzero : t ≠ 0) (square : IsSquare (d*t^2)) : IsSquare d := by
  obtain ⟨r, equation⟩ := square
  refine ⟨r*t⁻¹, ?_⟩
  apply mul_right_cancel₀ (pow_ne_zero 2 nonzero)
  calc
    d*t^2 = r*r := equation
    _ = ((r*t⁻¹)*(r*t⁻¹))*t^2 := by field_simp

theorem nonsquare_d_derives_the_actual_affine_double_denominators
    (d x y : F) (nonsquare : ¬ IsSquare d) (minusOneSquare : IsSquare (-1 : F)) :
    1+d*x^2*y^2 ≠ 0 ∧ 1-d*x^2*y^2 ≠ 0 := by
  have scaled : d*x^2*y^2 = d*(x*y)^2 := by ring
  constructor
  · intro zero
    have value : d*(x*y)^2 = -1 := by
      rw [← scaled]
      calc
        d*x^2*y^2 = (1+d*x^2*y^2)-1 := by ring
        _ = -1 := by rw [zero]; ring
    have productNonzero : x*y ≠ 0 := by
      intro productZero
      rw [productZero,zero_pow (by decide : 2 ≠ 0),mul_zero] at value
      exact neg_ne_zero.mpr one_ne_zero value.symm
    exact nonsquare (square_scaled_by_a_nonzero_square_derives_the_coefficient_square
      d (x*y) productNonzero (by rw [value]; exact minusOneSquare))
  · intro zero
    have value : d*(x*y)^2 = 1 := by rw [← scaled]; exact (sub_eq_zero.mp zero).symm
    have productNonzero : x*y ≠ 0 := by
      intro productZero
      rw [productZero,zero_pow (by decide : 2 ≠ 0),mul_zero] at value
      exact zero_ne_one value
    exact nonsquare (square_scaled_by_a_nonzero_square_derives_the_coefficient_square
      d (x*y) productNonzero (by rw [value]; exact ⟨1,by simp⟩))

theorem actual_projective_double_preserves_the_homogeneous_curve
    (d u v z : F) (curve : v^2*z^2-u^2*z^2 = z^4+d*u^2*v^2) :
    let p := sourceProjectiveDouble u v z
    p.2.1^2*p.2.2^2-p.1^2*p.2.2^2 = p.2.2^4+d*p.1^2*p.2.1^2 := by
  have residual : v^2*z^2-u^2*z^2-z^4-d*u^2*v^2 = 0 := by rw [curve]; ring
  have identity :
      ((v^2+u^2)*(v^2-u^2))^2*((v^2-u^2)*(2*z^2-(v^2-u^2)))^2 -
      ((2*u*v)*(2*z^2-(v^2-u^2)))^2*((v^2-u^2)*(2*z^2-(v^2-u^2)))^2 -
      ((v^2-u^2)*(2*z^2-(v^2-u^2)))^4 -
      d*((2*u*v)*(2*z^2-(v^2-u^2)))^2*((v^2+u^2)*(v^2-u^2))^2 =
      4*(v^2+u^2)^2*(v^2-u^2)^2*(2*z^2-(v^2-u^2))^2*
        (v^2*z^2-u^2*z^2-z^4-d*u^2*v^2) := by ring
  rw [residual,mul_zero] at identity
  have numerator : (u+v)^2-(v^2+u^2) = 2*u*v := by ring
  dsimp only [sourceProjectiveDouble]
  simp only [← pow_two,numerator]
  apply sub_eq_zero.mp
  convert identity using 1
  ring

theorem actual_projective_double_derives_nonzero_z_and_matching_affine_coordinates
    (d u v z : F) (zNonzero : z ≠ 0)
    (curve : v^2*z^2-u^2*z^2 = z^4+d*u^2*v^2)
    (nonsquare : ¬ IsSquare d) (minusOneSquare : IsSquare (-1 : F)) :
    (sourceProjectiveDouble u v z).2.2 ≠ 0 ∧
    sourceNormalizedCoordinates (sourceProjectiveDouble u v z) =
      sourceAffineSelfAdd d (u*z⁻¹) (v*z⁻¹) := by
  have denominators := nonsquare_d_derives_the_actual_affine_double_denominators
    d (u*z⁻¹) (v*z⁻¹) nonsquare minusOneSquare
  have factors := homogeneous_curve_row_derives_the_actual_doubling_factors d u v z zNonzero curve
  constructor
  · dsimp only [sourceProjectiveDouble]
    simp only [← pow_two]
    rw [factors.2,factors.1]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero 2 zNonzero) denominators.1)
      (mul_ne_zero (pow_ne_zero 2 zNonzero) denominators.2)
  · exact source_projective_double_normalization_is_the_actual_affine_self_add
      d u v z zNonzero curve denominators.1 denominators.2

def HomogeneousCurve (d : F) (p : F × F × F) : Prop :=
  p.2.1^2*p.2.2^2-p.1^2*p.2.2^2 = p.2.2^4+d*p.1^2*p.2.1^2

def sourceProjectiveSteps : Nat → F × F × F → F × F × F
  | 0, p => p
  | n+1, p =>
      let q := sourceProjectiveSteps n p
      sourceProjectiveDouble q.1 q.2.1 q.2.2

def sourceAffineSteps (d : F) : Nat → F × F → F × F
  | 0, p => p
  | n+1, p =>
      let q := sourceAffineSteps d n p
      sourceAffineSelfAdd d q.1 q.2

theorem symbolic_projective_steps_derive_all_curve_nonzero_and_affine_rows
    (d : F) (p : F × F × F) (curve : HomogeneousCurve d p) (zNonzero : p.2.2 ≠ 0)
    (nonsquare : ¬ IsSquare d) (minusOneSquare : IsSquare (-1 : F)) (n : Nat) :
    HomogeneousCurve d (sourceProjectiveSteps n p) ∧
    (sourceProjectiveSteps n p).2.2 ≠ 0 ∧
    sourceNormalizedCoordinates (sourceProjectiveSteps n p) =
      sourceAffineSteps d n (sourceNormalizedCoordinates p) := by
  induction n with
  | zero => exact ⟨curve,zNonzero,rfl⟩
  | succ n ih =>
    obtain ⟨currentCurve,currentNonzero,currentCoordinates⟩ := ih
    let q := sourceProjectiveSteps n p
    have derived := actual_projective_double_derives_nonzero_z_and_matching_affine_coordinates
      d q.1 q.2.1 q.2.2 currentNonzero currentCurve nonsquare minusOneSquare
    refine ⟨actual_projective_double_preserves_the_homogeneous_curve
      d q.1 q.2.1 q.2.2 currentCurve,derived.1,?_⟩
    change sourceNormalizedCoordinates (sourceProjectiveDouble q.1 q.2.1 q.2.2) =
      sourceAffineSelfAdd d
        (sourceAffineSteps d n (sourceNormalizedCoordinates p)).1
        (sourceAffineSteps d n (sourceNormalizedCoordinates p)).2
    rw [← currentCoordinates]
    exact derived.2

theorem actual_three_projective_doubles_match_three_affine_self_adds
    (d x y : F) (curve : y^2-x^2 = 1+d*x^2*y^2)
    (nonsquare : ¬ IsSquare d) (minusOneSquare : IsSquare (-1 : F)) :
    sourceNormalizedCoordinates (sourceProjectiveSteps 3 (x,y,1)) =
      sourceAffineSteps d 3 (x,y) := by
  have homogeneous : HomogeneousCurve d (x,y,1) := by
    simpa only [HomogeneousCurve,one_pow,mul_one] using curve
  have result := symbolic_projective_steps_derive_all_curve_nonzero_and_affine_rows
    d (x,y,1) homogeneous one_ne_zero nonsquare minusOneSquare 3
  simpa only [sourceNormalizedCoordinates,inv_one,mul_one] using result.2.2
set_option pp.all true in
#check @sourceProjectiveDouble
#print axioms sourceProjectiveDouble
set_option pp.all true in
#check @sourceNormalizedCoordinates
#print axioms sourceNormalizedCoordinates
set_option pp.all true in
#check @sourceAffineSelfAdd
#print axioms sourceAffineSelfAdd
set_option pp.all true in
#check @homogeneous_curve_row_derives_the_actual_doubling_factors
#print axioms homogeneous_curve_row_derives_the_actual_doubling_factors
set_option pp.all true in
#check @source_projective_double_normalization_is_the_actual_affine_self_add
#print axioms source_projective_double_normalization_is_the_actual_affine_self_add
set_option pp.all true in
#check @square_scaled_by_a_nonzero_square_derives_the_coefficient_square
#print axioms square_scaled_by_a_nonzero_square_derives_the_coefficient_square
set_option pp.all true in
#check @nonsquare_d_derives_the_actual_affine_double_denominators
#print axioms nonsquare_d_derives_the_actual_affine_double_denominators
set_option pp.all true in
#check @actual_projective_double_preserves_the_homogeneous_curve
#print axioms actual_projective_double_preserves_the_homogeneous_curve
set_option pp.all true in
#check @actual_projective_double_derives_nonzero_z_and_matching_affine_coordinates
#print axioms actual_projective_double_derives_nonzero_z_and_matching_affine_coordinates
set_option pp.all true in
#check @HomogeneousCurve
#print axioms HomogeneousCurve
set_option pp.all true in
#check @sourceProjectiveSteps
#print axioms sourceProjectiveSteps
set_option pp.all true in
#check @sourceAffineSteps
#print axioms sourceAffineSteps
set_option pp.all true in
#check @symbolic_projective_steps_derive_all_curve_nonzero_and_affine_rows
#print axioms symbolic_projective_steps_derive_all_curve_nonzero_and_affine_rows
set_option pp.all true in
#check @actual_three_projective_doubles_match_three_affine_self_adds
#print axioms actual_three_projective_doubles_match_three_affine_self_adds
end ShielddSecurity.TransferJubjubDouble01
