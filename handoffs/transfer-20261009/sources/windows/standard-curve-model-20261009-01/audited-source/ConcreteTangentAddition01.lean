import ShielddSecurity.ConcreteSecantAddition01
import ShielddSecurity.EdwardsTangentRational01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcreteTangentAddition01
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
open EdwardsWeierstrassAlgebra01 EdwardsWeierstrassEquiv01
variable [DecidableEq F]

theorem regular_tangent_image (point : Edwards parameters) (pointX : point.val.x ≠ 0)
    (nonzeroCross : Group.cross point.val point.val ≠ 0) :
    ConcreteWeierstrassPoint01.equivalence (EdwardsAdditionPilot01.addition parameters point point) =
      ConcreteWeierstrassPoint01.equivalence point + ConcreteWeierstrassPoint01.equivalence point := by
  let delta := Group.delta coefficient point.val point.val
  let diagonal := Group.diagonal point.val point.val
  let cross := (2 : F) * point.val.x * point.val.y
  let M := 1 - delta - diagonal
  let P := 1 - delta + diagonal
  let K := (2 : F) + point.val.y - coefficient * point.val.x * point.val.x * point.val.y
  let H := (2 : F) * point.val.x
  let S := B * K / H
  let sum := EdwardsAdditionPilot01.addition parameters point point
  have crossValue : Group.cross point.val point.val = cross := by
    unfold Group.cross
    dsimp only [cross]
    ring
  have nonzeroC : cross ≠ 0 := by simpa only [crossValue] using nonzeroCross
  have den := Group.denominators_nonzero coefficient imaginary parameters.nonSquare
    parameters.imaginarySquare point.val point.val point.property point.property
  have sumX : sum.val.x ≠ 0 := div_ne_zero nonzeroCross den.1
  have nonzeroM : M ≠ 0 := by
    intro zero
    apply ConcreteTorsionAddition01.regular_minus sum sumX
    change diagonal / (1 - delta) = 1
    apply (div_eq_iff den.2).mpr
    change 1 - delta - diagonal = 0 at zero
    linear_combination -zero
  have nonzeroH : H ≠ 0 := mul_ne_zero parameters.two pointX
  have minus : 1 - point.val.y ≠ 0 :=
    fun zero => ConcreteTorsionAddition01.regular_minus point pointX (sub_eq_zero.mp zero).symm
  have plus : 1 + point.val.y ≠ 0 :=
    fun zero => ConcreteTorsionAddition01.regular_plus point pointX (eq_neg_of_add_eq_zero_right zero)
  have inputCurve := (equation_iff _ _).mp (EdwardsWeierstrassMap01.forward_on_curve
    coefficient A B point.val.x point.val.y pointX minus
      (positive parameters) (negative parameters) point.property)
  have nonzeroForwardY : forwardY B point.val.x point.val.y ≠ 0 := by
    unfold forwardY
    exact div_ne_zero (mul_ne_zero (mul_ne_zero (nonzeroB parameters) (nonzeroB parameters)) plus)
      (mul_ne_zero minus pointX)
  have xValue : forwardX B sum.val.x sum.val.y = B * P / M :=
    EdwardsSecantRational01.cayley_quotient_x B (1 - delta) diagonal
      (Group.cross point.val point.val / (1 + delta)) den.2 nonzeroM
  have yValue : forwardY B sum.val.x sum.val.y = B * B * (1 + delta) * P / (M * cross) := by
    change forwardY B (Group.cross point.val point.val / (1 + delta))
      (diagonal / (1 - delta)) = _
    rw [crossValue]
    exact EdwardsSecantRational01.cayley_quotient_y B cross (1 + delta) (1 - delta) diagonal
      nonzeroC den.1 den.2 nonzeroM
  have polyX : ((1 + coefficient) * (P * (1 - point.val.y) * (1 - point.val.y) +
      2 * (1 - point.val.y * point.val.y) * M) +
      2 * (1 - coefficient) * M * (1 - point.val.y) * (1 - point.val.y)) * H ^ 2 +
      4 * K ^ 2 * M * (1 - point.val.y) * (1 - point.val.y) = 0 := by
    have raw := EdwardsTangentPolynomials01.tangent_x_polynomial coefficient
      point.val.x point.val.y point.property
    dsimp only at raw
    dsimp only [M, P, delta, diagonal, K, H, Group.delta, Group.diagonal]
    linear_combination (1 - point.val.y) * raw
  have normalizedX := EdwardsSecantRational01.normalized_x_row coefficient A B M P K H
    point.val.y point.val.y (oneAdd parameters) nonzeroM nonzeroH minus minus
      parameters.parameterA parameters.parameterB polyX
  have polyY : (1 + delta) * P * H * (1 - point.val.y) * point.val.x -
      K * ((1 + point.val.y) * M - P * (1 - point.val.y)) * cross * point.val.x +
      (1 + point.val.y) * M * cross * H = 0 :=
    EdwardsTangentPolynomials01.tangent_y_polynomial coefficient point.val.x point.val.y point.property
  have normalizedY := EdwardsSecantRational01.normalized_y_row (1 + delta) P H point.val.y
    point.val.x K M cross nonzeroH minus pointX nonzeroM nonzeroC polyY
  have polySlope : 4 * K * (1 - point.val.y * point.val.y) + point.val.x ^ 2 *
      ((1 + coefficient) * (3 * (1 + point.val.y) ^ 2 + (1 - point.val.y) ^ 2) +
        4 * (1 - coefficient) * (1 - point.val.y * point.val.y)) = 0 :=
    EdwardsTangentPolynomials01.tangent_slope_polynomial coefficient point.val.x point.val.y point.property
  have normalizedSlope := EdwardsTangentRational01.normalized_tangent_slope coefficient A B
    point.val.x point.val.y K (oneAdd parameters) parameters.parameterA parameters.parameterB polySlope
  have slopeRow : S * (2 * forwardY B point.val.x point.val.y) =
      3 * forwardX B point.val.x point.val.y ^ 2 + 2 * (A * B) *
        forwardX B point.val.x point.val.y + B * B := by
    dsimp only [S, H]
    unfold forwardX forwardY
    field_simp [parameters.two, pointX, minus]
    linear_combination B ^ 2 * normalizedSlope
  have xRow : forwardX B sum.val.x sum.val.y = S ^ 2 - A * B -
      forwardX B point.val.x point.val.y - forwardX B point.val.x point.val.y := by
    rw [xValue]
    dsimp only [S]
    unfold forwardX
    linear_combination B * normalizedX
  have yRow : forwardY B sum.val.x sum.val.y = S *
      (forwardX B point.val.x point.val.y - forwardX B sum.val.x sum.val.y) -
        forwardY B point.val.x point.val.y := by
    rw [yValue, xValue]
    dsimp only [S]
    unfold forwardX forwardY
    linear_combination B ^ 2 * normalizedY
  obtain ⟨sumCurve, equality⟩ := ConcretePointOperationRows01.tangent_rows inputCurve
    (mul_ne_zero parameters.two nonzeroForwardY) slopeRow xRow yRow
  change ConcreteWeierstrassPoint01.equivalence sum = _
  simp only [ConcreteTorsionAddition01.regular_equivalence sum sumX sumCurve,
    ConcreteTorsionAddition01.regular_equivalence point pointX inputCurve]
  exact equality.symm


set_option pp.all true in
#check @regular_tangent_image
#print axioms regular_tangent_image
end ShielddSecurity.ConcreteTangentAddition01
