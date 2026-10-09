import ShielddSecurity.ConcretePoleAddition01
import ShielddSecurity.EdwardsSecantRational01

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.ConcreteSecantAddition01
open ConcreteJubjubField01 ConcreteEdwardsParameters01 ConcreteWeierstrassPoint01
open EdwardsWeierstrassAlgebra01 EdwardsWeierstrassEquiv01
variable [DecidableEq F]

theorem regular_secant_image (left right : Edwards parameters)
    (leftX : left.val.x ≠ 0) (rightX : right.val.x ≠ 0)
    (differentY : left.val.y ≠ right.val.y)
    (nonzeroCross : Group.cross left.val right.val ≠ 0) :
    ConcreteWeierstrassPoint01.equivalence (EdwardsAdditionPilot01.addition parameters left right) =
      ConcreteWeierstrassPoint01.equivalence left + ConcreteWeierstrassPoint01.equivalence right := by
  let delta := Group.delta coefficient left.val right.val
  let diagonal := Group.diagonal left.val right.val
  let cross := Group.cross left.val right.val
  let M := 1 - delta - diagonal
  let P := 1 - delta + diagonal
  let N := right.val.x * (1 + left.val.y) * (1 - right.val.y) -
    left.val.x * (1 + right.val.y) * (1 - left.val.y)
  let H := (2 : F) * left.val.x * right.val.x * (left.val.y - right.val.y)
  let S := B * N / H
  let sum := EdwardsAdditionPilot01.addition parameters left right
  have den := Group.denominators_nonzero coefficient imaginary parameters.nonSquare
    parameters.imaginarySquare left.val right.val left.property right.property
  have sumX : sum.val.x ≠ 0 := div_ne_zero nonzeroCross den.1
  have sumNotOne := ConcreteTorsionAddition01.regular_minus sum sumX
  have nonzeroM : M ≠ 0 := by
    intro zero
    apply sumNotOne
    change diagonal / (1 - delta) = 1
    apply (div_eq_iff den.2).mpr
    change 1 - delta - diagonal = 0 at zero
    linear_combination -zero
  have nonzeroH : H ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero parameters.two leftX) rightX)
      (sub_ne_zero.mpr differentY)
  have minusLeft : 1 - left.val.y ≠ 0 :=
    fun zero => ConcreteTorsionAddition01.regular_minus left leftX (sub_eq_zero.mp zero).symm
  have minusRight : 1 - right.val.y ≠ 0 :=
    fun zero => ConcreteTorsionAddition01.regular_minus right rightX (sub_eq_zero.mp zero).symm
  have leftCurve := (equation_iff _ _).mp (EdwardsWeierstrassMap01.forward_on_curve
    coefficient A B left.val.x left.val.y leftX minusLeft
      (positive parameters) (negative parameters) left.property)
  have rightCurve := (equation_iff _ _).mp (EdwardsWeierstrassMap01.forward_on_curve
    coefficient A B right.val.x right.val.y rightX minusRight
      (positive parameters) (negative parameters) right.property)
  have differentX : forwardX B left.val.x left.val.y ≠ forwardX B right.val.x right.val.y :=
    fun same => differentY ((EdwardsTorsionAlgebra01.forward_x_eq_iff B
      left.val.x right.val.x left.val.y right.val.y parameters.two (nonzeroB parameters)
        minusLeft minusRight).mp same)
  have xValue : forwardX B sum.val.x sum.val.y = B * P / M :=
    EdwardsSecantRational01.cayley_quotient_x B (1 - delta) diagonal
      (cross / (1 + delta)) den.2 nonzeroM
  have yValue : forwardY B sum.val.x sum.val.y = B * B * (1 + delta) * P / (M * cross) :=
    EdwardsSecantRational01.cayley_quotient_y B cross (1 + delta) (1 - delta) diagonal
      nonzeroCross den.1 den.2 nonzeroM
  have polyX : ((1 + coefficient) * (P * (1 - left.val.y) * (1 - right.val.y) +
      2 * (1 - left.val.y * right.val.y) * M) +
      2 * (1 - coefficient) * M * (1 - left.val.y) * (1 - right.val.y)) * H ^ 2 +
      4 * N ^ 2 * M * (1 - left.val.y) * (1 - right.val.y) = 0 :=
    EdwardsSecantPolynomials01.secant_x_polynomial coefficient left.val.x right.val.x
      left.val.y right.val.y left.property right.property
  have normalizedX := EdwardsSecantRational01.normalized_x_row coefficient A B M P N H
    left.val.y right.val.y (oneAdd parameters) nonzeroM nonzeroH minusLeft minusRight
      parameters.parameterA parameters.parameterB polyX
  have polyY : (1 + delta) * P * H * (1 - left.val.y) * left.val.x -
      N * ((1 + left.val.y) * M - P * (1 - left.val.y)) * cross * left.val.x +
      (1 + left.val.y) * M * cross * H = 0 :=
    EdwardsSecantPolynomials01.secant_y_polynomial coefficient left.val.x right.val.x
      left.val.y right.val.y left.property right.property
  have normalizedY := EdwardsSecantRational01.normalized_y_row (1 + delta) P H left.val.y
    left.val.x N M cross nonzeroH minusLeft leftX nonzeroM nonzeroCross polyY
  have slopeRow : S * (forwardX B left.val.x left.val.y - forwardX B right.val.x right.val.y) =
      forwardY B left.val.x left.val.y - forwardY B right.val.x right.val.y :=
    EdwardsSecantRational01.secant_slope_row B left.val.x right.val.x left.val.y right.val.y
      parameters.two leftX rightX minusLeft minusRight (sub_ne_zero.mpr differentY)
  have xRow : forwardX B sum.val.x sum.val.y = S ^ 2 - A * B -
      forwardX B left.val.x left.val.y - forwardX B right.val.x right.val.y := by
    rw [xValue]
    dsimp only [S]
    unfold forwardX
    linear_combination B * normalizedX
  have yRow : forwardY B sum.val.x sum.val.y = S *
      (forwardX B left.val.x left.val.y - forwardX B sum.val.x sum.val.y) -
        forwardY B left.val.x left.val.y := by
    rw [yValue, xValue]
    dsimp only [S]
    unfold forwardX forwardY
    linear_combination B ^ 2 * normalizedY
  obtain ⟨sumCurve, equality⟩ := ConcretePointOperationRows01.secant_rows leftCurve rightCurve
    differentX slopeRow xRow yRow
  rw [ConcreteTorsionAddition01.regular_equivalence left leftX leftCurve,
    ConcreteTorsionAddition01.regular_equivalence right rightX rightCurve,
    ConcreteTorsionAddition01.regular_equivalence sum sumX sumCurve]
  exact equality.symm


set_option pp.all true in
#check @regular_secant_image
#print axioms regular_secant_image
end ShielddSecurity.ConcreteSecantAddition01
