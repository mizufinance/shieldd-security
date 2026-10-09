import ShielddSecurity.NativeBalanceCommitment

set_option maxHeartbeats 150000
set_option maxRecDepth 2048

namespace ShielddSecurity.GroupSignedPoint

variable {F : Type} [Field F]

/-- The owned balance source writes x - 2*negative*x and retains y.
The Boolean comes from the preceding signed-magnitude constructor. -/
def signed (negative : Bool) (point : Group.Point F) : Group.Point F :=
  ⟨point.x - 2 * (if negative then 1 else 0) * point.x,point.y⟩

theorem signed_false (point : Group.Point F) : signed false point = point := by
  cases point
  simp only [signed,Bool.false_eq_true,if_false,mul_zero,zero_mul,sub_zero]

theorem signed_true (point : Group.Point F) :
    signed true point = ⟨-point.x,point.y⟩ := by
  apply congrArg₂ Group.Point.mk
  · change point.x - 2 * (1 : F) * point.x = -point.x
    ring
  · rfl

/-- Curve truth is inherited from the preceding constructed unsigned point;
the sign product is calculated, rather than a desired coordinate premise. -/
theorem signed_on_curve (d : F) (negative : Bool) (point : Group.Point F)
    (curved : Group.OnCurve d point) : Group.OnCurve d (signed negative point) := by
  cases negative with
  | false => rw [signed_false]; exact curved
  | true =>
    rw [signed_true]
    simpa only [Group.OnCurve,mul_neg,neg_mul,neg_neg] using curved

theorem signed_native {J : Type} [AddCommGroup J] [DecidableEq F]
    [CharP F Scalar.modulus] (d imaginary : F)
    (model : Group.StandardCurveModel J d) (nonSquare : Group.NoUnitSquare d)
    (imaginarySquare : imaginary*imaginary = -1) (negative : Bool) (point : J) :
    signed negative (model.coordinates point) =
      model.coordinates (if negative then -point else point) := by
  cases negative with
  | false => simpa only [Bool.false_eq_true,if_false] using signed_false (model.coordinates point)
  | true =>
    simp only [if_true,signed_true]
    exact (NativeBalanceCommitment.coordinates_neg d imaginary model nonSquare imaginarySquare point).symm

/-- Final affine addition agrees with the same signed group value and the
independently constructed blinding endpoint, including zero blinding. -/
theorem final_native {J : Type} [AddCommGroup J] [DecidableEq F]
    [CharP F Scalar.modulus] (d imaginary : F)
    (model : Group.StandardCurveModel J d) (nonSquare : Group.NoUnitSquare d)
    (imaginarySquare : imaginary*imaginary = -1) (negative : Bool) (point blinding : J) :
    Group.affineAdd d (signed negative (model.coordinates point)) (model.coordinates blinding) =
      model.coordinates ((if negative then -point else point) + blinding) := by
  rw [signed_native d imaginary model nonSquare imaginarySquare negative point]
  exact (model.addition _ _).symm

set_option pp.all true in
#check @signed_false
#print axioms signed_false
set_option pp.all true in
#check @signed_true
#print axioms signed_true
set_option pp.all true in
#check @signed_on_curve
#print axioms signed_on_curve
set_option pp.all true in
#check @signed_native
#print axioms signed_native
set_option pp.all true in
#check @final_native
#print axioms final_native

end ShielddSecurity.GroupSignedPoint
