import ShielddSecurity.SDKSpendAuthCertificates01

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.SDKCompressedDecoder01

open ConcreteJubjubField01

theorem denominator_nonzero {K : Type} [Field K] (d imaginary y : K)
    (nonSquare : Group.NoUnitSquare d) (imaginarySquare : imaginary * imaginary = -1) :
    1 + d * y * y ≠ 0 := by
  intro zero
  apply nonSquare (imaginary * y)
  calc
    d * (imaginary * y) * (imaginary * y) = d * (imaginary * imaginary) * y * y := by ring
    _ = -(d * y * y) := by rw [imaginarySquare]; ring
    _ = 1 := by linear_combination -zero

theorem same_y_roots {K : Type} [Field K] (d : K) (left right : Group.Point K)
    (leftCurve : Group.OnCurve d left) (rightCurve : Group.OnCurve d right)
    (sameY : left.y = right.y) (denominator : 1 + d * right.y * right.y ≠ 0) :
    left.x = right.x ∨ left.x = -right.x := by
  have product : (1 + d * right.y * right.y) * (left.x ^ 2 - right.x ^ 2) = 0 := by
    dsimp [Group.OnCurve] at leftCurve rightCurve
    rw [sameY] at leftCurve
    linear_combination rightCurve - leftCurve
  have squares : left.x ^ 2 = right.x ^ 2 :=
    sub_eq_zero.mp ((mul_eq_zero.mp product).resolve_left denominator)
  exact sq_eq_sq_iff_eq_or_eq_neg.mp squares

theorem odd_neg_even (x : F) (odd : x.val % 2 = 1) : (-x).val % 2 = 0 := by
  have nonzero : x ≠ 0 := by intro zero; simp [zero] at odd
  letI : NeZero x := ⟨nonzero⟩
  rw [ZMod.val_neg_of_ne_zero]
  have bound := ZMod.val_lt x
  have primeOdd : Scalar.modulus % 2 = 1 := by decide +kernel
  omega

theorem sdk_x_value : SDKSpendAuthCertificates01.sdkBase.x.val = SDKSpendAuthCertificates01.sdkX := by
  rw [SDKSpendAuthCertificates01.sdk_base_coordinates]
  exact ZMod.val_natCast_of_lt SDKSpendAuthCertificates01.sdk_x_bound

theorem sdk_y_value : SDKSpendAuthCertificates01.sdkBase.y.val = SDKSpendAuthCertificates01.sdkY := by
  rw [SDKSpendAuthCertificates01.sdk_base_coordinates]
  exact ZMod.val_natCast_of_lt SDKSpendAuthCertificates01.sdk_y_bound

theorem sdk_unique (point : Group.Point F) (curve : Group.OnCurve coefficient point)
    (yValue : point.y.val = SDKSpendAuthCertificates01.sdkY) (sign : point.x.val % 2 = 1) :
    point = SDKSpendAuthCertificates01.sdkBase := by
  have sameY : point.y = SDKSpendAuthCertificates01.sdkBase.y := by
    apply ZMod.val_injective
    exact yValue.trans sdk_y_value.symm
  have denominator := denominator_nonzero coefficient imaginary
    SDKSpendAuthCertificates01.sdkBase.y coefficient_no_unit_square imaginary_square
  rcases same_y_roots coefficient point SDKSpendAuthCertificates01.sdkBase curve
    SDKSpendAuthCertificates01.sdkBase_on_curve sameY denominator with sameX | negativeX
  · have extensionality : ∀ (left right : Group.Point F),
        left.x = right.x → left.y = right.y → left = right := by
      intro left right hx hy
      cases left
      cases right
      congr 1
    exact extensionality point SDKSpendAuthCertificates01.sdkBase sameX sameY
  · have baseOdd : SDKSpendAuthCertificates01.sdkBase.x.val % 2 = 1 := by
      rw [sdk_x_value]
      exact SDKSpendAuthCertificates01.sdk_x_odd
    have even := odd_neg_even SDKSpendAuthCertificates01.sdkBase.x baseOdd
    rw [negativeX] at sign
    omega

/-- Algebraic contract of canonical field decode, sqrt and sign selection.
This is an explicit native-refinement obligation, not an assumed point identity. -/
def Decoded (y : F) (sign : Nat) (point : Group.Point F) : Prop :=
  point.y = y ∧ point.x ^ 2 = (y ^ 2 - 1) / (1 + coefficient * y ^ 2) ∧
    point.x.val % 2 = sign

theorem decoded_on_curve (y : F) (sign : Nat) (point : Group.Point F)
    (decoded : Decoded y sign point) : Group.OnCurve coefficient point := by
  rcases decoded with ⟨sameY, square, _⟩
  have denominator : 1 + coefficient * y ^ 2 ≠ 0 := by
    simpa only [pow_two, mul_assoc] using
      denominator_nonzero coefficient imaginary y coefficient_no_unit_square imaginary_square
  have equation := (eq_div_iff denominator).mp square
  dsimp [Group.OnCurve]
  rw [sameY]
  linear_combination -equation

theorem sdk_decoded_unique (point : Group.Point F)
    (decoded : Decoded (SDKSpendAuthCertificates01.sdkY : F) 1 point) :
    point = SDKSpendAuthCertificates01.sdkBase := by
  apply sdk_unique point (decoded_on_curve _ _ _ decoded)
  · rw [decoded.1]
    exact ZMod.val_natCast_of_lt SDKSpendAuthCertificates01.sdk_y_bound
  · exact decoded.2.2

end ShielddSecurity.SDKCompressedDecoder01


set_option pp.all true in
#check @ShielddSecurity.SDKCompressedDecoder01.denominator_nonzero
#print axioms ShielddSecurity.SDKCompressedDecoder01.denominator_nonzero
set_option pp.all true in
#check @ShielddSecurity.SDKCompressedDecoder01.same_y_roots
#print axioms ShielddSecurity.SDKCompressedDecoder01.same_y_roots
set_option pp.all true in
#check @ShielddSecurity.SDKCompressedDecoder01.odd_neg_even
#print axioms ShielddSecurity.SDKCompressedDecoder01.odd_neg_even
set_option pp.all true in
#check @ShielddSecurity.SDKCompressedDecoder01.sdk_x_value
#print axioms ShielddSecurity.SDKCompressedDecoder01.sdk_x_value
set_option pp.all true in
#check @ShielddSecurity.SDKCompressedDecoder01.sdk_y_value
#print axioms ShielddSecurity.SDKCompressedDecoder01.sdk_y_value
set_option pp.all true in
#check @ShielddSecurity.SDKCompressedDecoder01.sdk_unique
#print axioms ShielddSecurity.SDKCompressedDecoder01.sdk_unique
set_option pp.all true in
#check @ShielddSecurity.SDKCompressedDecoder01.Decoded
#print axioms ShielddSecurity.SDKCompressedDecoder01.Decoded
set_option pp.all true in
#check @ShielddSecurity.SDKCompressedDecoder01.decoded_on_curve
#print axioms ShielddSecurity.SDKCompressedDecoder01.decoded_on_curve
set_option pp.all true in
#check @ShielddSecurity.SDKCompressedDecoder01.sdk_decoded_unique
#print axioms ShielddSecurity.SDKCompressedDecoder01.sdk_decoded_unique
