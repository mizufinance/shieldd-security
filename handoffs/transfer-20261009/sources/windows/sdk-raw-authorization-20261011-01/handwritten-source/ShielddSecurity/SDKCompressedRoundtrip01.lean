import ShielddSecurity.SDKEncodingInjective01
import ShielddSecurity.SDKSignSelection01

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.SDKCompressedRoundtrip01
open ConcreteJubjubField01

theorem self_square (point : Group.Point F) (curve : Group.OnCurve coefficient point) :
    point.x ^ 2 = (point.y ^ 2 - 1) / (1 + coefficient * point.y ^ 2) := by
  have denominator : 1 + coefficient * point.y ^ 2 ≠ 0 := by
    simpa only [pow_two, mul_assoc] using SDKCompressedDecoder01.denominator_nonzero
      coefficient imaginary point.y coefficient_no_unit_square imaginary_square
  apply (eq_div_iff denominator).mpr
  dsimp only [Group.OnCurve] at curve
  linear_combination -curve

theorem self_decoded (point : Group.Point F) (curve : Group.OnCurve coefficient point) :
    SDKCompressedDecoder01.Decoded point.y (point.x.val % 2) point :=
  ⟨rfl, self_square point curve, rfl⟩

/-- For bytes encoded from a curve point, ZIP216's zero-root/sign-one failure
cannot occur, independently of which mathematical square root is supplied. -/
theorem root_guard (point : Group.Point F) (curve : Group.OnCurve coefficient point)
    (root : F) (squareRoot : root ^ 2 = (point.y ^ 2 - 1) / (1 + coefficient * point.y ^ 2)) :
    ¬(root = 0 ∧ point.x.val % 2 = 1) := by
  rintro ⟨zero, sign⟩
  have squares : point.x ^ 2 = root ^ 2 := (self_square point curve).trans squareRoot.symm
  simp only [zero, pow_two, mul_zero] at squares
  have xZero : point.x = 0 := (mul_eq_zero.mp squares).elim id id
  exact Nat.zero_ne_one (by simpa only [xZero, ZMod.val_zero, Nat.zero_mod] using sign)

theorem roundtrip (point : Group.Point F) (curve : Group.OnCurve coefficient point)
    (root : F) (squareRoot : root ^ 2 = (point.y ^ 2 - 1) / (1 + coefficient * point.y ^ 2)) :
    SDKSignSelection01.decodedPoint point.y root (point.x.val % 2) = point :=
  SDKEncodingInjective01.decoded_unique point _ curve
    (SDKSignSelection01.selected_decoded point.y root (point.x.val % 2)
      (Nat.mod_lt _ (by decide)) (root_guard point curve root squareRoot) squareRoot)

theorem encoded_roundtrip (point : Group.Point F) (curve : Group.OnCurve coefficient point)
    (root : F) (squareRoot : root ^ 2 = (point.y ^ 2 - 1) / (1 + coefficient * point.y ^ 2)) :
    SDKEncodingInjective01.encode (SDKSignSelection01.decodedPoint point.y root (point.x.val % 2)) =
      SDKEncodingInjective01.encode point := by
  rw [roundtrip point curve root squareRoot]

theorem selection_independent (point : Group.Point F) (curve : Group.OnCurve coefficient point)
    (left right : F)
    (leftSquare : left ^ 2 = (point.y ^ 2 - 1) / (1 + coefficient * point.y ^ 2))
    (rightSquare : right ^ 2 = (point.y ^ 2 - 1) / (1 + coefficient * point.y ^ 2)) :
    SDKSignSelection01.decodedPoint point.y left (point.x.val % 2) =
      SDKSignSelection01.decodedPoint point.y right (point.x.val % 2) :=
  (roundtrip point curve left leftSquare).trans (roundtrip point curve right rightSquare).symm

end ShielddSecurity.SDKCompressedRoundtrip01

set_option pp.all true in
#check @ShielddSecurity.SDKCompressedRoundtrip01.self_square
#print axioms ShielddSecurity.SDKCompressedRoundtrip01.self_square
set_option pp.all true in
#check @ShielddSecurity.SDKCompressedRoundtrip01.self_decoded
#print axioms ShielddSecurity.SDKCompressedRoundtrip01.self_decoded
set_option pp.all true in
#check @ShielddSecurity.SDKCompressedRoundtrip01.root_guard
#print axioms ShielddSecurity.SDKCompressedRoundtrip01.root_guard
set_option pp.all true in
#check @ShielddSecurity.SDKCompressedRoundtrip01.roundtrip
#print axioms ShielddSecurity.SDKCompressedRoundtrip01.roundtrip
set_option pp.all true in
#check @ShielddSecurity.SDKCompressedRoundtrip01.encoded_roundtrip
#print axioms ShielddSecurity.SDKCompressedRoundtrip01.encoded_roundtrip
set_option pp.all true in
#check @ShielddSecurity.SDKCompressedRoundtrip01.selection_independent
#print axioms ShielddSecurity.SDKCompressedRoundtrip01.selection_independent
