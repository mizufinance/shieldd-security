import ShielddSecurity.NativeEncryptionFixedArithmetic
import ShielddSecurity.NativeAssetMap

set_option maxHeartbeats 250000
set_option maxRecDepth 2048

namespace ShielddSecurity.NativeEncryptionInitializationSquares

variable {F : Type} [Field F] [DecidableEq F] [CharP F Scalar.modulus]

theorem polynomial_certificate (expression expected : Int)
    (certificate : expression % (Scalar.modulus : Int) = expected) :
    (expression : F) = (expected : F) := by
  have reduced := Compiler.coefficient_mod (F := F) (p := Scalar.modulus) expression
  rw [certificate] at reduced
  exact reduced.symm

/-- The map's rational x-square and y depend only on the selected root's
square. A normalized root's sign does not need to be chosen in a certificate.
The two inverse products are small arithmetic checks in each fixed instance. -/
theorem rational_squares (s t square inversePlus inverseSquare : F)
    (rootSquare : t * t = square)
    (plusUnit : (s + 1) * inversePlus = 1)
    (squareUnit : square * inverseSquare = 1) :
    (Elligator.rationalPoint s t).x * (Elligator.rationalPoint s t).x =
        s * s * inverseSquare ∧
      (Elligator.rationalPoint s t).y = (s - 1) * inversePlus := by
  have unit : ((s + 1) * t) * (inversePlus * t * inverseSquare) = 1 := by
    calc
      _ = ((s + 1) * inversePlus) * ((t * t) * inverseSquare) := by ring
      _ = 1 := by rw [plusUnit, rootSquare, squareUnit]; ring
  have nonzero : (s + 1) * t ≠ 0 := by
    intro zero
    rw [zero, zero_mul] at unit
    exact zero_ne_one unit
  have inverse : ((s + 1) * t)⁻¹ = inversePlus * t * inverseSquare :=
    inv_eq_of_mul_eq_one_right unit
  simp only [Elligator.rationalPoint, if_neg nonzero]
  rw [inverse]
  constructor
  · calc
      _ = (s * s * inverseSquare) * ((t * t) * inverseSquare) *
          ((s + 1) * inversePlus) * ((s + 1) * inversePlus) := by ring
      _ = s * s * inverseSquare := by rw [rootSquare, squareUnit, plusUnit]; ring
  · calc
      _ = (s - 1) * inversePlus * ((t * t) * inverseSquare) := by ring
      _ = (s - 1) * inversePlus := by rw [rootSquare, squareUnit]; ring

/-- One actual native doubling, retaining only x-square and y. The inverse
product is checked independently; neither an output point nor nonidentity
of the doubling is an argument. -/
theorem double_squares (d : F) (point : Group.Point F) (a b inverse : F)
    (xSquare : point.x * point.x = a) (yValue : point.y = b)
    (inverseUnit : ((1 + d * a * b * b) * (1 - d * a * b * b)) * inverse = 1) :
    let next := GroupFixedWindows.nativeAdd d point point
    next.x * next.x =
        (2 * b * (1 - d * a * b * b) * inverse) *
          (2 * b * (1 - d * a * b * b) * inverse) * a ∧
      next.y = (b * b + a) * (1 + d * a * b * b) * inverse := by
  have delta : Group.delta d point point = d * a * b * b := by
    calc
      _ = d * (point.x * point.x) * b * b := by rw [Group.delta, yValue]; ring
      _ = _ := by rw [xSquare]
  have inverseValue : ((1 + d * a * b * b) * (1 - d * a * b * b))⁻¹ = inverse :=
    inv_eq_of_mul_eq_one_right inverseUnit
  dsimp only
  simp only [GroupFixedWindows.nativeAdd, delta, inverseValue, Group.cross, Group.diagonal]
  constructor
  · calc
      _ = (2 * b * (1 - d * a * b * b) * inverse) *
          (2 * b * (1 - d * a * b * b) * inverse) * (point.x * point.x) := by
            rw [yValue]; ring
      _ = _ := by rw [xSquare]
  · rw [yValue, xSquare]

/-- Three native doubles use three local inverse and arithmetic checks. The
last square is a fixed nonzero integer in the generated instance; the desired
native output and its subgroup/nonidentity properties are not premises. -/
theorem three_double_nonzero (d : F) (point : Group.Point F)
    (a b : Fin 4 → F) (inverse : Fin 3 → F)
    (initial : point.x * point.x = a 0 ∧ point.y = b 0)
    (steps : ∀ index : Fin 3,
      let next : Fin 4 := ⟨index.val + 1, by omega⟩
      ((1 + d * a index.castSucc * b index.castSucc * b index.castSucc) *
        (1 - d * a index.castSucc * b index.castSucc * b index.castSucc)) * inverse index = 1 ∧
      (2 * b index.castSucc * (1 - d * a index.castSucc * b index.castSucc * b index.castSucc) * inverse index) *
        (2 * b index.castSucc * (1 - d * a index.castSucc * b index.castSucc * b index.castSucc) * inverse index) *
          a index.castSucc = a next ∧
      (b index.castSucc * b index.castSucc + a index.castSucc) *
        (1 + d * a index.castSucc * b index.castSucc * b index.castSucc) *
          inverse index = b next)
    (lastNonzero : a 3 ≠ 0) :
    (GroupNativeCofactor.nativeEight d point).x ≠ 0 := by
  let twice := GroupFixedWindows.nativeAdd d point point
  let four := GroupFixedWindows.nativeAdd d twice twice
  let eight := GroupFixedWindows.nativeAdd d four four
  have first := double_squares d point (a 0) (b 0) (inverse 0)
    initial.1 initial.2 (steps 0).1
  have firstSquare : twice.x * twice.x = a 1 := first.1.trans (steps 0).2.1
  have firstY : twice.y = b 1 := first.2.trans (steps 0).2.2
  have second := double_squares d twice (a 1) (b 1) (inverse 1)
    firstSquare firstY (steps 1).1
  have secondSquare : four.x * four.x = a 2 := second.1.trans (steps 1).2.1
  have secondY : four.y = b 2 := second.2.trans (steps 1).2.2
  have third := double_squares d four (a 2) (b 2) (inverse 2)
    secondSquare secondY (steps 2).1
  have thirdSquare : eight.x * eight.x = a 3 := third.1.trans (steps 2).2.1
  intro zero
  change eight.x = 0 at zero
  rw [zero, zero_mul] at thirdSquare
  exact lastNonzero thirdSquare.symm

set_option pp.all true in
#check @polynomial_certificate
#print axioms polynomial_certificate
set_option pp.all true in
#check @rational_squares
#print axioms rational_squares
set_option pp.all true in
#check @double_squares
#print axioms double_squares
set_option pp.all true in
#check @three_double_nonzero
#print axioms three_double_nonzero

end ShielddSecurity.NativeEncryptionInitializationSquares
