import ShielddSecurity.Compiler

set_option maxHeartbeats 500000

namespace ShielddSecurity.Group

variable {F : Type} [Field F]

structure Point (F : Type) where
  x : F
  y : F

def OnCurve (d : F) (point : Point F) : Prop :=
  point.y * point.y - point.x * point.x =
    1 + d * point.x * point.x * point.y * point.y

/-- The scalar-field instance must discharge this exact nonsquare property and
the square root of -1. They are algebraic parameters here, not assumptions that
addition is complete, nor claims for every extension field of characteristic p. -/
def NoUnitSquare (d : F) : Prop := ∀ value : F, d * value * value ≠ 1

def cross (left right : Point F) : F :=
  left.x * right.y + left.y * right.x

def diagonal (left right : Point F) : F :=
  left.y * right.y + left.x * right.x

def delta (d : F) (left right : Point F) : F :=
  d * left.x * right.x * left.y * right.y

theorem minus_factor (d : F) (left right : Point F)
    (hl : OnCurve d left) (hr : OnCurve d right)
    (zero : 1 - delta d left right = 0) :
    (left.x * right.y - right.x * left.y) *
      (left.y * right.y + left.x * right.x) = 0 := by
  calc
    _ = (1 - delta d left right) * (left.x * left.y - right.x * right.y) +
        left.x * left.y * (right.y * right.y - right.x * right.x -
          (1 + d * right.x * right.x * right.y * right.y)) -
        right.x * right.y * (left.y * left.y - left.x * left.x -
          (1 + d * left.x * left.x * left.y * left.y)) := by unfold delta; ring
    _ = 0 := by rw [zero, hl, hr]; ring

theorem plus_factor (d : F) (left right : Point F)
    (hl : OnCurve d left) (hr : OnCurve d right)
    (zero : 1 + delta d left right = 0) :
    (left.x * right.y + right.x * left.y) *
      (left.y * right.y - left.x * right.x) = 0 := by
  calc
    _ = (1 + delta d left right) * (left.x * left.y + right.x * right.y) +
        left.x * left.y * (right.y * right.y - right.x * right.x -
          (1 + d * right.x * right.x * right.y * right.y)) +
        right.x * right.y * (left.y * left.y - left.x * left.x -
          (1 + d * left.x * left.x * left.y * left.y)) := by unfold delta; ring
    _ = 0 := by rw [zero, hl, hr]; ring

/-- Derive the missing division precondition from curve equations and the field
parameters. A quotient row alone permits arbitrary 0/0; it is never enough. -/
theorem denominators_nonzero (d imaginary : F) (nonSquare : NoUnitSquare d)
    (imaginarySquare : imaginary * imaginary = -1) (left right : Point F)
    (hl : OnCurve d left) (hr : OnCurve d right) :
    1 + delta d left right ≠ 0 ∧ 1 - delta d left right ≠ 0 := by
  constructor
  · intro zero
    have negative : delta d left right = -1 := eq_neg_of_add_eq_zero_right zero
    rcases mul_eq_zero.mp (plus_factor d left right hl hr zero) with same | same
    · have opposite : right.x * left.y = -(left.x * right.y) :=
        eq_neg_of_add_eq_zero_right same
      apply nonSquare (left.x * right.y)
      calc
        _ = -(d * (left.x * right.y) * (right.x * left.y)) := by rw [opposite]; ring
        _ = -delta d left right := by unfold delta; ring
        _ = 1 := by rw [negative]; ring
    · have equal : left.y * right.y = left.x * right.x := sub_eq_zero.mp same
      apply nonSquare (imaginary * (left.x * right.x))
      calc
        _ = (imaginary * imaginary) * (d * (left.x * right.x) * (left.x * right.x)) := by ring
        _ = -(d * (left.x * right.x) * (left.y * right.y)) := by rw [imaginarySquare, equal]; ring
        _ = -delta d left right := by unfold delta; ring
        _ = 1 := by rw [negative]; ring
  · intro zero
    have positive : delta d left right = 1 := (sub_eq_zero.mp zero).symm
    rcases mul_eq_zero.mp (minus_factor d left right hl hr zero) with same | same
    · have equal : left.x * right.y = right.x * left.y := sub_eq_zero.mp same
      apply nonSquare (left.x * right.y)
      calc
        _ = d * (left.x * right.y) * (right.x * left.y) :=
          congrArg (fun value : F => d * (left.x * right.y) * value) equal
        _ = delta d left right := by unfold delta; ring
        _ = 1 := positive
    · have opposite : left.y * right.y = -(left.x * right.x) :=
        eq_neg_of_add_eq_zero_left same
      apply nonSquare (imaginary * (left.x * right.x))
      calc
        _ = (imaginary * imaginary) * (d * (left.x * right.x) * (left.x * right.x)) := by ring
        _ = d * (left.x * right.x) * (left.y * right.y) := by rw [imaginarySquare, opposite]; ring
        _ = delta d left right := by unfold delta; ring
        _ = 1 := positive

def affineAdd (d : F) (left right : Point F) : Point F :=
  ⟨cross left right / (1 + delta d left right),
   diagonal left right / (1 - delta d left right)⟩

theorem quotient_sound (numerator denominator quotient : F)
    (nonzero : denominator ≠ 0) (equation : quotient * denominator = numerator) :
    quotient = numerator / denominator := (eq_div_iff nonzero).mpr equation

theorem affine_rows_sound (d imaginary : F) (nonSquare : NoUnitSquare d)
    (imaginarySquare : imaginary * imaginary = -1) (left right output : Point F)
    (hl : OnCurve d left) (hr : OnCurve d right)
    (xRow : output.x * (1 + delta d left right) = cross left right)
    (yRow : output.y * (1 - delta d left right) = diagonal left right) :
    output = affineAdd d left right := by
  have denominators := denominators_nonzero d imaginary nonSquare imaginarySquare left right hl hr
  have hx := quotient_sound _ _ _ denominators.1 xRow
  have hy := quotient_sound _ _ _ denominators.2 yRow
  cases output
  simp_all only [affineAdd, Point.mk.injEq]

#print axioms denominators_nonzero
#print axioms quotient_sound
#print axioms affine_rows_sound

end ShielddSecurity.Group
