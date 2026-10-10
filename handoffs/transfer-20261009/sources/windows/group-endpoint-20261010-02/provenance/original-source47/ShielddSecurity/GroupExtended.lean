-- GENERATED SOURCE-only by header_recipe47.py; all fresh audits UNRUN.
import ShielddSecurity.GroupWindows

set_option maxHeartbeats 300000

namespace ShielddSecurity.GroupExtended

variable {F : Type} [Field F]

/-- The owned native implementation at shieldd.lock
844389ee069e1fb2e576708842d0b389b4d9a44a is
crates/crypto/circuits/src/group.rs (SHA256
ca75207acfd6bcb794f9f54b8ab3f52b236478f6b10761d459747dcbb9155971).
The coordinate equations below model its local Extended operations. This file
does not implement or prove the upstream field, codec, scalar-bit loop, or
native/circuit source correspondence contracts. -/
structure Extended (F : Type) where
  x : F
  y : F
  z : F
  t : F

/-- T is xyZ, not XY. Nonzero Z is proved at every operation before native
normalization uses its inverse. Curve membership is a separate input contract. -/
def Represents (value : Extended F) (point : Group.Point F) : Prop :=
  value.z ≠ 0 ∧ value.x = point.x * value.z ∧
    value.y = point.y * value.z ∧ value.t = point.x * point.y * value.z

def affine (point : Group.Point F) : Extended F :=
  ⟨point.x, point.y, 1, point.x * point.y⟩

/-- Shared final four products, in the native assignment order X,Y,Z,T. -/
def finish (e f g h : F) : Extended F := ⟨e * f, g * h, f * g, e * h⟩

def add (d : F) (left right : Extended F) : Extended F :=
  let a := (left.y - left.x) * (right.y - right.x)
  let b := (left.y + left.x) * (right.y + right.x)
  let c := left.t * right.t * (d + d)
  let dd := left.z * (right.z + right.z)
  let e := b - a
  let f := dd - c
  let g := dd + c
  let h := b + a
  finish e f g h

def double (value : Extended F) : Extended F :=
  let a := value.x * value.x
  let b := value.y * value.y
  let zz := value.z * value.z
  let c := zz + zz
  let d := -a
  let sum := value.x + value.y
  let e := sum * sum - a - b
  let g := d + b
  let f := g - c
  let h := d - b
  finish e f g h

def normalize (value : Extended F) : Group.Point F :=
  ⟨value.x * value.z⁻¹, value.y * value.z⁻¹⟩

def doubleXDenominator (point : Group.Point F) : F :=
  point.y * point.y - point.x * point.x

def doubleYDenominator (point : Group.Point F) : F :=
  2 - doubleXDenominator point

def doubleNumerator (point : Group.Point F) : F :=
  (point.x + point.y) * (point.x + point.y) - point.x * point.x - point.y * point.y

/-- The existing circuit's optimized affine double, before its curve equation
identifies these denominators with the complete Edwards denominators. -/
def optimizedDouble (point : Group.Point F) : Group.Point F :=
  ⟨doubleNumerator point / doubleXDenominator point,
   Group.diagonal point point / doubleYDenominator point⟩

theorem affine_represents (point : Group.Point F) : Represents (affine point) point := by
  simp [Represents, affine]

theorem normalize_represents (value : Extended F) (point : Group.Point F)
    (represented : Represents value point) : normalize value = point := by
  have hx : (normalize value).x = point.x := by
    change value.x * value.z⁻¹ = point.x
    rw [represented.2.1]
    simp only [mul_assoc, mul_inv_cancel₀ represented.1, mul_one]
  have hy : (normalize value).y = point.y := by
    change value.y * value.z⁻¹ = point.y
    rw [represented.2.2.1]
    simp only [mul_assoc, mul_inv_cancel₀ represented.1, mul_one]
  cases point
  exact congrArg₂ Group.Point.mk hx hy

/-- Small reusable invariant lemma. Its premises are the arithmetic quotient
equations and their nonzero denominators, never an output representation. -/
theorem finish_represents (e f g h : F) (point : Group.Point F)
    (fNonzero : f ≠ 0) (gNonzero : g ≠ 0)
    (xRow : point.x * g = e) (yRow : point.y * f = h) :
    Represents (finish e f g h) point := by
  refine ⟨mul_ne_zero fNonzero gNonzero, ?_, ?_, ?_⟩
  · change e * f = point.x * (f * g)
    calc
      _ = (point.x * g) * f := by rw [xRow]
      _ = point.x * (f * g) := by ring
  · change g * h = point.y * (f * g)
    calc
      _ = g * (point.y * f) := by rw [yRow]
      _ = point.y * (f * g) := by ring
  · change e * h = point.x * point.y * (f * g)
    calc
      _ = (point.x * g) * (point.y * f) := by rw [xRow, yRow]
      _ = point.x * point.y * (f * g) := by ring

/-- Factor the four native add intermediates separately. The polynomial walk
stops before multiplying E/F/G/H, keeping normalization small and reusable. -/
theorem add_factors (d : F) (left right : Extended F) (p q : Group.Point F)
    (leftRep : Represents left p) (rightRep : Represents right q) :
    add d left right =
      finish ((2 * (left.z * right.z)) * Group.cross p q)
        ((2 * (left.z * right.z)) * (1 - Group.delta d p q))
        ((2 * (left.z * right.z)) * (1 + Group.delta d p q))
        ((2 * (left.z * right.z)) * Group.diagonal p q) := by
  dsimp only [add]
  rw [leftRep.2.1, leftRep.2.2.1, leftRep.2.2.2,
      rightRep.2.1, rightRep.2.2.1, rightRep.2.2.2]
  congr 1 <;> dsimp only [Group.cross, Group.delta, Group.diagonal] <;> ring

/-- Doubling uses two negative factors F/H; retaining both signs is essential
to obtain the optimized y denominator 2-(y²-x²). -/
theorem double_factors (value : Extended F) (point : Group.Point F)
    (represented : Represents value point) :
    double value = finish ((value.z * value.z) * doubleNumerator point)
      (-((value.z * value.z) * doubleYDenominator point))
      ((value.z * value.z) * doubleXDenominator point)
      (-((value.z * value.z) * Group.diagonal point point)) := by
  dsimp only [double]
  rw [represented.2.1, represented.2.2.1]
  congr 1 <;>
    dsimp only [doubleNumerator, doubleXDenominator, doubleYDenominator, Group.diagonal] <;>
    ring

theorem optimized_denominators_nonzero (d imaginary : F)
    (nonSquare : Group.NoUnitSquare d) (imaginarySquare : imaginary * imaginary = -1)
    (point : Group.Point F) (valid : Group.OnCurve d point) :
    doubleXDenominator point ≠ 0 ∧ doubleYDenominator point ≠ 0 := by
  have denominators := Group.denominators_nonzero d imaginary nonSquare imaginarySquare
    point point valid valid
  have plus : doubleXDenominator point = 1 + Group.delta d point point := valid
  have minus : doubleYDenominator point = 1 - Group.delta d point point := by
    dsimp only [doubleYDenominator]
    rw [plus]
    ring
  exact ⟨by rw [plus]; exact denominators.1, by rw [minus]; exact denominators.2⟩

theorem optimized_double_sound (d imaginary : F)
    (nonSquare : Group.NoUnitSquare d) (imaginarySquare : imaginary * imaginary = -1)
    (point : Group.Point F) (valid : Group.OnCurve d point) :
    optimizedDouble point = Group.affineAdd d point point ∧
      Group.OnCurve d (optimizedDouble point) := by
  have denominators := optimized_denominators_nonzero d imaginary nonSquare imaginarySquare
    point valid
  apply Group.double_rows_sound d imaginary nonSquare imaginarySquare point
    (optimizedDouble point) valid
  · change (doubleNumerator point / doubleXDenominator point) *
      doubleXDenominator point = doubleNumerator point
    exact div_mul_cancel₀ _ denominators.1
  · change (Group.diagonal point point / doubleYDenominator point) *
      doubleYDenominator point = Group.diagonal point point
    exact div_mul_cancel₀ _ denominators.2

theorem add_represents (d imaginary : F)
    (nonSquare : Group.NoUnitSquare d) (imaginarySquare : imaginary * imaginary = -1)
    (two : (2 : F) ≠ 0) (left right : Extended F) (p q : Group.Point F)
    (leftRep : Represents left p) (rightRep : Represents right q)
    (pValid : Group.OnCurve d p) (qValid : Group.OnCurve d q) :
    Represents (add d left right) (Group.affineAdd d p q) := by
  have denominators := Group.denominators_nonzero d imaginary nonSquare imaginarySquare
    p q pValid qValid
  have scaleNonzero : 2 * (left.z * right.z) ≠ 0 :=
    mul_ne_zero two (mul_ne_zero leftRep.1 rightRep.1)
  have xRow : (Group.affineAdd d p q).x * (1 + Group.delta d p q) =
      Group.cross p q := by
    exact div_mul_cancel₀ _ denominators.1
  have yRow : (Group.affineAdd d p q).y * (1 - Group.delta d p q) =
      Group.diagonal p q := by
    exact div_mul_cancel₀ _ denominators.2
  rw [add_factors d left right p q leftRep rightRep]
  apply finish_represents
  · exact mul_ne_zero scaleNonzero denominators.2
  · exact mul_ne_zero scaleNonzero denominators.1
  · calc
      _ = (2 * (left.z * right.z)) *
          ((Group.affineAdd d p q).x * (1 + Group.delta d p q)) := by ring
      _ = _ := by rw [xRow]
  · calc
      _ = (2 * (left.z * right.z)) *
          ((Group.affineAdd d p q).y * (1 - Group.delta d p q)) := by ring
      _ = _ := by rw [yRow]

theorem double_represents_optimized (d imaginary : F)
    (nonSquare : Group.NoUnitSquare d) (imaginarySquare : imaginary * imaginary = -1)
    (value : Extended F) (point : Group.Point F)
    (represented : Represents value point) (valid : Group.OnCurve d point) :
    Represents (double value) (optimizedDouble point) := by
  have denominators := optimized_denominators_nonzero d imaginary nonSquare imaginarySquare
    point valid
  have scaleNonzero : value.z * value.z ≠ 0 := mul_ne_zero represented.1 represented.1
  have xRow : (optimizedDouble point).x * doubleXDenominator point =
      doubleNumerator point := by
    exact div_mul_cancel₀ _ denominators.1
  have yRow : (optimizedDouble point).y * doubleYDenominator point =
      Group.diagonal point point := by
    exact div_mul_cancel₀ _ denominators.2
  rw [double_factors value point represented]
  apply finish_represents
  · exact neg_ne_zero.mpr (mul_ne_zero scaleNonzero denominators.2)
  · exact mul_ne_zero scaleNonzero denominators.1
  · calc
      _ = (value.z * value.z) *
          ((optimizedDouble point).x * doubleXDenominator point) := by ring
      _ = _ := by rw [xRow]
  · calc
      _ = -((value.z * value.z) *
          ((optimizedDouble point).y * doubleYDenominator point)) := by ring
      _ = _ := by rw [yRow]

/-- Preservation retains Z≠0 and the T coordinate as well as normalized x/y.
Output curve membership follows from the existing complete affine law. -/
theorem double_represents (d imaginary : F)
    (nonSquare : Group.NoUnitSquare d) (imaginarySquare : imaginary * imaginary = -1)
    (value : Extended F) (point : Group.Point F)
    (represented : Represents value point) (valid : Group.OnCurve d point) :
    Represents (double value) (Group.affineAdd d point point) ∧
      Group.OnCurve d (Group.affineAdd d point point) := by
  have sound := optimized_double_sound d imaginary nonSquare imaginarySquare point valid
  have output := double_represents_optimized d imaginary nonSquare imaginarySquare
    value point represented valid
  rw [sound.1] at output
  exact ⟨output, by rw [← sound.1]; exact sound.2⟩

theorem add_normalize (d imaginary : F)
    (nonSquare : Group.NoUnitSquare d) (imaginarySquare : imaginary * imaginary = -1)
    (two : (2 : F) ≠ 0) (left right : Extended F) (p q : Group.Point F)
    (leftRep : Represents left p) (rightRep : Represents right q)
    (pValid : Group.OnCurve d p) (qValid : Group.OnCurve d q) :
    normalize (add d left right) = Group.affineAdd d p q ∧
      Group.OnCurve d (Group.affineAdd d p q) := by
  have represented := add_represents d imaginary nonSquare imaginarySquare two
    left right p q leftRep rightRep pValid qValid
  have denominators := Group.denominators_nonzero d imaginary nonSquare imaginarySquare
    p q pValid qValid
  refine ⟨normalize_represents _ _ represented, ?_⟩
  apply Group.affine_rows_onCurve d imaginary nonSquare imaginarySquare p q
    (Group.affineAdd d p q) pValid qValid
  · exact div_mul_cancel₀ _ denominators.1
  · exact div_mul_cancel₀ _ denominators.2

theorem double_normalize (d imaginary : F)
    (nonSquare : Group.NoUnitSquare d) (imaginarySquare : imaginary * imaginary = -1)
    (value : Extended F) (point : Group.Point F)
    (represented : Represents value point) (valid : Group.OnCurve d point) :
    normalize (double value) = Group.affineAdd d point point ∧
      Group.OnCurve d (Group.affineAdd d point point) := by
  have output := double_represents d imaginary nonSquare imaginarySquare
    value point represented valid
  exact ⟨normalize_represents _ _ output.1, output.2⟩

set_option pp.all true in
#check @affine_represents
#print axioms affine_represents
set_option pp.all true in
#check @normalize_represents
#print axioms normalize_represents
set_option pp.all true in
#check @finish_represents
#print axioms finish_represents
set_option pp.all true in
#check @add_factors
#print axioms add_factors
set_option pp.all true in
#check @double_factors
#print axioms double_factors
set_option pp.all true in
#check @optimized_denominators_nonzero
#print axioms optimized_denominators_nonzero
set_option pp.all true in
#check @optimized_double_sound
#print axioms optimized_double_sound
set_option pp.all true in
#check @add_represents
#print axioms add_represents
set_option pp.all true in
#check @double_represents_optimized
#print axioms double_represents_optimized
set_option pp.all true in
#check @double_represents
#print axioms double_represents
set_option pp.all true in
#check @add_normalize
#print axioms add_normalize
set_option pp.all true in
#check @double_normalize
#print axioms double_normalize

end ShielddSecurity.GroupExtended

set_option pp.all true in
#check @ShielddSecurity.GroupExtended.Extended
#print axioms ShielddSecurity.GroupExtended.Extended
set_option pp.all true in
#check @ShielddSecurity.GroupExtended.Represents
#print axioms ShielddSecurity.GroupExtended.Represents
set_option pp.all true in
#check @ShielddSecurity.GroupExtended.affine
#print axioms ShielddSecurity.GroupExtended.affine
set_option pp.all true in
#check @ShielddSecurity.GroupExtended.finish
#print axioms ShielddSecurity.GroupExtended.finish
set_option pp.all true in
#check @ShielddSecurity.GroupExtended.add
#print axioms ShielddSecurity.GroupExtended.add
set_option pp.all true in
#check @ShielddSecurity.GroupExtended.double
#print axioms ShielddSecurity.GroupExtended.double
set_option pp.all true in
#check @ShielddSecurity.GroupExtended.normalize
#print axioms ShielddSecurity.GroupExtended.normalize
set_option pp.all true in
#check @ShielddSecurity.GroupExtended.doubleXDenominator
#print axioms ShielddSecurity.GroupExtended.doubleXDenominator
set_option pp.all true in
#check @ShielddSecurity.GroupExtended.doubleYDenominator
#print axioms ShielddSecurity.GroupExtended.doubleYDenominator
set_option pp.all true in
#check @ShielddSecurity.GroupExtended.doubleNumerator
#print axioms ShielddSecurity.GroupExtended.doubleNumerator
set_option pp.all true in
#check @ShielddSecurity.GroupExtended.optimizedDouble
#print axioms ShielddSecurity.GroupExtended.optimizedDouble
