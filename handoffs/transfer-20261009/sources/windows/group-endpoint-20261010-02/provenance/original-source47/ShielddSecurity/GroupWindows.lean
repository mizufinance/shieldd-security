-- GENERATED SOURCE-only by header_recipe47.py; all fresh audits UNRUN.
import ShielddSecurity.Group

set_option maxHeartbeats 300000

namespace ShielddSecurity.Group

variable {F : Type} [Field F]

/-- Polynomial closure identity, before dividing by the two denominators.
The hypotheses are the input curve equations, not output curve membership. -/
theorem addition_closure_polynomial (d : F) (left right : Point F)
    (hl : OnCurve d left) (hr : OnCurve d right) :
    diagonal left right ^ 2 * (1 + delta d left right) ^ 2 -
      cross left right ^ 2 * (1 - delta d left right) ^ 2 -
      (1 - delta d left right ^ 2) ^ 2 -
      d * cross left right ^ 2 * diagonal left right ^ 2 = 0 := by
  calc
    _ = (left.y * left.y - left.x * left.x) *
          (right.y * right.y - right.x * right.x) *
          (1 + d ^ 2 * (left.x * left.x * left.y * left.y) *
            (right.x * right.x * right.y * right.y)) -
        d * ((left.x * left.x * left.y * left.y) *
          (right.y * right.y - right.x * right.x) ^ 2 +
          (right.x * right.x * right.y * right.y) *
          (left.y * left.y - left.x * left.x) ^ 2) -
        (1 - d ^ 2 * (left.x * left.x * left.y * left.y) *
          (right.x * right.x * right.y * right.y)) ^ 2 := by
            unfold cross diagonal delta
            ring
    _ = 0 := by rw [hl, hr]; ring

/-- Arbitrary quotient-row solutions remain on the curve. This supplies the
inductive invariant needed by window multiplication; it is not a subgroup or
scalar-multiplication theorem, nor a certificate for compiled runtime rows. -/
theorem affine_rows_onCurve (d imaginary : F) (nonSquare : NoUnitSquare d)
    (imaginarySquare : imaginary * imaginary = -1) (left right output : Point F)
    (hl : OnCurve d left) (hr : OnCurve d right)
    (xRow : output.x * (1 + delta d left right) = cross left right)
    (yRow : output.y * (1 - delta d left right) = diagonal left right) :
    OnCurve d output := by
  have denominators := denominators_nonzero d imaginary nonSquare imaginarySquare left right hl hr
  have closure := addition_closure_polynomial d left right hl hr
  rw [← xRow, ← yRow] at closure
  have factored : ((1 + delta d left right) ^ 2 * (1 - delta d left right) ^ 2) *
      (output.y * output.y - output.x * output.x -
        (1 + d * output.x * output.x * output.y * output.y)) = 0 := by
    calc
      _ = (output.y * (1 - delta d left right)) ^ 2 * (1 + delta d left right) ^ 2 -
          (output.x * (1 + delta d left right)) ^ 2 * (1 - delta d left right) ^ 2 -
          (1 - delta d left right ^ 2) ^ 2 -
          d * (output.x * (1 + delta d left right)) ^ 2 *
            (output.y * (1 - delta d left right)) ^ 2 := by ring
      _ = 0 := closure
  have nz : (1 + delta d left right) ^ 2 * (1 - delta d left right) ^ 2 ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ denominators.1) (pow_ne_zero _ denominators.2)
  exact sub_eq_zero.mp ((mul_eq_zero.mp factored).resolve_left nz)

def identityPoint : Point F := ⟨0, 1⟩

/-- The original subgroup constructor shares one inverse of the product of the
two addition denominators. Each premise is an arithmetic equation to discharge
from the actual source/row certificates; inverse correctness is not assumed from
the witness-generation closure. -/
theorem shared_inverse_rows (d inverse : F) (left right output : Point F)
    (inverseRow : ((1 + delta d left right) * (1 - delta d left right)) * inverse = 1)
    (xValue : output.x = cross left right * (1 - delta d left right) * inverse)
    (yValue : output.y = diagonal left right * (1 + delta d left right) * inverse) :
    output.x * (1 + delta d left right) = cross left right ∧
    output.y * (1 - delta d left right) = diagonal left right := by
  constructor
  · calc
      _ = cross left right * (((1 + delta d left right) *
          (1 - delta d left right)) * inverse) := by rw [xValue]; ring
      _ = cross left right := by rw [inverseRow]; ring
  · calc
      _ = diagonal left right * (((1 + delta d left right) *
          (1 - delta d left right)) * inverse) := by rw [yValue]; ring
      _ = diagonal left right := by rw [inverseRow]; ring

theorem shared_inverse_double_sound (d imaginary inverse : F)
    (nonSquare : NoUnitSquare d) (imaginarySquare : imaginary * imaginary = -1)
    (input output : Point F) (valid : OnCurve d input)
    (inverseRow : ((1 + delta d input input) * (1 - delta d input input)) * inverse = 1)
    (xValue : output.x = cross input input * (1 - delta d input input) * inverse)
    (yValue : output.y = diagonal input input * (1 + delta d input input) * inverse) :
    output = affineAdd d input input ∧ OnCurve d output := by
  have rows := shared_inverse_rows d inverse input input output inverseRow xValue yValue
  exact ⟨affine_rows_sound d imaginary nonSquare imaginarySquare input input output
      valid valid rows.1 rows.2,
    affine_rows_onCurve d imaginary nonSquare imaginarySquare input input output
      valid valid rows.1 rows.2⟩

/-- The optimized runtime doubling denominators are y²-x² and 2-(y²-x²).
Their agreement with complete affine addition follows from the input curve
equation; it is not an assumed total division operation. -/
theorem double_rows_sound (d imaginary : F) (nonSquare : NoUnitSquare d)
    (imaginarySquare : imaginary * imaginary = -1) (input output : Point F)
    (h : OnCurve d input)
    (xRow : output.x * (input.y * input.y - input.x * input.x) =
      (input.x + input.y) * (input.x + input.y) - input.x * input.x - input.y * input.y)
    (yRow : output.y * (2 - (input.y * input.y - input.x * input.x)) =
      input.y * input.y + input.x * input.x) :
    output = affineAdd d input input ∧ OnCurve d output := by
  have plus : input.y * input.y - input.x * input.x = 1 + delta d input input := by
    exact h
  have minus : 2 - (input.y * input.y - input.x * input.x) = 1 - delta d input input := by
    rw [plus]; ring
  have numerator : (input.x + input.y) * (input.x + input.y) -
      input.x * input.x - input.y * input.y = cross input input := by
    unfold cross; ring
  rw [plus, numerator] at xRow
  rw [minus] at yRow
  exact ⟨affine_rows_sound d imaginary nonSquare imaginarySquare input input output h h xRow yRow,
    affine_rows_onCurve d imaginary nonSquare imaginarySquare input input output h h xRow yRow⟩

theorem identity_onCurve (d : F) : OnCurve d (identityPoint : Point F) := by
  simp [OnCurve, identityPoint]

def chooseCoordinate (bit yes no : F) : F := no + bit * (yes - no)

def windowPoint (low high : F) (base twice triple : Point F) : Point F :=
  ⟨chooseCoordinate high (chooseCoordinate low triple.x twice.x)
      (chooseCoordinate low base.x 0),
   chooseCoordinate high (chooseCoordinate low triple.y twice.y)
      (chooseCoordinate low base.y 1)⟩

def windowCase (low high : Bool) (base twice triple : Point F) : Point F :=
  match high, low with
  | false, false => identityPoint
  | false, true => base
  | true, false => twice
  | true, true => triple

/-- Exact little-endian two-bit selector used by both runtime window loops.
The names twice/triple alone do not assert their multiplication semantics. -/
theorem window_correct (low high : Bool) (base twice triple : Point F) :
    windowPoint (if low then 1 else 0) (if high then 1 else 0) base twice triple =
      windowCase low high base twice triple := by
  cases low <;> cases high <;>
    simp [windowPoint, windowCase, chooseCoordinate, identityPoint]

theorem window_onCurve (d : F) (low high : Bool) (base twice triple : Point F)
    (hb : OnCurve d base) (hd : OnCurve d twice) (ht : OnCurve d triple) :
    OnCurve d (windowPoint (if low then 1 else 0) (if high then 1 else 0) base twice triple) := by
  rw [window_correct]
  cases low <;> cases high <;> simp only [windowCase]
  · exact identity_onCurve d
  · exact hd
  · exact hb
  · exact ht

/-- Explicit imported standard-curve model boundary. There is no instance or
axiom asserting it for arbitrary fields. The intended instance is the Jubjub
group in Zcash Protocol Specification 5.4.9.3: exact field/d, identity (0,1),
complete Edwards group law and order 8*r. Its standard group-law/order facts
remain independently justified primitive-model assumptions until instantiated
formally; they do not assert any circuit witness's subgroup membership.

Coordinates cover every *on-curve* pair and are injective, so the boundary
cannot silently omit valid preimages or identify different affine points. -/
structure StandardCurveModel (J : Type) [AddCommGroup J] (d : F) where
  coordinates : J → Point F
  onCurve : ∀ point, OnCurve d (coordinates point)
  covers : ∀ point, OnCurve d point → ∃ represented, coordinates represented = point
  injective : Function.Injective coordinates
  identity : coordinates 0 = identityPoint
  addition : ∀ left right, coordinates (left + right) =
    affineAdd d (coordinates left) (coordinates right)

/-- Three actual doubling equations imply membership in the r-annihilated
subgroup of the named standard group. The external order fact applies to ALL
standard curve points, not to the particular output being checked. For Jubjub,
it follows from the independently specified group cardinality 8*r. Actual row
certificates must discharge the three affine equations and preimage curve test.
No native cofactor-preimage constructor is a theorem premise. -/
theorem cofactor_image_annihilated {J : Type} [AddCommGroup J]
    (d : F) (model : StandardCurveModel J d) (r : Nat)
    (standardOrder : ∀ point : J, (8 * r) • point = 0)
    (preimage twice four eight : Point F) (valid : OnCurve d preimage)
    (first : twice = affineAdd d preimage preimage)
    (second : four = affineAdd d twice twice)
    (third : eight = affineAdd d four four) :
    ∃ represented : J, model.coordinates represented = eight ∧ r • represented = 0 := by
  obtain ⟨point, pointCoordinates⟩ := model.covers preimage valid
  have twiceCoordinates : model.coordinates (point + point) = twice := by
    rw [model.addition, pointCoordinates]
    exact first.symm
  have fourCoordinates : model.coordinates ((point + point) + (point + point)) = four := by
    rw [model.addition, twiceCoordinates]
    exact second.symm
  have eightCoordinates : model.coordinates
      (((point + point) + (point + point)) + ((point + point) + (point + point))) = eight := by
    rw [model.addition, fourCoordinates]
    exact third.symm
  have repeated : (((point + point) + (point + point)) +
      ((point + point) + (point + point))) = (8 : Nat) • point := by
    simp only [← two_nsmul, ← mul_nsmul]
  rw [repeated] at eightCoordinates
  refine ⟨8 • point, eightCoordinates, ?_⟩
  rw [← mul_nsmul]
  exact standardOrder point

/-- Nonidentity is supplied by the real x-inverse constraint, independently of
the cofactor relation. This conclusion does not imply knowledge of a secret
scalar or signature authorization. -/
theorem represented_nonidentity {J : Type} [AddCommGroup J]
    (d : F) (model : StandardCurveModel J d) (point : J)
    (nonzero : (model.coordinates point).x ≠ 0) : point ≠ 0 := by
  intro zero
  subst point
  exact nonzero (by rw [model.identity]; rfl)

#print axioms addition_closure_polynomial
#print axioms affine_rows_onCurve
#print axioms double_rows_sound
#print axioms window_correct
#print axioms window_onCurve
#print axioms cofactor_image_annihilated
#print axioms represented_nonidentity
#print axioms shared_inverse_rows
#print axioms shared_inverse_double_sound

end ShielddSecurity.Group

set_option pp.all true in
#check @ShielddSecurity.Group.addition_closure_polynomial
set_option pp.all true in
#check @ShielddSecurity.Group.invariant
#print axioms ShielddSecurity.Group.invariant
set_option pp.all true in
#check @ShielddSecurity.Group.affine_rows_onCurve
set_option pp.all true in
#check @ShielddSecurity.Group.identityPoint
#print axioms ShielddSecurity.Group.identityPoint
set_option pp.all true in
#check @ShielddSecurity.Group.shared_inverse_rows
set_option pp.all true in
#check @ShielddSecurity.Group.shared_inverse_double_sound
set_option pp.all true in
#check @ShielddSecurity.Group.double_rows_sound
set_option pp.all true in
#check @ShielddSecurity.Group.identity_onCurve
#print axioms ShielddSecurity.Group.identity_onCurve
set_option pp.all true in
#check @ShielddSecurity.Group.chooseCoordinate
#print axioms ShielddSecurity.Group.chooseCoordinate
set_option pp.all true in
#check @ShielddSecurity.Group.windowPoint
#print axioms ShielddSecurity.Group.windowPoint
set_option pp.all true in
#check @ShielddSecurity.Group.windowCase
#print axioms ShielddSecurity.Group.windowCase
set_option pp.all true in
#check @ShielddSecurity.Group.window_correct
set_option pp.all true in
#check @ShielddSecurity.Group.window_onCurve
set_option pp.all true in
#check @ShielddSecurity.Group.StandardCurveModel
#print axioms ShielddSecurity.Group.StandardCurveModel
set_option pp.all true in
#check @ShielddSecurity.Group.cofactor_image_annihilated
set_option pp.all true in
#check @ShielddSecurity.Group.represented_nonidentity
