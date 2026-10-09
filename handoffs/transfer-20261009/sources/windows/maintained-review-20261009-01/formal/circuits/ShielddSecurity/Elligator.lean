import ShielddSecurity.Group

set_option maxHeartbeats 150000

namespace ShielddSecurity.Elligator

variable {F : Type} [Field F]

def cubic (c1 c2 x : F) : F := ((x + c1) * x + c2) * x

/-- The native alternative's computed gx2 really is the same cubic at x2.
Only the first x-coordinate equation is needed; QR/root choice is separate. -/
theorem alternative_cubic (c1 c2 x tv : F)
    (coordinate : (1 + tv) * x = -c1) :
    cubic c1 c2 (-x - c1) = tv * cubic c1 c2 x := by
  have coefficient : c1 = -((1 + tv) * x) := by
    calc
      c1 = -(-c1) := by simp
      _ = -((1 + tv) * x) := by rw [coordinate]
  rw [coefficient]
  simp only [cubic]
  ring

/-- Over a field the two square roots differ only by sign, including zero. -/
theorem roots_equal_or_negative (left right : F)
    (squares : left * left = right * right) : left = right ∨ left = -right := by
  have product : (left - right) * (left + right) = 0 := by
    calc
      _ = left * left - right * right := by ring
      _ = 0 := by rw [squares]; ring
  rcases mul_eq_zero.mp product with difference | sum
  · exact Or.inl (sub_eq_zero.mp difference)
  · exact Or.inr (eq_neg_of_add_eq_zero_left sum)

/-- Canonical integer parity makes the root unique in an odd prime field.
Canonical bit/source/byte joins must establish these actual integer operands;
the theorem does not assume any native sqrt algorithm's selected output. -/
theorem canonical_root_unique {p : Nat} [CharP F p] (left right : Nat)
    (leftBound : left < p) (rightBound : right < p) (odd : p % 2 = 1)
    (squares : (left : F) * (left : F) = (right : F) * (right : F))
    (sameParity : left % 2 = right % 2) : left = right := by
  rcases roots_equal_or_negative (left : F) (right : F) squares with same | negative
  · exact bounded_cast_injective leftBound rightBound same
  · by_cases zero : right = 0
    · subst right
      exact bounded_cast_injective leftBound rightBound (by simpa using negative)
    · have complement : ((p - right : Nat) : F) = -(right : F) := by
        rw [Nat.cast_sub (Nat.le_of_lt rightBound), CharP.cast_eq_zero F p, zero_sub]
      have identity : left = p - right := bounded_cast_injective leftBound
        (by omega) (negative.trans complement.symm)
      omega

/-- The exceptional denominator in map::x_coordinates is impossible under the
exact field's global nonsquare contract. This is not a witness-specific premise. -/
theorem first_denominator_nonzero (z u : F)
    (nonSquare : Group.NoUnitSquare (-z)) : 1 + z * u * u ≠ 0 := by
  intro zero
  apply nonSquare u
  have equation := congrArg (fun value : F => 1 - value) zero
  calc
    (-z) * u * u = 1 - (1 + z * u * u) := by ring
    _ = 1 := by simpa using equation

/-- A nonzero quadratic residue and its nonsquare multiple cannot both have
roots. The global nonsquare fact is sufficient; no QR-choice fact is assumed. -/
theorem residue_alternative_exclusive (z g a b : F)
    (nonSquare : Group.NoUnitSquare z) (zNonzero : z ≠ 0)
    (gNonzero : g ≠ 0) (first : a * a = g) (second : b * b = z * g) : False := by
  have bNonzero : b ≠ 0 := by
    intro zero
    have impossible : z * g = 0 := by simpa [zero] using second.symm
    exact (mul_ne_zero zNonzero gNonzero) impossible
  apply nonSquare (a * b⁻¹)
  calc
    z * (a * b⁻¹) * (a * b⁻¹) = (z * (a * a)) * (b⁻¹ * b⁻¹) := by ring
    _ = (b * b) * (b⁻¹ * b⁻¹) := by rw [first, ← second]
    _ = (b * b⁻¹) * (b * b⁻¹) := by ring
    _ = 1 := by rw [mul_inv_cancel₀ bNonzero]; simp

/-- The circuit's separate QR-root equation pins the native square choice for
arbitrary assignments. The nonzero cubic and field nonsquare facts must be
instantiated at the actual map parameters, separately from this local proof. -/
theorem square_choice_sound (z g root : F) (choice : Bool)
    (nonSquare : Group.NoUnitSquare z) (zNonzero : z ≠ 0)
    (gNonzero : g ≠ 0)
    (rootEquation : root * root = if choice then g else z * g) :
    choice = true ↔ ∃ value : F, value * value = g := by
  cases choice
  · constructor
    · intro impossible; cases impossible
    · rintro ⟨value, square⟩
      exact False.elim (residue_alternative_exclusive z g value root
        nonSquare zNonzero gNonzero square (by simpa using rootEquation))
  · constructor
    · intro _; exact ⟨root, by simpa using rootEquation⟩
    · intro _; rfl

variable [DecidableEq F]

/-- The three actual inverse/zero assertions uniquely determine both witnesses.
No boolean constraint or honest-witness assumption is needed for this result. -/
theorem inverse_constraints_unique (denominator inverse zero : F)
    (product : denominator * inverse = 1 - zero)
    (annihilate : denominator * zero = 0)
    (inverseZero : inverse * zero = 0) :
    zero = (if denominator = 0 then 1 else 0) ∧
      inverse = (if denominator = 0 then 0 else denominator⁻¹) := by
  by_cases exceptional : denominator = 0
  · have flag : zero = 1 := by
      have h : 1 - zero = 0 := by simpa [exceptional] using product.symm
      exact (sub_eq_zero.mp h).symm
    have value : inverse = 0 := by simpa [flag] using inverseZero
    simp [exceptional, flag, value]
  · have flag : zero = 0 := (mul_eq_zero.mp annihilate).resolve_left exceptional
    have unit : denominator * inverse = 1 := by simpa [flag] using product
    have value : inverse = denominator⁻¹ := by
      calc
        inverse = denominator⁻¹ * (denominator * inverse) := by
          rw [← mul_assoc, inv_mul_cancel₀ exceptional, one_mul]
        _ = denominator⁻¹ := by rw [unit, mul_one]
    simp [exceptional, flag, value]

/-- Constructing the exact exceptional inverse witnesses satisfies all three
runtime assertions for every denominator, including zero. -/
theorem inverse_constraints_complete (denominator : F) :
    let inverse := if denominator = 0 then 0 else denominator⁻¹
    let zero := if denominator = 0 then (1 : F) else 0
    denominator * inverse = 1 - zero ∧
      denominator * zero = 0 ∧ inverse * zero = 0 := by
  by_cases exceptional : denominator = 0
  · simp [exceptional]
  · simp [exceptional]

def rationalPoint (s t : F) : Group.Point F :=
  let denominator := (s + 1) * t
  if denominator = 0 then ⟨0, 1⟩
  else ⟨denominator⁻¹ * (s + 1) * s,
    denominator⁻¹ * t * (s - 1)⟩

/-- The circuit's total rational-map formulas agree with the native exceptional
branch after the actual three inverse assertions; subgroup/cofactor and the
Elligator root choice remain distinct subsequent obligations. -/
theorem rational_point_sound (s t inverse zero : F)
    (product : ((s + 1) * t) * inverse = 1 - zero)
    (annihilate : ((s + 1) * t) * zero = 0)
    (inverseZero : inverse * zero = 0) :
    (⟨inverse * (s + 1) * s,
      inverse * t * (s - 1) + zero⟩ : Group.Point F) = rationalPoint s t := by
  obtain ⟨flag, value⟩ := inverse_constraints_unique ((s + 1) * t)
    inverse zero product annihilate inverseZero
  by_cases exceptional : (s + 1) * t = 0
  · simp [rationalPoint, exceptional] at flag value ⊢
    simp [flag, value]
  · simp [rationalPoint, exceptional] at flag value ⊢
    simp [flag, value]

set_option pp.all true in
#check @alternative_cubic
set_option pp.all true in
#check @roots_equal_or_negative
set_option pp.all true in
#check @canonical_root_unique
set_option pp.all true in
#check @first_denominator_nonzero
set_option pp.all true in
#check @residue_alternative_exclusive
set_option pp.all true in
#check @square_choice_sound
set_option pp.all true in
#check @inverse_constraints_unique
set_option pp.all true in
#check @inverse_constraints_complete
set_option pp.all true in
#check @rational_point_sound
#print axioms alternative_cubic
#print axioms roots_equal_or_negative
#print axioms canonical_root_unique
#print axioms first_denominator_nonzero
#print axioms residue_alternative_exclusive
#print axioms square_choice_sound
#print axioms inverse_constraints_unique
#print axioms inverse_constraints_complete
#print axioms rational_point_sound

end ShielddSecurity.Elligator
