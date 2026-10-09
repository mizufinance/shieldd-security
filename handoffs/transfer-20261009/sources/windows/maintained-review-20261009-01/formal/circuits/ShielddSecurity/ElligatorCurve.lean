import ShielddSecurity.Elligator

set_option maxHeartbeats 500000

namespace ShielddSecurity.ElligatorCurve

variable {F : Type} [Field F]

/-- Scaling the selected cubic uses the two actual map parameter equations.
The root equation is supplied by the selected square rows, not curve membership. -/
theorem scaled_cubic (k j c1 c2 x y : F)
    (first : k * c1 = j) (second : k * k * c2 = 1)
    (root : y * y = Elligator.cubic c1 c2 x) :
    k * (k * y) * (k * y) =
      (k * x) * (k * x) * (k * x) + j * (k * x) * (k * x) + k * x := by
  calc
    _ = k * k * k * (y * y) := by ring
    _ = k * k * k * Elligator.cubic c1 c2 x := by rw [root]
    _ = (k * x) * (k * x) * (k * x) +
        (k * c1) * (k * x) * (k * x) + (k * k * c2) * (k * x) := by
      unfold Elligator.cubic
      ring
    _ = _ := by rw [first, second]; ring

/-- A polynomial certificate for the rational Montgomery-to-Edwards map.
It covers every selected root, including a torsion point before cofactor clearing. -/
theorem rational_certificate (k j d s t : F)
    (scale : k = -(j + 2)) (edwards : k * d = j - 2)
    (cubic : k * t * t = s * s * s + j * s * s + s) :
    k * (t * t * (s - 1) * (s - 1) - s * s * (s + 1) * (s + 1) -
      t * t * (s + 1) * (s + 1) - d * s * s * (s - 1) * (s - 1)) = 0 := by
  calc
    _ = -4 * s * (k * t * t) - s * s *
        (k * (s + 1) * (s + 1) + (k * d) * (s - 1) * (s - 1)) := by ring
    _ = -4 * s * (s * s * s + j * s * s + s) - s * s *
        (-(j + 2) * (s + 1) * (s + 1) + (j - 2) * (s - 1) * (s - 1)) := by
      rw [cubic, edwards, scale]
    _ = 0 := by ring

variable [DecidableEq F]

theorem rational_coordinates_curve (d s t x y : F)
    (tNonzero : t ≠ 0) (sNonzero : s + 1 ≠ 0)
    (xRow : x * t = s) (yRow : y * (s + 1) = s - 1)
    (polynomial : t * t * (s - 1) * (s - 1) - s * s * (s + 1) * (s + 1) -
      t * t * (s + 1) * (s + 1) - d * s * s * (s - 1) * (s - 1) = 0) :
    Group.OnCurve d (⟨x, y⟩ : Group.Point F) := by
  have multiplied : (y * y - x * x - (1 + d * x * x * y * y)) *
      (t * t * (s + 1) * (s + 1)) = 0 := by
    calc
      _ = (y * (s + 1)) * (y * (s + 1)) * t * t -
          (x * t) * (x * t) * (s + 1) * (s + 1) -
          t * t * (s + 1) * (s + 1) -
          d * (x * t) * (x * t) * (y * (s + 1)) * (y * (s + 1)) := by ring
      _ = 0 := by rw [xRow, yRow]; simpa only [mul_comm, mul_left_comm, mul_assoc] using polynomial
  have denominator : t * t * (s + 1) * (s + 1) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero tNonzero tNonzero) sNonzero) sNonzero
  exact sub_eq_zero.mp ((mul_eq_zero.mp multiplied).resolve_right denominator)

/-- The total exceptional map is on the full Edwards curve. No subgroup or
nonidentity premise is silently obtained from this theorem. -/
theorem rational_on_curve (k j d s t : F)
    (nonzero : k ≠ 0) (scale : k = -(j + 2)) (edwards : k * d = j - 2)
    (cubic : k * t * t = s * s * s + j * s * s + s) :
    Group.OnCurve d (Elligator.rationalPoint s t) := by
  by_cases exceptional : (s + 1) * t = 0
  · simp [Elligator.rationalPoint, exceptional, Group.OnCurve]
  · have factors := mul_ne_zero_iff.mp exceptional
    have certificate := rational_certificate k j d s t scale edwards cubic
    have polynomial := (mul_eq_zero.mp certificate).resolve_left nonzero
    simp only [Elligator.rationalPoint, if_neg exceptional, Group.OnCurve]
    have inverse : ((s + 1) * t)⁻¹ * ((s + 1) * t) = 1 := inv_mul_cancel₀ exceptional
    have xRow : (((s + 1) * t)⁻¹ * (s + 1) * s) * t = s := by
      calc
        _ = (((s + 1) * t)⁻¹ * ((s + 1) * t)) * s := by ring
        _ = s := by rw [inverse, one_mul]
    have yRow : (((s + 1) * t)⁻¹ * t * (s - 1)) * (s + 1) = s - 1 := by
      calc
        _ = (((s + 1) * t)⁻¹ * ((s + 1) * t)) * (s - 1) := by ring
        _ = s - 1 := by rw [inverse, one_mul]
    exact rational_coordinates_curve d s t _ _ factors.2 factors.1 xRow yRow polynomial

set_option pp.all true in
#check @scaled_cubic
#print axioms scaled_cubic
set_option pp.all true in
#check @rational_certificate
#print axioms rational_certificate
set_option pp.all true in
#check @rational_coordinates_curve
#print axioms rational_coordinates_curve
set_option pp.all true in
#check @rational_on_curve
#print axioms rational_on_curve

end ShielddSecurity.ElligatorCurve
