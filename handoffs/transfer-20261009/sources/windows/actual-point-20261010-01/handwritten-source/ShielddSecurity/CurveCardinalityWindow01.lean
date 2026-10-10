import ShielddSecurity.Range

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.CurveCardinalityWindow01

def fieldModulus : Nat :=
  52435875175126190479447740508185965837690552500527637822603658699938581184513

def scalarModulus : Nat :=
  6554484396890773809930967563523245729705921265872317281365359162392183254199

/-- The exact integer window needed by the elementary torsion route. This
does not establish the cardinality of any curve or the legality of any point. -/
theorem integer_window : 2 * fieldModulus + 1 < 24 * scalarModulus := by
  decide

theorem scalar_positive : 0 < scalarModulus := by
  decide

/-- A positive multiple of eight times r below twenty-four times r has only
two possibilities. The curve-specific divisibility and upper bound are explicit
premises, to be supplied by separate mathematical proofs. -/
theorem two_cardinality_candidates (r n : Nat) (positive : 0 < n)
    (divisible : 8 * r ∣ n) (window : n < 24 * r) :
    n = 8 * r ∨ n = 16 * r := by
  obtain ⟨k, rfl⟩ := divisible
  have bound_eq : 24 * r = (8 * r) * 3 := by omega
  rw [bound_eq] at window
  have upper : k < 3 := Nat.lt_of_mul_lt_mul_left (a := 8 * r) window
  have nonzero : k ≠ 0 := by
    intro zero
    simp [zero] at positive
  have candidates : k = 1 ∨ k = 2 := by omega
  rcases candidates with one | two
  · subst k
    simp
  · subst k
    right
    omega

/-- Odd cardinality of the eight-multiplication image eliminates the second
candidate, once a separate kernel/image cardinality theorem identifies n/8. -/
theorem cardinality_from_odd_quotient (r n : Nat) (positive : 0 < n)
    (divisible : 8 * r ∣ n) (window : n < 24 * r)
    (oddQuotient : n / 8 % 2 = 1) : n = 8 * r := by
  rcases two_cardinality_candidates r n positive divisible window with eight | sixteen
  · exact eight
  · have quotient : n / 8 = 2 * r := by
      rw [sixteen]
      have factor : 16 * r = 8 * (2 * r) := by omega
      rw [factor]
      simp
    rw [quotient] at oddQuotient
    omega

end ShielddSecurity.CurveCardinalityWindow01

set_option pp.all true in
#check @ShielddSecurity.CurveCardinalityWindow01.integer_window
#print axioms ShielddSecurity.CurveCardinalityWindow01.integer_window
set_option pp.all true in
#check @ShielddSecurity.CurveCardinalityWindow01.scalar_positive
#print axioms ShielddSecurity.CurveCardinalityWindow01.scalar_positive
set_option pp.all true in
#check @ShielddSecurity.CurveCardinalityWindow01.two_cardinality_candidates
#print axioms ShielddSecurity.CurveCardinalityWindow01.two_cardinality_candidates
set_option pp.all true in
#check @ShielddSecurity.CurveCardinalityWindow01.cardinality_from_odd_quotient
#print axioms ShielddSecurity.CurveCardinalityWindow01.cardinality_from_odd_quotient
