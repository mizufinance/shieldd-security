import Mathlib.Algebra.Field.Defs

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity

variable {F : Type} [Field F]

/-- A square row is interpreted over every assignment, not honest witnesses. -/
def Square (a b : F) : Prop := a * a = b

theorem boolean_sound (x : F) (h : Square x x) : x = 0 ∨ x = 1 := by
  by_cases zero : x = 0
  · exact Or.inl zero
  · have cancelled := congrArg (fun y : F => y * x⁻¹) (show x * x = x from h)
    exact Or.inr (by
      simpa only [mul_assoc, mul_inv_cancel₀ zero, mul_one] using cancelled)

abbrev Linear := List (Nat × Int)

def eval {F : Type} [Field F] (rho : Nat → F) : Linear → F
  | [] => 0
  | (column, coefficient) :: terms => (coefficient : F) * rho column + eval rho terms


end ShielddSecurity

-- Fresh handwritten bounded successor; proof bodies retained.
set_option pp.all true in
#check @ShielddSecurity.boolean_sound
#print axioms ShielddSecurity.boolean_sound
