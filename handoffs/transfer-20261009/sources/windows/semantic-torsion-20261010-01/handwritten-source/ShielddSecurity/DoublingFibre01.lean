import Mathlib.Algebra.Field.Basic

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.DoublingFibre01

variable {J : Type} [AddCommGroup J]

/-- A complete two-torsion classification bounds every doubling fibre by
two explicit translates. The classification must come from the concrete curve. -/
theorem equal_double_cases (torsion left right : J)
    (classification : ∀ point : J, 2 • point = 0 → point = 0 ∨ point = torsion)
    (equal : 2 • left = 2 • right) :
    left = right ∨ left = right + torsion := by
  have killed : 2 • (left - right) = 0 := by
    rw [nsmul_sub, equal, sub_self]
  rcases classification (left - right) killed with zero | translated
  · exact Or.inl (sub_eq_zero.mp zero)
  · exact Or.inr (((sub_eq_iff_eq_add).mp translated).trans (add_comm torsion right))

end ShielddSecurity.DoublingFibre01

set_option pp.all true in
#check @ShielddSecurity.DoublingFibre01.equal_double_cases
#print axioms ShielddSecurity.DoublingFibre01.equal_double_cases
