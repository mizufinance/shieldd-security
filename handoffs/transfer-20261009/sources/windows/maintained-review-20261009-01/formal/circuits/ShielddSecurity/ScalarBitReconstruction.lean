import ShielddSecurity.ScalarIndexed
import ShielddSecurity.ScalarComparisonBounds

set_option maxHeartbeats 300000

namespace ShielddSecurity.ScalarBitReconstruction

/-- Scale a symbolic weighted column list, without repeatedly mapping a
concrete 252-term recursive binary expression in a kernel data check. -/
theorem weighted_scale (columns : List Nat) (factor weight : Int) :
    scaleLinear factor (weighted columns weight) = weighted columns (factor * weight) := by
  induction columns generalizing weight with
  | nil => rfl
  | cons column tail ih =>
      change (column, factor * weight) :: scaleLinear factor (weighted tail (weight * 2)) =
        (column, factor * weight) :: weighted tail ((factor * weight) * 2)
      rw [ih]
      simp only [mul_assoc]

/-- Exact syntax transport for the captured one-column Boolean witnesses.
This induction replaces quadratic nested LC scaling with a linear weight list. -/
theorem bitLinear_singletons (columns : List Nat) :
    ScalarBits.bitLinear (columns.map (fun column => [(column, 1)])) = weighted columns 1 := by
  induction columns with
  | nil => rfl
  | cons column tail ih =>
      change [(column, 1)] ++ scaleLinear 2
        (ScalarBits.bitLinear (tail.map (fun c => [(c, 1)]))) =
        (column, 1) :: weighted tail 2
      rw [ih, weighted_scale]
      rfl

/-- One exact indexed original assertion, in either captured orientation,
establishes the existing reconstruction checker. The bit/column equality is
structural; no decoded scalar value or reconstruction truth is assumed. -/
theorem checked_reconstruction_indexed (p : Nat) (rows : List Row) (index : Nat)
    (bits : List Linear) (columns : List Nat) (value : Linear)
    (sameBits : bits = columns.map (fun column => [(column, 1)]))
    (checked : (ScalarIndexed.checkRowAt p rows index
      ⟨Compiler.subtract (weighted columns 1) value, []⟩ ||
      ScalarIndexed.checkRowAt p rows index
        ⟨Compiler.subtract value (weighted columns 1), []⟩) = true) :
    ScalarComparisonBounds.checkEquality p rows (ScalarBits.bitLinear bits) value = true := by
  rw [sameBits, bitLinear_singletons]
  simp only [ScalarComparisonBounds.checkEquality, Bool.or_eq_true] at checked ⊢
  rcases checked with forward | backward
  · exact Or.inl (ScalarIndexed.checked_row_membership p rows index _ forward)
  · exact Or.inr (ScalarIndexed.checked_row_membership p rows index _ backward)

set_option pp.all true in
#check @weighted_scale
#print axioms weighted_scale
set_option pp.all true in
#check @bitLinear_singletons
#print axioms bitLinear_singletons
set_option pp.all true in
#check @checked_reconstruction_indexed
#print axioms checked_reconstruction_indexed

end ShielddSecurity.ScalarBitReconstruction
