import ShielddSecurity.RowOrientationSoundness

set_option maxHeartbeats 200000

namespace ShielddSecurity.EncryptionDhBoolean

/-- A Boolean assertion may concern an affine LC, not a fresh witness. -/
theorem asserted {F : Type} [Field F] {p : Nat} [CharP F p]
    (rho : Nat → F) (actual : List Row) (value : Linear)
    (checked : [Row.mk value value].all (fun row =>
      Compiler.checkRow p actual row ||
      Compiler.checkRow p actual ⟨scaleLinear (-1) row.a, row.b⟩) = true)
    (satisfied : Satisfies rho actual) :
    eval rho value = 0 ∨ eval rho value = 1 := by
  have rows := RowOrientationSoundness.checked_rows rho actual
    [Row.mk value value] checked satisfied
  exact boolean_sound _ (rows (Row.mk value value) (List.mem_cons.mpr (Or.inl rfl)))

/-- NOT needs the operand's Boolean proof and the actual affine identity. -/
theorem negation {F : Type} [Field F] (input output : F)
    (boolean : input = 0 ∨ input = 1) (expression : output = 1 - input) :
    output = 0 ∨ output = 1 := by
  rcases boolean with zero | one
  · right
    simpa [zero] using expression
  · left
    simpa [one] using expression

/-- AND needs both Boolean inputs and a derived multiplication equality. -/
theorem conjunction {F : Type} [Field F] (left right output : F)
    (leftBoolean : left = 0 ∨ left = 1) (rightBoolean : right = 0 ∨ right = 1)
    (product : output = left * right) : output = 0 ∨ output = 1 := by
  rcases leftBoolean with zero | one
  · left
    simpa [zero] using product
  · rcases rightBoolean with zero | rightOne
    · left
      simpa [zero] using product
    · right
      simpa [one, rightOne] using product

set_option pp.all true in
#check @asserted
#print axioms asserted
set_option pp.all true in
#check @negation
#print axioms negation
set_option pp.all true in
#check @conjunction
#print axioms conjunction

end ShielddSecurity.EncryptionDhBoolean
