import ShielddSecurity.Compiler

set_option maxHeartbeats 200000

namespace ShielddSecurity.CompilerSignedCompletion

variable {F : Type} [Field F] {p : Nat} [CharP F p]

/-- Left negation preserves a squared row; right coefficients are unchanged. -/
theorem signed_row (rho : Nat → F) (actual expected : Row)
    (left : Compiler.canonical p actual.a = Compiler.canonical p expected.a ∨
      Compiler.canonical p actual.a = Compiler.canonical p (scaleLinear (-1) expected.a))
    (right : Compiler.canonical p actual.b = Compiler.canonical p expected.b)
    (completed : Square (eval rho expected.a) (eval rho expected.b)) :
    Square (eval rho actual.a) (eval rho actual.b) := by
  rw [Compiler.canonical_equal rho _ _ right]
  rcases left with positive | negative
  · rw [Compiler.canonical_equal rho _ _ positive]
    exact completed
  · rw [Compiler.canonical_equal rho _ _ negative, eval_scale]
    simpa only [Int.cast_neg, Int.cast_one, neg_one_mul, Square, neg_mul_neg] using completed

/-- Transport exact original rows after a kept constant-copy link. The finite
coverage checks either orientation and never supplies a desired row equation. -/
theorem original_rows (rho : Nat → F) (expected actual : List Row) (copy : Nat)
    (linked : rho copy = rho 0) (completed : Satisfies rho expected)
    (coverage : ∀ row ∈ actual, ∃ source ∈ expected,
      (Compiler.canonical p (Compiler.unoutline copy row.a) = Compiler.canonical p source.a ∨
       Compiler.canonical p (Compiler.unoutline copy row.a) =
         Compiler.canonical p (scaleLinear (-1) source.a)) ∧
      Compiler.canonical p (Compiler.unoutline copy row.b) = Compiler.canonical p source.b) :
    Satisfies rho actual := by
  intro row member
  obtain ⟨source,present,left,right⟩ := coverage row member
  have result := signed_row rho
    (⟨Compiler.unoutline copy row.a,Compiler.unoutline copy row.b⟩ : Row)
    source left right (completed source present)
  simpa only [Compiler.eval_unoutline rho copy _ linked] using result

set_option pp.all true in
#check @signed_row
#print axioms signed_row
set_option pp.all true in
#check @original_rows
#print axioms original_rows

end ShielddSecurity.CompilerSignedCompletion
