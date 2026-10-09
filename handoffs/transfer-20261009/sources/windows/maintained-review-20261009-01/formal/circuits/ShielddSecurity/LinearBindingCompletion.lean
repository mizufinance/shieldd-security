import ShielddSecurity.Compiler

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

namespace ShielddSecurity.LinearBindingCompletion

variable {F : Type} [Field F]

/-- Own only the exact target witness of a computed-to-supplied assertion.
The source expression remains fixed; its semantic meaning is a separate
preceding constructor, never an assumed equality to this target. -/
def assignment (base : Nat → F) (computed : Linear) (target : Nat) : Nat → F :=
  patchAssignment base (fun _ => eval base computed) [target]

theorem preserves (base : Nat → F) (computed : Linear) (target column : Nat)
    (outside : column ≠ target) : assignment base computed target column = base column := by
  apply patchAssignment_preserves
  simpa only [List.mem_singleton] using outside

theorem value (base : Nat → F) (computed : Linear) (target : Nat) :
    assignment base computed target target = eval base computed := by
  simp [assignment, patchAssignment]

theorem eval_preserves (base : Nat → F) (computed terms : Linear) (target : Nat)
    (fresh : ∀ term ∈ terms, term.1 ≠ target) :
    eval (assignment base computed target) terms = eval base terms := by
  apply eval_agrees
  intro term member
  exact preserves base computed target term.1 (fresh term member)

/-- Both assertion orientations are transported from the exact normalized
original row. Column0 and its compiler copy are preserved explicitly. -/
theorem original_complete {p : Nat} [CharP F p]
    (base : Nat → F) (computed : Linear) (target copy : Nat) (original : Row)
    (fresh : ∀ term ∈ computed, term.1 ≠ target)
    (targetZero : target ≠ 0) (targetCopy : target ≠ copy)
    (linked : base copy = base 0)
    (left : Compiler.canonical p (Compiler.unoutline copy original.a) =
        Compiler.canonical p (Compiler.subtract computed [(target, 1)]) ∨
      Compiler.canonical p (Compiler.unoutline copy original.a) =
        Compiler.canonical p (Compiler.subtract [(target, 1)] computed))
    (right : Compiler.canonical p (Compiler.unoutline copy original.b) =
      Compiler.canonical p []) :
    Square (eval (assignment base computed target) original.a)
      (eval (assignment base computed target) original.b) := by
  let rho := assignment base computed target
  have computedValue : eval rho computed = eval base computed :=
    eval_preserves base computed computed target fresh
  have targetValue : eval rho [(target, 1)] = eval base computed := by
    simp only [eval, Int.cast_one, one_mul, add_zero, rho, value]
  have copyLink : rho copy = rho 0 := by
    dsimp only [rho]
    rw [preserves base computed target copy targetCopy.symm,
      preserves base computed target 0 targetZero.symm, linked]
  have actualLeft : eval rho (Compiler.unoutline copy original.a) = 0 := by
    rcases left with checked | checked
    · rw [Compiler.canonical_equal rho _ _ checked, Compiler.eval_subtract,
        computedValue, targetValue, sub_self]
    · rw [Compiler.canonical_equal rho _ _ checked, Compiler.eval_subtract,
        targetValue, computedValue, sub_self]
  have actualRight : eval rho (Compiler.unoutline copy original.b) = 0 := by
    rw [Compiler.canonical_equal rho _ _ right]
    rfl
  rw [Compiler.eval_unoutline rho copy original.a copyLink] at actualLeft
  rw [Compiler.eval_unoutline rho copy original.b copyLink] at actualRight
  simp only [rho] at actualLeft actualRight
  simp only [Square, actualLeft, actualRight, zero_mul]

set_option pp.all true in
#check @preserves
#print axioms preserves
set_option pp.all true in
#check @value
#print axioms value
set_option pp.all true in
#check @eval_preserves
#print axioms eval_preserves
set_option pp.all true in
#check @original_complete
#print axioms original_complete

end ShielddSecurity.LinearBindingCompletion
