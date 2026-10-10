-- GENERATED SOURCE-only by generate_and_prepare.py; fresh audits UNRUN.
import ShielddSecurity.ScalarCompletion

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.CompilerLinearCompletion

variable {F : Type} [Field F]

/-- A captured unit pivot in a lowered linear assertion. This writes one
actual column; it introduces no product or inverse witness. -/
def extend (base : Nat → F) (input remainder : Linear) (output : Nat) : Nat → F :=
  patchAssignment base (fun _ => eval base input - eval base remainder) [output]

def rows (input remainder : Linear) (output : Nat) : List Row :=
  [⟨Compiler.subtract ([(output, 1)] ++ remainder) input, []⟩]

theorem preserves (base : Nat → F) (input remainder : Linear) (output column : Nat)
    (outside : column ≠ output) : extend base input remainder output column = base column :=
  patchAssignment_preserves base _ [output] column (by simpa using outside)

/-- Construct a lowered assertion from its unique fresh unit pivot. There is
no equality, row satisfaction, honest output, or denominator premise. -/
theorem constructs (base : Nat → F) (input remainder : Linear) (output : Nat)
    (fresh : ∀ term ∈ input ++ remainder, term.1 ≠ output) :
    Satisfies (extend base input remainder output) (rows input remainder output) := by
  let rho := extend base input remainder output
  have agrees (terms : Linear) (included : ∀ term ∈ terms, term ∈ input ++ remainder) :
      eval rho terms = eval base terms := by
    apply eval_agrees
    intro term member
    exact preserves base input remainder output term.1 (fresh term (included term member))
  have inputValue := agrees input (by intro term member; exact List.mem_append_left remainder member)
  have remainderValue := agrees remainder (by intro term member; exact List.mem_append_right input member)
  have outputValue : rho output = eval base input - eval base remainder := by
    simp [rho, extend, patchAssignment]
  intro row member
  simp only [rows, List.mem_singleton] at member
  subst row
  change Square (eval rho (Compiler.subtract ([(output, 1)] ++ remainder) input)) (eval rho [])
  rw [Compiler.eval_subtract, eval_append, inputValue, remainderValue]
  simp only [eval, Int.cast_one, one_mul, add_zero, outputValue, Square]
  ring


end ShielddSecurity.CompilerLinearCompletion

set_option pp.all true in
#check @ShielddSecurity.CompilerLinearCompletion.extend
#print axioms ShielddSecurity.CompilerLinearCompletion.extend

set_option pp.all true in
#check @ShielddSecurity.CompilerLinearCompletion.rows
#print axioms ShielddSecurity.CompilerLinearCompletion.rows

set_option pp.all true in
#check @ShielddSecurity.CompilerLinearCompletion.preserves
#print axioms ShielddSecurity.CompilerLinearCompletion.preserves

set_option pp.all true in
#check @ShielddSecurity.CompilerLinearCompletion.constructs
#print axioms ShielddSecurity.CompilerLinearCompletion.constructs
