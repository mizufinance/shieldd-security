import ShielddSecurity.CompilerCompletion
import ShielddSecurity.NoteSpendCompletion

set_option maxHeartbeats 300000

namespace ShielddSecurity.NoteSpendRowCompletion

variable {F : Type} [Field F]

/-- Preserve a captured source LC while constructing only a product pivot and
its auxiliary. Actual instances discharge this syntactic condition in kernel. -/
theorem product_eval_preserves (base : Nat → F) (left right remainder terms : Linear)
    (output auxiliary : Nat)
    (outside : ∀ term ∈ terms, term.1 ∉ [output, auxiliary]) :
    eval (ScalarCompletion.extendProduct base left right remainder output auxiliary) terms =
      eval base terms := by
  apply eval_agrees
  intro term member
  exact ScalarCompletion.extend_product_preserves base left right remainder
    output auxiliary term.1 (outside term member)

/-- A fused compiler output is pivot plus remainder. Writing the pivot to the
product MINUS that remainder establishes the full captured LC value. No output
or product equation is a premise. Product-row legality is the separate generic
ScalarCompletion theorem used by CompilerCompletion.run_complete. -/
theorem materialized_value (base : Nat → F) (left right remainder : Linear)
    (output auxiliary : Nat)
    (fresh : ∀ term ∈ remainder, term.1 ∉ [output, auxiliary]) :
    eval (ScalarCompletion.extendProduct base left right remainder output auxiliary)
      ([(output, 1)] ++ remainder) = eval base left * eval base right := by
  have remainderValue := product_eval_preserves base left right remainder remainder
    output auxiliary fresh
  have outputValue : ScalarCompletion.extendProduct base left right remainder output auxiliary output =
      eval base left * eval base right - eval base remainder := by
    simp [ScalarCompletion.extendProduct, ScalarCompletion.productValues, patchAssignment]
  simp only [eval_append, eval, Int.cast_one, one_mul, add_zero, outputValue, remainderValue]
  ring

set_option pp.all true in
#check @product_eval_preserves
#print axioms product_eval_preserves
set_option pp.all true in
#check @materialized_value
#print axioms materialized_value

end ShielddSecurity.NoteSpendRowCompletion
