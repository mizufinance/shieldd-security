import ShielddSecurity.Compiler

set_option maxHeartbeats 500000

namespace ShielddSecurity.ScalarCompletion

variable {F : Type} [Field F]

/-- The original two-square compiler encoding, with a fresh unit-coefficient
output pivot and a possibly fused remainder. Completion owns these two columns
only. An actual scalar instance must certify the pivot and support conditions. -/
def productRows (left right remainder : Linear) (output auxiliary : Nat) : List Row :=
  [⟨Compiler.subtract left right, [(auxiliary, 1)]⟩,
   ⟨left ++ right, [(auxiliary, 1)] ++
     scaleLinear 4 ([(output, 1)] ++ remainder)⟩]

def productValues (base : Nat → F) (left right remainder : Linear)
    (output auxiliary column : Nat) : F :=
  if column = output then eval base left * eval base right - eval base remainder
  else if column = auxiliary then (eval base left - eval base right) ^ 2
  else base column

def extendProduct (base : Nat → F) (left right remainder : Linear)
    (output auxiliary : Nat) : Nat → F :=
  patchAssignment base (productValues base left right remainder output auxiliary)
    [output, auxiliary]

theorem extend_product_preserves (base : Nat → F) (left right remainder : Linear)
    (output auxiliary column : Nat) (outside : column ∉ [output, auxiliary]) :
    extendProduct base left right remainder output auxiliary column = base column :=
  patchAssignment_preserves base
    (productValues base left right remainder output auxiliary)
    [output, auxiliary] column outside

theorem extend_product_complete (base : Nat → F) (left right remainder : Linear)
    (output auxiliary : Nat) (distinct : output ≠ auxiliary)
    (fresh : ∀ term ∈ left ++ right ++ remainder, term.1 ∉ [output, auxiliary]) :
    Satisfies (extendProduct base left right remainder output auxiliary)
      (productRows left right remainder output auxiliary) := by
  let rho := extendProduct base left right remainder output auxiliary
  have agrees (terms : Linear) (included : ∀ term ∈ terms, term ∈ left ++ right ++ remainder) :
      eval rho terms = eval base terms := by
    apply eval_agrees
    intro term member
    exact extend_product_preserves base left right remainder output auxiliary term.1
      (fresh term (included term member))
  have leftValue : eval rho left = eval base left :=
    agrees left (by intro term member; simp [member])
  have rightValue : eval rho right = eval base right :=
    agrees right (by intro term member; simp [member])
  have remainderValue : eval rho remainder = eval base remainder :=
    agrees remainder (by intro term member; simp [member])
  have outputValue : rho output = eval base left * eval base right - eval base remainder := by
    simp [rho, extendProduct, patchAssignment, productValues]
  have auxiliaryValue : rho auxiliary = (eval base left - eval base right) ^ 2 := by
    simp [rho, extendProduct, patchAssignment, productValues, Ne.symm distinct]
  simp only [rho] at leftValue rightValue remainderValue outputValue auxiliaryValue
  intro row present
  simp only [productRows, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at present
  rcases present with rfl | rfl
  · simp only [Square, Compiler.eval_subtract, eval, Int.cast_one, mul_one,
      one_mul, add_zero, leftValue, rightValue, auxiliaryValue]
    ring
  · simp only [Square, eval_append, eval_scale, eval, Int.cast_one, one_mul,
      add_zero, leftValue, rightValue, remainderValue, outputValue, auxiliaryValue,
      Int.cast_ofNat]
    ring

theorem extend_product_preserves_rows (base : Nat → F) (left right remainder : Linear)
    (output auxiliary : Nat) (prior : List Row) (satisfied : Satisfies base prior)
    (disjoint : ∀ row ∈ prior, ∀ term ∈ row.a ++ row.b, term.1 ∉ [output, auxiliary]) :
    Satisfies (extendProduct base left right remainder output auxiliary) prior :=
  patch_preserves_rows base
    (productValues base left right remainder output auxiliary)
    [output, auxiliary] prior satisfied disjoint

/-- The unconditional IVK inverse is a distinct obligation from the quotient-eight
guard. This completes its original two product rows for a nonzero legal scalar;
it does not manufacture a nonzero witness for an illegal input. -/
def inverseRows (remainder : Linear) (inverse auxiliary : Nat) : List Row :=
  [⟨Compiler.subtract [(inverse, 1)] remainder, [(auxiliary, 1)]⟩,
   ⟨[(inverse, 1)] ++ remainder, [(auxiliary, 1)] ++ scaleLinear 4 [(0, 1)]⟩]

def inverseValues (base : Nat → F) (remainder : Linear)
    (inverse auxiliary column : Nat) : F :=
  if column = inverse then (eval base remainder)⁻¹
  else if column = auxiliary then ((eval base remainder)⁻¹ - eval base remainder) ^ 2
  else base column

def extendInverse (base : Nat → F) (remainder : Linear)
    (inverse auxiliary : Nat) : Nat → F :=
  patchAssignment base (inverseValues base remainder inverse auxiliary) [inverse, auxiliary]

theorem extend_inverse_preserves (base : Nat → F) (remainder : Linear)
    (inverse auxiliary column : Nat) (outside : column ∉ [inverse, auxiliary]) :
    extendInverse base remainder inverse auxiliary column = base column :=
  patchAssignment_preserves base (inverseValues base remainder inverse auxiliary)
    [inverse, auxiliary] column outside

theorem extend_inverse_complete (base : Nat → F) (remainder : Linear)
    (inverse auxiliary : Nat) (distinct : inverse ≠ auxiliary)
    (one : base 0 = 1) (constantFresh : 0 ∉ [inverse, auxiliary])
    (fresh : ∀ term ∈ remainder, term.1 ∉ [inverse, auxiliary])
    (legal : eval base remainder ≠ 0) :
    Satisfies (extendInverse base remainder inverse auxiliary)
      (inverseRows remainder inverse auxiliary) := by
  let rho := extendInverse base remainder inverse auxiliary
  have remainderValue : eval rho remainder = eval base remainder := by
    apply eval_agrees
    intro term member
    exact extend_inverse_preserves base remainder inverse auxiliary term.1 (fresh term member)
  have oneValue : rho 0 = 1 :=
    (extend_inverse_preserves base remainder inverse auxiliary 0 constantFresh).trans one
  have inverseValue : rho inverse = (eval base remainder)⁻¹ := by
    simp [rho, extendInverse, patchAssignment, inverseValues]
  have auxiliaryValue : rho auxiliary = ((eval base remainder)⁻¹ - eval base remainder) ^ 2 := by
    simp [rho, extendInverse, patchAssignment, inverseValues, Ne.symm distinct]
  have reciprocal : (eval base remainder)⁻¹ * eval base remainder = 1 := inv_mul_cancel₀ legal
  simp only [rho] at remainderValue oneValue inverseValue auxiliaryValue
  intro row present
  simp only [inverseRows, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at present
  rcases present with rfl | rfl
  · simp only [Square, Compiler.eval_subtract, eval, Int.cast_one, one_mul,
      add_zero, remainderValue, inverseValue, auxiliaryValue]
    ring
  · simp only [Square, eval_append, eval_scale, eval, Int.cast_one, one_mul,
      add_zero, remainderValue, inverseValue, auxiliaryValue, oneValue, Int.cast_ofNat]
    calc
      _ = ((eval base remainder)⁻¹ - eval base remainder) ^ 2 +
          4 * ((eval base remainder)⁻¹ * eval base remainder) := by ring
      _ = _ := by rw [reciprocal]

theorem extend_inverse_preserves_rows (base : Nat → F) (remainder : Linear)
    (inverse auxiliary : Nat) (prior : List Row) (satisfied : Satisfies base prior)
    (disjoint : ∀ row ∈ prior, ∀ term ∈ row.a ++ row.b, term.1 ∉ [inverse, auxiliary]) :
    Satisfies (extendInverse base remainder inverse auxiliary) prior :=
  patch_preserves_rows base (inverseValues base remainder inverse auxiliary)
    [inverse, auxiliary] prior satisfied disjoint

#print axioms extend_product_preserves
#print axioms extend_product_complete
#print axioms extend_product_preserves_rows
#print axioms extend_inverse_preserves
#print axioms extend_inverse_complete
#print axioms extend_inverse_preserves_rows

end ShielddSecurity.ScalarCompletion
