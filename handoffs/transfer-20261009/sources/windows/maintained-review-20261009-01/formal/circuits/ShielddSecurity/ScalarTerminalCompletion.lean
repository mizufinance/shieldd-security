import ShielddSecurity.ScalarCompletion

set_option maxHeartbeats 500000
set_option maxRecDepth 4096

namespace ShielddSecurity.ScalarTerminalCompletion

variable {F : Type} [Field F]

/-- The completion instance certifies the original row orientation/coefficients
against its constructed row, under the actual characteristic. -/
theorem canonical_row_complete {p : Nat} [CharP F p] (rho : Nat → F)
    (actual expected : Row)
    (left : Compiler.canonical p actual.a = Compiler.canonical p expected.a)
    (right : Compiler.canonical p actual.b = Compiler.canonical p expected.b)
    (completed : Square (eval rho expected.a) (eval rho expected.b)) :
    Square (eval rho actual.a) (eval rho actual.b) := by
  rw [Compiler.canonical_equal rho actual.a expected.a left,
    Compiler.canonical_equal rho actual.b expected.b right]
  exact completed

/-- Reverse the same source-column outlining used by the soundness lane. The
constant-copy equality must be preserved, rather than inferred from metadata. -/
theorem unoutline_complete (rho : Nat → F) (copy : Nat) (original : List Row)
    (linked : rho copy = rho 0) (completed : Satisfies rho (Compiler.unoutlineRows copy original)) :
    Satisfies rho original := by
  intro row member
  have normalized := completed ⟨Compiler.unoutline copy row.a, Compiler.unoutline copy row.b⟩
    (List.mem_map.mpr ⟨row, member, rfl⟩)
  simpa only [Compiler.eval_unoutline rho copy _ linked] using normalized

/-- The actual compiler product output is a fresh column. Its assertion is a
separate original row, rather than substituting zero/one into the product rows. -/
def terminalRows (left right target : Linear) (output auxiliary : Nat) : List Row :=
  ScalarCompletion.productRows left right [] output auxiliary ++
    [⟨Compiler.subtract target [(output, 1)], []⟩]

def extendTerminal (base : Nat → F) (left right : Linear)
    (output auxiliary : Nat) : Nat → F :=
  ScalarCompletion.extendProduct base left right [] output auxiliary

theorem preserves (base : Nat → F) (left right : Linear)
    (output auxiliary column : Nat) (outside : column ∉ [output, auxiliary]) :
    extendTerminal base left right output auxiliary column = base column :=
  ScalarCompletion.extend_product_preserves base left right [] output auxiliary column outside

/-- This is legal-input completion, not arbitrary-assignment soundness. The
legal condition must follow from the preceding actual comparator/inverse stage.
Freshness explicitly preserves column zero and all prior nonowned columns. -/
theorem complete (base : Nat → F) (left right target : Linear)
    (output auxiliary : Nat) (distinct : output ≠ auxiliary)
    (constantFresh : 0 ∉ [output, auxiliary])
    (fresh : ∀ term ∈ left ++ right ++ target, term.1 ∉ [output, auxiliary])
    (legal : eval base left * eval base right = eval base target) :
    Satisfies (extendTerminal base left right output auxiliary)
      (terminalRows left right target output auxiliary) := by
  let rho := extendTerminal base left right output auxiliary
  have product : Satisfies rho (ScalarCompletion.productRows left right [] output auxiliary) :=
    ScalarCompletion.extend_product_complete base left right [] output auxiliary distinct
      (by
        intro term member
        apply fresh term
        have member' : term ∈ left ++ right := by
          simpa only [List.append_nil] using member
        exact List.mem_append_left target member')
  have targetValue : eval rho target = eval base target := by
    apply eval_agrees
    intro term member
    exact preserves base left right output auxiliary term.1
      (fresh term (List.mem_append_right (left ++ right) member))
  have outputValue : rho output = eval base left * eval base right := by
    simp [rho, extendTerminal, ScalarCompletion.extendProduct,
      ScalarCompletion.productValues, patchAssignment, eval]
  intro row member
  simp only [terminalRows, List.mem_append, List.mem_singleton] at member
  rcases member with member | rfl
  · exact product row member
  · change Square (eval rho (Compiler.subtract target [(output, 1)])) (eval rho [])
    rw [Compiler.eval_subtract, targetValue]
    have outputEval : eval rho [(output, 1)] = eval base target := by
      simpa only [eval, Int.cast_one, mul_one, one_mul, add_zero] using
        outputValue.trans legal
    rw [outputEval]
    simp [Square, eval]

theorem preserves_one (base : Nat → F) (left right : Linear)
    (output auxiliary : Nat) (constantFresh : 0 ∉ [output, auxiliary])
    (one : base 0 = 1) :
    extendTerminal base left right output auxiliary 0 = 1 :=
  (preserves base left right output auxiliary 0 constantFresh).trans one

theorem preserves_prior (base : Nat → F) (left right : Linear)
    (output auxiliary : Nat) (prior : List Row) (satisfied : Satisfies base prior)
    (disjoint : ∀ row ∈ prior, ∀ term ∈ row.a ++ row.b, term.1 ∉ [output, auxiliary]) :
    Satisfies (extendTerminal base left right output auxiliary) prior :=
  ScalarCompletion.extend_product_preserves_rows base left right [] output auxiliary
    prior satisfied disjoint

/-- Allocate the dedicated inverse witness before completing its actual fresh
product output/auxiliary and separate assertion-one row. It is distinct from the
quotient-eight guard, and requires a nonzero legal input. -/
def assignInverse (base : Nat → F) (input : Linear) (inverse : Nat) : Nat → F :=
  patchAssignment base (fun _ => (eval base input)⁻¹) [inverse]

theorem inverse_preserves (base : Nat → F) (input : Linear)
    (inverse column : Nat) (outside : column ≠ inverse) :
    assignInverse base input inverse column = base column :=
  patchAssignment_preserves base (fun _ => (eval base input)⁻¹) [inverse] column
    (by simpa only [List.mem_singleton] using outside)

theorem inverse_product (base : Nat → F) (input : Linear) (inverse : Nat)
    (constantFresh : inverse ≠ 0)
    (fresh : ∀ term ∈ input, term.1 ≠ inverse) (legal : eval base input ≠ 0) :
    eval (assignInverse base input inverse) [(inverse, 1)] *
      eval (assignInverse base input inverse) input = 1 := by
  have inputValue : eval (assignInverse base input inverse) input = eval base input := by
    apply eval_agrees
    intro term member
    exact inverse_preserves base input inverse term.1 (fresh term member)
  have inverseValue : assignInverse base input inverse inverse = (eval base input)⁻¹ := by
    simp [assignInverse, patchAssignment]
  simpa only [eval, Int.cast_one, mul_one, one_mul, add_zero, inverseValue, inputValue]
    using inv_mul_cancel₀ legal

theorem inverse_preserves_one (base : Nat → F) (input : Linear)
    (inverse : Nat) (constantFresh : inverse ≠ 0) (one : base 0 = 1) :
    assignInverse base input inverse 0 = 1 :=
  (inverse_preserves base input inverse 0 (Ne.symm constantFresh)).trans one

theorem inverse_preserves_prior (base : Nat → F) (input : Linear)
    (inverse : Nat) (prior : List Row) (satisfied : Satisfies base prior)
    (disjoint : ∀ row ∈ prior, ∀ term ∈ row.a ++ row.b, term.1 ≠ inverse) :
    Satisfies (assignInverse base input inverse) prior :=
  patch_preserves_rows base (fun _ => (eval base input)⁻¹) [inverse] prior satisfied
    (by intro row member term present; simpa only [List.mem_singleton] using disjoint row member term present)

#print axioms complete
#print axioms canonical_row_complete
#print axioms unoutline_complete
#print axioms preserves
#print axioms preserves_one
#print axioms preserves_prior
#print axioms inverse_preserves
#print axioms inverse_product
#print axioms inverse_preserves_one
#print axioms inverse_preserves_prior

end ShielddSecurity.ScalarTerminalCompletion
