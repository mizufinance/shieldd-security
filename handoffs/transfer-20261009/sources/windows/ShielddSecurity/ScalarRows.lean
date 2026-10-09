import ShielddSecurity.Compiler
import ShielddSecurity.Scalar

set_option maxHeartbeats 500000

namespace ShielddSecurity.ScalarRows

variable {F : Type} [Field F]

/-- Finite data for the compiler's original product encodings. This is neither
an honest evaluator nor an assumed multiplication equation. -/
inductive ProductData where
  | foldedLeft (coefficient : Int)
  | foldedRight (coefficient : Int)
  | square
  | product (auxiliary : Linear)

def checkProduct (p : Nat) (rows : List Row) (left right output : Linear) :
    ProductData → Bool
  | .foldedLeft coefficient => decide
      (Compiler.canonical p left = Compiler.canonical p [(0, coefficient)] ∧
       Compiler.canonical p output = Compiler.canonical p (scaleLinear coefficient right))
  | .foldedRight coefficient => decide
      (Compiler.canonical p right = Compiler.canonical p [(0, coefficient)] ∧
       Compiler.canonical p output = Compiler.canonical p (scaleLinear coefficient left))
  | .square => decide (Compiler.canonical p left = Compiler.canonical p right) &&
      Compiler.checkRow p rows ⟨left, output⟩
  | .product auxiliary =>
      Compiler.checkRow p rows ⟨Compiler.subtract left right, auxiliary⟩ &&
      Compiler.checkRow p rows ⟨left ++ right, auxiliary ++ scaleLinear 4 output⟩

theorem checked_product_sound {p : Nat} [CharP F p]
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (rows : List Row) (satisfied : Satisfies rho rows)
    (left right output : Linear) (data : ProductData)
    (checked : checkProduct p rows left right output data = true) :
    eval rho output = eval rho left * eval rho right := by
  cases data with
  | foldedLeft coefficient =>
      have checks := of_decide_eq_true checked
      have constant : eval rho left = (coefficient : F) := by
        simpa [eval, one] using Compiler.canonical_equal rho left [(0, coefficient)] checks.1
      have folded := Compiler.canonical_equal rho output (scaleLinear coefficient right) checks.2
      simpa only [eval_scale, constant] using folded
  | foldedRight coefficient =>
      have checks := of_decide_eq_true checked
      have constant : eval rho right = (coefficient : F) := by
        simpa [eval, one] using Compiler.canonical_equal rho right [(0, coefficient)] checks.1
      have folded := Compiler.canonical_equal rho output (scaleLinear coefficient left) checks.2
      simpa only [eval_scale, constant, mul_comm] using folded
  | square =>
      simp only [checkProduct, Bool.and_eq_true, decide_eq_true_eq] at checked
      have same := Compiler.canonical_equal rho left right checked.1
      rw [← same]
      exact Compiler.checked_square_sound rho rows left output satisfied checked.2
  | product auxiliary =>
      simp only [checkProduct, Bool.and_eq_true] at checked
      exact Compiler.checked_product_sound rho rows left right output auxiliary four
        satisfied checked.1 checked.2

structure StepData where
  before : Linear
  left : Linear
  after : Linear
  right : Bool
  factor : Linear
  target : Linear
  product : ProductData

def factor (step : StepData) : Linear :=
  if step.right then step.left else [(0, 1)] ++ scaleLinear (-1) step.left

def target (step : StepData) : Linear :=
  if step.right then step.after ++ step.left ++ [(0, -1)] else step.after

def checkStep (p : Nat) (rows : List Row) (step : StepData) : Bool :=
  decide (Compiler.canonical p step.factor = Compiler.canonical p (factor step) ∧
    Compiler.canonical p step.target = Compiler.canonical p (target step)) &&
  checkProduct p rows step.before step.factor step.target step.product

theorem checked_step_sound {p : Nat} [CharP F p]
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (rows : List Row) (satisfied : Satisfies rho rows) (step : StepData)
    (checked : checkStep p rows step = true) :
    eval rho step.after = Scalar.comparisonPolynomial (eval rho step.before)
      (eval rho step.left) (if step.right then 1 else 0) := by
  simp only [checkStep, Bool.and_eq_true, decide_eq_true_eq] at checked
  have factorValue := Compiler.canonical_equal rho step.factor (factor step) checked.1.1
  have targetValue := Compiler.canonical_equal rho step.target (target step) checked.1.2
  have multiplication := checked_product_sound rho one four rows satisfied
    step.before step.factor step.target step.product checked.2
  rw [factorValue, targetValue] at multiplication
  cases right : step.right
  · simp only [factor, target, right, Bool.false_eq_true, ↓reduceIte,
      eval_append, eval_scale, eval, one] at multiplication ⊢
    simpa [Scalar.comparisonPolynomial, sub_eq_add_neg] using multiplication
  · simp only [factor, target, right, ↓reduceIte, eval_append, eval, one] at multiplication ⊢
    unfold Scalar.comparisonPolynomial
    calc
      eval rho step.after =
          (eval rho step.after + eval rho step.left - 1) + 1 - eval rho step.left := by ring
      _ = 1 - eval rho step.left + eval rho step.before * eval rho step.left := by
        have rearranged : eval rho step.after + eval rho step.left - 1 =
            eval rho step.before * eval rho step.left := by
          simpa [sub_eq_add_neg, add_assoc] using multiplication
        rw [rearranged]
        ring
      _ = _ := by ring

/-- Symbolic traversal over actual selected comparator steps. Each step retains
its own original rows; only the finite data checks, not security conclusions,
are evaluated by the kernel. List adjacency binds the preceding field state. -/
def checkChain (p : Nat) (rows : List Row) : Linear → List StepData → Bool
  | _, [] => true
  | previous, step :: tail =>
      (decide (Compiler.canonical p step.before = Compiler.canonical p previous) &&
        checkStep p rows step) && checkChain p rows step.after tail

def evaluateChain (rho : Nat → F) : Linear → List StepData → F
  | previous, [] => eval rho previous
  | _, step :: tail => evaluateChain rho step.after tail

def polynomialChain (rho : Nat → F) : F → List StepData → F
  | previous, [] => previous
  | previous, step :: tail => polynomialChain rho
      (Scalar.comparisonPolynomial previous (eval rho step.left) (if step.right then 1 else 0)) tail

theorem checked_chain_sound {p : Nat} [CharP F p]
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (rows : List Row) (satisfied : Satisfies rho rows)
    (previous : Linear) (steps : List StepData)
    (checked : checkChain p rows previous steps = true) :
    evaluateChain rho previous steps = polynomialChain rho (eval rho previous) steps := by
  induction steps generalizing previous with
  | nil => rfl
  | cons step tail ih =>
      simp only [checkChain, Bool.and_eq_true, decide_eq_true_eq] at checked
      have boundary := Compiler.canonical_equal rho step.before previous checked.1.1
      have stepValue := checked_step_sound rho one four rows satisfied step checked.1.2
      rw [boundary] at stepValue
      change evaluateChain rho step.after tail =
        polynomialChain rho (Scalar.comparisonPolynomial (eval rho previous)
          (eval rho step.left) (if step.right then 1 else 0)) tail
      rw [ih step.after checked.2, stepValue]

#print axioms checked_product_sound
#print axioms checked_step_sound
#print axioms checked_chain_sound

end ShielddSecurity.ScalarRows
