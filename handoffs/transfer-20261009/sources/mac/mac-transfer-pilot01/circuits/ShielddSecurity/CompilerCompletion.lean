import ShielddSecurity.ScalarCompletion

set_option maxHeartbeats 500000
set_option maxRecDepth 4096

namespace ShielddSecurity.CompilerCompletion

variable {F : Type} [Field F]

/-- Assign the actual fresh pivot of a materialized square. A fused output's
remaining linear terms are retained, rather than invented as a new column. -/
def extendSquare (base : Nat → F) (input remainder : Linear) (output : Nat) : Nat → F :=
  patchAssignment base (fun _ => (eval base input)^2 - eval base remainder) [output]

def squareRows (input remainder : Linear) (output : Nat) : List Row :=
  [⟨input, [(output, 1)] ++ remainder⟩]

theorem square_complete (base : Nat → F) (input remainder : Linear) (output : Nat)
    (fresh : ∀ term ∈ input ++ remainder, term.1 ≠ output) :
    Satisfies (extendSquare base input remainder output) (squareRows input remainder output) := by
  let rho := extendSquare base input remainder output
  have agrees (terms : Linear) (included : ∀ term ∈ terms, term ∈ input ++ remainder) :
      eval rho terms = eval base terms := by
    apply eval_agrees
    intro term member
    exact patchAssignment_preserves base _ [output] term.1
      (by simpa only [List.mem_singleton] using fresh term (included term member))
  have inputValue := agrees input (by intro term member; exact List.mem_append_left remainder member)
  have remainderValue := agrees remainder (by intro term member; exact List.mem_append_right input member)
  have outputValue : rho output = (eval base input)^2 - eval base remainder := by
    simp [rho, extendSquare, patchAssignment]
  simp only [rho] at inputValue remainderValue outputValue
  intro row member
  simp only [squareRows, List.mem_singleton] at member
  subst row
  simp only [Square, eval_append, eval, Int.cast_one, one_mul, add_zero,
    inputValue, remainderValue, outputValue]
  ring

/-- These are lowered compiler row constructors, not new source operations.
Deferred/folded source expressions contribute no rows. Their exact source DAG
semantics remain the existing Compiler/Poseidon graph-certificate obligation. -/
inductive Step where
  | square (input remainder : Linear) (output : Nat)
  | product (left right remainder : Linear) (output auxiliary : Nat)
  | equal (left right : Linear)
  | squareEqual (input target : Linear)

def Step.rows : Step → List Row
  | .square input remainder output => squareRows input remainder output
  | .product left right remainder output auxiliary =>
      ScalarCompletion.productRows left right remainder output auxiliary
  | .equal left right => [⟨Compiler.subtract left right, []⟩]
  | .squareEqual input target => [⟨input, target⟩]

def Step.writes : Step → List Nat
  | .square _ _ output => [output]
  | .product _ _ _ output auxiliary => [output, auxiliary]
  | .equal _ _ | .squareEqual _ _ => []

def Step.run (base : Nat → F) : Step → Nat → F
  | .square input remainder output => extendSquare base input remainder output
  | .product left right remainder output auxiliary =>
      ScalarCompletion.extendProduct base left right remainder output auxiliary
  | .equal _ _ | .squareEqual _ _ => base

/-- Only structural freshness/pivot checks, never a satisfaction premise. -/
def Step.Shape : Step → Prop
  | .square input remainder output => ∀ term ∈ input ++ remainder, term.1 ≠ output
  | .product left right remainder output auxiliary => output ≠ auxiliary ∧
      ∀ term ∈ left ++ right ++ remainder, term.1 ∉ [output, auxiliary]
  | .equal _ _ | .squareEqual _ _ => True

/-- Assertion equalities are an explicit legal-input boundary. An actual
instance must derive them from independently specified algorithm/legal-input
semantics; a list of these equalities is not a full Transfer completeness proof.
Materialization steps need no honest-witness or desired-row-value premise. -/
def Step.Legal (base : Nat → F) : Step → Prop
  | .square _ _ _ | .product _ _ _ _ _ => True
  | .equal left right => eval base left = eval base right
  | .squareEqual input target => eval base input * eval base input = eval base target

theorem step_preserves (step : Step) (base : Nat → F) (column : Nat)
    (outside : column ∉ step.writes) : step.run base column = base column := by
  cases step with
  | square input remainder output =>
      simpa only [Step.run, extendSquare] using
        (patchAssignment_preserves base (fun _ => (eval base input)^2 - eval base remainder) [output] column outside)
  | product left right remainder output auxiliary =>
      exact ScalarCompletion.extend_product_preserves base left right remainder output auxiliary column outside
  | equal left right => rfl
  | squareEqual input target => rfl

theorem step_complete (step : Step) (base : Nat → F)
    (shape : step.Shape) (legal : step.Legal base) : Satisfies (step.run base) step.rows := by
  cases step with
  | square input remainder output => exact square_complete base input remainder output shape
  | product left right remainder output auxiliary =>
      exact ScalarCompletion.extend_product_complete base left right remainder output auxiliary shape.1 shape.2
  | equal left right =>
      intro row member
      simp only [Step.rows, List.mem_singleton] at member
      subst row
      change Square (eval base (Compiler.subtract left right)) (eval base [])
      rw [Compiler.eval_subtract, show eval base left = eval base right from legal]
      simp [Square, eval]
  | squareEqual input target =>
      intro row member
      simp only [Step.rows, List.mem_singleton] at member
      subst row
      exact legal

theorem step_preserves_rows (step : Step) (base : Nat → F) (prior : List Row)
    (satisfied : Satisfies base prior)
    (disjoint : ∀ row ∈ prior, ∀ term ∈ row.a ++ row.b, term.1 ∉ step.writes) :
    Satisfies (step.run base) prior := by
  intro row member
  have agrees (terms : Linear) (included : ∀ term ∈ terms, term ∈ row.a ++ row.b) :
      eval (step.run base) terms = eval base terms := by
    apply eval_agrees
    intro term present
    exact step_preserves step base term.1 (disjoint row member term (included term present))
  rw [agrees row.a (by intro term present; exact List.mem_append_left row.b present),
    agrees row.b (by intro term present; exact List.mem_append_right row.a present)]
  exact satisfied row member

def run (base : Nat → F) : List Step → Nat → F
  | [] => base
  | step :: tail => run (step.run base) tail

def emitted : List Step → List Row
  | [] => []
  | step :: tail => step.rows ++ emitted tail

/-- Every later write must exclude both sides of every previously completed
row, plus fixed/public/caller-owned columns. Future consumers are completed in
their own stage; their satisfaction is never presumed before they are built. -/
def Topological (kept : List Nat) (prior : List Row) : List Step → Prop
  | [] => True
  | step :: tail => step.Shape ∧
      (∀ column ∈ kept, column ∉ step.writes) ∧
      (∀ row ∈ prior, ∀ term ∈ row.a ++ row.b, term.1 ∉ step.writes) ∧
      Topological kept (prior ++ step.rows) tail

def Legal (base : Nat → F) : List Step → Prop
  | [] => True
  | step :: tail => step.Legal base ∧ Legal (step.run base) tail

theorem run_preserves (base : Nat → F) (steps : List Step) (kept : List Nat)
    (prior : List Row) (ordered : Topological kept prior steps)
    (column : Nat) (member : column ∈ kept) : run base steps column = base column := by
  induction steps generalizing base prior with
  | nil => rfl
  | cons step tail ih =>
      exact (ih (step.run base) (prior ++ step.rows) ordered.2.2.2).trans
        (step_preserves step base column (ordered.2.1 column member))

/-- Constructive finite composition. Its recursion is on symbolic stages, not
an unrolled walk through 201396 constraints. Exact original-row coverage and
the derivation of legal assertions are separate mandatory instance obligations. -/
theorem run_complete (base : Nat → F) (steps : List Step) (kept : List Nat)
    (prior : List Row) (ordered : Topological kept prior steps) (legal : Legal base steps)
    (initial : Satisfies base prior) : Satisfies (run base steps) (prior ++ emitted steps) := by
  induction steps generalizing base prior with
  | nil => simpa [run, emitted] using initial
  | cons step tail ih =>
      have previous := step_preserves_rows step base prior initial ordered.2.2.1
      have current := step_complete step base ordered.1 legal.1
      have combined : Satisfies (step.run base) (prior ++ step.rows) := by
        intro row member
        rcases List.mem_append.mp member with member | member
        · exact previous row member
        · exact current row member
      simpa only [run, emitted, List.append_assoc] using
        ih (step.run base) (prior ++ step.rows) ordered.2.2.2 legal.2 combined

/-- Transport covers EVERY original row, not merely the observer's selected
8636 rows or an 18-column slice. The finite coverage certificate must bind
actual complete ordered row data to these stage rows; hashes do not supply it. -/
theorem original_rows_complete {p : Nat} [CharP F p]
    (base : Nat → F) (steps : List Step) (kept : List Nat) (original : List Row) (copy : Nat)
    (ordered : Topological kept [] steps) (legal : Legal base steps)
    (zeroKept : 0 ∈ kept) (copyKept : copy ∈ kept) (linked : base copy = base 0)
    (coverage : ∀ actual ∈ original, ∃ expected ∈ emitted steps,
      Compiler.canonical p (Compiler.unoutline copy actual.a) = Compiler.canonical p expected.a ∧
      Compiler.canonical p (Compiler.unoutline copy actual.b) = Compiler.canonical p expected.b) :
    Satisfies (run base steps) original ∧
      (∀ column ∈ kept, run base steps column = base column) := by
  have completed := run_complete base steps kept [] ordered legal (by intro row member; cases member)
  have preserves := run_preserves base steps kept [] ordered
  have copyLink : run base steps copy = run base steps 0 := by
    rw [preserves copy copyKept, preserves 0 zeroKept, linked]
  constructor
  · intro actual member
    obtain ⟨expected, present, left, right⟩ := coverage actual member
    have result := completed expected (by simpa using present)
    rw [← Compiler.canonical_equal (run base steps) _ _ left,
      ← Compiler.canonical_equal (run base steps) _ _ right] at result
    simpa only [Compiler.eval_unoutline (run base steps) copy _ copyLink] using result
  · exact preserves

set_option pp.all true in
#check @square_complete
#print axioms square_complete
set_option pp.all true in
#check @step_preserves
#print axioms step_preserves
set_option pp.all true in
#check @step_complete
#print axioms step_complete
set_option pp.all true in
#check @step_preserves_rows
#print axioms step_preserves_rows
set_option pp.all true in
#check @run_preserves
#print axioms run_preserves
set_option pp.all true in
#check @run_complete
#print axioms run_complete
set_option pp.all true in
#check @original_rows_complete
#print axioms original_rows_complete

end ShielddSecurity.CompilerCompletion
