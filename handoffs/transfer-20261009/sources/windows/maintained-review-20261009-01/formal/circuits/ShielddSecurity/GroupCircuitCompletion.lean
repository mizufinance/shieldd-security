import ShielddSecurity.CompilerCompletion
import ShielddSecurity.GroupRowCompletion
import ShielddSecurity.CompilerLinearCompletion

set_option maxHeartbeats 500000

namespace ShielddSecurity.GroupCircuitCompletion

variable {F : Type} [Field F]

/-- Lowered compiler stages interleaved with the actual three-write division
lowering. Folded arithmetic is represented by its existing compiler stages;
this type introduces no independent source operation or row observation. -/
inductive Step where
  | compiler (step : CompilerCompletion.Step)
  | quotient (numerator denominator remainder : Linear) (quotientColumn product auxiliary : Nat)
  | linear (input remainder : Linear) (output : Nat)

def Step.rows : Step → List Row
  | .compiler step => step.rows
  | .quotient numerator denominator remainder quotientColumn product auxiliary =>
      GroupRowCompletion.quotientRows numerator denominator remainder quotientColumn product auxiliary
  | .linear input remainder output => CompilerLinearCompletion.rows input remainder output

def Step.writes : Step → List Nat
  | .compiler step => step.writes
  | .quotient _ _ _ quotientColumn product auxiliary =>
      GroupRowCompletion.writes quotientColumn product auxiliary
  | .linear _ _ output => [output]

def Step.run (base : Nat → F) : Step → Nat → F
  | .compiler step => step.run base
  | .quotient numerator denominator remainder quotientColumn product auxiliary =>
      GroupRowCompletion.extendQuotient base numerator denominator remainder quotientColumn product auxiliary
  | .linear input remainder output => CompilerLinearCompletion.extend base input remainder output

/-- Ownership is syntactic: distinct pivots and actual input/remainder
supports disjoint from the stage's writes. It assumes no computed output. -/
def Step.Shape : Step → Prop
  | .compiler step => step.Shape
  | .quotient numerator denominator remainder quotientColumn product auxiliary =>
      quotientColumn ≠ product ∧ quotientColumn ≠ auxiliary ∧ product ≠ auxiliary ∧
        ∀ term ∈ numerator ++ denominator ++ remainder,
          term.1 ∉ GroupRowCompletion.writes quotientColumn product auxiliary
  | .linear input remainder output => ∀ term ∈ input ++ remainder, term.1 ≠ output

/-- The division denominator must be derived nonzero from the preceding
source/group stage. Compiler assertion legality is likewise independent
algorithm or legal-input semantics; it is never desired row satisfaction. -/
def Step.Legal (base : Nat → F) : Step → Prop
  | .compiler step => step.Legal base
  | .quotient _ denominator _ _ _ _ => eval base denominator ≠ 0
  | .linear _ _ _ => True

theorem step_preserves (step : Step) (base : Nat → F) (column : Nat)
    (outside : column ∉ step.writes) : step.run base column = base column := by
  cases step with
  | compiler step => exact CompilerCompletion.step_preserves step base column outside
  | quotient numerator denominator remainder quotientColumn product auxiliary =>
      exact GroupRowCompletion.extend_preserves base numerator denominator remainder
        quotientColumn product auxiliary column outside
  | linear input remainder output =>
      exact CompilerLinearCompletion.preserves base input remainder output column
        (by simpa only [Step.writes, List.mem_singleton] using outside)

theorem step_constructs (step : Step) (base : Nat → F)
    (shape : step.Shape) (legal : step.Legal base) :
    Satisfies (step.run base) step.rows := by
  cases step with
  | compiler step => exact CompilerCompletion.step_complete step base shape legal
  | quotient numerator denominator remainder quotientColumn product auxiliary =>
      exact GroupRowCompletion.extend_complete base numerator denominator remainder
        quotientColumn product auxiliary shape.1 shape.2.1 shape.2.2.1 shape.2.2.2 legal
  | linear input remainder output =>
      exact CompilerLinearCompletion.constructs base input remainder output shape

private theorem stage_preserves_prior (step : Step) (base : Nat → F) (prior : List Row)
    (initial : Satisfies base prior)
    (outside : ∀ row ∈ prior, ∀ term ∈ row.a ++ row.b, term.1 ∉ step.writes) :
    Satisfies (step.run base) prior := by
  cases step with
  | compiler step => exact CompilerCompletion.step_preserves_rows step base prior initial outside
  | quotient numerator denominator remainder quotientColumn product auxiliary =>
      exact GroupRowCompletion.preserves_rows base numerator denominator remainder
        quotientColumn product auxiliary prior initial outside
  | linear input remainder output =>
      intro row member
      have agrees (terms : Linear) (included : ∀ term ∈ terms, term ∈ row.a ++ row.b) :
          eval (CompilerLinearCompletion.extend base input remainder output) terms = eval base terms := by
        apply eval_agrees
        intro term present
        exact CompilerLinearCompletion.preserves base input remainder output term.1
          (by simpa only [Step.writes, List.mem_singleton] using
            outside row member term (included term present))
      change Square (eval (CompilerLinearCompletion.extend base input remainder output) row.a)
        (eval (CompilerLinearCompletion.extend base input remainder output) row.b)
      rw [agrees row.a (by intro term present; exact List.mem_append_left row.b present),
        agrees row.b (by intro term present; exact List.mem_append_right row.a present)]
      exact initial row member

def run (base : Nat → F) : List Step → Nat → F
  | [] => base
  | step :: tail => run (step.run base) tail

def emitted : List Step → List Row
  | [] => []
  | step :: tail => step.rows ++ emitted tail

/-- Exact supports of every preceding row and every caller-owned column
exclude each later write. Actual instances must prove this finite condition. -/
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

private theorem construct_with_prior (base : Nat → F) (steps : List Step) (kept : List Nat)
    (prior : List Row) (ordered : Topological kept prior steps) (legal : Legal base steps)
    (initial : Satisfies base prior) : Satisfies (run base steps) (prior ++ emitted steps) := by
  induction steps generalizing base prior with
  | nil => simpa [run, emitted] using initial
  | cons step tail ih =>
      have priorDone := stage_preserves_prior step base prior initial ordered.2.2.1
      have stageDone := step_constructs step base ordered.1 legal.1
      have combined : Satisfies (step.run base) (prior ++ step.rows) := by
        intro row member
        rcases List.mem_append.mp member with old | current
        · exact priorDone row old
        · exact stageDone row current
      simpa only [run, emitted, List.append_assoc] using
        ih (step.run base) (prior ++ step.rows) ordered.2.2.2 legal.2 combined

/-- Symbolic mixed-stage construction from an arbitrary base assignment.
There is no satisfaction, honest intermediate, or desired output premise. -/
theorem run_constructs (base : Nat → F) (steps : List Step) (kept : List Nat)
    (ordered : Topological kept [] steps) (legal : Legal base steps) :
    Satisfies (run base steps) (emitted steps) := by
  simpa only [List.nil_append] using
    construct_with_prior base steps kept [] ordered legal (by intro row member; cases member)

/-- Exact canonical/unoutline coverage of EVERY retained original row is
mandatory. Digests supply identities only. Shared columns remain those of the
initial assignment, including the original constant and its outlined copy. -/
theorem original_rows_complete {p : Nat} [CharP F p]
    (base : Nat → F) (steps : List Step) (kept : List Nat) (original : List Row) (copy : Nat)
    (ordered : Topological kept [] steps) (legal : Legal base steps)
    (zeroKept : 0 ∈ kept) (copyKept : copy ∈ kept) (linked : base copy = base 0)
    (coverage : ∀ actual ∈ original, ∃ expected ∈ emitted steps,
      Compiler.canonical p (Compiler.unoutline copy actual.a) = Compiler.canonical p expected.a ∧
      Compiler.canonical p (Compiler.unoutline copy actual.b) = Compiler.canonical p expected.b) :
    Satisfies (run base steps) original ∧
      (∀ column ∈ kept, run base steps column = base column) := by
  have completed := run_constructs base steps kept ordered legal
  have preserves := run_preserves base steps kept [] ordered
  have copyLink : run base steps copy = run base steps 0 := by
    rw [preserves copy copyKept, preserves 0 zeroKept, linked]
  constructor
  · intro actual member
    obtain ⟨expected, present, leftEqual, rightEqual⟩ := coverage actual member
    have result := completed expected present
    rw [← Compiler.canonical_equal (run base steps) _ _ leftEqual,
      ← Compiler.canonical_equal (run base steps) _ _ rightEqual] at result
    simpa only [Compiler.eval_unoutline (run base steps) copy _ copyLink] using result
  · exact preserves

set_option pp.all true in
#check @step_preserves
#print axioms step_preserves
set_option pp.all true in
#check @step_constructs
#print axioms step_constructs
set_option pp.all true in
#check @run_preserves
#print axioms run_preserves
set_option pp.all true in
#check @run_constructs
#print axioms run_constructs
set_option pp.all true in
#check @original_rows_complete
#print axioms original_rows_complete

end ShielddSecurity.GroupCircuitCompletion
