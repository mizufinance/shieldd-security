import ShielddSecurity.GroupCircuitOrder
import ShielddSecurity.GroupWindows

set_option maxHeartbeats 500000

namespace ShielddSecurity.GroupFixedCircuitCompletion

structure Program where
  stages : List GroupCircuitCompletion.Step
  rows : List Row
  input : Linear × Linear
  output : Linear × Linear
  low : Linear
  high : Linear
  lowBit : Bool
  highBit : Bool

variable {F : Type} [Field F]

def point (rho : Nat → F) (coordinates : Linear × Linear) : Group.Point F :=
  ⟨eval rho coordinates.1, eval rho coordinates.2⟩

def Program.build (program : Program) (rho : Nat → F) : Nat → F :=
  GroupCircuitCompletion.run rho program.stages

/-- This local constructor contract is discharged by each maintained actual
window proof, never imported as an unchecked metadata assertion. Its inputs
are independent curve/bit/caller meanings, and its outputs are proved rows and
the outgoing invariant. An actual whole-loop leaf must supply every proof. -/
def LocalConstruct (d : F) (copy : Nat) (program : Program) : Prop :=
  ∀ rho : Nat → F, rho 0 = 1 → rho copy = rho 0 →
    Group.OnCurve d (point rho program.input) →
    eval rho program.low = (if program.lowBit then 1 else 0) →
    eval rho program.high = (if program.highBit then 1 else 0) →
    Satisfies (program.build rho) program.rows ∧
      Group.OnCurve d (point (program.build rho) program.output)

def Protected (kept : List Nat) (program : Program) : Prop :=
  ∀ stage ∈ program.stages, ∀ column ∈ kept, column ∉ stage.writes

def Fresh (prior : List Row) : List Program → Prop
  | [] => True
  | program :: tail =>
      (∀ row ∈ prior, ∀ term ∈ row.a ++ row.b,
        ∀ stage ∈ program.stages, term.1 ∉ stage.writes) ∧
      Fresh (prior ++ program.rows) tail

def Aligned (input : Linear × Linear) : List Program → Prop
  | [] => True
  | program :: tail => program.input = input ∧ Aligned program.output tail

def output (input : Linear × Linear) : List Program → Linear × Linear
  | [] => input
  | program :: tail => output program.output tail

def run (rho : Nat → F) : List Program → Nat → F
  | [] => rho
  | program :: tail => run (program.build rho) tail

def rows : List Program → List Row
  | [] => []
  | program :: tail => program.rows ++ rows tail

theorem run_preserves (rho : Nat → F) (programs : List Program) (kept : List Nat)
    (protection : ∀ program ∈ programs, Protected kept program)
    (column : Nat) (member : column ∈ kept) : run rho programs column = rho column := by
  induction programs generalizing rho with
  | nil => rfl
  | cons program tail ih =>
      exact (ih (program.build rho)
        (by intro next present; exact protection next (List.mem_cons_of_mem _ present))).trans
        (GroupCircuitOrder.run_outside rho program.stages column
          (by intro stage present; exact protection program (by simp) stage present column member))

private theorem build_preserves_rows (rho : Nat → F) (program : Program) (prior : List Row)
    (initial : Satisfies rho prior)
    (fresh : ∀ row ∈ prior, ∀ term ∈ row.a ++ row.b,
      ∀ stage ∈ program.stages, term.1 ∉ stage.writes) :
    Satisfies (program.build rho) prior := by
  intro row member
  have agrees (terms : Linear) (inside : ∀ term ∈ terms, term ∈ row.a ++ row.b) :
      eval (program.build rho) terms = eval rho terms := by
    apply eval_agrees
    intro term present
    exact GroupCircuitOrder.run_outside rho program.stages term.1
      (fresh row member term (inside term present))
  change Square (eval (program.build rho) row.a) (eval (program.build rho) row.b)
  rw [agrees row.a (by intro term present; exact List.mem_append_left row.b present),
    agrees row.b (by intro term present; exact List.mem_append_right row.a present)]
  exact initial row member

/-- Symbolic induction in the number of programs, including126 windows. No
wide row walk or desired scalar/output invariant is assumed. Exact original
row ownership, bit supports, source adjacency and all local constructor proofs
remain mandatory when this rule is instantiated from actual captures. -/
theorem constructs (d : F) (copy : Nat) (rho : Nat → F) (programs : List Program)
    (input : Linear × Linear) (prior : List Row) (kept : List Nat)
    (constructors : ∀ program ∈ programs, LocalConstruct d copy program)
    (protection : ∀ program ∈ programs, Protected kept program)
    (bitSupports : ∀ program ∈ programs, ∀ term ∈ program.low ++ program.high, term.1 ∈ kept)
    (fresh : Fresh prior programs) (alignment : Aligned input programs)
    (oneKept : 0 ∈ kept) (copyKept : copy ∈ kept)
    (one : rho 0 = 1) (linked : rho copy = rho 0)
    (initial : Satisfies rho prior) (incoming : Group.OnCurve d (point rho input))
    (bits : ∀ program ∈ programs,
      eval rho program.low = (if program.lowBit then 1 else 0) ∧
      eval rho program.high = (if program.highBit then 1 else 0)) :
    Satisfies (run rho programs) (prior ++ rows programs) ∧
      Group.OnCurve d (point (run rho programs) (output input programs)) ∧
      (∀ column ∈ kept, run rho programs column = rho column) := by
  induction programs generalizing rho input prior with
  | nil =>
      have preserved : ∀ column ∈ kept, rho column = rho column := by
        intro column member
        rfl
      exact ⟨by simpa only [run, rows, List.append_nil] using initial,
        incoming, preserved⟩
  | cons program tail ih =>
      have localBits := bits program (by simp)
      have localIncoming : Group.OnCurve d (point rho program.input) := by
        rw [alignment.1]
        exact incoming
      have completed := constructors program (by simp) rho one linked localIncoming localBits.1 localBits.2
      have previous := build_preserves_rows rho program prior initial fresh.1
      have combined : Satisfies (program.build rho) (prior ++ program.rows) := by
        intro row member
        rcases List.mem_append.mp member with before | now
        · exact previous row before
        · exact completed.1 row now
      have preserves (column : Nat) (member : column ∈ kept) : program.build rho column = rho column :=
        GroupCircuitOrder.run_outside rho program.stages column
          (by intro stage present; exact protection program (by simp) stage present column member)
      have oneBuilt : program.build rho 0 = 1 := (preserves 0 oneKept).trans one
      have linkBuilt : program.build rho copy = program.build rho 0 := by
        rw [preserves copy copyKept, preserves 0 oneKept, linked]
      have remainingBits : ∀ next ∈ tail,
          eval (program.build rho) next.low = (if next.lowBit then 1 else 0) ∧
          eval (program.build rho) next.high = (if next.highBit then 1 else 0) := by
        intro next member
        have present := List.mem_cons_of_mem program member
        have values := bits next present
        have agrees (terms : Linear) (inside : ∀ term ∈ terms, term ∈ next.low ++ next.high) :
            eval (program.build rho) terms = eval rho terms := by
          apply eval_agrees
          intro term member
          exact preserves term.1 (bitSupports next present term (inside term member))
        constructor
        · exact (agrees next.low (by intro term member; exact List.mem_append_left next.high member)).trans values.1
        · exact (agrees next.high (by intro term member; exact List.mem_append_right next.low member)).trans values.2
      have rest := ih (program.build rho) program.output (prior ++ program.rows)
        (by intro next member; exact constructors next (List.mem_cons_of_mem program member))
        (by intro next member; exact protection next (List.mem_cons_of_mem program member))
        (by intro next member; exact bitSupports next (List.mem_cons_of_mem program member))
        fresh.2 alignment.2 oneBuilt linkBuilt combined completed.2 remainingBits
      refine ⟨?_, ?_, ?_⟩
      · simpa only [run, rows, List.append_assoc] using rest.1
      · exact rest.2.1
      · intro column member
        exact (rest.2.2 column member).trans (preserves column member)

set_option pp.all true in
#check @run_preserves
#print axioms run_preserves
set_option pp.all true in
#check @constructs
#print axioms constructs

end ShielddSecurity.GroupFixedCircuitCompletion
