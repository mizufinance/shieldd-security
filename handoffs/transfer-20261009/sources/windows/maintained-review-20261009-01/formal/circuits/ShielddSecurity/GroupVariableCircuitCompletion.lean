import ShielddSecurity.GroupFixedCircuitCompletion
import ShielddSecurity.GroupCircuitSequenceCompletion

set_option maxHeartbeats 300000

namespace ShielddSecurity.GroupVariableCircuitCompletion

open GroupFixedCircuitCompletion
variable {F : Type} [Field F]

structure Tables where
  base : Linear × Linear
  twice : Linear × Linear
  triple : Linear × Linear

def Tables.terms (tables : Tables) : Linear :=
  tables.base.1 ++ tables.base.2 ++ tables.twice.1 ++ tables.twice.2 ++
    tables.triple.1 ++ tables.triple.2

def Curved (d : F) (tables : Tables) (rho : Nat → F) : Prop :=
  Group.OnCurve d (point rho tables.base) ∧
    Group.OnCurve d (point rho tables.twice) ∧
    Group.OnCurve d (point rho tables.triple)

/-- Shared variable-base tables are source coordinates, rather than constant
tables. Their initial curve facts come from the actual native precomputation.
Each local proof constructs its own rows from these independent table and bit
facts. The sequence preserves those facts using finite support certificates. -/
def LocalConstruct (d : F) (copy : Nat) (tables : Tables) (program : Program) : Prop :=
  ∀ rho : Nat → F, rho 0 = 1 → rho copy = rho 0 →
    Group.OnCurve d (point rho program.input) → Curved d tables rho →
    eval rho program.low = (if program.lowBit then 1 else 0) →
    eval rho program.high = (if program.highBit then 1 else 0) →
    Satisfies (program.build rho) program.rows ∧
      Group.OnCurve d (point (program.build rho) program.output)

theorem table_preserved (rho : Nat → F) (program : Program) (tables : Tables)
    (kept : List Nat) (protection : Protected kept program)
    (supports : ∀ term ∈ tables.terms, term.1 ∈ kept) :
    point (program.build rho) tables.base = point rho tables.base ∧
      point (program.build rho) tables.twice = point rho tables.twice ∧
      point (program.build rho) tables.triple = point rho tables.triple := by
  have agrees (terms : Linear) (inside : ∀ term ∈ terms, term ∈ tables.terms) :
      eval (program.build rho) terms = eval rho terms := by
    apply eval_agrees
    intro term member
    exact GroupCircuitOrder.run_outside rho program.stages term.1
      (by intro stage present; exact protection stage present term.1 (supports term (inside term member)))
  refine ⟨congrArg₂ Group.Point.mk ?_ ?_,congrArg₂ Group.Point.mk ?_ ?_,congrArg₂ Group.Point.mk ?_ ?_⟩
  all_goals
    apply agrees
    intro term member
    simp [Tables.terms,member]

/-- List induction covers an arbitrary number of actual variable windows.
Prior rows are the proved output of preceding owned constructors. No desired
scalar or point output is supplied: only local proofs, source adjacency,
actual support/write exclusion, initial curve tables and Boolean meanings. -/
theorem constructs (d : F) (copy : Nat) (rho : Nat → F) (tables : Tables)
    (programs : List Program) (input : Linear × Linear) (prior : List Row) (kept : List Nat)
    (constructors : ∀ program ∈ programs, LocalConstruct d copy tables program)
    (protection : ∀ program ∈ programs, Protected kept program)
    (tableSupports : ∀ term ∈ tables.terms, term.1 ∈ kept)
    (bitSupports : ∀ program ∈ programs, ∀ term ∈ program.low ++ program.high, term.1 ∈ kept)
    (fresh : Fresh prior programs) (alignment : Aligned input programs)
    (oneKept : 0 ∈ kept) (copyKept : copy ∈ kept)
    (one : rho 0 = 1) (linked : rho copy = rho 0)
    (initial : Satisfies rho prior) (incoming : Group.OnCurve d (point rho input))
    (tableCurves : Curved d tables rho)
    (bits : ∀ program ∈ programs,
      eval rho program.low = (if program.lowBit then 1 else 0) ∧
      eval rho program.high = (if program.highBit then 1 else 0)) :
    Satisfies (run rho programs) (prior ++ rows programs) ∧
      Group.OnCurve d (point (run rho programs) (output input programs)) ∧
      Curved d tables (run rho programs) ∧
      (∀ column ∈ kept, run rho programs column = rho column) := by
  induction programs generalizing rho input prior with
  | nil =>
      exact ⟨by simpa only [run,rows,List.append_nil] using initial,
        incoming,tableCurves,by intro column member; rfl⟩
  | cons program tail ih =>
      have localBits := bits program (by simp)
      have localIncoming : Group.OnCurve d (point rho program.input) := by
        rw [alignment.1]
        exact incoming
      have completed := constructors program (by simp) rho one linked localIncoming tableCurves localBits.1 localBits.2
      have previous : Satisfies (program.build rho) prior := by
        apply GroupCircuitSequenceCompletion.preserves_rows rho program.stages prior initial
        intro row member term present written
        obtain ⟨stage,stageMember,columnMember⟩ := List.mem_flatMap.mp written
        exact fresh.1 row member term present stage stageMember columnMember
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
        rw [preserves copy copyKept,preserves 0 oneKept,linked]
      have unchanged := table_preserved rho program tables kept (protection program (by simp)) tableSupports
      have nextTables : Curved d tables (program.build rho) := by
        unfold Curved
        rw [unchanged.1,unchanged.2.1,unchanged.2.2]
        exact tableCurves
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
        exact ⟨(agrees next.low (by intro term member; exact List.mem_append_left next.high member)).trans values.1,
          (agrees next.high (by intro term member; exact List.mem_append_right next.low member)).trans values.2⟩
      have rest := ih (program.build rho) program.output (prior ++ program.rows)
        (by intro next member; exact constructors next (List.mem_cons_of_mem program member))
        (by intro next member; exact protection next (List.mem_cons_of_mem program member))
        (by intro next member; exact bitSupports next (List.mem_cons_of_mem program member))
        fresh.2 alignment.2 oneBuilt linkBuilt combined completed.2 nextTables remainingBits
      refine ⟨?_,?_,?_,?_⟩
      · simpa only [run,rows,List.append_assoc] using rest.1
      · exact rest.2.1
      · exact rest.2.2.1
      · intro column member
        exact (rest.2.2.2 column member).trans (preserves column member)

set_option pp.all true in
#check @table_preserved
#print axioms table_preserved
set_option pp.all true in
#check @constructs
#print axioms constructs

end ShielddSecurity.GroupVariableCircuitCompletion
