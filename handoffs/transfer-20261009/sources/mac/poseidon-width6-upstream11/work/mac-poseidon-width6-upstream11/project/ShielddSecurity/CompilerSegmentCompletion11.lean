import ShielddSecurity.CompilerSequenceCompletion
set_option autoImplicit false
namespace ShielddSecurity.CompilerSegmentCompletion11
open Compiler CompilerCompletion
variable {F : Type} [Field F]

/-- A concrete program fragment, with local row construction and numerical frame. -/
structure Segment (F : Type) [Field F] (copy : Nat) where
  steps : List Step
  rows : List Row
  low : Nat
  high : Nat
  writes : ∀ column∈PoseidonCompletion.writes steps, low≤column ∧ column<high
  support : ∀ row∈rows,∀ term∈row.a++row.b,term.1<high ∨ term.1=copy
  complete : ∀ base : Nat → F,base copy=base 0 → Satisfies (run base steps) rows

theorem outside (copy : Nat) (segment : Segment F copy) (base : Nat → F)
    (column : Nat) (bound : column<segment.low ∨ segment.high≤column) :
    run base segment.steps column=base column := by
  apply PoseidonCompletion.run_outside
  intro member
  have limits := segment.writes column member
  omega

def append (copy : Nat) (first second : Segment F copy)
    (separated : first.high≤second.low) (ordered : first.low≤second.low)
    (high : first.high≤second.high) (zero : 0<first.low)
    (fixed : first.high≤copy ∧ second.high≤copy) : Segment F copy where
  steps := first.steps++second.steps
  rows := first.rows++second.rows
  low := first.low
  high := second.high
  writes := by
    intro column member
    simp only [PoseidonCompletion.writes,List.flatMap_append,List.mem_append] at member
    rcases member with member|member
    · have limits := first.writes column member
      omega
    · have limits := second.writes column member
      omega
  support := by
    intro row member term present
    rcases List.mem_append.mp member with member|member
    · rcases first.support row member term present with below|equal
      · exact Or.inl (by omega)
      · exact Or.inr equal
    · exact second.support row member term present
  complete := by
    intro base linked
    have copyFrame := outside copy first base copy (Or.inr fixed.1)
    have zeroFrame := outside copy first base 0 (Or.inl zero)
    have link : run base first.steps copy=run base first.steps 0 := by
      rw [copyFrame,zeroFrame]
      exact linked
    have firstDone := first.complete base linked
    have secondDone := second.complete (run base first.steps) link
    have preserved := CompilerSequenceCompletion.preserves_rows (run base first.steps)
      second.steps first.rows firstDone (by
        intro row member term present written
        have upper := first.support row member term present
        have lower := second.writes term.1 written
        rcases upper with below|equal
        · omega
        · omega)
    rw [CompilerSequenceCompletion.run_append]
    intro row member
    rcases List.mem_append.mp member with member|member
    · exact preserved row member
    · exact secondDone row member

theorem prior_preserved (copy : Nat) (segment : Segment F copy) (base : Nat → F)
    (rows : List Row) (satisfied : Satisfies base rows)
    (support : ∀ row∈rows,∀ term∈row.a++row.b,term.1<segment.low ∨ segment.high≤term.1) :
    Satisfies (run base segment.steps) rows := by
  apply CompilerSequenceCompletion.preserves_rows base segment.steps rows satisfied
  intro row member term present written
  have bounds := segment.writes term.1 written
  have excluded := support row member term present
  omega

end ShielddSecurity.CompilerSegmentCompletion11
set_option pp.all true in
#check @ShielddSecurity.CompilerSegmentCompletion11.outside
#print axioms ShielddSecurity.CompilerSegmentCompletion11.outside
set_option pp.all true in
#check @ShielddSecurity.CompilerSegmentCompletion11.append
#print axioms ShielddSecurity.CompilerSegmentCompletion11.append
set_option pp.all true in
#check @ShielddSecurity.CompilerSegmentCompletion11.prior_preserved
#print axioms ShielddSecurity.CompilerSegmentCompletion11.prior_preserved
