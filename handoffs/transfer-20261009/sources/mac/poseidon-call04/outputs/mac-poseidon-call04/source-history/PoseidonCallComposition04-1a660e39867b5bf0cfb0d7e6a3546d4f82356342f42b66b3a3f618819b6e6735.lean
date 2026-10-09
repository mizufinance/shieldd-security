import ShielddSecurity.Poseidon
import ShielddSecurity.CompilerOrderComposition
set_option maxHeartbeats 900000
namespace ShielddSecurity.PoseidonCallComposition04
open Compiler CompilerCompletion Poseidon
variable {F : Type} [Field F]

theorem rounds_chain {width count : Nat} (parameters : Parameters F width)
    (before after : Nat → State F width) (initialState : State F width)
    (initial : before 0=initialState)
    (boundary : ∀ index,index+1<count → before (index+1)=after index)
    (roundSound : ∀ index,index<count → after index=round parameters index (before index)) :
    ∀ index,index<count → after index=rounds parameters (index+1) initialState := by
  intro index
  induction index with
  | zero =>
    intro bound
    rw [roundSound 0 bound,initial]
    rfl
  | succ index ih =>
    intro bound
    rw [roundSound (index+1) bound,boundary index bound,ih (by omega)]
    rfl

theorem emitted_append (first second : List Step) : emitted (first++second)=emitted first++emitted second := by
  induction first with
  | nil => rfl
  | cons step tail ih => simp only [List.cons_append,emitted,ih,List.append_assoc]

theorem legal_append (base : Nat → F) (first second : List Step)
    (firstLegal : Legal base first) (secondLegal : Legal (run base first) second) : Legal base (first++second) := by
  induction first generalizing base with
  | nil => exact secondLegal
  | cons step tail ih =>
    exact ⟨firstLegal.1,ih (step.run base) firstLegal.2 secondLegal⟩

theorem reverse_append (p copy : Nat) (firstRows secondRows : List Row) (first second : List Step)
    (firstCoverage : ∀ actual∈firstRows,∃ expected∈emitted first,
      canonical p (unoutline copy actual.a)=canonical p expected.a ∧ canonical p (unoutline copy actual.b)=canonical p expected.b)
    (secondCoverage : ∀ actual∈secondRows,∃ expected∈emitted second,
      canonical p (unoutline copy actual.a)=canonical p expected.a ∧ canonical p (unoutline copy actual.b)=canonical p expected.b) :
    ∀ actual∈firstRows++secondRows,∃ expected∈emitted (first++second),
      canonical p (unoutline copy actual.a)=canonical p expected.a ∧ canonical p (unoutline copy actual.b)=canonical p expected.b := by
  intro actual member
  rw [emitted_append]
  rcases List.mem_append.mp member with member|member
  · obtain ⟨expected,included,equations⟩ := firstCoverage actual member
    exact ⟨expected,List.mem_append_left _ included,equations⟩
  · obtain ⟨expected,included,equations⟩ := secondCoverage actual member
    exact ⟨expected,List.mem_append_right _ included,equations⟩

theorem topological_append_by_floor (kept : List Nat) (first second : List Step) (floor : Nat)
    (firstOrder : Topological kept [] first) (secondOrder : Topological kept [] second)
    (support : ∀ row∈emitted first,∀ term∈row.a++row.b,term.1<floor)
    (writes : ∀ column∈PoseidonCompletion.writes second,floor≤column) : Topological kept [] (first++second) := by
  apply CompilerOrderComposition.append kept [] first second firstOrder
  have extended := CompilerOrderComposition.extend kept [] (emitted first) second secondOrder
    (by intro row member term present step stepMember written
        have lower := writes term.1 (List.mem_flatMap.mpr ⟨step,stepMember,written⟩)
        exact Nat.not_le_of_lt (support row member term present) lower)
  simpa only [List.append_nil,List.nil_append] using extended
end ShielddSecurity.PoseidonCallComposition04
set_option pp.all true in
#check @ShielddSecurity.PoseidonCallComposition04.rounds_chain
#print axioms ShielddSecurity.PoseidonCallComposition04.rounds_chain
set_option pp.all true in
#check @ShielddSecurity.PoseidonCallComposition04.emitted_append
#print axioms ShielddSecurity.PoseidonCallComposition04.emitted_append
set_option pp.all true in
#check @ShielddSecurity.PoseidonCallComposition04.legal_append
#print axioms ShielddSecurity.PoseidonCallComposition04.legal_append
set_option pp.all true in
#check @ShielddSecurity.PoseidonCallComposition04.reverse_append
#print axioms ShielddSecurity.PoseidonCallComposition04.reverse_append
set_option pp.all true in
#check @ShielddSecurity.PoseidonCallComposition04.topological_append_by_floor
#print axioms ShielddSecurity.PoseidonCallComposition04.topological_append_by_floor
