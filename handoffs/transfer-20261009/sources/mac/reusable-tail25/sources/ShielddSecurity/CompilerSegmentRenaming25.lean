import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerSegmentCompletion11
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CompilerSegmentRenaming25
open Compiler CompilerCompletion CompilerColumnRenaming05 CompilerWindowRenaming05
open CompilerSegmentCompletion11

theorem mapped_writes (rename : Nat → Nat) (program : List Step) :
    PoseidonCompletion.writes (steps rename program)=(PoseidonCompletion.writes program).map rename := by
  induction program with
  | nil => rfl
  | cons head tail ih =>
    simp only [steps,List.map_cons,PoseidonCompletion.writes,List.flatMap_cons,List.map_append] at *
    rw [ih]
    cases head <;> rfl

theorem mapped_support (rename : Nat → Nat) (original : List Row)
    (predicate : Nat → Prop)
    (support : ∀ value∈original,∀ term∈value.a++value.b,predicate (rename term.1)) :
    ∀ value∈rows rename original,∀ term∈value.a++value.b,predicate term.1 := by
  intro value member term present
  obtain ⟨old,oldMember,rfl⟩ := List.mem_map.mp member
  change term∈linear rename old.a++linear rename old.b at present
  have mapped : linear rename old.a++linear rename old.b=linear rename (old.a++old.b) := by
    simp only [linear,List.map_append]
  rw [mapped] at present
  obtain ⟨source,sourceMember,rfl⟩ := List.mem_map.mp present
  exact support old oldMember source sourceMember

variable {F : Type} [Field F]
def translated (copy start width offset : Nat) (source : Segment F copy)
    (separate : width≤offset) (startPositive : 0<start)
    (insideLow : start≤source.low) (insideHigh : source.high≤start+width)
    (copyAbove : start+offset+width≤copy) : Segment F copy where
  steps := steps (swap start width offset) source.steps
  rows := rows (swap start width offset) source.rows
  low := source.low+offset
  high := source.high+offset
  writes := by
    intro column member
    rw [mapped_writes] at member
    obtain ⟨old,present,rfl⟩ := List.mem_map.mp member
    have bounds := source.writes old present
    rw [CompilerWindowRenaming05.translated start width offset old (by omega) (by omega)]
    omega
  support := by
    apply mapped_support (swap start width offset) source.rows (fun c => c<source.high+offset ∨ c=copy)
    intro value member term present
    rcases source.support value member term present with below|fixed
    · apply Or.inl
      unfold swap
      split_ifs <;> omega
    · apply Or.inr
      rw [fixed]
      exact above_fixed start width offset copy separate copyAbove
  complete := by
    intro base linked
    apply completed_rows _ (CompilerWindowRenaming05.injective start width offset separate)
    apply source.complete
    rw [above_fixed start width offset copy separate copyAbove,
      below_fixed start width offset 0 startPositive]
    exact linked

theorem frame (copy start width offset : Nat) (source : Segment F copy)
    (separate : width≤offset) (startPositive : 0<start)
    (insideLow : start≤source.low) (insideHigh : source.high≤start+width)
    (copyAbove : start+offset+width≤copy) (base : Nat → F) (column : Nat)
    (outside : column<source.low+offset ∨ source.high+offset≤column) :
    run base (translated copy start width offset source separate startPositive insideLow insideHigh copyAbove).steps column=base column :=
  CompilerSegmentCompletion11.outside copy _ base column outside
end ShielddSecurity.CompilerSegmentRenaming25

set_option pp.all true in
#check @ShielddSecurity.CompilerSegmentRenaming25.mapped_writes
#print axioms ShielddSecurity.CompilerSegmentRenaming25.mapped_writes
set_option pp.all true in
#check @ShielddSecurity.CompilerSegmentRenaming25.mapped_support
#print axioms ShielddSecurity.CompilerSegmentRenaming25.mapped_support
set_option pp.all true in
#check @ShielddSecurity.CompilerSegmentRenaming25.translated
#print axioms ShielddSecurity.CompilerSegmentRenaming25.translated
set_option pp.all true in
#check @ShielddSecurity.CompilerSegmentRenaming25.frame
#print axioms ShielddSecurity.CompilerSegmentRenaming25.frame
