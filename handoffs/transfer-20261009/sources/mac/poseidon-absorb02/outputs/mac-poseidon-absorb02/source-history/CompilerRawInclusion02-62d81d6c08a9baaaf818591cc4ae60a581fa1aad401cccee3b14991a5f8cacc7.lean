import ShielddSecurity.CompilerIndexed01
namespace ShielddSecurity.CompilerRawInclusion02
open Compiler CompilerIndexed01

def checkAt (p : Nat) (local full : Array Row) (mapping : Array Nat) (index : Fin local.size) : Bool :=
  match mapping[index.val]? with
  | none => false
  | some position => checkRowAt p full position local[index]

def check (p : Nat) (local full : Array Row) (mapping : Array Nat) : Bool :=
  decide (mapping.size=local.size) && (List.finRange local.size).all (checkAt p local full mapping)

theorem checked_satisfies {F : Type} [Field F] {p : Nat} [CharP F p]
    (local full : Array Row) (mapping : Array Nat) (checked : check p local full mapping=true)
    (rho : Nat → F) (satisfied : Satisfies rho full.toList) : Satisfies rho local.toList := by
  have all := (Bool.and_eq_true.mp checked).2
  intro row member
  have arrayMember : row∈local := by simpa using member
  obtain ⟨index,bound,equality⟩ := Array.getElem_of_mem arrayMember
  have accepted := List.all_eq_true.mp all ⟨index,bound⟩ (List.mem_finRange ⟨index,bound⟩)
  cases found : mapping[index]? with
  | none => simp only [checkAt,found] at accepted; contradiction
  | some position =>
    have acceptedAt : checkRowAt p full position local[index]=true := by
      simpa only [checkAt,found] using accepted
    have actual := checked_row_sound rho full.toList local[index] satisfied
      (checkRowAt_sound p full position local[index] acceptedAt)
    simpa only [equality] using actual
end ShielddSecurity.CompilerRawInclusion02
set_option pp.all true in
#check @ShielddSecurity.CompilerRawInclusion02.checked_satisfies
#print axioms ShielddSecurity.CompilerRawInclusion02.checked_satisfies
