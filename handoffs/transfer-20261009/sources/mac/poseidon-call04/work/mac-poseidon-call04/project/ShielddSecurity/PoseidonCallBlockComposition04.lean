import ShielddSecurity.PoseidonCallComposition04
namespace ShielddSecurity.PoseidonCallBlockComposition04
open Compiler CompilerCompletion

theorem support_append (bound : Nat) (first second : List Step)
    (firstSupport : ∀ row∈emitted first,∀ term∈row.a++row.b,term.1<bound)
    (secondSupport : ∀ row∈emitted second,∀ term∈row.a++row.b,term.1<bound) :
    ∀ row∈emitted (first++second),∀ term∈row.a++row.b,term.1<bound := by
  intro row member term present
  rw [PoseidonCallComposition04.emitted_append] at member
  rcases List.mem_append.mp member with firstMember|secondMember
  · exact firstSupport row firstMember term present
  · exact secondSupport row secondMember term present

theorem writes_lower_append (floor : Nat) (first second : List Step)
    (firstLower : ∀ column∈PoseidonCompletion.writes first,floor≤column)
    (secondLower : ∀ column∈PoseidonCompletion.writes second,floor≤column) :
    ∀ column∈PoseidonCompletion.writes (first++second),floor≤column := by
  intro column member
  simp only [PoseidonCompletion.writes,List.flatMap_append] at member
  rcases List.mem_append.mp member with firstMember|secondMember
  · exact firstLower column firstMember
  · exact secondLower column secondMember

variable {F : Type} [Field F]
theorem satisfies_inclusion (rho : Nat → F) (part full : List Row)
    (included : ∀ row∈part,row∈full) (satisfied : Satisfies rho full) : Satisfies rho part :=
  fun row member => satisfied row (included row member)
end ShielddSecurity.PoseidonCallBlockComposition04
set_option pp.all true in
#check @ShielddSecurity.PoseidonCallBlockComposition04.support_append
#print axioms ShielddSecurity.PoseidonCallBlockComposition04.support_append
set_option pp.all true in
#check @ShielddSecurity.PoseidonCallBlockComposition04.writes_lower_append
#print axioms ShielddSecurity.PoseidonCallBlockComposition04.writes_lower_append
set_option pp.all true in
#check @ShielddSecurity.PoseidonCallBlockComposition04.satisfies_inclusion
#print axioms ShielddSecurity.PoseidonCallBlockComposition04.satisfies_inclusion
