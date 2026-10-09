import ShielddSecurity.CompilerIndexCoverage01
import ShielddSecurity.PoseidonCallComposition04
namespace ShielddSecurity.PoseidonCallTraversal04

def check (indices : List (Fin 65)) (output : Fin 6) : Bool :=
  CompilerIndexCoverage01.checkCoverage indices && decide (output.val=1)

theorem coverage (indices : List (Fin 65)) (output : Fin 6)
    (checked : check indices output=true) (index : Fin 65) : index∈indices :=
  CompilerIndexCoverage01.checkCoverage_sound indices (Bool.and_eq_true.mp checked).1 index

theorem output_one (indices : List (Fin 65)) (output : Fin 6)
    (checked : check indices output=true) : output=⟨1,by decide⟩ :=
  Fin.ext (of_decide_eq_true (Bool.and_eq_true.mp checked).2)

theorem checked_rounds {F : Type} [Field F] (parameters : Poseidon.Parameters F 6)
    (before after : Nat → Poseidon.State F 6) (initial : Poseidon.State F 6)
    (indices : List (Fin 65)) (output : Fin 6) (checked : check indices output=true)
    (start : before 0=initial)
    (boundary : ∀ index,index+1<65 → before (index+1)=after index)
    (covered : ∀ index∈indices,after index.val=Poseidon.round parameters index.val (before index.val)) :
    after 64=Poseidon.permute parameters initial := by
  apply PoseidonCallComposition04.rounds_chain (count:=65) parameters before after initial start boundary
  · intro index bound
    exact covered ⟨index,bound⟩ (coverage indices output checked ⟨index,bound⟩)
  · decide

end ShielddSecurity.PoseidonCallTraversal04
set_option pp.all true in
#check @ShielddSecurity.PoseidonCallTraversal04.coverage
#print axioms ShielddSecurity.PoseidonCallTraversal04.coverage
set_option pp.all true in
#check @ShielddSecurity.PoseidonCallTraversal04.output_one
#print axioms ShielddSecurity.PoseidonCallTraversal04.output_one
set_option pp.all true in
#check @ShielddSecurity.PoseidonCallTraversal04.checked_rounds
#print axioms ShielddSecurity.PoseidonCallTraversal04.checked_rounds
