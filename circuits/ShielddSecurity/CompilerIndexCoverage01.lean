import ShielddSecurity.Compiler
namespace ShielddSecurity.CompilerIndexCoverage01

def checkCoverage {nodes : Nat} (indices : List (Fin nodes)) : Bool :=
  (List.finRange nodes).all (fun index => decide (index ∈ indices))

theorem checkCoverage_sound {nodes : Nat} (indices : List (Fin nodes))
    (checked : checkCoverage indices=true) (index : Fin nodes) : index ∈ indices :=
  of_decide_eq_true (List.all_eq_true.mp checked index (List.mem_finRange index))

end ShielddSecurity.CompilerIndexCoverage01
set_option pp.all true in
#check @ShielddSecurity.CompilerIndexCoverage01.checkCoverage_sound
#print axioms ShielddSecurity.CompilerIndexCoverage01.checkCoverage_sound
