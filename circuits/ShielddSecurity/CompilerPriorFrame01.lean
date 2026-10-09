import ShielddSecurity.PoseidonCompletion
namespace ShielddSecurity.CompilerPriorFrame01
open CompilerCompletion

def checkSupport (inputs : Nat) (terms : Nat → Linear) (steps : List Step) : Bool :=
  (List.range inputs).all (fun input => (terms input).all (fun term => decide (term.1 ∉ PoseidonCompletion.writes steps)))

theorem checked_support (inputs : Nat) (terms : Nat → Linear) (steps : List Step)
    (checked : checkSupport inputs terms steps=true) (input : Nat) (bound : input<inputs)
    (term : Nat × Int) (member : term∈terms input) : term.1 ∉ PoseidonCompletion.writes steps :=
  of_decide_eq_true (List.all_eq_true.mp
    (List.all_eq_true.mp checked input (List.mem_range.mpr bound)) term member)

theorem completed_inputs (inputs : Nat) (terms : Nat → Linear) (steps : List Step)
    (checked : checkSupport inputs terms steps=true) {F : Type} [Field F]
    (base : Nat → F) (input : Nat) (bound : input<inputs) :
    eval (run base steps) (terms input)=eval base (terms input) :=
  PoseidonCompletion.eval_run_preserves base steps (terms input)
    (fun term member => checked_support inputs terms steps checked input bound term member)
end ShielddSecurity.CompilerPriorFrame01
set_option pp.all true in
#check @ShielddSecurity.CompilerPriorFrame01.checked_support
#print axioms ShielddSecurity.CompilerPriorFrame01.checked_support
set_option pp.all true in
#check @ShielddSecurity.CompilerPriorFrame01.completed_inputs
#print axioms ShielddSecurity.CompilerPriorFrame01.completed_inputs
