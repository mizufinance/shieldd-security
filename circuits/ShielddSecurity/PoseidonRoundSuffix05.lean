import ShielddSecurity.Poseidon
namespace ShielddSecurity.PoseidonRoundSuffix05
open Poseidon
variable {F : Type} [Field F]

def roundsFrom (parameters : Parameters F 6) (start : Nat) : Nat → State F 6 → State F 6
  | 0,state => state
  | count+1,state => round parameters (start+count) (roundsFrom parameters start count state)

theorem chain (parameters : Parameters F 6) (start count : Nat)
    (before after : Nat → State F 6) (initial : State F 6)
    (first : before start=initial)
    (boundary : ∀ index,index+1<count → before (start+index+1)=after (start+index))
    (rounds : ∀ index,index<count → after (start+index)=round parameters (start+index) (before (start+index)))
    (index : Nat) (bound : index<count) :
    after (start+index)=roundsFrom parameters start (index+1) initial := by
  induction index with
  | zero => simpa only [Nat.add_zero,roundsFrom,first] using rounds 0 bound
  | succ index ih =>
    have previous := ih (by omega)
    rw [rounds (index+1) bound]
    rw [show start+(index+1)=start+index+1 by omega,boundary index bound,previous]
    rfl

end ShielddSecurity.PoseidonRoundSuffix05
set_option pp.all true in
#check @ShielddSecurity.PoseidonRoundSuffix05.chain
#print axioms ShielddSecurity.PoseidonRoundSuffix05.chain
