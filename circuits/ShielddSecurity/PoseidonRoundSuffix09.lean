import ShielddSecurity.Poseidon
namespace ShielddSecurity.PoseidonRoundSuffix09
open Poseidon
variable {F : Type} [Field F] {width : Nat}

def roundsFrom (parameters : Parameters F width) (start : Nat) : Nat → State F width → State F width
  | 0,state => state
  | count+1,state => round parameters (start+count) (roundsFrom parameters start count state)

theorem chain (parameters : Parameters F width) (start count : Nat)
    (before after : Nat → State F width) (initial : State F width)
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

end ShielddSecurity.PoseidonRoundSuffix09
set_option pp.all true in
#check @ShielddSecurity.PoseidonRoundSuffix09.chain
#print axioms ShielddSecurity.PoseidonRoundSuffix09.chain
