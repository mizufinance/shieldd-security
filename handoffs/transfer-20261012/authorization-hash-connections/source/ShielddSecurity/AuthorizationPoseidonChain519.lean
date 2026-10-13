import ShielddSecurity.AuthorizationPoseidonPhase517
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.AuthorizationPoseidonChain519
open Poseidon
variable {F : Type} [Field F]
theorem chain {width : Nat} (parameters : Parameters F width) (count : Nat)
    (before after : Nat → State F width)
    (boundary : ∀ index,index+1<count → before (index+1)=after index)
    (step : ∀ index,index<count → after index=round parameters index (before index))
    (index : Nat) (bound : index<count) :
    after index=Poseidon.rounds parameters (index+1) (before 0) := by
  induction index with
  | zero => simpa only [Poseidon.rounds] using step 0 bound
  | succ index ih =>
    rw [step (index+1) bound,boundary index bound,ih (by omega)]
    rfl
def roundsFrom {width : Nat} (parameters : Parameters F width) (start : Nat) : Nat → State F width → State F width
  | 0,state => state
  | count+1,state => round parameters (start+count) (roundsFrom parameters start count state)
theorem suffix_chain {width : Nat} (parameters : Parameters F width) (start count : Nat)
    (before after : Nat → State F width)
    (boundary : ∀ index,index+1<count → before (start+index+1)=after (start+index))
    (step : ∀ index,index<count → after (start+index)=round parameters (start+index) (before (start+index)))
    (index : Nat) (bound : index<count) :
    after (start+index)=roundsFrom parameters start (index+1) (before start) := by
  induction index with
  | zero => simpa only [Nat.add_zero,roundsFrom] using step 0 bound
  | succ index ih =>
    have previous := ih (by omega)
    rw [step (index+1) bound]
    rw [show start+(index+1)=start+index+1 by omega,boundary index bound,previous]
    rfl
end ShielddSecurity.AuthorizationPoseidonChain519
set_option pp.all true in
#check @ShielddSecurity.AuthorizationPoseidonChain519.chain
#print axioms ShielddSecurity.AuthorizationPoseidonChain519.chain
set_option pp.all true in
#check @ShielddSecurity.AuthorizationPoseidonChain519.suffix_chain
#print axioms ShielddSecurity.AuthorizationPoseidonChain519.suffix_chain
