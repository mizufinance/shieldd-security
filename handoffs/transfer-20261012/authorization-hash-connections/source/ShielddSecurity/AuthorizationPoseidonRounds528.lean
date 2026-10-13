import ShielddSecurity.AuthorizationPoseidonChain519
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.AuthorizationPoseidonRounds528
open Poseidon AuthorizationPoseidonChain519
variable {F : Type} [Field F]
theorem rounds_bridge {width : Nat} (parameters : Parameters F width) (count : Nat)
    (state : State F width) :
    roundsFrom parameters 2 count (round parameters 1 (round parameters 0 state))=
      rounds parameters (count+2) state := by
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [roundsFrom,ih]
    rw [show 2+count=count+2 by omega]
    rfl
theorem permutation_bridge {width : Nat} (parameters : Parameters F width) (state : State F width) :
    roundsFrom parameters 2 63 (round parameters 1 (round parameters 0 state))=permute parameters state :=
  rounds_bridge parameters 63 state
end ShielddSecurity.AuthorizationPoseidonRounds528
set_option pp.all true in
#check @ShielddSecurity.AuthorizationPoseidonRounds528.rounds_bridge
#print axioms ShielddSecurity.AuthorizationPoseidonRounds528.rounds_bridge
set_option pp.all true in
#check @ShielddSecurity.AuthorizationPoseidonRounds528.permutation_bridge
#print axioms ShielddSecurity.AuthorizationPoseidonRounds528.permutation_bridge
