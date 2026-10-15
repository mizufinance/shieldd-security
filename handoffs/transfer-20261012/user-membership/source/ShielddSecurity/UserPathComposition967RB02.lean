-- GENERATED from maintained bounded user path composition; do not edit.
import ShielddSecurity.UserPathLevel966RL08
import ShielddSecurity.UserPathLevel966RL09
import ShielddSecurity.UserPathLevel966RL10
import ShielddSecurity.UserPathLevel966RL11
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.UserPathComposition967RB02
open Compiler CompilerAssertionBlock51 ConcreteJubjubField01 TransferSem
open VolumePathAssignment942 (assignment)
attribute [local irreducible] assignment ConcreteRegistrySharedEncoding294.model
  UserTreeMeaning965.value PoseidonNatural192.hash Poseidon.hash6 userLeaf
variable (original : Nat → F) (u : F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F)
theorem result (previous : eval (assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial) UserPathHash958C46.result=(UserTreeMeaning965.value (BalanceBlindingDomain670.crypto c) w.asset w.receiver 8:F)) :
    eval (assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial) UserPathHash958C50.result=(UserTreeMeaning965.value (BalanceBlindingDomain670.crypto c) w.asset w.receiver 12:F) := by
  have h9 := UserPathLevel966RL08.result original u c w legal rkInitial authInitial initial senderInitial receiverInitial previous
  have h10 := UserPathLevel966RL09.result original u c w legal rkInitial authInitial initial senderInitial receiverInitial h9
  have h11 := UserPathLevel966RL10.result original u c w legal rkInitial authInitial initial senderInitial receiverInitial h10
  have h12 := UserPathLevel966RL11.result original u c w legal rkInitial authInitial initial senderInitial receiverInitial h11
  exact h12
end ShielddSecurity.UserPathComposition967RB02

set_option pp.all true in
#check @ShielddSecurity.UserPathComposition967RB02.result
#print axioms ShielddSecurity.UserPathComposition967RB02.result
