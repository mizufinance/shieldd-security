-- GENERATED from maintained bounded user path composition; do not edit.
import ShielddSecurity.UserPathLevel966RL04
import ShielddSecurity.UserPathLevel966RL05
import ShielddSecurity.UserPathLevel966RL06
import ShielddSecurity.UserPathLevel966RL07
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.UserPathComposition967RB01
open Compiler CompilerAssertionBlock51 ConcreteJubjubField01 TransferSem
open VolumePathAssignment942 (assignment)
attribute [local irreducible] assignment ConcreteRegistrySharedEncoding294.model
  UserTreeMeaning965.value PoseidonNatural192.hash Poseidon.hash6 userLeaf
variable (original : Nat → F) (u : F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F)
theorem result (previous : eval (assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial) UserPathHash958C42.result=(UserTreeMeaning965.value (BalanceBlindingDomain670.crypto c) w.asset w.receiver 4:F)) :
    eval (assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial) UserPathHash958C46.result=(UserTreeMeaning965.value (BalanceBlindingDomain670.crypto c) w.asset w.receiver 8:F) := by
  have h5 := UserPathLevel966RL04.result original u c w legal rkInitial authInitial initial senderInitial receiverInitial previous
  have h6 := UserPathLevel966RL05.result original u c w legal rkInitial authInitial initial senderInitial receiverInitial h5
  have h7 := UserPathLevel966RL06.result original u c w legal rkInitial authInitial initial senderInitial receiverInitial h6
  have h8 := UserPathLevel966RL07.result original u c w legal rkInitial authInitial initial senderInitial receiverInitial h7
  exact h8
end ShielddSecurity.UserPathComposition967RB01

set_option pp.all true in
#check @ShielddSecurity.UserPathComposition967RB01.result
#print axioms ShielddSecurity.UserPathComposition967RB01.result
