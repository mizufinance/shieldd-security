-- GENERATED from maintained bounded user path composition; do not edit.
import ShielddSecurity.UserPathLevel966SL04
import ShielddSecurity.UserPathLevel966SL05
import ShielddSecurity.UserPathLevel966SL06
import ShielddSecurity.UserPathLevel966SL07
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.UserPathComposition967SB01
open Compiler CompilerAssertionBlock51 ConcreteJubjubField01 TransferSem
open VolumePathAssignment942 (assignment)
attribute [local irreducible] assignment ConcreteRegistrySharedEncoding294.model
  UserTreeMeaning965.value PoseidonNatural192.hash Poseidon.hash6 userLeaf
variable (original : Nat → F) (u : F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F)
theorem result (previous : eval (assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial) UserPathHash958C25.result=(UserTreeMeaning965.value (BalanceBlindingDomain670.crypto c) w.asset w.sender 4:F)) :
    eval (assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial) UserPathHash958C29.result=(UserTreeMeaning965.value (BalanceBlindingDomain670.crypto c) w.asset w.sender 8:F) := by
  have h5 := UserPathLevel966SL04.result original u c w legal rkInitial authInitial initial senderInitial receiverInitial previous
  have h6 := UserPathLevel966SL05.result original u c w legal rkInitial authInitial initial senderInitial receiverInitial h5
  have h7 := UserPathLevel966SL06.result original u c w legal rkInitial authInitial initial senderInitial receiverInitial h6
  have h8 := UserPathLevel966SL07.result original u c w legal rkInitial authInitial initial senderInitial receiverInitial h7
  exact h8
end ShielddSecurity.UserPathComposition967SB01

set_option pp.all true in
#check @ShielddSecurity.UserPathComposition967SB01.result
#print axioms ShielddSecurity.UserPathComposition967SB01.result
