-- GENERATED from maintained bounded user path composition; do not edit.
import ShielddSecurity.UserPathLevel966SL12
import ShielddSecurity.UserPathLevel966SL13
import ShielddSecurity.UserPathLevel966SL14
import ShielddSecurity.UserPathLevel966SL15
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.UserPathComposition967SB03
open Compiler CompilerAssertionBlock51 ConcreteJubjubField01 TransferSem
open VolumePathAssignment942 (assignment)
attribute [local irreducible] assignment ConcreteRegistrySharedEncoding294.model
  UserTreeMeaning965.value PoseidonNatural192.hash Poseidon.hash6 userLeaf
variable (original : Nat → F) (u : F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F)
theorem result (previous : eval (assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial) UserPathHash958C33.result=(UserTreeMeaning965.value (BalanceBlindingDomain670.crypto c) w.asset w.sender 12:F)) :
    eval (assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial) UserPathHash958C37.result=(UserTreeMeaning965.value (BalanceBlindingDomain670.crypto c) w.asset w.sender 16:F) := by
  have h13 := UserPathLevel966SL12.result original u c w legal rkInitial authInitial initial senderInitial receiverInitial previous
  have h14 := UserPathLevel966SL13.result original u c w legal rkInitial authInitial initial senderInitial receiverInitial h13
  have h15 := UserPathLevel966SL14.result original u c w legal rkInitial authInitial initial senderInitial receiverInitial h14
  have h16 := UserPathLevel966SL15.result original u c w legal rkInitial authInitial initial senderInitial receiverInitial h15
  exact h16
end ShielddSecurity.UserPathComposition967SB03

set_option pp.all true in
#check @ShielddSecurity.UserPathComposition967SB03.result
#print axioms ShielddSecurity.UserPathComposition967SB03.result
