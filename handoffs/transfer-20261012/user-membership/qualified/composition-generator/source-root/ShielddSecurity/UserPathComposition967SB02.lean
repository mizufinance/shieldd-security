-- GENERATED from maintained bounded user path composition; do not edit.
import ShielddSecurity.UserPathLevel966SL08
import ShielddSecurity.UserPathLevel966SL09
import ShielddSecurity.UserPathLevel966SL10
import ShielddSecurity.UserPathLevel966SL11
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.UserPathComposition967SB02
open Compiler CompilerAssertionBlock51 ConcreteJubjubField01 TransferSem
open VolumePathAssignment942 (assignment)
attribute [local irreducible] assignment ConcreteRegistrySharedEncoding294.model
  UserTreeMeaning965.value PoseidonNatural192.hash Poseidon.hash6 userLeaf
variable (original : Nat → F) (u : F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F)
theorem result (previous : eval (assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial) UserPathHash958C29.result=(UserTreeMeaning965.value (BalanceBlindingDomain670.crypto c) w.asset w.sender 8:F)) :
    eval (assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial) UserPathHash958C33.result=(UserTreeMeaning965.value (BalanceBlindingDomain670.crypto c) w.asset w.sender 12:F) := by
  have h9 := UserPathLevel966SL08.result original u c w legal rkInitial authInitial initial senderInitial receiverInitial previous
  have h10 := UserPathLevel966SL09.result original u c w legal rkInitial authInitial initial senderInitial receiverInitial h9
  have h11 := UserPathLevel966SL10.result original u c w legal rkInitial authInitial initial senderInitial receiverInitial h10
  have h12 := UserPathLevel966SL11.result original u c w legal rkInitial authInitial initial senderInitial receiverInitial h11
  exact h12
end ShielddSecurity.UserPathComposition967SB02

set_option pp.all true in
#check @ShielddSecurity.UserPathComposition967SB02.result
#print axioms ShielddSecurity.UserPathComposition967SB02.result
