-- GENERATED from maintained bounded user path composition; do not edit.
import ShielddSecurity.UserPathLevel966SL00
import ShielddSecurity.UserPathLevel966SL01
import ShielddSecurity.UserPathLevel966SL02
import ShielddSecurity.UserPathLevel966SL03
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.UserPathComposition967SB00
open Compiler CompilerAssertionBlock51 ConcreteJubjubField01 TransferSem
open VolumePathAssignment942 (assignment)
attribute [local irreducible] assignment ConcreteRegistrySharedEncoding294.model
  UserTreeMeaning965.value PoseidonNatural192.hash Poseidon.hash6 userLeaf
variable (original : Nat → F) (u : F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F)
theorem result (previous : eval (assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial) UserPathHash958C21.result=(UserTreeMeaning965.value (BalanceBlindingDomain670.crypto c) w.asset w.sender 0:F)) :
    eval (assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial) UserPathHash958C25.result=(UserTreeMeaning965.value (BalanceBlindingDomain670.crypto c) w.asset w.sender 4:F) := by
  have h1 := UserPathLevel966SL00.result original u c w legal rkInitial authInitial initial senderInitial receiverInitial previous
  have h2 := UserPathLevel966SL01.result original u c w legal rkInitial authInitial initial senderInitial receiverInitial h1
  have h3 := UserPathLevel966SL02.result original u c w legal rkInitial authInitial initial senderInitial receiverInitial h2
  have h4 := UserPathLevel966SL03.result original u c w legal rkInitial authInitial initial senderInitial receiverInitial h3
  exact h4
end ShielddSecurity.UserPathComposition967SB00

set_option pp.all true in
#check @ShielddSecurity.UserPathComposition967SB00.result
#print axioms ShielddSecurity.UserPathComposition967SB00.result
