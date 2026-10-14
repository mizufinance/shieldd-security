-- GENERATED from maintained bounded path composition; do not edit.
import ShielddSecurity.VolumePathLevel948L12
import ShielddSecurity.VolumePathLevel948L13
import ShielddSecurity.VolumePathLevel948L14
import ShielddSecurity.VolumePathLevel948L15
import ShielddSecurity.VolumePathLevel948L16
import ShielddSecurity.VolumePathLevel948L17
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.VolumePathComposition949B02
open Compiler CompilerAssertionBlock51 ConcreteJubjubField01 TransferSem
open VolumePathAssignment942 (assignment)
attribute [local irreducible] assignment ConcreteRegistrySharedEncoding294.model
  VolumePathMeaning946.value PoseidonNatural192.hash Poseidon.hash6 volumeState
variable (original : Nat → F) (u : F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F)
theorem result (previous : eval (assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial) VolumePathHash931C136.result=(VolumePathMeaning946.value (BalanceBlindingDomain670.crypto c) w 12:F)) :
    eval (assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial) VolumePathHash931C142.result=(VolumePathMeaning946.value (BalanceBlindingDomain670.crypto c) w 18:F) := by
  have h13 := VolumePathLevel948L12.result original u c w legal rkInitial authInitial initial senderInitial receiverInitial previous
  have h14 := VolumePathLevel948L13.result original u c w legal rkInitial authInitial initial senderInitial receiverInitial h13
  have h15 := VolumePathLevel948L14.result original u c w legal rkInitial authInitial initial senderInitial receiverInitial h14
  have h16 := VolumePathLevel948L15.result original u c w legal rkInitial authInitial initial senderInitial receiverInitial h15
  have h17 := VolumePathLevel948L16.result original u c w legal rkInitial authInitial initial senderInitial receiverInitial h16
  have h18 := VolumePathLevel948L17.result original u c w legal rkInitial authInitial initial senderInitial receiverInitial h17
  exact h18
end ShielddSecurity.VolumePathComposition949B02

set_option pp.all true in
#check @ShielddSecurity.VolumePathComposition949B02.result
#print axioms ShielddSecurity.VolumePathComposition949B02.result
