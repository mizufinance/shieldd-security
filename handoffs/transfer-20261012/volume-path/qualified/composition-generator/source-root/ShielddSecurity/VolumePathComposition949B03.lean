-- GENERATED from maintained bounded path composition; do not edit.
import ShielddSecurity.VolumePathLevel948L18
import ShielddSecurity.VolumePathLevel948L19
import ShielddSecurity.VolumePathLevel948L20
import ShielddSecurity.VolumePathLevel948L21
import ShielddSecurity.VolumePathLevel948L22
import ShielddSecurity.VolumePathLevel948L23
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.VolumePathComposition949B03
open Compiler CompilerAssertionBlock51 ConcreteJubjubField01 TransferSem
open VolumePathAssignment942 (assignment)
attribute [local irreducible] assignment ConcreteRegistrySharedEncoding294.model
  VolumePathMeaning946.value PoseidonNatural192.hash Poseidon.hash6 volumeState
variable (original : Nat → F) (u : F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F)
theorem result (previous : eval (assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial) VolumePathHash931C142.result=(VolumePathMeaning946.value (BalanceBlindingDomain670.crypto c) w 18:F)) :
    eval (assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial) VolumePathHash931C148.result=(VolumePathMeaning946.value (BalanceBlindingDomain670.crypto c) w 24:F) := by
  have h19 := VolumePathLevel948L18.result original u c w legal rkInitial authInitial initial senderInitial receiverInitial previous
  have h20 := VolumePathLevel948L19.result original u c w legal rkInitial authInitial initial senderInitial receiverInitial h19
  have h21 := VolumePathLevel948L20.result original u c w legal rkInitial authInitial initial senderInitial receiverInitial h20
  have h22 := VolumePathLevel948L21.result original u c w legal rkInitial authInitial initial senderInitial receiverInitial h21
  have h23 := VolumePathLevel948L22.result original u c w legal rkInitial authInitial initial senderInitial receiverInitial h22
  have h24 := VolumePathLevel948L23.result original u c w legal rkInitial authInitial initial senderInitial receiverInitial h23
  exact h24
end ShielddSecurity.VolumePathComposition949B03

set_option pp.all true in
#check @ShielddSecurity.VolumePathComposition949B03.result
#print axioms ShielddSecurity.VolumePathComposition949B03.result
