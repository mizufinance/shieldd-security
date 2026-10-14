-- GENERATED from maintained bounded path composition; do not edit.
import ShielddSecurity.VolumePathLevel948L00
import ShielddSecurity.VolumePathLevel948L01
import ShielddSecurity.VolumePathLevel948L02
import ShielddSecurity.VolumePathLevel948L03
import ShielddSecurity.VolumePathLevel948L04
import ShielddSecurity.VolumePathLevel948L05
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.VolumePathComposition949B00
open Compiler CompilerAssertionBlock51 ConcreteJubjubField01 TransferSem
open VolumePathAssignment942 (assignment)
attribute [local irreducible] assignment ConcreteRegistrySharedEncoding294.model
  VolumePathMeaning946.value PoseidonNatural192.hash Poseidon.hash6 volumeState
variable (original : Nat → F) (u : F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F)
theorem result (previous : eval (assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial) VolumePriorHash908.result=(VolumePathMeaning946.value (BalanceBlindingDomain670.crypto c) w 0:F)) :
    eval (assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial) VolumePathHash931C130.result=(VolumePathMeaning946.value (BalanceBlindingDomain670.crypto c) w 6:F) := by
  have h1 := VolumePathLevel948L00.result original u c w legal rkInitial authInitial initial senderInitial receiverInitial previous
  have h2 := VolumePathLevel948L01.result original u c w legal rkInitial authInitial initial senderInitial receiverInitial h1
  have h3 := VolumePathLevel948L02.result original u c w legal rkInitial authInitial initial senderInitial receiverInitial h2
  have h4 := VolumePathLevel948L03.result original u c w legal rkInitial authInitial initial senderInitial receiverInitial h3
  have h5 := VolumePathLevel948L04.result original u c w legal rkInitial authInitial initial senderInitial receiverInitial h4
  have h6 := VolumePathLevel948L05.result original u c w legal rkInitial authInitial initial senderInitial receiverInitial h5
  exact h6
end ShielddSecurity.VolumePathComposition949B00

set_option pp.all true in
#check @ShielddSecurity.VolumePathComposition949B00.result
#print axioms ShielddSecurity.VolumePathComposition949B00.result
