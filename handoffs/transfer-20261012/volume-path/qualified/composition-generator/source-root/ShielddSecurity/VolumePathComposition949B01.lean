-- GENERATED from maintained bounded path composition; do not edit.
import ShielddSecurity.VolumePathLevel948L06
import ShielddSecurity.VolumePathLevel948L07
import ShielddSecurity.VolumePathLevel948L08
import ShielddSecurity.VolumePathLevel948L09
import ShielddSecurity.VolumePathLevel948L10
import ShielddSecurity.VolumePathLevel948L11
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.VolumePathComposition949B01
open Compiler CompilerAssertionBlock51 ConcreteJubjubField01 TransferSem
open VolumePathAssignment942 (assignment)
attribute [local irreducible] assignment ConcreteRegistrySharedEncoding294.model
  VolumePathMeaning946.value PoseidonNatural192.hash Poseidon.hash6 volumeState
variable (original : Nat → F) (u : F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F)
theorem result (previous : eval (assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial) VolumePathHash931C130.result=(VolumePathMeaning946.value (BalanceBlindingDomain670.crypto c) w 6:F)) :
    eval (assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial) VolumePathHash931C136.result=(VolumePathMeaning946.value (BalanceBlindingDomain670.crypto c) w 12:F) := by
  have h7 := VolumePathLevel948L06.result original u c w legal rkInitial authInitial initial senderInitial receiverInitial previous
  have h8 := VolumePathLevel948L07.result original u c w legal rkInitial authInitial initial senderInitial receiverInitial h7
  have h9 := VolumePathLevel948L08.result original u c w legal rkInitial authInitial initial senderInitial receiverInitial h8
  have h10 := VolumePathLevel948L09.result original u c w legal rkInitial authInitial initial senderInitial receiverInitial h9
  have h11 := VolumePathLevel948L10.result original u c w legal rkInitial authInitial initial senderInitial receiverInitial h10
  have h12 := VolumePathLevel948L11.result original u c w legal rkInitial authInitial initial senderInitial receiverInitial h11
  exact h12
end ShielddSecurity.VolumePathComposition949B01

set_option pp.all true in
#check @ShielddSecurity.VolumePathComposition949B01.result
#print axioms ShielddSecurity.VolumePathComposition949B01.result
