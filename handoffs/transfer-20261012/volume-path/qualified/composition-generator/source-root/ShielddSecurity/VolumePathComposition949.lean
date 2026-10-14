-- GENERATED from maintained bounded path composition; do not edit.
import ShielddSecurity.VolumePathComposition949B00
import ShielddSecurity.VolumePathComposition949B01
import ShielddSecurity.VolumePathComposition949B02
import ShielddSecurity.VolumePathComposition949B03
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.VolumePathComposition949
open Compiler CompilerAssertionBlock51 ConcreteJubjubField01 TransferSem
open VolumePathAssignment942 (assignment)
attribute [local irreducible] assignment ConcreteRegistrySharedEncoding294.model
  VolumePathMeaning946.value PoseidonNatural192.hash Poseidon.hash6 volumeState
variable (original : Nat → F) (u : F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F)
theorem result : eval (assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial) VolumePathHash931C148.result=
    (root (BalanceBlindingDomain670.crypto c) .state w.volume.priorPosition
      (volumeState (BalanceBlindingDomain670.crypto c) w.volume.subject w.volume.dayStart w.volume.prior w.volume.priorBlinding)
      w.volume.priorSiblings:F) := by
  have h0 := VolumePathValues947.prior original u c w legal rkInitial authInitial initial senderInitial receiverInitial
  have h1 := VolumePathComposition949B00.result original u c w legal rkInitial authInitial initial senderInitial receiverInitial h0
  have h2 := VolumePathComposition949B01.result original u c w legal rkInitial authInitial initial senderInitial receiverInitial h1
  have h3 := VolumePathComposition949B02.result original u c w legal rkInitial authInitial initial senderInitial receiverInitial h2
  have h4 := VolumePathComposition949B03.result original u c w legal rkInitial authInitial initial senderInitial receiverInitial h3
  exact h4.trans (congrArg (fun n : Nat => (n:F)) (VolumePathMeaning946.final _ w))
end ShielddSecurity.VolumePathComposition949

set_option pp.all true in
#check @ShielddSecurity.VolumePathComposition949.result
#print axioms ShielddSecurity.VolumePathComposition949.result
