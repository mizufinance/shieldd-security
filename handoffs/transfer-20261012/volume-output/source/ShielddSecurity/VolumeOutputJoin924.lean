import ShielddSecurity.VolumeOutputAlgebra923
import ShielddSecurity.VolumeOutputMeaning921
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.VolumeOutputJoin924
open Compiler CompilerAssertionBlock51 ConcreteJubjubField01 TransferSem
open VolumeHashAssignment892 (assignment)
attribute [local irreducible] assignment ConcreteRegistrySharedEncoding294.model SatisfiesAt PoseidonNatural192.hash Poseidon.hash6 TransferSem.volumeState
variable (original : Nat → F) (u : F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F)
theorem state_value : eval (assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial) VolumeOutputHash918C151.result=
    (volumeState (BalanceBlindingDomain670.crypto c) w.volume.subject w.volume.dayStart w.volume.successor w.volume.successorBlinding:F) := by
  rw [VolumePriorValues909.state_eq]
  exact VolumeOutputMeaning921.hash151 original u c w legal rkInitial authInitial initial senderInitial receiverInitial

theorem values : VolumeOutputAlgebra923.Values (assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial) (BalanceBlindingDomain670.crypto c) w := by
  have inputs : TierFlagMeaning619.Inputs (assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial) w := by
    unfold assignment RoutingParameterAssignment872.assignment VolumeCandidateAssignment854.assignment VolumeBoundaryAssignment842.assignment
    exact VolumeTransitionBindings827.inputs _ u c w legal rkInitial authInitial initial senderInitial receiverInitial
  refine ⟨?_,inputs.context,inputs.useReal,
    VolumePriorValues909.starts_new_day original u c w legal rkInitial authInitial initial senderInitial receiverInitial,VolumeHashAssignment892.nullifier original u c w legal rkInitial authInitial initial senderInitial receiverInitial,VolumeHashAssignment892.commitment original u c w legal rkInitial authInitial initial senderInitial receiverInitial,
    VolumeOutputMeaning921.hash149 original u c w legal rkInitial authInitial initial senderInitial receiverInitial,VolumeOutputMeaning921.hash150 original u c w legal rkInitial authInitial initial senderInitial receiverInitial,state_value original u c w legal rkInitial authInitial initial senderInitial receiverInitial,
    VolumeOutputMeaning921.hash152 original u c w legal rkInitial authInitial initial senderInitial receiverInitial,VolumeOutputMeaning921.hash153 original u c w legal rkInitial authInitial initial senderInitial receiverInitial⟩
  unfold assignment
  exact RoutingParameterValues879.copied _ u c w legal rkInitial authInitial initial senderInitial receiverInitial

theorem rows : VolumeOutputCapture922.Rows (assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial) := by
  apply VolumeOutputAlgebra923.rows _ (BalanceBlindingDomain670.crypto c) w legal.2.1.2.2.2.2.2.2.1 (values original u c w legal rkInitial authInitial initial senderInitial receiverInitial)
  unfold assignment
  exact RoutingParameterValues879.arithmetic _ u c w legal rkInitial authInitial initial senderInitial receiverInitial
end ShielddSecurity.VolumeOutputJoin924

set_option pp.all true in
#check @ShielddSecurity.VolumeOutputJoin924.values
#print axioms ShielddSecurity.VolumeOutputJoin924.values

set_option pp.all true in
#check @ShielddSecurity.VolumeOutputJoin924.rows
#print axioms ShielddSecurity.VolumeOutputJoin924.rows

set_option pp.all true in
#check @ShielddSecurity.VolumeOutputJoin924.state_value
#print axioms ShielddSecurity.VolumeOutputJoin924.state_value
