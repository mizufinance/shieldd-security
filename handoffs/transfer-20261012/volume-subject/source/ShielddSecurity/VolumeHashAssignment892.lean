import ShielddSecurity.VolumeHashBindings891
import ShielddSecurity.RoutingParameterAssignment872
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.VolumeHashAssignment892
open ConcreteJubjubField01 TransferSem
attribute [local irreducible] ConcreteRegistrySharedEncoding294.model RoutingParameterAssignment872.assignment VolumeCandidateAssignment854.assignment
  VolumeBoundaryAssignment842.assignment RoutingPrecisionRows819.assignment SemanticCopiesRows801.assignment
  CheckingInverseRows789.assignment RecoveryInverseRows781.assignment OutputAmountRows773.assignment
  DetectionNonidentityRows765.assignment BalanceFinalRows753.assignment MapAssignmentValues720.assignment

def assignment (original : Nat → F) (u : F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) : Nat → F :=
  RoutingParameterAssignment872.assignment (VolumeHashSeed886.seed original w) u c w legal
    rkInitial authInitial initial senderInitial receiverInitial
attribute [local irreducible] assignment
variable (original : Nat → F) (u : F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F)
theorem frame (column : Nat) (member : column∈VolumeHashLayout883.columns) :
    assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial column=
      VolumeHashSeed886.seed original w column := by
  have bounds := VolumeHashLayout883.bounds column member
  have alternatives := VolumeHashLayout883.alternatives column member
  have parameter := RoutingParameterSeed866.outside (VolumeHashSeed886.seed original w) w column (Or.inl (by omega))
  have candidate := VolumeCandidateSeed848.outside (RoutingParameterSeed866.seed (VolumeHashSeed886.seed original w) w) w column (by omega)
  have boundary : VolumeBoundarySeed836.seed (VolumeCandidateSeed848.seed (RoutingParameterSeed866.seed (VolumeHashSeed886.seed original w) w) w) w column=
      VolumeCandidateSeed848.seed (RoutingParameterSeed866.seed (VolumeHashSeed886.seed original w) w) w column := by
    simp only [VolumeBoundarySeed836.seed,if_neg (show column≠7739 by omega),if_neg (show column≠8255 by omega)]
  have routing := RoutingPrecisionSeed811.outside (VolumeBoundarySeed836.seed (VolumeCandidateSeed848.seed (RoutingParameterSeed866.seed (VolumeHashSeed886.seed original w) w) w) w) w column (Or.inl (by omega))
  unfold assignment RoutingParameterAssignment872.assignment VolumeCandidateAssignment854.assignment VolumeBoundaryAssignment842.assignment RoutingPrecisionRows819.assignment
  exact (VolumeHashBindings891.current_frame _ u c w legal rkInitial authInitial initial senderInitial receiverInitial
    column member (by intro impossible; simp only [VolumeHashLayout883.flags,List.not_mem_nil] at impossible)).trans
      (routing.trans (boundary.trans (candidate.trans parameter)))
theorem subject : assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial 7740=(w.volume.subject:F) :=
  (frame original u c w legal rkInitial authInitial initial senderInitial receiverInitial 7740 (by decide +kernel)).trans (VolumeHashSeed886.subject original w)
theorem priorBlinding : assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial 8385=(w.volume.priorBlinding:F) :=
  (frame original u c w legal rkInitial authInitial initial senderInitial receiverInitial 8385 (by decide +kernel)).trans (VolumeHashSeed886.priorBlinding original w)
theorem priorCommitment : assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial 8386=(w.volume.priorCommitment:F) :=
  (frame original u c w legal rkInitial authInitial initial senderInitial receiverInitial 8386 (by decide +kernel)).trans (VolumeHashSeed886.priorCommitment original w)
theorem successorBlinding : assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial 8508=(w.volume.successorBlinding:F) :=
  (frame original u c w legal rkInitial authInitial initial senderInitial receiverInitial 8508 (by decide +kernel)).trans (VolumeHashSeed886.successorBlinding original w)
theorem nullifier : assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial 8509=(w.volume.nullifier:F) :=
  (frame original u c w legal rkInitial authInitial initial senderInitial receiverInitial 8509 (by decide +kernel)).trans (VolumeHashSeed886.nullifier original w)
theorem commitment : assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial 8510=(w.volume.commitment:F) :=
  (frame original u c w legal rkInitial authInitial initial senderInitial receiverInitial 8510 (by decide +kernel)).trans (VolumeHashSeed886.commitment original w)
end ShielddSecurity.VolumeHashAssignment892

set_option pp.all true in
#check @ShielddSecurity.VolumeHashAssignment892.frame
#print axioms ShielddSecurity.VolumeHashAssignment892.frame

set_option pp.all true in
#check @ShielddSecurity.VolumeHashAssignment892.subject
#print axioms ShielddSecurity.VolumeHashAssignment892.subject

set_option pp.all true in
#check @ShielddSecurity.VolumeHashAssignment892.priorBlinding
#print axioms ShielddSecurity.VolumeHashAssignment892.priorBlinding

set_option pp.all true in
#check @ShielddSecurity.VolumeHashAssignment892.priorCommitment
#print axioms ShielddSecurity.VolumeHashAssignment892.priorCommitment

set_option pp.all true in
#check @ShielddSecurity.VolumeHashAssignment892.successorBlinding
#print axioms ShielddSecurity.VolumeHashAssignment892.successorBlinding

set_option pp.all true in
#check @ShielddSecurity.VolumeHashAssignment892.nullifier
#print axioms ShielddSecurity.VolumeHashAssignment892.nullifier

set_option pp.all true in
#check @ShielddSecurity.VolumeHashAssignment892.commitment
#print axioms ShielddSecurity.VolumeHashAssignment892.commitment
