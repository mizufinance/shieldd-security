import ShielddSecurity.RoutingParameterBindings871
import ShielddSecurity.VolumeCandidateAssignment854
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.RoutingParameterAssignment872
open ConcreteJubjubField01 TransferSem
attribute [local irreducible] ConcreteRegistrySharedEncoding294.model VolumeCandidateAssignment854.assignment
  VolumeBoundaryAssignment842.assignment RoutingPrecisionRows819.assignment SemanticCopiesRows801.assignment
  CheckingInverseRows789.assignment RecoveryInverseRows781.assignment OutputAmountRows773.assignment
  DetectionNonidentityRows765.assignment BalanceFinalRows753.assignment MapAssignmentValues720.assignment

def assignment (original : Nat → F) (u : F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) : Nat → F :=
  VolumeCandidateAssignment854.assignment (RoutingParameterSeed866.seed original w) u c w legal
    rkInitial authInitial initial senderInitial receiverInitial
attribute [local irreducible] assignment
variable (original : Nat → F) (u : F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F)
theorem frame (column : Nat) (member : column∈RoutingParameterLayout863.columns) :
    assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial column=
      RoutingParameterSeed866.seed original w column := by
  have bounds := RoutingParameterLayout863.bounds column member
  have candidate := VolumeCandidateSeed848.outside (RoutingParameterSeed866.seed original w) w column (Or.inr (by omega))
  have boundary := VolumeBoundarySeed836.outside (VolumeCandidateSeed848.seed (RoutingParameterSeed866.seed original w) w) w column (Or.inr (by omega))
  have routing := RoutingPrecisionSeed811.outside (VolumeBoundarySeed836.seed (VolumeCandidateSeed848.seed (RoutingParameterSeed866.seed original w) w) w) w column (Or.inr (by omega))
  unfold assignment VolumeCandidateAssignment854.assignment VolumeBoundaryAssignment842.assignment RoutingPrecisionRows819.assignment
  exact (RoutingParameterBindings871.current_frame _ u c w legal rkInitial authInitial initial senderInitial receiverInitial
    column member (by intro impossible; simp only [RoutingParameterLayout863.flags,List.not_mem_nil] at impossible)).trans
      (routing.trans (boundary.trans candidate))
theorem parameter_set : assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial 19589=(w.routing.parameterSet:F) :=
  (frame original u c w legal rkInitial authInitial initial senderInitial receiverInitial 19589 (by decide +kernel)).trans
    (RoutingParameterSeed866.parameter_set original w)
theorem height : assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial 19590=(w.routing.height:F) :=
  (frame original u c w legal rkInitial authInitial initial senderInitial receiverInitial 19590 (by decide +kernel)).trans
    (RoutingParameterSeed866.height original w)
end ShielddSecurity.RoutingParameterAssignment872

set_option pp.all true in
#check @ShielddSecurity.RoutingParameterAssignment872.frame
#print axioms ShielddSecurity.RoutingParameterAssignment872.frame

set_option pp.all true in
#check @ShielddSecurity.RoutingParameterAssignment872.parameter_set
#print axioms ShielddSecurity.RoutingParameterAssignment872.parameter_set

set_option pp.all true in
#check @ShielddSecurity.RoutingParameterAssignment872.height
#print axioms ShielddSecurity.RoutingParameterAssignment872.height
