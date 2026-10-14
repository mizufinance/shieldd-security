import ShielddSecurity.VolumePriorValues909
import ShielddSecurity.AuthorizationScalarInputs531
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.VolumeOutputValues920
open Compiler CompilerAssertionBlock51 ConcreteJubjubField01 TransferSem
open VolumeHashAssignment892 (assignment)
attribute [local irreducible] assignment ConcreteRegistrySharedEncoding294.model SatisfiesAt
  PoseidonNatural192.hash Poseidon.hash6 RoutingParameterAssignment872.assignment
  VolumeCandidateAssignment854.assignment VolumeBoundaryAssignment842.assignment RoutingPrecisionRows819.assignment
  SemanticCopiesRows801.assignment CheckingInverseRows789.assignment RecoveryInverseRows781.assignment
  OutputAmountRows773.assignment DetectionNonidentityRows765.assignment BalanceFinalRows753.assignment MapAssignmentValues720.assignment
variable (original : Nat → F) (u : F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F)
theorem key : assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial 1993=(w.auth.nk:F) := by
  unfold assignment RoutingParameterAssignment872.assignment VolumeCandidateAssignment854.assignment VolumeBoundaryAssignment842.assignment RoutingPrecisionRows819.assignment SemanticCopiesRows801.assignment CheckingInverseRows789.assignment RecoveryInverseRows781.assignment OutputAmountRows773.assignment DetectionNonidentityRows765.assignment BalanceFinalRows753.assignment MapAssignmentValues720.assignment BalanceCombined696.assignment BalanceBlindingBindings680.assignment BalanceSignBindings652.assignment TierFlagBindings630.assignment TierBindings617.assignment OwnershipBindings604.assignment PublishedInverseSeed592.assignment PublishedPointSeed584.assignment PayloadBindings565.assignment FixedFamilyBindings551.assignment
  exact (AuthorizationScalarInputs531.rk _ _ w legal rkInitial authInitial initial senderInitial receiverInitial).key

theorem base_nonce (original : Nat → F) (c : Crypto) (w : TransferSem.Witness) (initial : Fin 4 → Group.Point F) :
    HeaderRegisteredConstruction310.completed original c w initial 8=(w.nonce:F) :=
  (SharedRegulatedValue316.original_frame original c w initial 8 (by constructor <;> decide) (by decide)).trans
    ((RegisteredConstructorFrame309.prepared_outside original c w 8 (by decide) (by constructor <;> decide)).trans
      (HeaderRegistrySeed299.original_headers original c w).2.2.2.2.2.2.2.2.1)

theorem nonce : assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial 8=(w.nonce:F) := by
  unfold assignment RoutingParameterAssignment872.assignment VolumeCandidateAssignment854.assignment VolumeBoundaryAssignment842.assignment RoutingPrecisionRows819.assignment SemanticCopiesRows801.assignment CheckingInverseRows789.assignment RecoveryInverseRows781.assignment OutputAmountRows773.assignment DetectionNonidentityRows765.assignment BalanceFinalRows753.assignment MapAssignmentValues720.assignment BalanceCombined696.assignment BalanceBlindingBindings680.assignment BalanceSignBindings652.assignment TierFlagBindings630.assignment TierBindings617.assignment OwnershipBindings604.assignment PublishedInverseSeed592.assignment PublishedPointSeed584.assignment PayloadBindings565.assignment FixedFamilyBindings551.assignment AuthorizationRkSeed505.assignment AuthorizationFixedSeed487.assignment AuthorizationDhSeed473.assignment
    AuthorizationTraceAssignment457.assignment IvkInverseSeed426.assignment AuthorizationSharedFrame420B.assignment
    SharedAuthorizationNonidentity413.assignment SemanticWordFrame373.assignment UserLifecycleWord345.assignment
    HighZeroCompletionFrame332.assignment SharedComparisonBlocks327.assignment
  exact base_nonce _ _ w initial
theorem successor : assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial 7742=(w.volume.successor:F) := by
  unfold assignment RoutingParameterAssignment872.assignment VolumeCandidateAssignment854.assignment VolumeBoundaryAssignment842.assignment
  exact VolumeTransitionBindings827.words _ u c w legal rkInitial authInitial initial senderInitial receiverInitial 7742 (by decide +kernel)
theorem position : assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial 8387=(w.volume.priorPosition:F) := by
  unfold assignment RoutingParameterAssignment872.assignment VolumeCandidateAssignment854.assignment VolumeBoundaryAssignment842.assignment
  exact VolumeTransitionBindings827.words _ u c w legal rkInitial authInitial initial senderInitial receiverInitial 8387 (by decide +kernel)
end ShielddSecurity.VolumeOutputValues920

set_option pp.all true in
#check @ShielddSecurity.VolumeOutputValues920.key
#print axioms ShielddSecurity.VolumeOutputValues920.key

set_option pp.all true in
#check @ShielddSecurity.VolumeOutputValues920.base_nonce
#print axioms ShielddSecurity.VolumeOutputValues920.base_nonce

set_option pp.all true in
#check @ShielddSecurity.VolumeOutputValues920.nonce
#print axioms ShielddSecurity.VolumeOutputValues920.nonce

set_option pp.all true in
#check @ShielddSecurity.VolumeOutputValues920.successor
#print axioms ShielddSecurity.VolumeOutputValues920.successor

set_option pp.all true in
#check @ShielddSecurity.VolumeOutputValues920.position
#print axioms ShielddSecurity.VolumeOutputValues920.position
