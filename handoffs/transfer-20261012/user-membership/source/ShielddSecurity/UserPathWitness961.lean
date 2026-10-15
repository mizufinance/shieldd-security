import ShielddSecurity.VolumePathAssignment942
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.UserPathWitness961
open ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem
attribute [local irreducible] model
attribute [local irreducible] VolumePathAssignment942.assignment
  VolumeHashAssignment892.assignment RoutingParameterAssignment872.assignment VolumeCandidateAssignment854.assignment
  VolumeBoundaryAssignment842.assignment RoutingPrecisionRows819.assignment SemanticCopiesRows801.assignment
  CheckingInverseRows789.assignment RecoveryInverseRows781.assignment OutputAmountRows773.assignment
  DetectionNonidentityRows765.assignment BalanceFinalRows753.assignment MapAssignmentValues720.assignment

variable (original : Nat → F) (u : F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F)
theorem sender_siblings (level : Fin 16) (slot : Fin 3) :
    VolumePathAssignment942.assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial (1531+3*level.val+slot.val)=(w.sender.siblings level slot:F) := by
  unfold VolumePathAssignment942.assignment VolumeHashAssignment892.assignment RoutingParameterAssignment872.assignment
    VolumeCandidateAssignment854.assignment VolumeBoundaryAssignment842.assignment RoutingPrecisionRows819.assignment
    SemanticCopiesRows801.assignment CheckingInverseRows789.assignment RecoveryInverseRows781.assignment
    OutputAmountRows773.assignment DetectionNonidentityRows765.assignment BalanceFinalRows753.assignment
    MapAssignmentValues720.assignment BalanceCombined696.assignment BalanceBlindingBindings680.assignment
    BalanceSignBindings652.assignment TierFlagBindings630.assignment TierBindings617.assignment OwnershipBindings604.assignment
    PublishedInverseSeed592.assignment PublishedPointSeed584.assignment PayloadBindings565.assignment FixedFamilyBindings551.assignment
    AuthorizationRkSeed505.assignment AuthorizationFixedSeed487.assignment AuthorizationDhSeed473.assignment
    AuthorizationTraceAssignment457.assignment IvkInverseSeed426.assignment AuthorizationSharedFrame420B.assignment
    SharedAuthorizationNonidentity413.assignment
  unfold SemanticWordFrame373.assignment
  exact UserPathFrame363.sender_siblings _ _ w initial senderInitial receiverInitial level slot
theorem sender_coordinate (slot : Fin 3) (offset : Fin 8) :
    VolumePathAssignment942.assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial (1504+8*slot.val+offset.val)=UserSubgroupSeed352.value w.sender senderInitial slot offset.val := by
  unfold VolumePathAssignment942.assignment VolumeHashAssignment892.assignment RoutingParameterAssignment872.assignment
    VolumeCandidateAssignment854.assignment VolumeBoundaryAssignment842.assignment RoutingPrecisionRows819.assignment
    SemanticCopiesRows801.assignment CheckingInverseRows789.assignment RecoveryInverseRows781.assignment
    OutputAmountRows773.assignment DetectionNonidentityRows765.assignment BalanceFinalRows753.assignment
    MapAssignmentValues720.assignment BalanceCombined696.assignment BalanceBlindingBindings680.assignment
    BalanceSignBindings652.assignment TierFlagBindings630.assignment TierBindings617.assignment OwnershipBindings604.assignment
    PublishedInverseSeed592.assignment PublishedPointSeed584.assignment PayloadBindings565.assignment FixedFamilyBindings551.assignment
    AuthorizationRkSeed505.assignment AuthorizationFixedSeed487.assignment AuthorizationDhSeed473.assignment
    AuthorizationTraceAssignment457.assignment IvkInverseSeed426.assignment AuthorizationSharedFrame420B.assignment
    SharedAuthorizationNonidentity413.assignment
  unfold SemanticWordFrame373.assignment
  exact UserSubgroupFrame354.sender_value _ _ w initial senderInitial receiverInitial slot offset
theorem receiver_siblings (level : Fin 16) (slot : Fin 3) :
    VolumePathAssignment942.assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial (1769+3*level.val+slot.val)=(w.receiver.siblings level slot:F) := by
  unfold VolumePathAssignment942.assignment VolumeHashAssignment892.assignment RoutingParameterAssignment872.assignment
    VolumeCandidateAssignment854.assignment VolumeBoundaryAssignment842.assignment RoutingPrecisionRows819.assignment
    SemanticCopiesRows801.assignment CheckingInverseRows789.assignment RecoveryInverseRows781.assignment
    OutputAmountRows773.assignment DetectionNonidentityRows765.assignment BalanceFinalRows753.assignment
    MapAssignmentValues720.assignment BalanceCombined696.assignment BalanceBlindingBindings680.assignment
    BalanceSignBindings652.assignment TierFlagBindings630.assignment TierBindings617.assignment OwnershipBindings604.assignment
    PublishedInverseSeed592.assignment PublishedPointSeed584.assignment PayloadBindings565.assignment FixedFamilyBindings551.assignment
    AuthorizationRkSeed505.assignment AuthorizationFixedSeed487.assignment AuthorizationDhSeed473.assignment
    AuthorizationTraceAssignment457.assignment IvkInverseSeed426.assignment AuthorizationSharedFrame420B.assignment
    SharedAuthorizationNonidentity413.assignment
  unfold SemanticWordFrame373.assignment
  exact UserPathFrame363.receiver_siblings _ _ w initial senderInitial receiverInitial level slot
theorem receiver_coordinate (slot : Fin 3) (offset : Fin 8) :
    VolumePathAssignment942.assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial (1742+8*slot.val+offset.val)=UserSubgroupSeed352.value w.receiver receiverInitial slot offset.val := by
  unfold VolumePathAssignment942.assignment VolumeHashAssignment892.assignment RoutingParameterAssignment872.assignment
    VolumeCandidateAssignment854.assignment VolumeBoundaryAssignment842.assignment RoutingPrecisionRows819.assignment
    SemanticCopiesRows801.assignment CheckingInverseRows789.assignment RecoveryInverseRows781.assignment
    OutputAmountRows773.assignment DetectionNonidentityRows765.assignment BalanceFinalRows753.assignment
    MapAssignmentValues720.assignment BalanceCombined696.assignment BalanceBlindingBindings680.assignment
    BalanceSignBindings652.assignment TierFlagBindings630.assignment TierBindings617.assignment OwnershipBindings604.assignment
    PublishedInverseSeed592.assignment PublishedPointSeed584.assignment PayloadBindings565.assignment FixedFamilyBindings551.assignment
    AuthorizationRkSeed505.assignment AuthorizationFixedSeed487.assignment AuthorizationDhSeed473.assignment
    AuthorizationTraceAssignment457.assignment IvkInverseSeed426.assignment AuthorizationSharedFrame420B.assignment
    SharedAuthorizationNonidentity413.assignment
  unfold SemanticWordFrame373.assignment
  exact UserSubgroupFrame354.receiver_value _ _ w initial senderInitial receiverInitial slot offset
theorem commitments :
    VolumePathAssignment942.assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial 1528=(w.sender.rnkCommitment:F) ∧
    VolumePathAssignment942.assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial 1766=(w.receiver.rnkCommitment:F) := by
  unfold VolumePathAssignment942.assignment VolumeHashAssignment892.assignment RoutingParameterAssignment872.assignment
    VolumeCandidateAssignment854.assignment VolumeBoundaryAssignment842.assignment RoutingPrecisionRows819.assignment
    SemanticCopiesRows801.assignment CheckingInverseRows789.assignment RecoveryInverseRows781.assignment
    OutputAmountRows773.assignment DetectionNonidentityRows765.assignment BalanceFinalRows753.assignment
    MapAssignmentValues720.assignment BalanceCombined696.assignment BalanceBlindingBindings680.assignment
    BalanceSignBindings652.assignment TierFlagBindings630.assignment TierBindings617.assignment OwnershipBindings604.assignment
    PublishedInverseSeed592.assignment PublishedPointSeed584.assignment PayloadBindings565.assignment FixedFamilyBindings551.assignment
    AuthorizationRkSeed505.assignment AuthorizationFixedSeed487.assignment AuthorizationDhSeed473.assignment
    AuthorizationTraceAssignment457.assignment IvkInverseSeed426.assignment AuthorizationSharedFrame420B.assignment
    SharedAuthorizationNonidentity413.assignment
  unfold SemanticWordFrame373.assignment
  exact UserPathFrame363.commitments _ _ w initial senderInitial receiverInitial
theorem regulated :
    VolumePathAssignment942.assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial 10=(if w.regulated then 1 else 0) := by
  unfold VolumePathAssignment942.assignment VolumeHashAssignment892.assignment RoutingParameterAssignment872.assignment
    VolumeCandidateAssignment854.assignment VolumeBoundaryAssignment842.assignment RoutingPrecisionRows819.assignment
    SemanticCopiesRows801.assignment CheckingInverseRows789.assignment RecoveryInverseRows781.assignment
    OutputAmountRows773.assignment DetectionNonidentityRows765.assignment BalanceFinalRows753.assignment
    MapAssignmentValues720.assignment BalanceCombined696.assignment BalanceBlindingBindings680.assignment
    BalanceSignBindings652.assignment TierFlagBindings630.assignment TierBindings617.assignment OwnershipBindings604.assignment
    PublishedInverseSeed592.assignment PublishedPointSeed584.assignment PayloadBindings565.assignment FixedFamilyBindings551.assignment
    AuthorizationRkSeed505.assignment AuthorizationFixedSeed487.assignment AuthorizationDhSeed473.assignment
    AuthorizationTraceAssignment457.assignment IvkInverseSeed426.assignment AuthorizationSharedFrame420B.assignment
    SharedAuthorizationNonidentity413.assignment
  unfold SemanticWordFrame373.assignment
  exact UserLifecycleWord345.control _ _ w initial
end ShielddSecurity.UserPathWitness961

set_option pp.all true in
#check @ShielddSecurity.UserPathWitness961.sender_siblings
#print axioms ShielddSecurity.UserPathWitness961.sender_siblings

set_option pp.all true in
#check @ShielddSecurity.UserPathWitness961.sender_coordinate
#print axioms ShielddSecurity.UserPathWitness961.sender_coordinate

set_option pp.all true in
#check @ShielddSecurity.UserPathWitness961.receiver_siblings
#print axioms ShielddSecurity.UserPathWitness961.receiver_siblings

set_option pp.all true in
#check @ShielddSecurity.UserPathWitness961.receiver_coordinate
#print axioms ShielddSecurity.UserPathWitness961.receiver_coordinate

set_option pp.all true in
#check @ShielddSecurity.UserPathWitness961.commitments
#print axioms ShielddSecurity.UserPathWitness961.commitments

set_option pp.all true in
#check @ShielddSecurity.UserPathWitness961.regulated
#print axioms ShielddSecurity.UserPathWitness961.regulated
