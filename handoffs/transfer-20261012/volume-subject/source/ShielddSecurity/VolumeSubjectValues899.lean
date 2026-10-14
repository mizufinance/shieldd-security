import ShielddSecurity.VolumeHashAssignment892
import ShielddSecurity.VolumeSubjectHash898
import ShielddSecurity.RoutingParameterValues879
import ShielddSecurity.MapAssetHashMeaning740
import ShielddSecurity.AuthorizationTraceBindings458
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.VolumeSubjectValues899
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
theorem asset : assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial 6=(w.asset:F) := by
  unfold assignment RoutingParameterAssignment872.assignment VolumeCandidateAssignment854.assignment VolumeBoundaryAssignment842.assignment RoutingPrecisionRows819.assignment SemanticCopiesRows801.assignment CheckingInverseRows789.assignment RecoveryInverseRows781.assignment OutputAmountRows773.assignment DetectionNonidentityRows765.assignment BalanceFinalRows753.assignment
  exact MapAssetHashMeaning740.asset _ u c w legal rkInitial authInitial initial senderInitial receiverInitial

theorem sender_point (slot : Fin 3) :
    VariableWindowColumns449.columnPoint (assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial) (1504+8*slot.val)=
      SubgroupSeedCompletion203.fieldPoint (UserPointDomain351.point w.sender slot) := by
  unfold assignment RoutingParameterAssignment872.assignment VolumeCandidateAssignment854.assignment VolumeBoundaryAssignment842.assignment RoutingPrecisionRows819.assignment SemanticCopiesRows801.assignment CheckingInverseRows789.assignment RecoveryInverseRows781.assignment OutputAmountRows773.assignment DetectionNonidentityRows765.assignment BalanceFinalRows753.assignment MapAssignmentValues720.assignment BalanceCombined696.assignment BalanceBlindingBindings680.assignment
    BalanceSignBindings652.assignment TierFlagBindings630.assignment TierBindings617.assignment OwnershipBindings604.assignment
    PublishedInverseSeed592.assignment PublishedPointSeed584.assignment PayloadBindings565.assignment FixedFamilyBindings551.assignment
    AuthorizationRkSeed505.assignment AuthorizationFixedSeed487.assignment AuthorizationDhSeed473.assignment
  exact AuthorizationTraceBindings458.sender_point _ _ w legal authInitial initial senderInitial receiverInitial slot

theorem sender_coordinates :
    assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial 1504=(w.sender.address.diversified.x:F) ∧
    assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial 1505=(w.sender.address.diversified.y:F) ∧
    assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial 1512=(w.sender.address.transmission.x:F) ∧
    assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial 1513=(w.sender.address.transmission.y:F) := by
  have diversified := sender_point original u c w legal rkInitial authInitial initial senderInitial receiverInitial 0
  have transmission := sender_point original u c w legal rkInitial authInitial initial senderInitial receiverInitial 1
  exact ⟨congrArg Group.Point.x diversified,congrArg Group.Point.y diversified,
    congrArg Group.Point.x transmission,congrArg Group.Point.y transmission⟩

theorem arithmetic : SatisfiesAt (assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial) CapturedFullArithmetic52.rowAt 177954 := by
  unfold assignment
  exact RoutingParameterValues879.arithmetic _ u c w legal rkInitial authInitial initial senderInitial receiverInitial
theorem copied : assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial CapturedInitial73419Generic01.copy=1 := by
  unfold assignment
  exact RoutingParameterValues879.copied _ u c w legal rkInitial authInitial initial senderInitial receiverInitial
theorem zero : assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial 0=1 := by
  unfold assignment
  exact RoutingParameterValues879.zero _ u c w legal rkInitial authInitial initial senderInitial receiverInitial

theorem inputs : TierFlagMeaning619.Inputs (assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial) w := by
  unfold assignment RoutingParameterAssignment872.assignment VolumeCandidateAssignment854.assignment VolumeBoundaryAssignment842.assignment
  exact VolumeTransitionBindings827.inputs _ u c w legal rkInitial authInitial initial senderInitial receiverInitial

theorem natural_hash (c : Crypto) (w : TransferSem.Witness) :
    ((BalanceBlindingDomain670.crypto c).hash .volumeSubject (addressFields w.sender.address++[w.asset]):F)=
    Poseidon.hash6 (Poseidon.castParameters VolumeSubjectHash898.parameters) 4
      [(w.sender.address.diversified.x:F),(w.sender.address.diversified.y:F),
       (w.sender.address.transmission.x:F),(w.sender.address.transmission.y:F),(w.asset:F)] := by
  change (PoseidonNatural192.hash RegistryNatural193.small RegistryNatural193.wide ConcreteRegistrySharedEncoding294.representation
    .volumeSubject (addressFields w.sender.address++[w.asset]):F)=_
  rw [show Poseidon.castParameters VolumeSubjectHash898.parameters=(RegistryNatural193.wide : Poseidon.Parameters F 6) from rfl]
  rw [PoseidonNatural192.hash_cast]
  unfold Poseidon.hash
  rw [if_neg (by change ¬5≤2;decide)]
  rfl

theorem hash_value : eval (assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial) VolumeSubjectHash898.result=
    ((BalanceBlindingDomain670.crypto c).hash .volumeSubject (addressFields w.sender.address++[w.asset]):F) := by
  have z := zero original u c w legal rkInitial authInitial initial senderInitial receiverInitial
  have cp := copied original u c w legal rkInitial authInitial initial senderInitial receiverInitial
  have ar := arithmetic original u c w legal rkInitial authInitial initial senderInitial receiverInitial
  have result := VolumeSubjectHash898.hash _ z (cp.trans z.symm) ar
  have coordinates := sender_coordinates original u c w legal rkInitial authInitial initial senderInitial receiverInitial
  rw [coordinates.1,coordinates.2.1,coordinates.2.2.1,coordinates.2.2.2,asset original u c w legal rkInitial authInitial initial senderInitial receiverInitial] at result
  exact result.trans (natural_hash c w).symm
end ShielddSecurity.VolumeSubjectValues899

set_option pp.all true in
#check @ShielddSecurity.VolumeSubjectValues899.asset
#print axioms ShielddSecurity.VolumeSubjectValues899.asset

set_option pp.all true in
#check @ShielddSecurity.VolumeSubjectValues899.sender_point
#print axioms ShielddSecurity.VolumeSubjectValues899.sender_point

set_option pp.all true in
#check @ShielddSecurity.VolumeSubjectValues899.sender_coordinates
#print axioms ShielddSecurity.VolumeSubjectValues899.sender_coordinates

set_option pp.all true in
#check @ShielddSecurity.VolumeSubjectValues899.arithmetic
#print axioms ShielddSecurity.VolumeSubjectValues899.arithmetic

set_option pp.all true in
#check @ShielddSecurity.VolumeSubjectValues899.copied
#print axioms ShielddSecurity.VolumeSubjectValues899.copied

set_option pp.all true in
#check @ShielddSecurity.VolumeSubjectValues899.zero
#print axioms ShielddSecurity.VolumeSubjectValues899.zero

set_option pp.all true in
#check @ShielddSecurity.VolumeSubjectValues899.inputs
#print axioms ShielddSecurity.VolumeSubjectValues899.inputs

set_option pp.all true in
#check @ShielddSecurity.VolumeSubjectValues899.natural_hash
#print axioms ShielddSecurity.VolumeSubjectValues899.natural_hash

set_option pp.all true in
#check @ShielddSecurity.VolumeSubjectValues899.hash_value
#print axioms ShielddSecurity.VolumeSubjectValues899.hash_value
