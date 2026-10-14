import ShielddSecurity.VolumeCandidateAssignment854
import ShielddSecurity.VolumeWordEncoding855
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.VolumeCandidateValues856
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 ConcreteJubjubField01 TransferSem
open VolumeCandidateAssignment854 (assignment)
attribute [local irreducible] ConcreteRegistrySharedEncoding294.model SatisfiesAt assignment
  VolumeBoundaryAssignment842.assignment RoutingPrecisionRows819.assignment
  SemanticCopiesRows801.assignment CheckingInverseRows789.assignment RecoveryInverseRows781.assignment
  OutputAmountRows773.assignment DetectionNonidentityRows765.assignment BalanceFinalRows753.assignment MapAssignmentValues720.assignment

variable (original : Nat → F) (u : F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F)

theorem candidate : fieldBinary ((List.range' 8127 128).map
    (assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial))=
      ((w.volume.prior+(w.outputs 0).amount:Nat):F) := by
  apply VolumeWordEncoding855.candidate _ w
  · exact legal.2.1.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.1
  · exact VolumeCandidateAssignment854.bits original u c w legal rkInitial authInitial initial senderInitial receiverInitial

theorem limit : fieldBinary ((List.range' 7999 128).map
    (assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial))=(w.registry.dailyLimit:F) := by
  unfold assignment VolumeBoundaryAssignment842.assignment RoutingPrecisionRows819.assignment
    SemanticCopiesRows801.assignment CheckingInverseRows789.assignment RecoveryInverseRows781.assignment
    OutputAmountRows773.assignment DetectionNonidentityRows765.assignment BalanceFinalRows753.assignment
    MapAssignmentValues720.assignment BalanceCombined696.assignment BalanceBlindingBindings680.assignment
    BalanceSignBindings652.assignment TierFlagBindings630.assignment TierBindings617.assignment OwnershipBindings604.assignment
    PublishedInverseSeed592.assignment PublishedPointSeed584.assignment PayloadBindings565.assignment FixedFamilyBindings551.assignment
    AuthorizationRkSeed505.assignment AuthorizationFixedSeed487.assignment AuthorizationDhSeed473.assignment
    AuthorizationTraceAssignment457.assignment IvkInverseSeed426.assignment AuthorizationSharedFrame420B.assignment
    SharedAuthorizationNonidentity413.assignment SemanticWordFrame373.assignment UserLifecycleWord345.assignment
    HighZeroCompletionFrame332.assignment SharedComparisonBlocks327.assignment
  exact VolumeWordEncoding855.header_limit _ _ w legal.1
    legal.2.1.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.1 initial

theorem words (column : Nat) (member : column∈RemainingWordSeed369.values) :
    assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial column=(RemainingWordSeed369.value w column:F) := by
  unfold assignment VolumeBoundaryAssignment842.assignment
  exact VolumeTransitionBindings827.words _ u c w legal rkInitial authInitial initial senderInitial receiverInitial column member

theorem borrow : assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial 8255=VolumeBoundarySeed836.borrow w := by
  unfold assignment
  exact VolumeBoundaryAssignment842.borrow _ u c w legal rkInitial authInitial initial senderInitial receiverInitial
end ShielddSecurity.VolumeCandidateValues856

set_option pp.all true in
#check @ShielddSecurity.VolumeCandidateValues856.candidate
#print axioms ShielddSecurity.VolumeCandidateValues856.candidate

set_option pp.all true in
#check @ShielddSecurity.VolumeCandidateValues856.limit
#print axioms ShielddSecurity.VolumeCandidateValues856.limit

set_option pp.all true in
#check @ShielddSecurity.VolumeCandidateValues856.words
#print axioms ShielddSecurity.VolumeCandidateValues856.words

set_option pp.all true in
#check @ShielddSecurity.VolumeCandidateValues856.borrow
#print axioms ShielddSecurity.VolumeCandidateValues856.borrow
