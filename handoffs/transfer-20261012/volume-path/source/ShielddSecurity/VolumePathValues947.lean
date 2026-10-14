import ShielddSecurity.VolumePathMeaning946
import ShielddSecurity.VolumeOutputValues920
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.VolumePathValues947
open Compiler CompilerAssertionBlock51 ConcreteJubjubField01 TransferSem
open VolumePathAssignment942 (assignment)
attribute [local irreducible] assignment ConcreteRegistrySharedEncoding294.model SatisfiesAt PoseidonNatural192.hash Poseidon.hash6 volumeState
variable (original : Nat → F) (u : F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F)
theorem zero : assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial 0=1 := by
  unfold assignment VolumeHashAssignment892.assignment
  exact RoutingParameterValues879.zero _ u c w legal rkInitial authInitial initial senderInitial receiverInitial
theorem copied : assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial CapturedInitial73419Generic01.copy=1 := by
  unfold assignment VolumeHashAssignment892.assignment
  exact RoutingParameterValues879.copied _ u c w legal rkInitial authInitial initial senderInitial receiverInitial
theorem arithmetic : SatisfiesAt (assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial) CapturedFullArithmetic52.rowAt 177954 := by
  unfold assignment VolumeHashAssignment892.assignment
  exact RoutingParameterValues879.arithmetic _ u c w legal rkInitial authInitial initial senderInitial receiverInitial
theorem prior : eval (assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial) VolumePriorHash908.result=
    (VolumePathMeaning946.value (BalanceBlindingDomain670.crypto c) w 0:F) := by
  rw [VolumePathMeaning946.zero]
  unfold assignment
  exact VolumePriorValues909.hash_value _ u c w legal rkInitial authInitial initial senderInitial receiverInitial

theorem base_anchor (original : Nat → F) (c : Crypto) (w : TransferSem.Witness) (initial : Fin 4 → Group.Point F) :
    HeaderRegisteredConstruction310.completed original c w initial 3=(w.anchor:F) :=
  (SharedRegulatedValue316.original_frame original c w initial 3 (by constructor <;> decide) (by decide)).trans
    ((RegisteredConstructorFrame309.prepared_outside original c w 3 (by decide) (by constructor <;> decide)).trans
      (HeaderRegistrySeed299.original_headers original c w).2.2.2.1)

theorem anchor : assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial 3=(w.anchor:F) := by
  unfold assignment VolumeHashAssignment892.assignment RoutingParameterAssignment872.assignment VolumeCandidateAssignment854.assignment VolumeBoundaryAssignment842.assignment RoutingPrecisionRows819.assignment SemanticCopiesRows801.assignment CheckingInverseRows789.assignment RecoveryInverseRows781.assignment OutputAmountRows773.assignment DetectionNonidentityRows765.assignment BalanceFinalRows753.assignment MapAssignmentValues720.assignment BalanceCombined696.assignment BalanceBlindingBindings680.assignment BalanceSignBindings652.assignment TierFlagBindings630.assignment TierBindings617.assignment OwnershipBindings604.assignment PublishedInverseSeed592.assignment PublishedPointSeed584.assignment PayloadBindings565.assignment FixedFamilyBindings551.assignment AuthorizationRkSeed505.assignment AuthorizationFixedSeed487.assignment AuthorizationDhSeed473.assignment
    AuthorizationTraceAssignment457.assignment IvkInverseSeed426.assignment AuthorizationSharedFrame420B.assignment
    SharedAuthorizationNonidentity413.assignment SemanticWordFrame373.assignment UserLifecycleWord345.assignment
    HighZeroCompletionFrame332.assignment SharedComparisonBlocks327.assignment
  exact base_anchor _ _ w initial
end ShielddSecurity.VolumePathValues947

set_option pp.all true in
#check @ShielddSecurity.VolumePathValues947.zero
#print axioms ShielddSecurity.VolumePathValues947.zero

set_option pp.all true in
#check @ShielddSecurity.VolumePathValues947.copied
#print axioms ShielddSecurity.VolumePathValues947.copied

set_option pp.all true in
#check @ShielddSecurity.VolumePathValues947.arithmetic
#print axioms ShielddSecurity.VolumePathValues947.arithmetic

set_option pp.all true in
#check @ShielddSecurity.VolumePathValues947.prior
#print axioms ShielddSecurity.VolumePathValues947.prior

set_option pp.all true in
#check @ShielddSecurity.VolumePathValues947.base_anchor
#print axioms ShielddSecurity.VolumePathValues947.base_anchor

set_option pp.all true in
#check @ShielddSecurity.VolumePathValues947.anchor
#print axioms ShielddSecurity.VolumePathValues947.anchor
