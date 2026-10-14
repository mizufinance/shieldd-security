import ShielddSecurity.VolumePathAssignment942
import ShielddSecurity.SharedWordLimbMeaning321
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.VolumePathBits943
open Compiler CompilerArithmeticTransport41 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem
attribute [local irreducible] model

def base (original : Nat → F) (w : TransferSem.Witness)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) : Nat → F :=
  UserLifecycleWord345.originalBase (UserSubgroupSeed352.seed
    (UserPathSeed361.seed (AuthScalarSeed366.seed (RemainingWordSeed369.seed original w) w) w)
    w senderInitial receiverInitial) w

theorem number (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) (bound : w.volume.priorPosition<2^48) :
    HeaderRegisteredConstruction310.numbers (base original w senderInitial receiverInitial) c w 8387=w.volume.priorPosition := by
  change representation.value (RegisteredConstructorFrame309.prepared (base original w senderInitial receiverInitial) c w 8387)=_
  rw [RegisteredConstructorFrame309.prepared_outside _ c w 8387 (by decide) (by constructor <;> decide)]
  unfold HeaderRegistrySeed299.combined base UserLifecycleWord345.originalBase
  rw [RegistryNaturalSeed298.untouched _ w.registry 8387 (by decide +kernel) (by decide),
    HeaderRegistrySeed299.seed_outside _ c w 8387 (by decide) (by decide),
    RegistryComparisonSeed318.seed_outside _ w 8387 (by decide +kernel),
    HighZeroSeed329.outside _ w 8387 (by decide) (by decide),
    UserWordSeed342.seed_outside _ w 8387 (by decide +kernel),
    UserSubgroupSeed352.outside _ w senderInitial receiverInitial 8387 (by decide) (by decide),
    UserPathSeed361.outside _ w 8387 (by decide) (by decide) (by decide) (by decide),
    AuthScalarSeed366.seed_outside _ w 8387 (by decide +kernel),
    RemainingWordSeed369.seed_value _ w 8387 (by decide +kernel)]
  change representation.value (w.volume.priorPosition:F)=w.volume.priorPosition
  exact RegistryNaturalSeed298.represented_nat _ (lt_trans bound (by decide +kernel))

theorem semantic_bits (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (initial : Fin 4 → Group.Point F) (senderInitial receiverInitial : Fin 3 → Group.Point F)
    (bound : w.volume.priorPosition<2^48) (index : Nat) (inside : index<48) :
    SemanticWordFrame373.assignment original c w initial senderInitial receiverInitial (8460+index)=
      BooleanHints207.bitValue ((encodeBits 48 w.volume.priorPosition)[index]?.getD false) := by
  let entry : WordHints210.Slot × Nat := (CapturedWordSlots211B009.W36.slot,CapturedWordSlots211B009.W36.first)
  have member : entry∈CapturedWordRoot213.words := by simp [entry,CapturedWordRoot213.words]
  have point := SharedWordLimbMeaning321.encoded_point
    (CapturedFourSubgroupSeed89.seeded (RegisteredConstructorFrame309.prepared (base original w senderInitial receiverInitial) c w) initial)
    (LegalWordNormalization272.normalized (HeaderRegisteredConstruction310.numbers (base original w senderInitial receiverInitial) c w))
    (HeaderRegisteredConstruction310.fallback (base original w senderInitial receiverInitial) c w)
    (LegalWordNormalization272.coherent _) entry member index inside
  have fixed := (LegalWordNormalization272.fixed
    (HeaderRegisteredConstruction310.numbers (base original w senderInitial receiverInitial) c w) 8387 (by decide +kernel)).trans
    (number original c w senderInitial receiverInitial bound)
  change SemanticWordFrame373.assignment original c w initial senderInitial receiverInitial (8460+index)=
    BooleanHints207.bitValue ((encodeBits 48 (LegalWordNormalization272.normalized
      (HeaderRegisteredConstruction310.numbers (base original w senderInitial receiverInitial) c w) 8387))[index]?.getD false) at point
  rw [fixed] at point
  exact point

attribute [local irreducible] VolumePathAssignment942.assignment
  VolumeHashAssignment892.assignment RoutingParameterAssignment872.assignment VolumeCandidateAssignment854.assignment
  VolumeBoundaryAssignment842.assignment RoutingPrecisionRows819.assignment SemanticCopiesRows801.assignment
  CheckingInverseRows789.assignment RecoveryInverseRows781.assignment OutputAmountRows773.assignment
  DetectionNonidentityRows765.assignment BalanceFinalRows753.assignment MapAssignmentValues720.assignment

theorem bits (original : Nat → F) (u : F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) (index : Nat) (inside : index<48) :
    VolumePathAssignment942.assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial (8460+index)=
      BooleanHints207.bitValue ((encodeBits 48 w.volume.priorPosition)[index]?.getD false) := by
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
  exact semantic_bits _ _ w initial senderInitial receiverInitial
    legal.2.1.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.1 index inside
end ShielddSecurity.VolumePathBits943

set_option pp.all true in
#check @ShielddSecurity.VolumePathBits943.number
#print axioms ShielddSecurity.VolumePathBits943.number

set_option pp.all true in
#check @ShielddSecurity.VolumePathBits943.semantic_bits
#print axioms ShielddSecurity.VolumePathBits943.semantic_bits

set_option pp.all true in
#check @ShielddSecurity.VolumePathBits943.bits
#print axioms ShielddSecurity.VolumePathBits943.bits
