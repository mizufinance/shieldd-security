import ShielddSecurity.CheckingInverseRows789
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.VolumeTimestampBindings791
open ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem
open CheckingInverseRows789 (assignment)
attribute [local irreducible] model assignment RecoveryInverseRows781.assignment OutputAmountRows773.assignment
  DetectionNonidentityRows765.assignment BalanceFinalRows753.assignment MapAssignmentValues720.assignment

theorem header (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (initial : Fin 4 → Group.Point F) :
    HeaderRegisteredConstruction310.completed original c w initial 7=(w.timestamp:F) :=
  (SharedRegulatedValue316.original_frame original c w initial 7 (by constructor <;> decide) (by decide)).trans
    ((RegisteredConstructorFrame309.prepared_outside original c w 7 (by decide) (by constructor <;> decide)).trans
      (HeaderRegistrySeed299.original_headers original c w).2.2.2.2.2.2.2.1)

theorem base_timestamp (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    AuthorizationRkSeed505.assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial 7=(w.timestamp:F) := by
  unfold AuthorizationRkSeed505.assignment AuthorizationFixedSeed487.assignment AuthorizationDhSeed473.assignment
    AuthorizationTraceAssignment457.assignment IvkInverseSeed426.assignment AuthorizationSharedFrame420B.assignment
    SharedAuthorizationNonidentity413.assignment SemanticWordFrame373.assignment UserLifecycleWord345.assignment
    HighZeroCompletionFrame332.assignment SharedComparisonBlocks327.assignment
  exact header _ _ w initial

variable (original : Nat → F) (u : F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F)

theorem timestamp : assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial 7=(w.timestamp:F) := by
  unfold assignment RecoveryInverseRows781.assignment OutputAmountRows773.assignment DetectionNonidentityRows765.assignment
    BalanceFinalRows753.assignment MapAssignmentValues720.assignment BalanceCombined696.assignment BalanceBlindingBindings680.assignment
    BalanceSignBindings652.assignment TierFlagBindings630.assignment TierBindings617.assignment OwnershipBindings604.assignment
    PublishedInverseSeed592.assignment PublishedPointSeed584.assignment PayloadBindings565.assignment FixedFamilyBindings551.assignment
  exact base_timestamp _ _ w legal rkInitial authInitial initial senderInitial receiverInitial

theorem words (column : Nat) (member : column∈RemainingWordSeed369.values) :
    assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial column=
      (RemainingWordSeed369.value w column:F) := by
  unfold assignment RecoveryInverseRows781.assignment OutputAmountRows773.assignment DetectionNonidentityRows765.assignment
    BalanceFinalRows753.assignment MapAssignmentValues720.assignment BalanceCombined696.assignment BalanceBlindingBindings680.assignment
  exact BalanceWordValues653.values _ _ w legal rkInitial authInitial initial senderInitial receiverInitial column member

theorem relation :
    assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial 7=
      86400*assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial 7608+
      assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial 7609 := by
  have day := words original u c w legal rkInitial authInitial initial senderInitial receiverInitial 7608 (by decide)
  have second := words original u c w legal rkInitial authInitial initial senderInitial receiverInitial 7609 (by decide)
  change assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial 7608=(w.volume.dayIndex:F) at day
  change assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial 7609=(w.volume.second:F) at second
  rw [timestamp original u c w legal rkInitial authInitial initial senderInitial receiverInitial,day,second]
  have volume := legal.2.1.2.2.2.2.2.2.1
  rw [volume.2.2.2.1]
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
end ShielddSecurity.VolumeTimestampBindings791

set_option pp.all true in
#check @ShielddSecurity.VolumeTimestampBindings791.header
#print axioms ShielddSecurity.VolumeTimestampBindings791.header

set_option pp.all true in
#check @ShielddSecurity.VolumeTimestampBindings791.base_timestamp
#print axioms ShielddSecurity.VolumeTimestampBindings791.base_timestamp

set_option pp.all true in
#check @ShielddSecurity.VolumeTimestampBindings791.timestamp
#print axioms ShielddSecurity.VolumeTimestampBindings791.timestamp

set_option pp.all true in
#check @ShielddSecurity.VolumeTimestampBindings791.words
#print axioms ShielddSecurity.VolumeTimestampBindings791.words

set_option pp.all true in
#check @ShielddSecurity.VolumeTimestampBindings791.relation
#print axioms ShielddSecurity.VolumeTimestampBindings791.relation
