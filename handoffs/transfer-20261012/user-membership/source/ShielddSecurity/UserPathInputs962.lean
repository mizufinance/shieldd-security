import ShielddSecurity.VolumePathAssignment942
import ShielddSecurity.QuaternarySelector944
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.UserPathInputs962
open Compiler CompilerArithmeticTransport41 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem
attribute [local irreducible] model
attribute [local irreducible] VolumePathAssignment942.assignment
  VolumeHashAssignment892.assignment RoutingParameterAssignment872.assignment VolumeCandidateAssignment854.assignment
  VolumeBoundaryAssignment842.assignment RoutingPrecisionRows819.assignment SemanticCopiesRows801.assignment
  CheckingInverseRows789.assignment RecoveryInverseRows781.assignment OutputAmountRows773.assignment
  DetectionNonidentityRows765.assignment BalanceFinalRows753.assignment MapAssignmentValues720.assignment

theorem word_unselected (column : Nat) (member : column∈UserWordSeed342.values) :
    column∉SharedWordWitness221.seedColumns ∧ column∉CapturedFourSubgroupSeed89.hintColumns := by
  have ranges : (1504≤column ∧ column<1579) ∨ (1742≤column ∧ column<1817) := by
    simp only [UserWordSeed342.values,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl <;> omega
  constructor
  · intro selected
    rcases List.mem_append.mp selected with boolean|word
    · obtain ⟨slot,present,equal⟩ := List.mem_map.mp boolean
      have excluded := of_decide_eq_true (List.all_eq_true.mp UserRecordAvoid362.checked slot present)
      change slot.2=column at equal
      rw [equal] at excluded
      exact Or.elim ranges excluded.1 excluded.2
    · obtain ⟨slot,present,inWindow⟩ := List.mem_flatMap.mp word
      obtain ⟨entry,known,equal⟩ := List.mem_map.mp present
      subst slot
      have outside := of_decide_eq_true (List.all_eq_true.mp UserPathFrame363.word_windows_checked entry known)
      obtain ⟨offset,bound,atColumn⟩ := List.mem_range'.mp inWindow
      simp only [Nat.one_mul] at atColumn
      omega
  · simp only [UserWordSeed342.values,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl <;> decide +kernel

theorem semantic_word (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (initial : Fin 4 → Group.Point F) (senderInitial receiverInitial : Fin 3 → Group.Point F)
    (column : Nat) (member : column∈UserWordSeed342.values) :
    SemanticWordFrame373.assignment original c w initial senderInitial receiverInitial column=(UserWordSeed342.value w column:F) := by
  have bounds : 135≤column ∧ column<2000 := by
    simp only [UserWordSeed342.values,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl <;> constructor <;> decide
  have outside := word_unselected column member
  unfold SemanticWordFrame373.assignment UserLifecycleWord345.assignment HighZeroCompletionFrame332.assignment
    SharedComparisonBlocks327.assignment HeaderRegisteredConstruction310.completed SharedWordWitness221.completed
  apply Eq.trans (SharedRegisteredGeneral308.candidate_original _ column (by omega) (by omega))
  apply Eq.trans (BooleanHints207.seeded_outside _ _ _ column outside.1)
  apply Eq.trans (CapturedFourSubgroupSeed89.seeded_outside _ initial column outside.2)
  rw [RegisteredConstructorFrame309.prepared_outside _ c w column (Or.inr bounds.1)
    (by change column≠200692 ∧ column≠1 ∧ column≠2;omega)]
  exact UserWordSeed342.combined_value _ c w column member

variable (original : Nat → F) (u : F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F)
theorem words (column : Nat) (member : column∈UserWordSeed342.values) :
    VolumePathAssignment942.assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial column=(UserWordSeed342.value w column:F) := by
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
  exact semantic_word _ _ w initial senderInitial receiverInitial column member
theorem sender_bits (index : Nat) (inside : index<32) :
    VolumePathAssignment942.assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial (1579+index)=BooleanHints207.bitValue ((encodeBits 32 w.sender.position)[index]?.getD false) := by
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
  exact UserLifecycleWord345.selected_bits _ _ w initial legal
    (CapturedWordSlots211B002.W11.slot,CapturedWordSlots211B002.W11.first) (by simp [CapturedWordRoot213.words]) (by decide +kernel) index inside
theorem receiver_bits (index : Nat) (inside : index<32) :
    VolumePathAssignment942.assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial (1817+index)=BooleanHints207.bitValue ((encodeBits 32 w.receiver.position)[index]?.getD false) := by
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
  exact UserLifecycleWord345.selected_bits _ _ w initial legal
    (CapturedWordSlots211B003.W14.slot,CapturedWordSlots211B003.W14.first) (by simp [CapturedWordRoot213.words]) (by decide +kernel) index inside
theorem asset : VolumePathAssignment942.assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial 6=(w.asset:F) := by
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
  unfold UserLifecycleWord345.assignment HighZeroCompletionFrame332.assignment SharedComparisonBlocks327.assignment
  exact SharedRegulatedValue316.asset_meaning _ _ w initial
theorem anchor : VolumePathAssignment942.assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial 5=(w.userAnchor:F) := by
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
  unfold UserLifecycleWord345.assignment HighZeroCompletionFrame332.assignment SharedComparisonBlocks327.assignment
  apply Eq.trans (SharedRegulatedValue316.original_frame _ _ w initial 5 (by constructor <;> decide) (by decide))
  rw [RegisteredConstructorFrame309.prepared_outside _ _ w 5 (by decide) (by constructor <;> decide)]
  exact (HeaderRegistrySeed299.original_headers _ _ w).2.2.2.2.2.1
theorem encoded_slot (position level : Nat) (inside : level<16) :
    (if (encodeBits 32 position)[2*level+1]?.getD false then
      (if (encodeBits 32 position)[2*level]?.getD false then 3 else 2)
    else (if (encodeBits 32 position)[2*level]?.getD false then 1 else 0))=position/4^level%4 := by
  rw [UserLifecycleBits344.encoded_bit 32 position (2*level+1) (by omega),
    UserLifecycleBits344.encoded_bit 32 position (2*level) (by omega)]
  exact QuaternarySelector944.bit_slot position level
end ShielddSecurity.UserPathInputs962

set_option pp.all true in
#check @ShielddSecurity.UserPathInputs962.word_unselected
#print axioms ShielddSecurity.UserPathInputs962.word_unselected

set_option pp.all true in
#check @ShielddSecurity.UserPathInputs962.semantic_word
#print axioms ShielddSecurity.UserPathInputs962.semantic_word

set_option pp.all true in
#check @ShielddSecurity.UserPathInputs962.words
#print axioms ShielddSecurity.UserPathInputs962.words

set_option pp.all true in
#check @ShielddSecurity.UserPathInputs962.sender_bits
#print axioms ShielddSecurity.UserPathInputs962.sender_bits

set_option pp.all true in
#check @ShielddSecurity.UserPathInputs962.receiver_bits
#print axioms ShielddSecurity.UserPathInputs962.receiver_bits

set_option pp.all true in
#check @ShielddSecurity.UserPathInputs962.asset
#print axioms ShielddSecurity.UserPathInputs962.asset

set_option pp.all true in
#check @ShielddSecurity.UserPathInputs962.anchor
#print axioms ShielddSecurity.UserPathInputs962.anchor

set_option pp.all true in
#check @ShielddSecurity.UserPathInputs962.encoded_slot
#print axioms ShielddSecurity.UserPathInputs962.encoded_slot
