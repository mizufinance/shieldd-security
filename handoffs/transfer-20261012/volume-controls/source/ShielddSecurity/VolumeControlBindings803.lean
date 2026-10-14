import ShielddSecurity.SemanticCopiesRows801
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.VolumeControlBindings803
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
open ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem
open SemanticCopiesRows801 (assignment)
attribute [local irreducible] model assignment CheckingInverseRows789.assignment RecoveryInverseRows781.assignment
  OutputAmountRows773.assignment DetectionNonidentityRows765.assignment BalanceFinalRows753.assignment
  MapAssignmentValues720.assignment SatisfiesAt

def leftColumn (slot : Fin 4) : Nat := if slot.val=0 then 1504 else if slot.val=1 then 1505 else if slot.val=2 then 1512 else 1513
def rightColumn (slot : Fin 4) : Nat := if slot.val=0 then 1742 else if slot.val=1 then 1743 else if slot.val=2 then 1750 else 1751

variable (original : Nat → F) (u : F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F)

theorem left (slot : Fin 4) :
    assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial (leftColumn slot)=
      (TierFlagSeed623.left w slot:F) := by
  unfold assignment CheckingInverseRows789.assignment RecoveryInverseRows781.assignment OutputAmountRows773.assignment
    DetectionNonidentityRows765.assignment BalanceFinalRows753.assignment MapAssignmentValues720.assignment
    BalanceCombined696.assignment BalanceBlindingBindings680.assignment BalanceSignBindings652.assignment
    TierFlagBindings630.assignment TierBindings617.assignment OwnershipBindings604.assignment PublishedInverseSeed592.assignment
    PublishedPointSeed584.assignment PayloadBindings565.assignment FixedFamilyBindings551.assignment AuthorizationRkSeed505.assignment
    AuthorizationFixedSeed487.assignment AuthorizationDhSeed473.assignment AuthorizationTraceAssignment457.assignment
    IvkInverseSeed426.assignment AuthorizationSharedFrame420B.assignment SharedAuthorizationNonidentity413.assignment SemanticWordFrame373.assignment
  rcases slot with ⟨slot,bound⟩
  have cases : slot=0 ∨ slot=1 ∨ slot=2 ∨ slot=3 := by omega
  rcases cases with rfl|rfl|rfl|rfl
  · exact UserSubgroupFrame354.sender_value _ _ w initial senderInitial receiverInitial ⟨0,by decide⟩ ⟨0,by decide⟩
  · exact UserSubgroupFrame354.sender_value _ _ w initial senderInitial receiverInitial ⟨0,by decide⟩ ⟨1,by decide⟩
  · exact UserSubgroupFrame354.sender_value _ _ w initial senderInitial receiverInitial ⟨1,by decide⟩ ⟨0,by decide⟩
  · exact UserSubgroupFrame354.sender_value _ _ w initial senderInitial receiverInitial ⟨1,by decide⟩ ⟨1,by decide⟩

theorem right (slot : Fin 4) :
    assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial (rightColumn slot)=
      (TierFlagSeed623.right w slot:F) := by
  unfold assignment CheckingInverseRows789.assignment RecoveryInverseRows781.assignment OutputAmountRows773.assignment
    DetectionNonidentityRows765.assignment BalanceFinalRows753.assignment MapAssignmentValues720.assignment
    BalanceCombined696.assignment BalanceBlindingBindings680.assignment BalanceSignBindings652.assignment
    TierFlagBindings630.assignment TierBindings617.assignment OwnershipBindings604.assignment PublishedInverseSeed592.assignment
    PublishedPointSeed584.assignment PayloadBindings565.assignment FixedFamilyBindings551.assignment AuthorizationRkSeed505.assignment
    AuthorizationFixedSeed487.assignment AuthorizationDhSeed473.assignment AuthorizationTraceAssignment457.assignment
    IvkInverseSeed426.assignment AuthorizationSharedFrame420B.assignment SharedAuthorizationNonidentity413.assignment SemanticWordFrame373.assignment
  rcases slot with ⟨slot,bound⟩
  have cases : slot=0 ∨ slot=1 ∨ slot=2 ∨ slot=3 := by omega
  rcases cases with rfl|rfl|rfl|rfl
  · exact UserSubgroupFrame354.receiver_value _ _ w initial senderInitial receiverInitial ⟨0,by decide⟩ ⟨0,by decide⟩
  · exact UserSubgroupFrame354.receiver_value _ _ w initial senderInitial receiverInitial ⟨0,by decide⟩ ⟨1,by decide⟩
  · exact UserSubgroupFrame354.receiver_value _ _ w initial senderInitial receiverInitial ⟨1,by decide⟩ ⟨0,by decide⟩
  · exact UserSubgroupFrame354.receiver_value _ _ w initial senderInitial receiverInitial ⟨1,by decide⟩ ⟨1,by decide⟩

theorem flag (slot : Fin 4) :
    assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial (7597+2*slot.val)=FieldZeroSeed125.flag (TierFlagSeed623.delta w slot) := by
  unfold assignment CheckingInverseRows789.assignment RecoveryInverseRows781.assignment OutputAmountRows773.assignment
    DetectionNonidentityRows765.assignment BalanceFinalRows753.assignment MapAssignmentValues720.assignment
    BalanceCombined696.assignment BalanceBlindingBindings680.assignment BalanceSignBindings652.assignment
  have member : 7597+2*slot.val∈TierFlagLayout620.columns := by
    have bound := slot.isLt
    apply List.mem_range'.mpr
    exact ⟨2*slot.val,by omega,by omega⟩
  exact (TierFlagBindings630.flag_frame _ _ w legal rkInitial authInitial initial senderInitial receiverInitial _ member).trans
    (TierFlagSeed623.flag _ w slot)

theorem inverse (slot : Fin 4) :
    assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial (7598+2*slot.val)=(TierFlagSeed623.delta w slot)⁻¹ := by
  unfold assignment CheckingInverseRows789.assignment RecoveryInverseRows781.assignment OutputAmountRows773.assignment
    DetectionNonidentityRows765.assignment BalanceFinalRows753.assignment MapAssignmentValues720.assignment
    BalanceCombined696.assignment BalanceBlindingBindings680.assignment BalanceSignBindings652.assignment
  have member : 7598+2*slot.val∈TierFlagLayout620.columns := by
    have bound := slot.isLt
    apply List.mem_range'.mpr
    exact ⟨1+2*slot.val,by omega,by omega⟩
  exact (TierFlagBindings630.flag_frame _ _ w legal rkInitial authInitial initial senderInitial receiverInitial _ member).trans
    (TierFlagSeed623.inverse _ w slot)

theorem context : assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial 7607=(w.volume.context:F) := by
  unfold assignment CheckingInverseRows789.assignment RecoveryInverseRows781.assignment OutputAmountRows773.assignment
    DetectionNonidentityRows765.assignment BalanceFinalRows753.assignment MapAssignmentValues720.assignment
    BalanceCombined696.assignment BalanceBlindingBindings680.assignment BalanceSignBindings652.assignment
  exact (TierFlagBindings630.inputs _ _ w legal rkInitial authInitial initial senderInitial receiverInitial).context

theorem copied : assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial copy=1 := by
  unfold assignment CheckingInverseRows789.assignment
  exact CheckingInverseBindings788.copied _ u c w legal rkInitial authInitial initial senderInitial receiverInitial

theorem arithmetic : SatisfiesAt (assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial)
    CapturedFullArithmetic52.rowAt 177954 := by
  unfold assignment CheckingInverseRows789.assignment
  exact CheckingInverseBindings788.arithmetic _ u c w legal rkInitial authInitial initial senderInitial receiverInitial
end ShielddSecurity.VolumeControlBindings803

set_option pp.all true in
#check @ShielddSecurity.VolumeControlBindings803.left
#print axioms ShielddSecurity.VolumeControlBindings803.left

set_option pp.all true in
#check @ShielddSecurity.VolumeControlBindings803.right
#print axioms ShielddSecurity.VolumeControlBindings803.right

set_option pp.all true in
#check @ShielddSecurity.VolumeControlBindings803.flag
#print axioms ShielddSecurity.VolumeControlBindings803.flag

set_option pp.all true in
#check @ShielddSecurity.VolumeControlBindings803.inverse
#print axioms ShielddSecurity.VolumeControlBindings803.inverse

set_option pp.all true in
#check @ShielddSecurity.VolumeControlBindings803.context
#print axioms ShielddSecurity.VolumeControlBindings803.context

set_option pp.all true in
#check @ShielddSecurity.VolumeControlBindings803.copied
#print axioms ShielddSecurity.VolumeControlBindings803.copied

set_option pp.all true in
#check @ShielddSecurity.VolumeControlBindings803.arithmetic
#print axioms ShielddSecurity.VolumeControlBindings803.arithmetic
