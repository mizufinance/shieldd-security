import ShielddSecurity.RecoveryInverseCapture779
import ShielddSecurity.RecoveryInverseFrame777
import ShielddSecurity.OutputAmountRows773
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.RecoveryInverseBindings780
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
open ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem
open OutputAmountRows773 (assignment)
attribute [local irreducible] model assignment MapAssignmentValues720.assignment BalanceFinalRows753.assignment
  DetectionNonidentityRows765.assignment SatisfiesAt

theorem operand_column (slot : Fin 2) : FixedPublishedRows580.rightColumn (RecoveryInverseSeed778.family slot)=
    RecoveryInverseSeed778.operand slot := by
  rcases slot with ⟨slot,bound⟩
  have cases : slot=0 ∨ slot=1 := by omega
  rcases cases with rfl|rfl <;> rfl

theorem hint_inside (slot : Fin 2) : RecoveryInverseLayout775.Inside (RecoveryInverseSeed778.hint slot) := by
  rcases slot with ⟨slot,bound⟩
  have cases : slot=0 ∨ slot=1 := by omega
  rcases cases with rfl|rfl <;>
    simp [RecoveryInverseLayout775.Inside,RecoveryInverseLayout775.values,RecoveryInverseSeed778.hint]

variable (original : Nat → F) (u : F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F)

theorem point (slot : Fin 2) : VariableWindowColumns449.columnPoint
    (assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial)
    (RecoveryInverseSeed778.operand slot)=
      SubgroupSeedCompletion203.fieldPoint (FixedFamilyPublished579.published w (RecoveryInverseSeed778.family slot)) := by
  rw [←operand_column slot]
  unfold assignment DetectionNonidentityRows765.assignment BalanceFinalRows753.assignment MapAssignmentValues720.assignment
    BalanceCombined696.assignment BalanceBlindingBindings680.assignment BalanceSignBindings652.assignment
    TierFlagBindings630.assignment TierBindings617.assignment OwnershipBindings604.assignment PublishedInverseSeed592.assignment
  exact PublishedPointSeed584.published_point _ (DetectionGroupDomain611.baseCrypto (BalanceBlindingDomain670.withBlinding c))
    w legal rkInitial authInitial initial senderInitial receiverInitial (RecoveryInverseSeed778.family slot)

theorem operand (slot : Fin 2) :
    assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial (RecoveryInverseSeed778.operand slot)=
      RecoveryInverseSeed778.value w slot :=
  congrArg Group.Point.x (point original u c w legal rkInitial authInitial initial senderInitial receiverInitial slot)

theorem copied : assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial copy=1 := by
  unfold assignment
  exact OutputAmountBindings772.copied _ u c w legal rkInitial authInitial initial senderInitial receiverInitial

theorem arithmetic : SatisfiesAt
    (assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial)
    CapturedFullArithmetic52.rowAt 177954 := by
  unfold assignment
  exact OutputAmountBindings772.arithmetic _ u c w legal rkInitial authInitial initial senderInitial receiverInitial

theorem hint (slot : Fin 2) :
    assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial (RecoveryInverseSeed778.hint slot)=
      original (RecoveryInverseSeed778.hint slot) := by
  have inside := hint_inside slot
  have bounds := RecoveryInverseLayout775.bounds _ inside
  unfold assignment DetectionNonidentityRows765.assignment BalanceFinalRows753.assignment MapAssignmentValues720.assignment BalanceCombined696.assignment
  rw [RecoveryInverseFrame777.blinding_frame _ c w legal rkInitial authInitial initial senderInitial receiverInitial _ inside,
    BalanceMagnitudeTrace640.outside _ _ _ _ (Or.inl (by omega)),
    BalanceMapSeed703.outside _ u _ (by
      simp only [BalanceMapSeed703.columns,List.mem_cons,List.not_mem_nil,or_false];omega)]
  simp only [BalanceFinalDomain751.seed,DetectionNonidentityDomain759.seed,OutputAmountDomain767.seed,
    if_neg (show RecoveryInverseSeed778.hint slot≠22736 by omega),
    if_neg (show RecoveryInverseSeed778.hint slot≠1503 by omega),
    if_neg (show RecoveryInverseSeed778.hint slot≠4919 by omega)]
end ShielddSecurity.RecoveryInverseBindings780

set_option pp.all true in
#check @ShielddSecurity.RecoveryInverseBindings780.operand_column
#print axioms ShielddSecurity.RecoveryInverseBindings780.operand_column

set_option pp.all true in
#check @ShielddSecurity.RecoveryInverseBindings780.hint_inside
#print axioms ShielddSecurity.RecoveryInverseBindings780.hint_inside

set_option pp.all true in
#check @ShielddSecurity.RecoveryInverseBindings780.point
#print axioms ShielddSecurity.RecoveryInverseBindings780.point

set_option pp.all true in
#check @ShielddSecurity.RecoveryInverseBindings780.operand
#print axioms ShielddSecurity.RecoveryInverseBindings780.operand

set_option pp.all true in
#check @ShielddSecurity.RecoveryInverseBindings780.copied
#print axioms ShielddSecurity.RecoveryInverseBindings780.copied

set_option pp.all true in
#check @ShielddSecurity.RecoveryInverseBindings780.arithmetic
#print axioms ShielddSecurity.RecoveryInverseBindings780.arithmetic

set_option pp.all true in
#check @ShielddSecurity.RecoveryInverseBindings780.hint
#print axioms ShielddSecurity.RecoveryInverseBindings780.hint
