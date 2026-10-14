import ShielddSecurity.CheckingInverseCapture787
import ShielddSecurity.CheckingInverseFrame786
import ShielddSecurity.RecoveryInverseRows781
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CheckingInverseBindings788
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
open ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem
open RecoveryInverseRows781 (assignment)
attribute [local irreducible] model assignment MapAssignmentValues720.assignment BalanceFinalRows753.assignment
  DetectionNonidentityRows765.assignment OutputAmountRows773.assignment SatisfiesAt

theorem hint_inside (slot : Fin 2) : CheckingInverseLayout784.Inside (CheckingInverseSeed783.hint slot) := by
  rcases slot with ⟨slot,bound⟩
  have cases : slot=0 ∨ slot=1 := by omega
  rcases cases with rfl|rfl <;>
    simp [CheckingInverseLayout784.Inside,CheckingInverseLayout784.values,CheckingInverseSeed783.hint]

variable (original : Nat → F) (u : F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F)

theorem inputs : CheckingInputFrame596.Inputs
    (assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial) w := by
  unfold assignment OutputAmountRows773.assignment DetectionNonidentityRows765.assignment BalanceFinalRows753.assignment
    MapAssignmentValues720.assignment BalanceCombined696.assignment BalanceBlindingBindings680.assignment
    BalanceSignBindings652.assignment TierFlagBindings630.assignment TierBindings617.assignment OwnershipBindings604.assignment
  exact CheckingBase598.inputs _ (DetectionGroupDomain611.baseCrypto (BalanceBlindingDomain670.withBlinding c))
    w legal rkInitial authInitial initial senderInitial receiverInitial

theorem copied : assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial copy=1 := by
  unfold assignment
  exact RecoveryInverseBindings780.copied _ u c w legal rkInitial authInitial initial senderInitial receiverInitial

theorem arithmetic : SatisfiesAt
    (assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial)
    CapturedFullArithmetic52.rowAt 177954 := by
  unfold assignment
  exact RecoveryInverseBindings780.arithmetic _ u c w legal rkInitial authInitial initial senderInitial receiverInitial

theorem operand : eval (assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial)
    CheckingBase598.baseX=CheckingInverseSeed783.value
      (DetectionGroupDomain611.baseCrypto (BalanceBlindingDomain670.withBlinding c)) w := by
  have point := CheckingBase598.selected _ (DetectionGroupDomain611.baseCrypto (BalanceBlindingDomain670.withBlinding c)) w
    (copied original u c w legal rkInitial authInitial initial senderInitial receiverInitial)
    (arithmetic original u c w legal rkInitial authInitial initial senderInitial receiverInitial)
    (inputs original u c w legal rkInitial authInitial initial senderInitial receiverInitial)
  exact congrArg Group.Point.x point

theorem hint (slot : Fin 2) :
    assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial (CheckingInverseSeed783.hint slot)=
      original (CheckingInverseSeed783.hint slot) := by
  have inside := hint_inside slot
  have bounds := CheckingInverseLayout784.bounds _ inside
  unfold assignment OutputAmountRows773.assignment DetectionNonidentityRows765.assignment BalanceFinalRows753.assignment
    MapAssignmentValues720.assignment BalanceCombined696.assignment
  rw [CheckingInverseFrame786.blinding_frame _ c w legal rkInitial authInitial initial senderInitial receiverInitial _ inside,
    BalanceMagnitudeTrace640.outside _ _ _ _ (Or.inl (by omega)),
    BalanceMapSeed703.outside _ u _ (by
      simp only [BalanceMapSeed703.columns,List.mem_cons,List.not_mem_nil,or_false];omega)]
  simp only [BalanceFinalDomain751.seed,DetectionNonidentityDomain759.seed,OutputAmountDomain767.seed,RecoveryInverseSeed778.seed,
    if_neg (show CheckingInverseSeed783.hint slot≠22736 by omega),
    if_neg (show CheckingInverseSeed783.hint slot≠1503 by omega),
    if_neg (show CheckingInverseSeed783.hint slot≠4919 by omega),
    if_neg (show CheckingInverseSeed783.hint slot≠6192 by omega),
    if_neg (show CheckingInverseSeed783.hint slot≠7596 by omega)]
end ShielddSecurity.CheckingInverseBindings788

set_option pp.all true in
#check @ShielddSecurity.CheckingInverseBindings788.hint_inside
#print axioms ShielddSecurity.CheckingInverseBindings788.hint_inside

set_option pp.all true in
#check @ShielddSecurity.CheckingInverseBindings788.inputs
#print axioms ShielddSecurity.CheckingInverseBindings788.inputs

set_option pp.all true in
#check @ShielddSecurity.CheckingInverseBindings788.copied
#print axioms ShielddSecurity.CheckingInverseBindings788.copied

set_option pp.all true in
#check @ShielddSecurity.CheckingInverseBindings788.arithmetic
#print axioms ShielddSecurity.CheckingInverseBindings788.arithmetic

set_option pp.all true in
#check @ShielddSecurity.CheckingInverseBindings788.operand
#print axioms ShielddSecurity.CheckingInverseBindings788.operand

set_option pp.all true in
#check @ShielddSecurity.CheckingInverseBindings788.hint
#print axioms ShielddSecurity.CheckingInverseBindings788.hint
