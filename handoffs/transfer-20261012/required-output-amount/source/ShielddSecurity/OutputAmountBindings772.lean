import ShielddSecurity.OutputAmountCapture771
import ShielddSecurity.OutputInverseFrame770
import ShielddSecurity.OutputAmountDomain767
import ShielddSecurity.DetectionNonidentityRows765
import ShielddSecurity.BalanceWordValues653
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.OutputAmountBindings772
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
open ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem
open DetectionNonidentityRows765 (assignment)
attribute [local irreducible] model assignment MapAssignmentValues720.assignment BalanceFinalRows753.assignment SatisfiesAt
variable (original : Nat → F) (u : F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F)

theorem amount : assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial 4789=
    ((w.outputs 0).amount:F) := by
  unfold assignment BalanceFinalRows753.assignment MapAssignmentValues720.assignment BalanceCombined696.assignment
    BalanceBlindingBindings680.assignment
  exact BalanceWordValues653.values _ (BalanceBlindingDomain670.withBlinding c) w legal
    rkInitial authInitial initial senderInitial receiverInitial 4789 (by decide)

theorem copied : assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial copy=1 := by
  unfold assignment
  exact DetectionInverseBindings764.copied _ u c w legal rkInitial authInitial initial senderInitial receiverInitial

theorem arithmetic : SatisfiesAt
    (assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial)
    CapturedFullArithmetic52.rowAt 177954 := by
  unfold assignment
  exact DetectionInverseBindings764.arithmetic _ u c w legal rkInitial authInitial initial senderInitial receiverInitial

theorem hint : assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial 4919=original 4919 := by
  unfold assignment BalanceFinalRows753.assignment MapAssignmentValues720.assignment BalanceCombined696.assignment
  rw [OutputInverseFrame770.blinding_frame _ c w legal rkInitial authInitial initial senderInitial receiverInitial 4919 (by change 4919∈([4919]:List Nat);decide),
    BalanceMagnitudeTrace640.outside _ _ _ 4919 (Or.inl (by decide)),
    BalanceMapSeed703.outside _ u 4919 (by decide)]
  simp only [BalanceFinalDomain751.seed,DetectionNonidentityDomain759.seed,
    if_neg (show (4919:Nat)≠22736 by decide),if_neg (show (4919:Nat)≠1503 by decide)]
end ShielddSecurity.OutputAmountBindings772

set_option pp.all true in
#check @ShielddSecurity.OutputAmountBindings772.amount
#print axioms ShielddSecurity.OutputAmountBindings772.amount

set_option pp.all true in
#check @ShielddSecurity.OutputAmountBindings772.copied
#print axioms ShielddSecurity.OutputAmountBindings772.copied

set_option pp.all true in
#check @ShielddSecurity.OutputAmountBindings772.arithmetic
#print axioms ShielddSecurity.OutputAmountBindings772.arithmetic

set_option pp.all true in
#check @ShielddSecurity.OutputAmountBindings772.hint
#print axioms ShielddSecurity.OutputAmountBindings772.hint
