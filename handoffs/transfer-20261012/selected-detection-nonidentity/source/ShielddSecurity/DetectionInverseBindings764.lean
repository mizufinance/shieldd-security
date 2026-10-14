import ShielddSecurity.DetectionNonidentityCapture763
import ShielddSecurity.DetectionInverseFrame762
import ShielddSecurity.DetectionNonidentityDomain759
import ShielddSecurity.BalanceFinalRows753
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.DetectionInverseBindings764
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
open ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem
open BalanceFinalRows753 (assignment)
attribute [local irreducible] model assignment MapAssignmentValues720.assignment SatisfiesAt
variable (original : Nat → F) (u : F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F)

theorem inputs : DetectionInputFrame625.Inputs
    (assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial) w := by
  unfold assignment MapAssignmentValues720.assignment BalanceCombined696.assignment
    BalanceBlindingBindings680.assignment BalanceSignBindings652.assignment TierFlagBindings630.assignment
  exact DetectionBase627.inputs _ (BalanceBlindingDomain670.withBlinding c) w legal
    rkInitial authInitial initial senderInitial receiverInitial

theorem copied : assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial copy=1 := by
  unfold assignment
  exact MapAssignmentValues720.copied _ u c w legal rkInitial authInitial initial senderInitial receiverInitial

theorem arithmetic : SatisfiesAt
    (assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial)
    CapturedFullArithmetic52.rowAt 177954 := by
  unfold assignment
  exact MapAssignmentValues720.arithmetic _ u c w legal rkInitial authInitial initial senderInitial receiverInitial

theorem selected_x : eval (assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial)
    DetectionBase627.baseX=((DetectionGroupDomain611.selected (BalanceBlindingDomain670.withBlinding c) w).x:F) := by
  have point := DetectionBase627.selected _ (BalanceBlindingDomain670.withBlinding c) w
    (copied original u c w legal rkInitial authInitial initial senderInitial receiverInitial)
    (arithmetic original u c w legal rkInitial authInitial initial senderInitial receiverInitial)
    (inputs original u c w legal rkInitial authInitial initial senderInitial receiverInitial)
  exact congrArg Group.Point.x point

theorem hint : assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial 1503=original 1503 := by
  unfold assignment MapAssignmentValues720.assignment BalanceCombined696.assignment
  rw [DetectionInverseFrame762.blinding_frame _ c w legal rkInitial authInitial initial senderInitial receiverInitial 1503 (by change 1503∈([1503]:List Nat);decide),
    BalanceMagnitudeTrace640.outside _ _ _ 1503 (Or.inl (by decide)),
    BalanceMapSeed703.outside _ u 1503 (by decide)]
  simp only [BalanceFinalDomain751.seed,if_neg (show (1503:Nat)≠22736 by decide)]
end ShielddSecurity.DetectionInverseBindings764

set_option pp.all true in
#check @ShielddSecurity.DetectionInverseBindings764.inputs
#print axioms ShielddSecurity.DetectionInverseBindings764.inputs

set_option pp.all true in
#check @ShielddSecurity.DetectionInverseBindings764.copied
#print axioms ShielddSecurity.DetectionInverseBindings764.copied

set_option pp.all true in
#check @ShielddSecurity.DetectionInverseBindings764.arithmetic
#print axioms ShielddSecurity.DetectionInverseBindings764.arithmetic

set_option pp.all true in
#check @ShielddSecurity.DetectionInverseBindings764.selected_x
#print axioms ShielddSecurity.DetectionInverseBindings764.selected_x

set_option pp.all true in
#check @ShielddSecurity.DetectionInverseBindings764.hint
#print axioms ShielddSecurity.DetectionInverseBindings764.hint
