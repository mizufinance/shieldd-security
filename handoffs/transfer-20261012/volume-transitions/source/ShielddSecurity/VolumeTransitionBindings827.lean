import ShielddSecurity.RoutingPrecisionRows819
import ShielddSecurity.VolumeTimestampBindings791
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.VolumeTransitionBindings827
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 ConcreteJubjubField01 TransferSem
open RoutingPrecisionRows819 (assignment)
attribute [local irreducible] ConcreteRegistrySharedEncoding294.model SatisfiesAt assignment
  SemanticCopiesRows801.assignment CheckingInverseRows789.assignment RecoveryInverseRows781.assignment
  OutputAmountRows773.assignment DetectionNonidentityRows765.assignment BalanceFinalRows753.assignment MapAssignmentValues720.assignment

theorem eligible_polynomial (rho : Nat → F)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 108482=(2*rho copy-rho 7607)*rho 10*(rho copy-rho 7597*rho 7599*rho 7601*rho 7603) := by
  have eligible := TierFlagCapture618.eligible_value rho arithmetic
  have regulatedExternal := TierFlagCapture618.regulatedExternal_value rho arithmetic
  have same0123 := TierFlagCapture618.same0123_value rho arithmetic
  have same012 := TierFlagCapture618.same012_value rho arithmetic
  have same01 := TierFlagCapture618.same01_value rho arithmetic
  simp only [eval,Int.cast_one,Int.cast_neg,Int.cast_ofNat,one_mul,add_zero,neg_mul] at *
  rw [eligible,regulatedExternal,same0123,same012,same01]
  unfold copy
  ring

theorem eligible_value (rho : Nat → F) (w : TransferSem.Witness)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954)
    (one : rho copy=1) (inputs : TierFlagMeaning619.Inputs rho w)
    (context : w.volume.context=1 ∨ w.volume.context=2) : rho 108482=if eligible w then 1 else 0 := by
  rw [eligible_polynomial rho arithmetic,one,inputs.context,inputs.regulated,
    inputs.same0,inputs.same1,inputs.same2,inputs.same3,TierFlagMeaning619.coordinate_indicators]
  by_cases address : w.sender.address=w.receiver.address <;>
    cases regulated : w.regulated <;> rcases context with context|context <;>
    norm_num [eligible,external,address,regulated,context]

variable (original : Nat → F) (u : F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F)

theorem inputs : TierFlagMeaning619.Inputs
    (assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial) w := by
  unfold assignment SemanticCopiesRows801.assignment CheckingInverseRows789.assignment RecoveryInverseRows781.assignment
    OutputAmountRows773.assignment DetectionNonidentityRows765.assignment BalanceFinalRows753.assignment
    MapAssignmentValues720.assignment BalanceCombined696.assignment BalanceBlindingBindings680.assignment BalanceSignBindings652.assignment
  exact TierFlagBindings630.inputs _ _ w legal rkInitial authInitial initial senderInitial receiverInitial

theorem starts_new_day : assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial 7606=
    (if w.volume.startsNewDay then 1 else 0) := by
  unfold assignment SemanticCopiesRows801.assignment CheckingInverseRows789.assignment RecoveryInverseRows781.assignment
    OutputAmountRows773.assignment DetectionNonidentityRows765.assignment BalanceFinalRows753.assignment
    MapAssignmentValues720.assignment BalanceCombined696.assignment BalanceBlindingBindings680.assignment BalanceSignBindings652.assignment
  exact (TierFlagBindings630.flag_frame _ _ w legal rkInitial authInitial initial senderInitial receiverInitial 7606 (by decide +kernel)).trans
    (TierFlagSeed623.control_values _ w).2.1

theorem words (column : Nat) (member : column∈RemainingWordSeed369.values) :
    assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial column=(RemainingWordSeed369.value w column:F) := by
  unfold assignment SemanticCopiesRows801.assignment
  exact VolumeTimestampBindings791.words _ u c w legal rkInitial authInitial initial senderInitial receiverInitial column member

theorem arithmetic : SatisfiesAt (assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial)
    CapturedFullArithmetic52.rowAt 177954 := by
  unfold assignment
  exact VolumeControlBindings803.arithmetic _ u c w legal rkInitial authInitial initial senderInitial receiverInitial

theorem copied : assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial copy=1 := by
  unfold assignment
  exact VolumeControlBindings803.copied _ u c w legal rkInitial authInitial initial senderInitial receiverInitial

theorem eligible : assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial 108482=
    (if TransferSem.eligible w then 1 else 0) := by
  have volume := legal.2.1.2.2.2.2.2.2.1
  exact eligible_value _ w (arithmetic original u c w legal rkInitial authInitial initial senderInitial receiverInitial)
    (copied original u c w legal rkInitial authInitial initial senderInitial receiverInitial)
    (inputs original u c w legal rkInitial authInitial initial senderInitial receiverInitial) volume.2.2.2.2.1
end ShielddSecurity.VolumeTransitionBindings827

set_option pp.all true in
#check @ShielddSecurity.VolumeTransitionBindings827.eligible_polynomial
#print axioms ShielddSecurity.VolumeTransitionBindings827.eligible_polynomial

set_option pp.all true in
#check @ShielddSecurity.VolumeTransitionBindings827.eligible_value
#print axioms ShielddSecurity.VolumeTransitionBindings827.eligible_value

set_option pp.all true in
#check @ShielddSecurity.VolumeTransitionBindings827.inputs
#print axioms ShielddSecurity.VolumeTransitionBindings827.inputs

set_option pp.all true in
#check @ShielddSecurity.VolumeTransitionBindings827.starts_new_day
#print axioms ShielddSecurity.VolumeTransitionBindings827.starts_new_day

set_option pp.all true in
#check @ShielddSecurity.VolumeTransitionBindings827.words
#print axioms ShielddSecurity.VolumeTransitionBindings827.words

set_option pp.all true in
#check @ShielddSecurity.VolumeTransitionBindings827.arithmetic
#print axioms ShielddSecurity.VolumeTransitionBindings827.arithmetic

set_option pp.all true in
#check @ShielddSecurity.VolumeTransitionBindings827.copied
#print axioms ShielddSecurity.VolumeTransitionBindings827.copied

set_option pp.all true in
#check @ShielddSecurity.VolumeTransitionBindings827.eligible
#print axioms ShielddSecurity.VolumeTransitionBindings827.eligible
