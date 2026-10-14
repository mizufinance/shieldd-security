import ShielddSecurity.VolumeControlCapture804
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.VolumeControlRows805
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 ConcreteJubjubField01 TransferSem
attribute [local irreducible] ConcreteRegistrySharedEncoding294.model SatisfiesAt
  SemanticCopiesRows801.assignment CheckingInverseRows789.assignment RecoveryInverseRows781.assignment
  OutputAmountRows773.assignment DetectionNonidentityRows765.assignment BalanceFinalRows753.assignment MapAssignmentValues720.assignment

theorem rows (original : Nat → F) (u : F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    VolumeControlCapture804.Rows (SemanticCopiesRows801.assignment original u c w legal
      rkInitial authInitial initial senderInitial receiverInitial) := by
  let rho := SemanticCopiesRows801.assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial
  have one := VolumeControlBindings803.copied original u c w legal rkInitial authInitial initial senderInitial receiverInitial
  have arithmetic := VolumeControlBindings803.arithmetic original u c w legal rkInitial authInitial initial senderInitial receiverInitial
  apply VolumeControlCapture804.rows rho one
  · intro slot
    have equations := VolumeControlCapture804.equations rho arithmetic slot
    have left := VolumeControlBindings803.left original u c w legal rkInitial authInitial initial senderInitial receiverInitial slot
    have right := VolumeControlBindings803.right original u c w legal rkInitial authInitial initial senderInitial receiverInitial slot
    have flag := VolumeControlBindings803.flag original u c w legal rkInitial authInitial initial senderInitial receiverInitial slot
    have inverse := VolumeControlBindings803.inverse original u c w legal rkInitial authInitial initial senderInitial receiverInitial slot
    change rho (VolumeControlBindings803.leftColumn slot)=(TierFlagSeed623.left w slot:F) at left
    change rho (VolumeControlBindings803.rightColumn slot)=(TierFlagSeed623.right w slot:F) at right
    change rho (7597+2*slot.val)=FieldZeroSeed125.flag (TierFlagSeed623.delta w slot) at flag
    change rho (7598+2*slot.val)=(TierFlagSeed623.delta w slot)⁻¹ at inverse
    rw [left,right,inverse,flag] at equations
    apply VolumeControlCapture804.family_rows rho one slot
    · rw [flag]
      exact equations.1.trans (FieldZeroSeed125.inverse (TierFlagSeed623.delta w slot))
    · exact equations.2.trans (FieldZeroSeed125.annihilated (TierFlagSeed623.delta w slot))
  · have context := VolumeControlBindings803.context original u c w legal rkInitial authInitial initial senderInitial receiverInitial
    change rho 7607=(w.volume.context:F) at context
    rw [context]
    have volume := legal.2.1.2.2.2.2.2.2.1
    rcases volume.2.2.2.2.1 with allowed|allowed <;> rw [allowed] <;> norm_num
end ShielddSecurity.VolumeControlRows805

set_option pp.all true in
#check @ShielddSecurity.VolumeControlRows805.rows
#print axioms ShielddSecurity.VolumeControlRows805.rows
