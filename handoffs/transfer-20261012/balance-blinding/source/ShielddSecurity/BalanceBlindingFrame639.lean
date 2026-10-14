import ShielddSecurity.BalanceBlindingBits638
import ShielddSecurity.TierFlagBindings630
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.BalanceBlindingFrame639
open ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem

theorem shared_bits (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (crypto c) w)
    (authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) (index : Nat) (before : index<252) :
    AuthorizationSharedFrame420B.assignment original c w authInitial initial senderInitial receiverInitial (22232+index)=
      if (encodeBits 252 w.blinding)[index]?.getD false then 1 else 0 := by
  unfold AuthorizationSharedFrame420B.assignment SharedAuthorizationNonidentity413.assignment
    SemanticWordFrame373.assignment UserLifecycleWord345.assignment HighZeroCompletionFrame332.assignment
    SharedComparisonBlocks327.assignment
  exact BalanceBlindingBits638.bits _ c w initial legal index before

theorem rk_bits (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) (index : Nat) (before : index<252) :
    AuthorizationRkSeed505.assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial (22232+index)=
      if (encodeBits 252 w.blinding)[index]?.getD false then 1 else 0 := by
  unfold AuthorizationRkSeed505.assignment AuthorizationFixedSeed487.assignment AuthorizationDhSeed473.assignment
    AuthorizationTraceAssignment457.assignment
  exact shared_bits _ (ConcreteAuthorizationCrypto430.withOperations (AuthorizationFixedDomain485.withGenerator c))
    w legal authInitial initial senderInitial receiverInitial index before

theorem tier_bits (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (DetectionGroupDomain611.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) (index : Nat) (before : index<252) :
    TierFlagBindings630.assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial (22232+index)=
      if (encodeBits 252 w.blinding)[index]?.getD false then 1 else 0 := by
  unfold TierFlagBindings630.assignment TierBindings617.assignment OwnershipBindings604.assignment
    PublishedInverseSeed592.assignment PublishedPointSeed584.assignment PayloadBindings565.assignment FixedFamilyBindings551.assignment
  exact rk_bits _ (DetectionGroupDomain611.baseCrypto c) w legal rkInitial authInitial initial senderInitial receiverInitial index before
end ShielddSecurity.BalanceBlindingFrame639

set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingFrame639.shared_bits
#print axioms ShielddSecurity.BalanceBlindingFrame639.shared_bits

set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingFrame639.rk_bits
#print axioms ShielddSecurity.BalanceBlindingFrame639.rk_bits

set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingFrame639.tier_bits
#print axioms ShielddSecurity.BalanceBlindingFrame639.tier_bits
