import ShielddSecurity.BalanceBlindingBindings680
import ShielddSecurity.BalanceBlindingCanonicalRows690F00
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.BalanceBlindingCanonical691
open ConcreteJubjubField01 TransferSem
open BalanceBlindingBindings680 (assignment)
attribute [local irreducible] assignment ConcreteRegistrySharedEncoding294.model

theorem canonical_bound (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w) : w.blinding<TransferCore.scalarOrder :=
  BalanceBlindingBits638.scalar_bound
    (ConcreteAuthorizationCrypto430.withOperations
      (AuthorizationFixedDomain485.withGenerator (DetectionGroupDomain611.baseCrypto (BalanceBlindingDomain670.withBlinding c)))) w legal

theorem zero (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) : assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial 0=1 := by
  unfold assignment BalanceSignBindings652.assignment TierFlagBindings630.assignment TierBindings617.assignment
    OwnershipBindings604.assignment PublishedInverseSeed592.assignment PublishedPointSeed584.assignment
    PayloadBindings565.assignment FixedFamilyBindings551.assignment
  exact AuthorizationRkSeed505.zero _ (DetectionGroupDomain611.baseCrypto (BalanceBlindingDomain670.withBlinding c))
    w legal rkInitial authInitial initial senderInitial receiverInitial

theorem rows (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    CompilerAssertionBlock51.SatisfiesAt (assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial)
      (fun i => CapturedFullRelation58.rowAt (177954+22557+i)) 2 := by
  apply BalanceBlindingCanonicalRows690F00.complete (assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial) w.blinding
    (canonical_bound c w legal) (zero original c w legal rkInitial authInitial initial senderInitial receiverInitial)
    (BalanceBlindingBindings680.copied original c w legal rkInitial authInitial initial senderInitial receiverInitial)
    (BalanceBlindingBindings680.arithmetic original c w legal rkInitial authInitial initial senderInitial receiverInitial)
  intro index before
  exact BalanceBlindingBindings680.bits original c w legal rkInitial authInitial initial senderInitial receiverInitial index before
end ShielddSecurity.BalanceBlindingCanonical691

set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingCanonical691.canonical_bound
#print axioms ShielddSecurity.BalanceBlindingCanonical691.canonical_bound

set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingCanonical691.zero
#print axioms ShielddSecurity.BalanceBlindingCanonical691.zero

set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingCanonical691.rows
#print axioms ShielddSecurity.BalanceBlindingCanonical691.rows
