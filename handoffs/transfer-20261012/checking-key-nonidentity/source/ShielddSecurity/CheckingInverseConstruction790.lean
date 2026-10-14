import ShielddSecurity.CheckingInverseRows789
import ShielddSecurity.RecoveryInverseConstruction782
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CheckingInverseConstruction790
open ConcreteJubjubField01 TransferSem
attribute [local irreducible] ConcreteRegistrySharedEncoding294.model CompilerAssertionBlock51.SatisfiesAt
  RecoveryInverseConstruction782.Earlier RecoveryInverseConstruction782.Rows
  MapAssignmentValues720.assignment BalanceFinalRows753.assignment DetectionNonidentityRows765.assignment
  OutputAmountRows773.assignment RecoveryInverseRows781.assignment CheckingInverseRows789.assignment

def Earlier (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (MapAssetDomain743.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) : Prop :=
  RecoveryInverseConstruction782.Earlier (CheckingInverseSeed783.seed original (DetectionGroupDomain611.baseCrypto (BalanceBlindingDomain670.withBlinding (MapAssetDomain743.withAsset c))) w) c w legal
    rkInitial authInitial initial senderInitial receiverInitial ∧
  RecoveryInverseConstruction782.Rows (CheckingInverseRows789.assignment original (BalanceFinalConstruction754.input c w)
    (MapAssetDomain743.withAsset c) w legal rkInitial authInitial initial senderInitial receiverInitial)

def Rows (rho : Nat → F) : Prop := ∀ slot : Fin 2, CheckingInverseCapture787.Rows rho slot

theorem legal_completed (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (MapAssetDomain743.crypto c) w) :
    ∃ rkInitial authInitial : Group.Point F, ∃ senderInitial : Fin 3 → Group.Point F,
    ∃ receiverInitial : Fin 3 → Group.Point F, ∃ initial : Fin 4 → Group.Point F,
      Earlier original c w legal rkInitial authInitial initial senderInitial receiverInitial ∧
      Rows (CheckingInverseRows789.assignment original (BalanceFinalConstruction754.input c w)
        (MapAssetDomain743.withAsset c) w legal rkInitial authInitial initial senderInitial receiverInitial) := by
  obtain ⟨rkInitial,authInitial,senderInitial,receiverInitial,initial,earlier,rows⟩ :=
    RecoveryInverseConstruction782.legal_completed (CheckingInverseSeed783.seed original (DetectionGroupDomain611.baseCrypto (BalanceBlindingDomain670.withBlinding (MapAssetDomain743.withAsset c))) w) c w legal
  refine ⟨rkInitial,authInitial,senderInitial,receiverInitial,initial,?_,
    CheckingInverseRows789.rows original (BalanceFinalConstruction754.input c w) (MapAssetDomain743.withAsset c) w legal
      rkInitial authInitial initial senderInitial receiverInitial⟩
  unfold Earlier CheckingInverseRows789.assignment
  exact ⟨earlier,rows⟩
end ShielddSecurity.CheckingInverseConstruction790

set_option pp.all true in
#check @ShielddSecurity.CheckingInverseConstruction790.Earlier
#print axioms ShielddSecurity.CheckingInverseConstruction790.Earlier

set_option pp.all true in
#check @ShielddSecurity.CheckingInverseConstruction790.Rows
#print axioms ShielddSecurity.CheckingInverseConstruction790.Rows

set_option pp.all true in
#check @ShielddSecurity.CheckingInverseConstruction790.legal_completed
#print axioms ShielddSecurity.CheckingInverseConstruction790.legal_completed
