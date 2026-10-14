import ShielddSecurity.RecoveryInverseRows781
import ShielddSecurity.OutputAmountConstruction774
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.RecoveryInverseConstruction782
open ConcreteJubjubField01 TransferSem
attribute [local irreducible] ConcreteRegistrySharedEncoding294.model CompilerAssertionBlock51.SatisfiesAt
  OutputAmountConstruction774.Earlier OutputAmountConstruction774.Rows
  MapAssignmentValues720.assignment BalanceFinalRows753.assignment DetectionNonidentityRows765.assignment
  OutputAmountRows773.assignment RecoveryInverseRows781.assignment

def Earlier (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (MapAssetDomain743.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) : Prop :=
  OutputAmountConstruction774.Earlier (RecoveryInverseSeed778.seed original w) c w legal
    rkInitial authInitial initial senderInitial receiverInitial ∧
  OutputAmountConstruction774.Rows (RecoveryInverseRows781.assignment original (BalanceFinalConstruction754.input c w)
    (MapAssetDomain743.withAsset c) w legal rkInitial authInitial initial senderInitial receiverInitial)

def Rows (rho : Nat → F) : Prop := ∀ slot : Fin 2, RecoveryInverseCapture779.Rows rho slot

theorem legal_completed (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (MapAssetDomain743.crypto c) w) :
    ∃ rkInitial authInitial : Group.Point F, ∃ senderInitial : Fin 3 → Group.Point F,
    ∃ receiverInitial : Fin 3 → Group.Point F, ∃ initial : Fin 4 → Group.Point F,
      Earlier original c w legal rkInitial authInitial initial senderInitial receiverInitial ∧
      Rows (RecoveryInverseRows781.assignment original (BalanceFinalConstruction754.input c w)
        (MapAssetDomain743.withAsset c) w legal rkInitial authInitial initial senderInitial receiverInitial) := by
  obtain ⟨rkInitial,authInitial,senderInitial,receiverInitial,initial,earlier,rows⟩ :=
    OutputAmountConstruction774.legal_completed (RecoveryInverseSeed778.seed original w) c w legal
  refine ⟨rkInitial,authInitial,senderInitial,receiverInitial,initial,?_,
    RecoveryInverseRows781.rows original (BalanceFinalConstruction754.input c w) (MapAssetDomain743.withAsset c) w legal
      rkInitial authInitial initial senderInitial receiverInitial⟩
  unfold Earlier RecoveryInverseRows781.assignment
  exact ⟨earlier,rows⟩
end ShielddSecurity.RecoveryInverseConstruction782

set_option pp.all true in
#check @ShielddSecurity.RecoveryInverseConstruction782.Earlier
#print axioms ShielddSecurity.RecoveryInverseConstruction782.Earlier

set_option pp.all true in
#check @ShielddSecurity.RecoveryInverseConstruction782.Rows
#print axioms ShielddSecurity.RecoveryInverseConstruction782.Rows

set_option pp.all true in
#check @ShielddSecurity.RecoveryInverseConstruction782.legal_completed
#print axioms ShielddSecurity.RecoveryInverseConstruction782.legal_completed
