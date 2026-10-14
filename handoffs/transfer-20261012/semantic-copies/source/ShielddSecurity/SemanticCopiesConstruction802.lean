import ShielddSecurity.SemanticCopiesRows801
import ShielddSecurity.VolumeTimestampConstruction794
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.SemanticCopiesConstruction802
open ConcreteJubjubField01 TransferSem
attribute [local irreducible] ConcreteRegistrySharedEncoding294.model CompilerAssertionBlock51.SatisfiesAt
  VolumeTimestampConstruction794.Earlier VolumeTimestampCapture792.Rows
  CheckingInverseRows789.assignment RecoveryInverseRows781.assignment OutputAmountRows773.assignment
  DetectionNonidentityRows765.assignment BalanceFinalRows753.assignment MapAssignmentValues720.assignment SemanticCopiesRows801.assignment

def Earlier (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (MapAssetDomain743.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) : Prop :=
  VolumeTimestampConstruction794.Earlier (SemanticCopiesSeed798.seed original w) c w legal
    rkInitial authInitial initial senderInitial receiverInitial ∧
  VolumeTimestampConstruction794.Rows (SemanticCopiesRows801.assignment original (BalanceFinalConstruction754.input c w)
    (MapAssetDomain743.withAsset c) w legal rkInitial authInitial initial senderInitial receiverInitial)

abbrev Rows := SemanticCopiesCapture800.Rows

theorem legal_completed (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (MapAssetDomain743.crypto c) w) :
    ∃ rkInitial authInitial : Group.Point F, ∃ senderInitial : Fin 3 → Group.Point F,
    ∃ receiverInitial : Fin 3 → Group.Point F, ∃ initial : Fin 4 → Group.Point F,
      Earlier original c w legal rkInitial authInitial initial senderInitial receiverInitial ∧
      Rows (SemanticCopiesRows801.assignment original (BalanceFinalConstruction754.input c w)
        (MapAssetDomain743.withAsset c) w legal rkInitial authInitial initial senderInitial receiverInitial) := by
  obtain ⟨rkInitial,authInitial,senderInitial,receiverInitial,initial,earlier,rows⟩ :=
    VolumeTimestampConstruction794.legal_completed (SemanticCopiesSeed798.seed original w) c w legal
  refine ⟨rkInitial,authInitial,senderInitial,receiverInitial,initial,?_,
    SemanticCopiesRows801.rows original (BalanceFinalConstruction754.input c w) (MapAssetDomain743.withAsset c) w legal
      rkInitial authInitial initial senderInitial receiverInitial⟩
  unfold Earlier SemanticCopiesRows801.assignment
  exact ⟨earlier,rows⟩
end ShielddSecurity.SemanticCopiesConstruction802

set_option pp.all true in
#check @ShielddSecurity.SemanticCopiesConstruction802.Earlier
#print axioms ShielddSecurity.SemanticCopiesConstruction802.Earlier

set_option pp.all true in
#check @ShielddSecurity.SemanticCopiesConstruction802.Rows
#print axioms ShielddSecurity.SemanticCopiesConstruction802.Rows

set_option pp.all true in
#check @ShielddSecurity.SemanticCopiesConstruction802.legal_completed
#print axioms ShielddSecurity.SemanticCopiesConstruction802.legal_completed
