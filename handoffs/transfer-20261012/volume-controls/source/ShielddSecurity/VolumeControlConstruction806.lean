import ShielddSecurity.VolumeControlRows805
import ShielddSecurity.SemanticCopiesConstruction802
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.VolumeControlConstruction806
open ConcreteJubjubField01 TransferSem
attribute [local irreducible] ConcreteRegistrySharedEncoding294.model CompilerAssertionBlock51.SatisfiesAt
  SemanticCopiesConstruction802.Earlier SemanticCopiesCapture800.Rows SemanticCopiesRows801.assignment CheckingInverseRows789.assignment
  RecoveryInverseRows781.assignment OutputAmountRows773.assignment DetectionNonidentityRows765.assignment
  BalanceFinalRows753.assignment MapAssignmentValues720.assignment

def Earlier (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (MapAssetDomain743.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) : Prop :=
  SemanticCopiesConstruction802.Earlier original c w legal rkInitial authInitial initial senderInitial receiverInitial ∧
  SemanticCopiesConstruction802.Rows (SemanticCopiesRows801.assignment original (BalanceFinalConstruction754.input c w)
    (MapAssetDomain743.withAsset c) w legal rkInitial authInitial initial senderInitial receiverInitial)

abbrev Rows := VolumeControlCapture804.Rows

theorem legal_completed (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (MapAssetDomain743.crypto c) w) :
    ∃ rkInitial authInitial : Group.Point F, ∃ senderInitial : Fin 3 → Group.Point F,
    ∃ receiverInitial : Fin 3 → Group.Point F, ∃ initial : Fin 4 → Group.Point F,
      Earlier original c w legal rkInitial authInitial initial senderInitial receiverInitial ∧
      Rows (SemanticCopiesRows801.assignment original (BalanceFinalConstruction754.input c w)
        (MapAssetDomain743.withAsset c) w legal rkInitial authInitial initial senderInitial receiverInitial) := by
  obtain ⟨rkInitial,authInitial,senderInitial,receiverInitial,initial,earlier,rows⟩ :=
    SemanticCopiesConstruction802.legal_completed original c w legal
  exact ⟨rkInitial,authInitial,senderInitial,receiverInitial,initial,⟨earlier,rows⟩,
    VolumeControlRows805.rows original (BalanceFinalConstruction754.input c w) (MapAssetDomain743.withAsset c) w legal
      rkInitial authInitial initial senderInitial receiverInitial⟩
end ShielddSecurity.VolumeControlConstruction806

set_option pp.all true in
#check @ShielddSecurity.VolumeControlConstruction806.Earlier
#print axioms ShielddSecurity.VolumeControlConstruction806.Earlier

set_option pp.all true in
#check @ShielddSecurity.VolumeControlConstruction806.Rows
#print axioms ShielddSecurity.VolumeControlConstruction806.Rows

set_option pp.all true in
#check @ShielddSecurity.VolumeControlConstruction806.legal_completed
#print axioms ShielddSecurity.VolumeControlConstruction806.legal_completed
