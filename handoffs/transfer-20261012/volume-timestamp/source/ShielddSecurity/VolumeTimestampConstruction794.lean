import ShielddSecurity.VolumeTimestampRows793
import ShielddSecurity.CheckingInverseConstruction790
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.VolumeTimestampConstruction794
open ConcreteJubjubField01 TransferSem
attribute [local irreducible] ConcreteRegistrySharedEncoding294.model CompilerAssertionBlock51.SatisfiesAt
  CheckingInverseConstruction790.Earlier CheckingInverseConstruction790.Rows CheckingInverseRows789.assignment
  RecoveryInverseRows781.assignment OutputAmountRows773.assignment DetectionNonidentityRows765.assignment
  BalanceFinalRows753.assignment MapAssignmentValues720.assignment

def Earlier (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (MapAssetDomain743.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) : Prop :=
  CheckingInverseConstruction790.Earlier original c w legal rkInitial authInitial initial senderInitial receiverInitial ∧
  CheckingInverseConstruction790.Rows (CheckingInverseRows789.assignment original (BalanceFinalConstruction754.input c w)
    (MapAssetDomain743.withAsset c) w legal rkInitial authInitial initial senderInitial receiverInitial)

abbrev Rows := VolumeTimestampCapture792.Rows

theorem legal_completed (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (MapAssetDomain743.crypto c) w) :
    ∃ rkInitial authInitial : Group.Point F, ∃ senderInitial : Fin 3 → Group.Point F,
    ∃ receiverInitial : Fin 3 → Group.Point F, ∃ initial : Fin 4 → Group.Point F,
      Earlier original c w legal rkInitial authInitial initial senderInitial receiverInitial ∧
      Rows (CheckingInverseRows789.assignment original (BalanceFinalConstruction754.input c w)
        (MapAssetDomain743.withAsset c) w legal rkInitial authInitial initial senderInitial receiverInitial) := by
  obtain ⟨rkInitial,authInitial,senderInitial,receiverInitial,initial,earlier,rows⟩ :=
    CheckingInverseConstruction790.legal_completed original c w legal
  exact ⟨rkInitial,authInitial,senderInitial,receiverInitial,initial,⟨earlier,rows⟩,
    VolumeTimestampRows793.rows original (BalanceFinalConstruction754.input c w) (MapAssetDomain743.withAsset c) w legal
      rkInitial authInitial initial senderInitial receiverInitial⟩
end ShielddSecurity.VolumeTimestampConstruction794

set_option pp.all true in
#check @ShielddSecurity.VolumeTimestampConstruction794.Earlier
#print axioms ShielddSecurity.VolumeTimestampConstruction794.Earlier

set_option pp.all true in
#check @ShielddSecurity.VolumeTimestampConstruction794.Rows
#print axioms ShielddSecurity.VolumeTimestampConstruction794.Rows

set_option pp.all true in
#check @ShielddSecurity.VolumeTimestampConstruction794.legal_completed
#print axioms ShielddSecurity.VolumeTimestampConstruction794.legal_completed
