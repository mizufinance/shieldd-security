import ShielddSecurity.OutputAmountRows773
import ShielddSecurity.DetectionNonidentityConstruction766
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.OutputAmountConstruction774
open ConcreteJubjubField01 TransferSem
attribute [local irreducible] ConcreteRegistrySharedEncoding294.model CompilerAssertionBlock51.SatisfiesAt
  DetectionNonidentityConstruction766.Earlier DetectionNonidentityConstruction766.Rows
  MapAssignmentValues720.assignment BalanceFinalRows753.assignment DetectionNonidentityRows765.assignment OutputAmountRows773.assignment

def Earlier (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (MapAssetDomain743.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) : Prop :=
  DetectionNonidentityConstruction766.Earlier (OutputAmountDomain767.seed original w) c w legal
    rkInitial authInitial initial senderInitial receiverInitial ∧
  DetectionNonidentityConstruction766.Rows (OutputAmountRows773.assignment original (BalanceFinalConstruction754.input c w)
    (MapAssetDomain743.withAsset c) w legal rkInitial authInitial initial senderInitial receiverInitial)

def Rows (rho : Nat → F) : Prop :=
  CompilerAssertionBlock51.SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+4783+i)) 1

theorem legal_completed (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (MapAssetDomain743.crypto c) w) :
    ∃ rkInitial authInitial : Group.Point F, ∃ senderInitial : Fin 3 → Group.Point F,
    ∃ receiverInitial : Fin 3 → Group.Point F, ∃ initial : Fin 4 → Group.Point F,
      Earlier original c w legal rkInitial authInitial initial senderInitial receiverInitial ∧
      Rows (OutputAmountRows773.assignment original (BalanceFinalConstruction754.input c w)
        (MapAssetDomain743.withAsset c) w legal rkInitial authInitial initial senderInitial receiverInitial) := by
  obtain ⟨rkInitial,authInitial,senderInitial,receiverInitial,initial,earlier,rows⟩ :=
    DetectionNonidentityConstruction766.legal_completed (OutputAmountDomain767.seed original w) c w legal
  refine ⟨rkInitial,authInitial,senderInitial,receiverInitial,initial,?_,
    OutputAmountRows773.rows original (BalanceFinalConstruction754.input c w) (MapAssetDomain743.withAsset c) w legal
      rkInitial authInitial initial senderInitial receiverInitial⟩
  unfold Earlier OutputAmountRows773.assignment
  exact ⟨earlier,rows⟩
end ShielddSecurity.OutputAmountConstruction774

set_option pp.all true in
#check @ShielddSecurity.OutputAmountConstruction774.Earlier
#print axioms ShielddSecurity.OutputAmountConstruction774.Earlier

set_option pp.all true in
#check @ShielddSecurity.OutputAmountConstruction774.Rows
#print axioms ShielddSecurity.OutputAmountConstruction774.Rows

set_option pp.all true in
#check @ShielddSecurity.OutputAmountConstruction774.legal_completed
#print axioms ShielddSecurity.OutputAmountConstruction774.legal_completed
