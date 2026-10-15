import ShielddSecurity.PublicStatementMeaning996
import ShielddSecurity.PublicStatementCapture997
import ShielddSecurity.UserPathConstruction970
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.PublicStatementConstruction998
open ConcreteJubjubField01 TransferSem
attribute [local irreducible] ConcreteRegistrySharedEncoding294.model CompilerAssertionBlock51.SatisfiesAt
  UserPathConstruction970.Earlier UserPathCapture968.Rows VolumePathAssignment942.assignment

def Earlier (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (MapAssetDomain743.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) : Prop :=
  UserPathConstruction970.Earlier (PublicStatementSeed980.seed original w) c w legal rkInitial authInitial initial senderInitial receiverInitial ∧
  UserPathConstruction970.Rows (VolumePathAssignment942.assignment (PublicStatementSeed980.seed original w) (BalanceFinalConstruction754.input c w)
    (MapAssetDomain743.withAsset c) w legal rkInitial authInitial initial senderInitial receiverInitial)

abbrev Rows := PublicStatementCapture997.Rows (F:=F)

theorem legal_completed (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (MapAssetDomain743.crypto c) w) :
    ∃ rkInitial authInitial : Group.Point F, ∃ senderInitial : Fin 3 → Group.Point F,
    ∃ receiverInitial : Fin 3 → Group.Point F, ∃ initial : Fin 4 → Group.Point F,
      Earlier original c w legal rkInitial authInitial initial senderInitial receiverInitial ∧
      Rows (VolumePathAssignment942.assignment (PublicStatementSeed980.seed original w) (BalanceFinalConstruction754.input c w)
        (MapAssetDomain743.withAsset c) w legal rkInitial authInitial initial senderInitial receiverInitial) := by
  obtain ⟨rkInitial,authInitial,senderInitial,receiverInitial,initial,earlier,rows⟩ :=
    UserPathConstruction970.legal_completed (PublicStatementSeed980.seed original w) c w legal
  exact ⟨rkInitial,authInitial,senderInitial,receiverInitial,initial,⟨earlier,rows⟩,
    PublicStatementCapture997.rows _
      (PublicStatementMeaning996.claimed original c w legal rkInitial authInitial initial senderInitial receiverInitial)⟩
end ShielddSecurity.PublicStatementConstruction998

set_option pp.all true in
#check @ShielddSecurity.PublicStatementConstruction998.Earlier
#print axioms ShielddSecurity.PublicStatementConstruction998.Earlier

set_option pp.all true in
#check @ShielddSecurity.PublicStatementConstruction998.Rows
#print axioms ShielddSecurity.PublicStatementConstruction998.Rows

set_option pp.all true in
#check @ShielddSecurity.PublicStatementConstruction998.legal_completed
#print axioms ShielddSecurity.PublicStatementConstruction998.legal_completed
