import ShielddSecurity.VolumeCandidateJoin858
import ShielddSecurity.VolumeBoundaryConstruction845
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.VolumeCandidateConstruction859
open ConcreteJubjubField01 TransferSem
attribute [local irreducible] ConcreteRegistrySharedEncoding294.model CompilerAssertionBlock51.SatisfiesAt
  VolumeBoundaryConstruction845.Earlier VolumeBoundaryCapture843.Rows VolumeCandidateAssignment854.assignment
  RoutingPrecisionRows819.assignment CheckingInverseRows789.assignment RecoveryInverseRows781.assignment
  OutputAmountRows773.assignment DetectionNonidentityRows765.assignment BalanceFinalRows753.assignment MapAssignmentValues720.assignment

def Earlier (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (MapAssetDomain743.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) : Prop :=
  VolumeBoundaryConstruction845.Earlier (VolumeCandidateSeed848.seed original w) c w legal
    rkInitial authInitial initial senderInitial receiverInitial ∧
  VolumeBoundaryConstruction845.Rows (VolumeCandidateAssignment854.assignment original (BalanceFinalConstruction754.input c w)
    (MapAssetDomain743.withAsset c) w legal rkInitial authInitial initial senderInitial receiverInitial)

abbrev Rows := VolumeCandidateCapture857.Rows (F:=F)

theorem legal_completed (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (MapAssetDomain743.crypto c) w) :
    ∃ rkInitial authInitial : Group.Point F, ∃ senderInitial : Fin 3 → Group.Point F,
    ∃ receiverInitial : Fin 3 → Group.Point F, ∃ initial : Fin 4 → Group.Point F,
      Earlier original c w legal rkInitial authInitial initial senderInitial receiverInitial ∧
      Rows (VolumeCandidateAssignment854.assignment original (BalanceFinalConstruction754.input c w)
        (MapAssetDomain743.withAsset c) w legal rkInitial authInitial initial senderInitial receiverInitial) := by
  obtain ⟨rkInitial,authInitial,senderInitial,receiverInitial,initial,earlier,rows⟩ :=
    VolumeBoundaryConstruction845.legal_completed (VolumeCandidateSeed848.seed original w) c w legal
  refine ⟨rkInitial,authInitial,senderInitial,receiverInitial,initial,⟨earlier,?_⟩,?_⟩
  · simpa only [VolumeCandidateAssignment854.assignment] using rows
  · exact VolumeCandidateJoin858.rows original (BalanceFinalConstruction754.input c w) (MapAssetDomain743.withAsset c) w legal
      rkInitial authInitial initial senderInitial receiverInitial
end ShielddSecurity.VolumeCandidateConstruction859

set_option pp.all true in
#check @ShielddSecurity.VolumeCandidateConstruction859.Earlier
#print axioms ShielddSecurity.VolumeCandidateConstruction859.Earlier

set_option pp.all true in
#check @ShielddSecurity.VolumeCandidateConstruction859.Rows
#print axioms ShielddSecurity.VolumeCandidateConstruction859.Rows

set_option pp.all true in
#check @ShielddSecurity.VolumeCandidateConstruction859.legal_completed
#print axioms ShielddSecurity.VolumeCandidateConstruction859.legal_completed
