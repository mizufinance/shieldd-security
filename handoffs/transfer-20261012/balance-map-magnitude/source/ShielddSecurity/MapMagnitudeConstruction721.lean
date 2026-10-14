import ShielddSecurity.MapMagnitudeComposition729
import ShielddSecurity.BalanceCanonicalConstruction692
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.MapMagnitudeConstruction721
open ConcretePointTorsion01 ConcreteJubjubField01 TransferSem
open MapAssignmentValues720 (assignment)
attribute [local irreducible] assignment ConcreteRegistrySharedEncoding294.model
  BalanceCanonicalConstruction692.Earlier BalanceCanonicalConstruction692.Rows
  CompilerAssertionBlock51.SatisfiesAt

noncomputable def seeded (original : Nat → F) (u : F) (w : TransferSem.Witness) : Nat → F :=
  BalanceMagnitudeTrace640.seed (BalanceMapSeed703.seed original u)
    (BalanceMapPoint701.represented u) (RemainingWordSeed369.magnitude w)

noncomputable def Earlier (original : Nat → F) (u : F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) : Prop :=
  BalanceCanonicalConstruction692.Earlier (seeded original u w) c w legal rkInitial authInitial initial senderInitial receiverInitial ∧
  BalanceCanonicalConstruction692.Rows (assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial)

noncomputable def Rows (rho : Nat → F) : Prop :=
  CompilerAssertionBlock51.SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+21914+i)) 390

-- The map parameter is free here. Exact asset-hash correspondence and final
-- semantic balance are separate obligations; this theorem supplies row construction.
theorem legal_completed (original : Nat → F) (u : F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w) :
    ∃ rkInitial authInitial : Group.Point F, ∃ senderInitial : Fin 3 → Group.Point F,
    ∃ receiverInitial : Fin 3 → Group.Point F, ∃ initial : Fin 4 → Group.Point F,
      Earlier original u c w legal rkInitial authInitial initial senderInitial receiverInitial ∧
      Rows (assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial) := by
  obtain ⟨rkInitial,authInitial,senderInitial,receiverInitial,initial,earlier,canonicalRows⟩ :=
    BalanceCanonicalConstruction692.legal_completed (seeded original u w) c w legal
  have canonicalRows' : BalanceCanonicalConstruction692.Rows
      (assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial) := by
    unfold MapAssignmentValues720.assignment BalanceCombined696.assignment
    exact canonicalRows
  exact ⟨rkInitial,authInitial,senderInitial,receiverInitial,initial,⟨earlier,canonicalRows'⟩,
    MapMagnitudeComposition729.magnitude_rows original u c w legal rkInitial authInitial initial senderInitial receiverInitial⟩
end ShielddSecurity.MapMagnitudeConstruction721

set_option pp.all true in
#check @ShielddSecurity.MapMagnitudeConstruction721.Earlier
#print axioms ShielddSecurity.MapMagnitudeConstruction721.Earlier

set_option pp.all true in
#check @ShielddSecurity.MapMagnitudeConstruction721.Rows
#print axioms ShielddSecurity.MapMagnitudeConstruction721.Rows

set_option pp.all true in
#check @ShielddSecurity.MapMagnitudeConstruction721.legal_completed
#print axioms ShielddSecurity.MapMagnitudeConstruction721.legal_completed
