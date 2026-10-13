import ShielddSecurity.AuthorizationIncomingHash532
import ShielddSecurity.IncomingReduction533
import ShielddSecurity.AuthorizationRkConstruction512
import ShielddSecurity.AuthorizationHashes530
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.IncomingConstruction534
open ConcreteJubjubField01 TransferSem
open AuthorizationRkSeed505 (assignment)
attribute [local irreducible] assignment SemanticWordFrame373.assignment
  AuthorizationRkConstruction512.Earlier AuthorizationRkConstruction512.Rows

theorem reduction_rows (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    IncomingReduction533.Rows (assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial) :=
  (IncomingReduction533.rows_iff _).mpr
    (AuthorizationIncomingHash532.reduction original c w legal rkInitial authInitial initial senderInitial receiverInitial).symm

theorem legal_completed (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w) :
    ∃ rkInitial authInitial : Group.Point F, ∃ senderInitial : Fin 3 → Group.Point F,
    ∃ receiverInitial : Fin 3 → Group.Point F, ∃ initial : Fin 4 → Group.Point F,
      AuthorizationRkConstruction512.Earlier original c w legal rkInitial authInitial initial senderInitial receiverInitial ∧
      AuthorizationRkConstruction512.Rows (assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial) ∧
      IncomingReduction533.Rows (assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial) := by
  obtain ⟨rkInitial,authInitial,senderInitial,receiverInitial,initial,earlier,rows⟩ :=
    AuthorizationRkConstruction512.legal_completed original c w legal
  exact ⟨rkInitial,authInitial,senderInitial,receiverInitial,initial,earlier,rows,
    reduction_rows original c w legal rkInitial authInitial initial senderInitial receiverInitial⟩
end ShielddSecurity.IncomingConstruction534
set_option pp.all true in
#check @ShielddSecurity.IncomingConstruction534.reduction_rows
#print axioms ShielddSecurity.IncomingConstruction534.reduction_rows
set_option pp.all true in
#check @ShielddSecurity.IncomingConstruction534.legal_completed
#print axioms ShielddSecurity.IncomingConstruction534.legal_completed
