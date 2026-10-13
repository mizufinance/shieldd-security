import ShielddSecurity.AuthorizationFinalPoint467
import ShielddSecurity.TransmissionRows470
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.AuthorizationTransmission469
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
open ConcretePointTorsion01 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem
open AuthorizationTraceAssignment457 AuthorizationTraceSeed451
attribute [local irreducible] CapturedFullRelation58.rowAt PointEqualityAdapter440.check

def Rows (rho : Nat → F) : Prop :=
  SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+3013+i)) 2

theorem all_rows (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (ConcreteAuthorizationCrypto430.crypto c) w)
    (authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    Rows (assignment original c w legal authInitial initial senderInitial receiverInitial) := by
  let rho := assignment original c w legal authInitial initial senderInitial receiverInitial
  exact (TransmissionRows470.rows_iff rho).mpr
    (AuthorizationFinalPoint467.transmission original c w legal authInitial initial senderInitial receiverInitial)

theorem legal_completed (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (ConcreteAuthorizationCrypto430.crypto c) w) :
    ∃ authInitial : Group.Point F, ∃ senderInitial : Fin 3 → Group.Point F,
    ∃ receiverInitial : Fin 3 → Group.Point F, ∃ initial : Fin 4 → Group.Point F,
      IvkInverseConstruction429.Earlier (seed original (bases c w legal) w.auth.ivk)
        (ConcreteAuthorizationCrypto430.withOperations c) w authInitial senderInitial receiverInitial initial ∧
      CapturedIvkInverse427.Rows (assignment original c w legal authInitial initial senderInitial receiverInitial) ∧
      AuthorizationWindowBlock461.Rows (assignment original c w legal authInitial initial senderInitial receiverInitial) ∧
      AuthorizationPrefixConstruction464.Rows (assignment original c w legal authInitial initial senderInitial receiverInitial) ∧
      AuthorizationInitial466.Rows (assignment original c w legal authInitial initial senderInitial receiverInitial) ∧
      Rows (assignment original c w legal authInitial initial senderInitial receiverInitial) := by
  obtain ⟨authInitial,senderInitial,receiverInitial,initial,earlier,inverse,windows,precomputed,first⟩ :=
    AuthorizationInitial466.legal_completed original c w legal
  exact ⟨authInitial,senderInitial,receiverInitial,initial,earlier,inverse,windows,precomputed,first,
    all_rows original c w legal authInitial initial senderInitial receiverInitial⟩
end ShielddSecurity.AuthorizationTransmission469

set_option pp.all true in
#check @ShielddSecurity.AuthorizationTransmission469.Rows
#print axioms ShielddSecurity.AuthorizationTransmission469.Rows

set_option pp.all true in
#check @ShielddSecurity.AuthorizationTransmission469.all_rows
#print axioms ShielddSecurity.AuthorizationTransmission469.all_rows

set_option pp.all true in
#check @ShielddSecurity.AuthorizationTransmission469.legal_completed
#print axioms ShielddSecurity.AuthorizationTransmission469.legal_completed
