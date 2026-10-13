import ShielddSecurity.AuthorizationPrefix462
import ShielddSecurity.AuthorizationPrefixCapture463
import ShielddSecurity.AuthorizationWindowBlock461
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.AuthorizationPrefixConstruction464
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
open ConcretePointTorsion01 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem
open AuthorizationTraceAssignment457 AuthorizationPrefixCapture463

theorem add_comm {K : Type} [Field K] (d : K) (left right output : Group.Point K)
    (equations : TransferOwnership.AddEquations d left right output) :
    TransferOwnership.AddEquations d right left output := by
  simpa only [TransferOwnership.AddEquations,Group.delta,Group.cross,
    mul_comm,mul_left_comm,mul_assoc,add_comm,add_left_comm,add_assoc] using equations

def Rows (rho : Nat → F) : Prop :=
  SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+2257+i)) 2 ∧
  SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+2259+i)) 2 ∧
  SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+3015+i)) 2 ∧
  SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+3017+i)) 2

theorem all_rows (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (ConcreteAuthorizationCrypto430.crypto c) w)
    (authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    Rows (assignment original c w legal authInitial initial senderInitial receiverInitial) := by
  let rho := assignment original c w legal authInitial initial senderInitial receiverInitial
  have one := copied original c w legal authInitial initial senderInitial receiverInitial
  have arith := arithmetic original c w legal authInitial initial senderInitial receiverInitial
  have family0 := AuthorizationPrefix462.precompute_equations original c w legal authInitial initial senderInitial receiverInitial 0 (by decide)
  have family1 := AuthorizationPrefix462.precompute_equations original c w legal authInitial initial senderInitial receiverInitial 1 (by decide)
  have rows00 := (VariableOperationAdapter434.equations_iff entry00 entry00_checked rho one arith).mpr
    ((entry00_equations rho).mpr family0.1)
  have rows01 := (VariableOperationAdapter434.equations_iff entry01 entry01_checked rho one arith).mpr
    ((entry01_equations rho).mpr (add_comm _ _ _ _ family0.2))
  have rows10 := (VariableOperationAdapter434.equations_iff entry10 entry10_checked rho one arith).mpr
    ((entry10_equations rho).mpr family1.1)
  have rows11 := (VariableOperationAdapter434.equations_iff entry11 entry11_checked rho one arith).mpr
    ((entry11_equations rho).mpr (add_comm _ _ _ _ family1.2))
  exact ⟨rows00,rows01,rows10,rows11⟩

theorem legal_completed (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (ConcreteAuthorizationCrypto430.crypto c) w) :
    ∃ authInitial : Group.Point F, ∃ senderInitial : Fin 3 → Group.Point F,
    ∃ receiverInitial : Fin 3 → Group.Point F, ∃ initial : Fin 4 → Group.Point F,
      IvkInverseConstruction429.Earlier (AuthorizationTraceSeed451.seed original (bases c w legal) w.auth.ivk)
        (ConcreteAuthorizationCrypto430.withOperations c) w authInitial senderInitial receiverInitial initial ∧
      CapturedIvkInverse427.Rows (assignment original c w legal authInitial initial senderInitial receiverInitial) ∧
      AuthorizationWindowBlock461.Rows (assignment original c w legal authInitial initial senderInitial receiverInitial) ∧
      Rows (assignment original c w legal authInitial initial senderInitial receiverInitial) := by
  obtain ⟨authInitial,senderInitial,receiverInitial,initial,earlier,inverse,windows⟩ :=
    AuthorizationWindowBlock461.legal_completed original c w legal
  exact ⟨authInitial,senderInitial,receiverInitial,initial,earlier,inverse,windows,
    all_rows original c w legal authInitial initial senderInitial receiverInitial⟩
end ShielddSecurity.AuthorizationPrefixConstruction464

set_option pp.all true in
#check @ShielddSecurity.AuthorizationPrefixConstruction464.add_comm
#print axioms ShielddSecurity.AuthorizationPrefixConstruction464.add_comm

set_option pp.all true in
#check @ShielddSecurity.AuthorizationPrefixConstruction464.Rows
#print axioms ShielddSecurity.AuthorizationPrefixConstruction464.Rows

set_option pp.all true in
#check @ShielddSecurity.AuthorizationPrefixConstruction464.all_rows
#print axioms ShielddSecurity.AuthorizationPrefixConstruction464.all_rows

set_option pp.all true in
#check @ShielddSecurity.AuthorizationPrefixConstruction464.legal_completed
#print axioms ShielddSecurity.AuthorizationPrefixConstruction464.legal_completed
