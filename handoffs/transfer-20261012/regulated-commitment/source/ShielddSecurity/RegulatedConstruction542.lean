import ShielddSecurity.RegulatedMeaning541
import ShielddSecurity.IncomingConstruction534
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.RegulatedConstruction542
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 ConcreteJubjubField01 TransferSem
open AuthorizationRkSeed505 (assignment)
attribute [local irreducible] assignment SemanticWordFrame373.assignment
  ConcreteRegistrySharedEncoding294.model SubgroupSeedCompletion203.fieldPoint
  PoseidonNatural192.hash Poseidon.hash6 Poseidon.hash3
  AuthorizationRkConstruction512.Earlier AuthorizationRkConstruction512.Rows IncomingReduction533.Rows

theorem gated_zero (rho : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (data : RegulatedInputFrame536.Inputs rho w)
    (points : RegulatedPointFrame537.Points rho (AuthorizationFixedDomain485.withGenerator c) w)
    (one : rho 0=1) (copied : rho copy=1)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) : rho 61930=0 := by
  rw [RegulatedCapture538.gate_value rho arithmetic]
  by_cases regulated : w.regulated=true
  · have meaning := RegulatedMeaning541.commitment_meaning rho c w data points one copied arithmetic regulated
    have auth := legal.2.1.2.2.2.1
    rcases auth with ⟨_,_,_,_,_,_,_,commitment,_,_,_,_⟩
    have equality := congrArg (fun x : Nat => (x:F)) (commitment regulated)
    dsimp only at equality
    rw [meaning,equality,data.commitment,sub_self,mul_zero]
  · have zero : rho 10=0 := by simpa only [if_neg regulated] using data.flag
    rw [zero,zero_mul]
set_option pp.all true in
#check @gated_zero
#print axioms gated_zero

theorem commitment_rows (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    RegulatedCapture538.Rows (assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial) := by
  apply (RegulatedCapture538.rows_iff _).mpr
  exact gated_zero _ c w legal
    (RegulatedInputFrame536.rk original c w legal rkInitial authInitial initial senderInitial receiverInitial)
    (RegulatedPointFrame537.rk original c w legal rkInitial authInitial initial senderInitial receiverInitial)
    (AuthorizationRkSeed505.zero original c w legal rkInitial authInitial initial senderInitial receiverInitial)
    (AuthorizationRkSeed505.copied original c w legal rkInitial authInitial initial senderInitial receiverInitial)
    (AuthorizationRkSeed505.arithmetic original c w legal rkInitial authInitial initial senderInitial receiverInitial)
set_option pp.all true in
#check @commitment_rows
#print axioms commitment_rows

theorem legal_completed (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w) :
    ∃ rkInitial authInitial : Group.Point F, ∃ senderInitial : Fin 3 → Group.Point F,
    ∃ receiverInitial : Fin 3 → Group.Point F, ∃ initial : Fin 4 → Group.Point F,
      AuthorizationRkConstruction512.Earlier original c w legal rkInitial authInitial initial senderInitial receiverInitial ∧
      AuthorizationRkConstruction512.Rows (assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial) ∧
      IncomingReduction533.Rows (assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial) ∧
      RegulatedCapture538.Rows (assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial) := by
  obtain ⟨rkInitial,authInitial,senderInitial,receiverInitial,initial,earlier,rows,incoming⟩ :=
    IncomingConstruction534.legal_completed original c w legal
  exact ⟨rkInitial,authInitial,senderInitial,receiverInitial,initial,earlier,rows,incoming,
    commitment_rows original c w legal rkInitial authInitial initial senderInitial receiverInitial⟩
set_option pp.all true in
#check @legal_completed
#print axioms legal_completed
end ShielddSecurity.RegulatedConstruction542
