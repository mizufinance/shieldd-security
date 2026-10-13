import ShielddSecurity.AuthorizationInitialCapture465
import ShielddSecurity.AuthorizationPrefixConstruction464
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.AuthorizationInitial466
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
open ConcretePointTorsion01 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem
open AuthorizationTraceAssignment457 AuthorizationTraceSeed451 AuthorizationTraceIndex450

theorem first_equation (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (ConcreteAuthorizationCrypto430.crypto c) w)
    (authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) (index : Nat) (bound : index<2) :
    let rho := assignment original c w legal authInitial initial senderInitial receiverInitial
    VariableWindowColumns449.columnPoint rho (2257+756*index)=
      Group.windowPoint (rho 2250) (rho 2251)
        (VariableWindowColumns449.columnPoint rho (1504+16*index))
        (VariableWindowColumns449.columnPoint rho (2253+756*index))
        (VariableWindowColumns449.columnPoint rho (2255+756*index)) := by
  dsimp only
  have twice := AuthorizationPrefix462.prefix_point original c w legal authInitial initial senderInitial receiverInitial index 0 bound (by decide)
  have triple := AuthorizationPrefix462.prefix_point original c w legal authInitial initial senderInitial receiverInitial index 1 bound (by decide)
  have output := AuthorizationPrefix462.prefix_point original c w legal authInitial initial senderInitial receiverInitial index 2 bound (by decide)
  change VariableWindowColumns449.columnPoint _ (2253+756*index)=model.coordinates (2 • bases c w legal index) at twice
  have triplePos : column index 0 1 0=2255+756*index := by unfold column;omega
  have outputPos : column index 0 2 0=2257+756*index := by unfold column;omega
  rw [triplePos] at triple
  rw [outputPos] at output
  change VariableWindowColumns449.columnPoint _ (2255+756*index)=model.coordinates (3 • bases c w legal index) at triple
  change VariableWindowColumns449.columnPoint _ (2257+756*index)=(windowAt (bases c w legal index) w.auth.ivk 0).output at output
  have pair := VariableTraceBitIndex454.windows_bits model (bases c w legal index) (encodeBits 252 w.auth.ivk)
    (by simp) empty 0 (by decide)
  have low := congrArg Prod.fst pair
  have high := congrArg Prod.snd pair
  change (windowAt (bases c w legal index) w.auth.ivk 0).low=(encodeBits 252 w.auth.ivk)[250]?.getD false at low
  change (windowAt (bases c w legal index) w.auth.ivk 0).high=(encodeBits 252 w.auth.ivk)[251]?.getD false at high
  have lowBit := AuthorizationTraceBindings458.bits original c w legal authInitial initial senderInitial receiverInitial 250 (by decide)
  have highBit := AuthorizationTraceBindings458.bits original c w legal authInitial initial senderInitial receiverInitial 251 (by decide)
  rw [output,AuthorizationTraceBindings458.base original c w legal authInitial initial senderInitial receiverInitial index bound,
    twice,triple,lowBit,highBit,←low,←high]
  exact AuthorizationPrefix462.first_output (bases c w legal index) w.auth.ivk

def Rows (rho : Nat → F) : Prop :=
  SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+2261+i)) 2 ∧
  SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+3019+i)) 2

theorem all_rows (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (ConcreteAuthorizationCrypto430.crypto c) w)
    (authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    Rows (assignment original c w legal authInitial initial senderInitial receiverInitial) := by
  have one := copied original c w legal authInitial initial senderInitial receiverInitial
  have arith := arithmetic original c w legal authInitial initial senderInitial receiverInitial
  constructor
  · exact (AuthorizationInitialCapture465.rows0_iff _ one arith).mpr
      (first_equation original c w legal authInitial initial senderInitial receiverInitial 0 (by decide))
  · exact (AuthorizationInitialCapture465.rows1_iff _ one arith).mpr
      (first_equation original c w legal authInitial initial senderInitial receiverInitial 1 (by decide))

theorem legal_completed (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (ConcreteAuthorizationCrypto430.crypto c) w) :
    ∃ authInitial : Group.Point F, ∃ senderInitial : Fin 3 → Group.Point F,
    ∃ receiverInitial : Fin 3 → Group.Point F, ∃ initial : Fin 4 → Group.Point F,
      IvkInverseConstruction429.Earlier (seed original (bases c w legal) w.auth.ivk)
        (ConcreteAuthorizationCrypto430.withOperations c) w authInitial senderInitial receiverInitial initial ∧
      CapturedIvkInverse427.Rows (assignment original c w legal authInitial initial senderInitial receiverInitial) ∧
      AuthorizationWindowBlock461.Rows (assignment original c w legal authInitial initial senderInitial receiverInitial) ∧
      AuthorizationPrefixConstruction464.Rows (assignment original c w legal authInitial initial senderInitial receiverInitial) ∧
      Rows (assignment original c w legal authInitial initial senderInitial receiverInitial) := by
  obtain ⟨authInitial,senderInitial,receiverInitial,initial,earlier,inverse,windows,precomputed⟩ :=
    AuthorizationPrefixConstruction464.legal_completed original c w legal
  exact ⟨authInitial,senderInitial,receiverInitial,initial,earlier,inverse,windows,precomputed,
    all_rows original c w legal authInitial initial senderInitial receiverInitial⟩
end ShielddSecurity.AuthorizationInitial466

set_option pp.all true in
#check @ShielddSecurity.AuthorizationInitial466.first_equation
#print axioms ShielddSecurity.AuthorizationInitial466.first_equation

set_option pp.all true in
#check @ShielddSecurity.AuthorizationInitial466.Rows
#print axioms ShielddSecurity.AuthorizationInitial466.Rows

set_option pp.all true in
#check @ShielddSecurity.AuthorizationInitial466.all_rows
#print axioms ShielddSecurity.AuthorizationInitial466.all_rows

set_option pp.all true in
#check @ShielddSecurity.AuthorizationInitial466.legal_completed
#print axioms ShielddSecurity.AuthorizationInitial466.legal_completed
