import ShielddSecurity.AuthorizationWindowSchedule460
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.AuthorizationWindowBlock461
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
open ConcretePointTorsion01 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem
open AuthorizationTraceAssignment457

def Rows (rho : Nat → F) : Prop :=
  SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+2263+i)) 750 ∧
  SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+3021+i)) 750

theorem segment (rho : Nat → F) (index window : Nat) (e : VariableWindowJoin443.Entry)
    (layout : VariableWindowLayout447.Valid (AuthorizationWindowRows455.family index) window e)
    (rows : VariableWindowJoin443.Rows rho e) :
    SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+2263+758*index+6*(window-1)+i)) 6 := by
  intro i bound row found
  have first := layout.2.2.1
  have second := layout.2.2.2.1
  have addition := layout.2.2.2.2.1
  dsimp only [AuthorizationWindowRows455.family] at first second addition
  by_cases low : i<2
  · apply rows.1 i low row
    change CapturedFullRelation58.rowAt (177954+e.first.assertionStart+i)=some row
    have same : 177954+e.first.assertionStart+i=177954+2263+758*index+6*(window-1)+i := by omega
    rw [same]
    exact found
  · by_cases middle : i<4
    · apply rows.2.1 (i-2) (by omega) row
      change CapturedFullRelation58.rowAt (177954+e.second.assertionStart+(i-2))=some row
      have same : 177954+e.second.assertionStart+(i-2)=177954+2263+758*index+6*(window-1)+i := by omega
      rw [same]
      exact found
    · apply rows.2.2 (i-4) (by omega) row
      change CapturedFullRelation58.rowAt (177954+e.addition.assertionStart+(i-4))=some row
      have same : 177954+e.addition.assertionStart+(i-4)=177954+2263+758*index+6*(window-1)+i := by omega
      rw [same]
      exact found

theorem family_rows (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (ConcreteAuthorizationCrypto430.crypto c) w)
    (authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) (index : Nat) (bound : index<2) :
    SatisfiesAt (assignment original c w legal authInitial initial senderInitial receiverInitial)
      (fun i => CapturedFullRelation58.rowAt (177954+2263+758*index+i)) 750 := by
  intro offset before row found
  obtain ⟨e,checked⟩ := AuthorizationWindowSchedule460.window_entry index (offset/6+1) bound (by omega) (by omega)
  have complete : AuthorizationWindowRows455.Complete ⟨AuthorizationWindowRows455.family index,offset/6+1,e⟩ :=
    of_decide_eq_true checked
  have layout : VariableWindowLayout447.Valid (AuthorizationWindowRows455.family index) (offset/6+1) e :=
    of_decide_eq_true complete.1
  have rows := AuthorizationWindows459.rows original c w legal authInitial initial senderInitial receiverInitial
    index (offset/6+1) bound e checked
  apply segment _ index (offset/6+1) e layout rows (offset%6) (by omega) row
  change CapturedFullRelation58.rowAt (177954+2263+758*index+6*(offset/6+1-1)+offset%6)=some row
  have same : 177954+2263+758*index+6*(offset/6+1-1)+offset%6=177954+2263+758*index+offset := by omega
  rw [same]
  exact found

theorem all_rows (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (ConcreteAuthorizationCrypto430.crypto c) w)
    (authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    Rows (assignment original c w legal authInitial initial senderInitial receiverInitial) := by
  constructor
  · exact family_rows original c w legal authInitial initial senderInitial receiverInitial 0 (by decide)
  · exact family_rows original c w legal authInitial initial senderInitial receiverInitial 1 (by decide)

theorem legal_completed (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (ConcreteAuthorizationCrypto430.crypto c) w) :
    ∃ authInitial : Group.Point F, ∃ senderInitial : Fin 3 → Group.Point F,
    ∃ receiverInitial : Fin 3 → Group.Point F, ∃ initial : Fin 4 → Group.Point F,
      IvkInverseConstruction429.Earlier (AuthorizationTraceSeed451.seed original (bases c w legal) w.auth.ivk)
        (ConcreteAuthorizationCrypto430.withOperations c) w authInitial senderInitial receiverInitial initial ∧
      CapturedIvkInverse427.Rows (assignment original c w legal authInitial initial senderInitial receiverInitial) ∧
      Rows (assignment original c w legal authInitial initial senderInitial receiverInitial) := by
  obtain ⟨authInitial,senderInitial,receiverInitial,initial,earlier,inverse⟩ := retained original c w legal
  exact ⟨authInitial,senderInitial,receiverInitial,initial,earlier,inverse,
    all_rows original c w legal authInitial initial senderInitial receiverInitial⟩
end ShielddSecurity.AuthorizationWindowBlock461

set_option pp.all true in
#check @ShielddSecurity.AuthorizationWindowBlock461.Rows
#print axioms ShielddSecurity.AuthorizationWindowBlock461.Rows

set_option pp.all true in
#check @ShielddSecurity.AuthorizationWindowBlock461.segment
#print axioms ShielddSecurity.AuthorizationWindowBlock461.segment

set_option pp.all true in
#check @ShielddSecurity.AuthorizationWindowBlock461.family_rows
#print axioms ShielddSecurity.AuthorizationWindowBlock461.family_rows

set_option pp.all true in
#check @ShielddSecurity.AuthorizationWindowBlock461.all_rows
#print axioms ShielddSecurity.AuthorizationWindowBlock461.all_rows

set_option pp.all true in
#check @ShielddSecurity.AuthorizationWindowBlock461.legal_completed
#print axioms ShielddSecurity.AuthorizationWindowBlock461.legal_completed
