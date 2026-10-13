import ShielddSecurity.AuthorizationFixedWindows496
import ShielddSecurity.AuthorizationFixedSchedule489
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.AuthorizationFixedConstruction497
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
open ConcretePointTorsion01 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem
open AuthorizationFixedSeed487 (assignment)

def Rows (rho : Nat → F) : Prop :=
  SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+4030+i)) 250

theorem entry (index : Nat) (lower : 1 ≤ index) (upper : index<126) :
    ∃ e∈AuthorizationFixedSchedule489.entries,e.index=index := by
  have member : index∈AuthorizationFixedSchedule489.entries.map (fun e => e.index) := by
    rw [AuthorizationFixedSchedule489.schedule]
    exact List.mem_range'.mpr ⟨index-1,by omega,by omega⟩
  exact List.mem_map.mp member

theorem all_rows (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    Rows (assignment original c w legal authInitial initial senderInitial receiverInitial) := by
  intro offset before row found
  obtain ⟨e,member,index⟩ := entry (offset/2+1) (by omega) (by omega)
  have checked := List.all_eq_true.mp AuthorizationFixedSchedule489.checked e member
  have matched := List.all_eq_true.mp AuthorizationFixedSchedule489.meanings_checked e member
  have rows := AuthorizationFixedWindows496.rows original c w legal authInitial initial senderInitial receiverInitial e checked matched
  have valid : FixedWindowJoin488.Valid e := of_decide_eq_true checked
  rcases valid with ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,position⟩
  apply rows (offset%2) (by omega) row
  change CapturedFullRelation58.rowAt (177954+e.operation.assertionStart+offset%2)=some row
  have same : 177954+e.operation.assertionStart+offset%2=177954+4030+offset := by omega
  rw [same]
  exact found

theorem legal_completed (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w) :
    ∃ authInitial : Group.Point F, ∃ senderInitial : Fin 3 → Group.Point F,
    ∃ receiverInitial : Fin 3 → Group.Point F, ∃ initial : Fin 4 → Group.Point F,
      AuthorizationFixedBindings492.Earlier original c w legal authInitial initial senderInitial receiverInitial ∧
      Rows (assignment original c w legal authInitial initial senderInitial receiverInitial) := by
  obtain ⟨authInitial,senderInitial,receiverInitial,initial,earlier⟩ := AuthorizationFixedBindings492.retained original c w legal
  exact ⟨authInitial,senderInitial,receiverInitial,initial,earlier,
    all_rows original c w legal authInitial initial senderInitial receiverInitial⟩
end ShielddSecurity.AuthorizationFixedConstruction497

set_option pp.all true in
#check @ShielddSecurity.AuthorizationFixedConstruction497.Rows
#print axioms ShielddSecurity.AuthorizationFixedConstruction497.Rows

set_option pp.all true in
#check @ShielddSecurity.AuthorizationFixedConstruction497.entry
#print axioms ShielddSecurity.AuthorizationFixedConstruction497.entry

set_option pp.all true in
#check @ShielddSecurity.AuthorizationFixedConstruction497.all_rows
#print axioms ShielddSecurity.AuthorizationFixedConstruction497.all_rows

set_option pp.all true in
#check @ShielddSecurity.AuthorizationFixedConstruction497.legal_completed
#print axioms ShielddSecurity.AuthorizationFixedConstruction497.legal_completed
