import ShielddSecurity.FixedFamilyRows552
import ShielddSecurity.FixedFamilies544F00
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.FixedFamilyConstruction553
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
open ConcretePointTorsion01 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem
open FixedFamilyBindings551 (assignment)
attribute [local irreducible] assignment AuthorizationRkConstruction512.Earlier AuthorizationRkConstruction512.Rows IncomingReduction533.Rows RegulatedCapture538.Rows

def Rows (rho : Nat → F) : Prop :=
  SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+5042+i)) 250

theorem entry (index : Nat) (lower : 1 ≤ index) (upper : index<126) :
    ∃ e∈FixedFamilies544F00.entries,e.index=index := by
  have member : index∈FixedFamilies544F00.entries.map (fun e => e.index) := by
    rw [FixedFamilies544F00.schedule]
    exact List.mem_range'.mpr ⟨index-1,by omega,by omega⟩
  exact List.mem_map.mp member

theorem all_rows (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    Rows (assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial) := by
  intro offset before row found
  obtain ⟨e,member,index⟩ := entry (offset/2+1) (by omega) (by omega)
  have checked := List.all_eq_true.mp FixedFamilies544F00.checked e member
  have matched := List.all_eq_true.mp FixedFamilies544F00.matched e member
  have rows := FixedFamilyRows552.rows original c w legal rkInitial authInitial initial senderInitial receiverInitial ⟨0,by decide⟩ FixedFamilies544F00.layout rfl rfl e checked matched
  have valid : FixedFamilyJoin543.Valid FixedFamilies544F00.layout e := of_decide_eq_true checked
  rcases valid with ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,position⟩
  apply rows (offset%2) (by omega) row
  change CapturedFullRelation58.rowAt (177954+e.operation.assertionStart+offset%2)=some row
  change e.operation.assertionStart=5042+2*(e.index-1) at position
  have same : 177954+e.operation.assertionStart+offset%2=177954+5042+offset := by omega
  rw [same]
  exact found

def Earlier (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) : Prop :=
  AuthorizationRkConstruction512.Earlier (FixedFamilySeed549.seed original w) c w legal rkInitial authInitial initial senderInitial receiverInitial ∧
  AuthorizationRkConstruction512.Rows (assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial) ∧
  IncomingReduction533.Rows (assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial) ∧
  RegulatedCapture538.Rows (assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial)

theorem legal_completed (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w) :
    ∃ rkInitial authInitial : Group.Point F, ∃ senderInitial : Fin 3 → Group.Point F,
    ∃ receiverInitial : Fin 3 → Group.Point F, ∃ initial : Fin 4 → Group.Point F,
      Earlier original c w legal rkInitial authInitial initial senderInitial receiverInitial ∧
      Rows (assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial) := by
  obtain ⟨rkInitial,authInitial,senderInitial,receiverInitial,initial,earlier,rows,incoming,regulated⟩ :=
    RegulatedConstruction542.legal_completed (FixedFamilySeed549.seed original w) c w legal
  refine ⟨rkInitial,authInitial,senderInitial,receiverInitial,initial,?_,
    all_rows original c w legal rkInitial authInitial initial senderInitial receiverInitial⟩
  unfold Earlier assignment
  exact ⟨earlier,rows,incoming,regulated⟩
end ShielddSecurity.FixedFamilyConstruction553

set_option pp.all true in
#check @ShielddSecurity.FixedFamilyConstruction553.Rows
#print axioms ShielddSecurity.FixedFamilyConstruction553.Rows

set_option pp.all true in
#check @ShielddSecurity.FixedFamilyConstruction553.entry
#print axioms ShielddSecurity.FixedFamilyConstruction553.entry

set_option pp.all true in
#check @ShielddSecurity.FixedFamilyConstruction553.all_rows
#print axioms ShielddSecurity.FixedFamilyConstruction553.all_rows

set_option pp.all true in
#check @ShielddSecurity.FixedFamilyConstruction553.legal_completed
#print axioms ShielddSecurity.FixedFamilyConstruction553.legal_completed
