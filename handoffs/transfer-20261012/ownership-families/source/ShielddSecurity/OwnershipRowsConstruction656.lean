import ShielddSecurity.OwnershipRows605
import ShielddSecurity.OwnershipInitial607
import ShielddSecurity.OwnershipCapture599F00
import ShielddSecurity.OwnershipCapture599F01
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.OwnershipRowsConstruction656
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
open ConcreteJubjubField01 TransferSem OwnershipLayout600 VariableFamilyLayout562
open OwnershipBindings604 (assignment)
attribute [local irreducible] assignment SemanticWordFrame373.assignment ConcreteRegistrySharedEncoding294.model
  OwnershipCapture599F00.entries OwnershipCapture599F01.entries

noncomputable def start (family : Fin 2) : Nat := [9100,10640][family.val]!
set_option pp.all true in
#check @ShielddSecurity.OwnershipRowsConstruction656.start
#print axioms ShielddSecurity.OwnershipRowsConstruction656.start

noncomputable def layout (family : Fin 2) : Family :=
  ⟨CheckingBase598.baseX,CheckingBase598.baseY,ScalarCanonicalRows395.bitStart (scalarFamily family),pointStart family,start family⟩
set_option pp.all true in
#check @ShielddSecurity.OwnershipRowsConstruction656.layout
#print axioms ShielddSecurity.OwnershipRowsConstruction656.layout

noncomputable def entries (family : Fin 2) : List (Nat × VariableWindowJoin443.Entry) :=
  if family.val=0 then OwnershipCapture599F00.entries else OwnershipCapture599F01.entries
set_option pp.all true in
#check @ShielddSecurity.OwnershipRowsConstruction656.entries
#print axioms ShielddSecurity.OwnershipRowsConstruction656.entries

theorem checked (family : Fin 2) : (entries family).all (fun e => checkComplete ⟨layout family,e.1,e.2⟩)=true := by
  have cases : family=⟨0,by decide⟩ ∨ family=⟨1,by decide⟩ := by
    have bound := family.isLt
    simp only [Fin.ext_iff]
    omega
  rcases cases with rfl|rfl
  · exact OwnershipCapture599F00.checked
  · exact OwnershipCapture599F01.checked
theorem schedule (family : Fin 2) : (entries family).map Prod.fst=List.range' 1 125 := by
  have cases : family=⟨0,by decide⟩ ∨ family=⟨1,by decide⟩ := by
    have bound := family.isLt
    simp only [Fin.ext_iff]
    omega
  rcases cases with rfl|rfl
  · exact OwnershipCapture599F00.schedule
  · exact OwnershipCapture599F01.schedule
theorem initial_rows (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) (family : Fin 2) :
    SatisfiesAt (assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial) (fun i => CapturedFullRelation58.rowAt (177954+start family+i)) 6 := by
  have cases : family=⟨0,by decide⟩ ∨ family=⟨1,by decide⟩ := by
    have bound := family.isLt
    simp only [Fin.ext_iff]
    omega
  rcases cases with rfl|rfl
  · exact OwnershipInitial607.family0 original c w legal rkInitial authInitial initial senderInitial receiverInitial
  · exact OwnershipInitial607.family1 original c w legal rkInitial authInitial initial senderInitial receiverInitial

noncomputable def Rows (rho : Nat → F) : Prop := ∀ family : Fin 2,
  SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+start family+i)) 756

theorem all_rows (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) : Rows (assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial) := by
  intro family offset before row found
  by_cases first : offset<6
  · exact initial_rows original c w legal rkInitial authInitial initial senderInitial receiverInitial family offset first row found
  · have member : (offset-6)/6+1∈(entries family).map Prod.fst := by
      rw [schedule]
      exact List.mem_range'.mpr ⟨(offset-6)/6,by omega,by omega⟩
    obtain ⟨entry,member,index⟩ := List.mem_map.mp member
    have checked := List.all_eq_true.mp (checked family) entry member
    have complete : Complete ⟨layout family,entry.1,entry.2⟩ := of_decide_eq_true checked
    have valid : Valid (layout family) entry.1 entry.2 := of_decide_eq_true complete.1
    rcases valid with ⟨_,_,firstPosition,secondPosition,addPosition,_⟩
    have rows := OwnershipRows605.rows original c w legal rkInitial authInitial initial senderInitial receiverInitial family (layout family) rfl rfl rfl rfl entry.1 entry.2 checked
    change entry.2.first.assertionStart=start family+6+6*(entry.1-1) at firstPosition
    change entry.2.second.assertionStart=start family+8+6*(entry.1-1) at secondPosition
    change entry.2.addition.assertionStart=start family+10+6*(entry.1-1) at addPosition
    by_cases low : (offset-6)%6<2
    · apply rows.1 ((offset-6)%6) low row
      change CapturedFullRelation58.rowAt (177954+entry.2.first.assertionStart+(offset-6)%6)=some row
      simpa only [show 177954+entry.2.first.assertionStart+(offset-6)%6=177954+start family+offset by omega] using found
    · by_cases middle : (offset-6)%6<4
      · apply rows.2.1 ((offset-6)%6-2) (by omega) row
        change CapturedFullRelation58.rowAt (177954+entry.2.second.assertionStart+((offset-6)%6-2))=some row
        simpa only [show 177954+entry.2.second.assertionStart+((offset-6)%6-2)=177954+start family+offset by omega] using found
      · apply rows.2.2 ((offset-6)%6-4) (by omega) row
        change CapturedFullRelation58.rowAt (177954+entry.2.addition.assertionStart+((offset-6)%6-4))=some row
        simpa only [show 177954+entry.2.addition.assertionStart+((offset-6)%6-4)=177954+start family+offset by omega] using found

end ShielddSecurity.OwnershipRowsConstruction656

set_option pp.all true in
#check @ShielddSecurity.OwnershipRowsConstruction656.checked
#print axioms ShielddSecurity.OwnershipRowsConstruction656.checked

set_option pp.all true in
#check @ShielddSecurity.OwnershipRowsConstruction656.schedule
#print axioms ShielddSecurity.OwnershipRowsConstruction656.schedule

set_option pp.all true in
#check @ShielddSecurity.OwnershipRowsConstruction656.initial_rows
#print axioms ShielddSecurity.OwnershipRowsConstruction656.initial_rows

set_option pp.all true in
#check @ShielddSecurity.OwnershipRowsConstruction656.all_rows
#print axioms ShielddSecurity.OwnershipRowsConstruction656.all_rows
