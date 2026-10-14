import ShielddSecurity.TierRows633
import ShielddSecurity.TierInitial635
import ShielddSecurity.TierCapture610F00
import ShielddSecurity.TierCapture610F01
import ShielddSecurity.TierCapture610F02
import ShielddSecurity.TierCapture610F03
import ShielddSecurity.TierCapture610F04
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.TierRowsConstruction657
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
open ConcreteJubjubField01 TransferSem TierLayout613 VariableFamilyLayout562
open TierFlagBindings630 (assignment)
attribute [local irreducible] assignment SemanticWordFrame373.assignment ConcreteRegistrySharedEncoding294.model
  TierCapture610F00.entries TierCapture610F01.entries TierCapture610F02.entries
  TierCapture610F03.entries TierCapture610F04.entries

noncomputable def start (family : Fin 5) : Nat := [11909,12665,13931,15197,16463][family.val]!
noncomputable def layout (family : Fin 5) : Family :=
  ⟨TierBase632.baseX family,TierBase632.baseY family,ScalarCanonicalRows395.bitStart (scalarFamily family),pointStart family,start family⟩
noncomputable def entries (family : Fin 5) : List (Nat × VariableWindowJoin443.Entry) :=
  if family.val=0 then TierCapture610F00.entries
  else if family.val=1 then TierCapture610F01.entries
  else if family.val=2 then TierCapture610F02.entries
  else if family.val=3 then TierCapture610F03.entries else TierCapture610F04.entries
theorem checked (family : Fin 5) : (entries family).all (fun e => checkComplete ⟨layout family,e.1,e.2⟩)=true := by
  have cases : family=⟨0,by decide⟩ ∨ family=⟨1,by decide⟩ ∨ family=⟨2,by decide⟩ ∨ family=⟨3,by decide⟩ ∨ family=⟨4,by decide⟩ := by
    have bound := family.isLt
    simp only [Fin.ext_iff]
    omega
  rcases cases with rfl|rfl|rfl|rfl|rfl
  · exact TierCapture610F00.checked
  · exact TierCapture610F01.checked
  · exact TierCapture610F02.checked
  · exact TierCapture610F03.checked
  · exact TierCapture610F04.checked
theorem schedule (family : Fin 5) : (entries family).map Prod.fst=List.range' 1 125 := by
  have cases : family=⟨0,by decide⟩ ∨ family=⟨1,by decide⟩ ∨ family=⟨2,by decide⟩ ∨ family=⟨3,by decide⟩ ∨ family=⟨4,by decide⟩ := by
    have bound := family.isLt
    simp only [Fin.ext_iff]
    omega
  rcases cases with rfl|rfl|rfl|rfl|rfl
  · exact TierCapture610F00.schedule
  · exact TierCapture610F01.schedule
  · exact TierCapture610F02.schedule
  · exact TierCapture610F03.schedule
  · exact TierCapture610F04.schedule
theorem initial_rows (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (DetectionGroupDomain611.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) (family : Fin 5) :
    SatisfiesAt (assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial) (fun i => CapturedFullRelation58.rowAt (177954+start family+i)) 6 := by
  have cases : family=⟨0,by decide⟩ ∨ family=⟨1,by decide⟩ ∨ family=⟨2,by decide⟩ ∨ family=⟨3,by decide⟩ ∨ family=⟨4,by decide⟩ := by
    have bound := family.isLt
    simp only [Fin.ext_iff]
    omega
  rcases cases with rfl|rfl|rfl|rfl|rfl
  · exact TierInitial635.family0 original c w legal rkInitial authInitial initial senderInitial receiverInitial
  · exact TierInitial635.family1 original c w legal rkInitial authInitial initial senderInitial receiverInitial
  · exact TierInitial635.family2 original c w legal rkInitial authInitial initial senderInitial receiverInitial
  · exact TierInitial635.family3 original c w legal rkInitial authInitial initial senderInitial receiverInitial
  · exact TierInitial635.family4 original c w legal rkInitial authInitial initial senderInitial receiverInitial

noncomputable def Rows (rho : Nat → F) : Prop := ∀ family : Fin 5,
  SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+start family+i)) 756

theorem all_rows (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (DetectionGroupDomain611.crypto c) w)
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
    have rows := TierRows633.rows original c w legal rkInitial authInitial initial senderInitial receiverInitial family (layout family) rfl rfl rfl rfl entry.1 entry.2 checked
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

end ShielddSecurity.TierRowsConstruction657

set_option pp.all true in
#check @ShielddSecurity.TierRowsConstruction657.checked
#print axioms ShielddSecurity.TierRowsConstruction657.checked

set_option pp.all true in
#check @ShielddSecurity.TierRowsConstruction657.schedule
#print axioms ShielddSecurity.TierRowsConstruction657.schedule

set_option pp.all true in
#check @ShielddSecurity.TierRowsConstruction657.initial_rows
#print axioms ShielddSecurity.TierRowsConstruction657.initial_rows

set_option pp.all true in
#check @ShielddSecurity.TierRowsConstruction657.all_rows
#print axioms ShielddSecurity.TierRowsConstruction657.all_rows
