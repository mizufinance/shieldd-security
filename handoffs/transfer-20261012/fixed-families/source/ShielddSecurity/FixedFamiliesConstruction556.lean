import ShielddSecurity.FixedFamilyConstruction553
import ShielddSecurity.FixedFamilyInitial554
import ShielddSecurity.FixedFamilies544F01
import ShielddSecurity.FixedFamilies544F02
import ShielddSecurity.FixedFamilies544F03
import ShielddSecurity.FixedFamilies544F04
import ShielddSecurity.FixedFamilies544F05
import ShielddSecurity.FixedFamilies544F06
import ShielddSecurity.FixedFamilies544F07
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.FixedFamiliesConstruction556
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
open ConcreteJubjubField01 TransferSem FixedFamilyLayout545
open FixedFamilyBindings551 (assignment)
attribute [local irreducible] assignment SemanticWordFrame373.assignment ConcreteRegistrySharedEncoding294.model
  FixedFamilyConstruction553.Earlier

def start (family : Fin 8) : Nat := [5040,6443,8574,10114,11654,13676,14942,16208][family.val]!
def layout (family : Fin 8) : FixedFamilyJoin543.Layout :=
  ⟨ScalarCanonicalRows395.bitStart (scalarFamily family),pointStart family,start family+2⟩
def entries (family : Fin 8) : List FixedWindowJoin488.Entry :=
  [FixedFamilies544F00.entries,FixedFamilies544F01.entries,FixedFamilies544F02.entries,FixedFamilies544F03.entries,FixedFamilies544F04.entries,FixedFamilies544F05.entries,FixedFamilies544F06.entries,FixedFamilies544F07.entries][family.val]!
theorem checked (family : Fin 8) : (entries family).all (FixedFamilyJoin543.check (layout family))=true := by
  have cases : family=⟨0,by decide⟩ ∨ family=⟨1,by decide⟩ ∨ family=⟨2,by decide⟩ ∨ family=⟨3,by decide⟩ ∨
      family=⟨4,by decide⟩ ∨ family=⟨5,by decide⟩ ∨ family=⟨6,by decide⟩ ∨ family=⟨7,by decide⟩ := by
    have bound := family.isLt
    simp only [Fin.ext_iff]
    omega
  rcases cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact FixedFamilies544F00.checked
  · exact FixedFamilies544F01.checked
  · exact FixedFamilies544F02.checked
  · exact FixedFamilies544F03.checked
  · exact FixedFamilies544F04.checked
  · exact FixedFamilies544F05.checked
  · exact FixedFamilies544F06.checked
  · exact FixedFamilies544F07.checked
set_option pp.all true in
#check @checked
#print axioms checked
theorem matched (family : Fin 8) : (entries family).all FixedWindowMeaning491.check=true := by
  have cases : family=⟨0,by decide⟩ ∨ family=⟨1,by decide⟩ ∨ family=⟨2,by decide⟩ ∨ family=⟨3,by decide⟩ ∨
      family=⟨4,by decide⟩ ∨ family=⟨5,by decide⟩ ∨ family=⟨6,by decide⟩ ∨ family=⟨7,by decide⟩ := by
    have bound := family.isLt
    simp only [Fin.ext_iff]
    omega
  rcases cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact FixedFamilies544F00.matched
  · exact FixedFamilies544F01.matched
  · exact FixedFamilies544F02.matched
  · exact FixedFamilies544F03.matched
  · exact FixedFamilies544F04.matched
  · exact FixedFamilies544F05.matched
  · exact FixedFamilies544F06.matched
  · exact FixedFamilies544F07.matched
set_option pp.all true in
#check @matched
#print axioms matched
theorem schedule (family : Fin 8) : (entries family).map (fun e => e.index)=List.range' 1 125 := by
  have cases : family=⟨0,by decide⟩ ∨ family=⟨1,by decide⟩ ∨ family=⟨2,by decide⟩ ∨ family=⟨3,by decide⟩ ∨
      family=⟨4,by decide⟩ ∨ family=⟨5,by decide⟩ ∨ family=⟨6,by decide⟩ ∨ family=⟨7,by decide⟩ := by
    have bound := family.isLt
    simp only [Fin.ext_iff]
    omega
  rcases cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact FixedFamilies544F00.schedule
  · exact FixedFamilies544F01.schedule
  · exact FixedFamilies544F02.schedule
  · exact FixedFamilies544F03.schedule
  · exact FixedFamilies544F04.schedule
  · exact FixedFamilies544F05.schedule
  · exact FixedFamilies544F06.schedule
  · exact FixedFamilies544F07.schedule
set_option pp.all true in
#check @schedule
#print axioms schedule
theorem initial_rows (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) (family : Fin 8) :
    SatisfiesAt (assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial)
      (fun i => CapturedFullRelation58.rowAt (177954+start family+i)) 2 := by
  have cases : family=⟨0,by decide⟩ ∨ family=⟨1,by decide⟩ ∨ family=⟨2,by decide⟩ ∨ family=⟨3,by decide⟩ ∨
      family=⟨4,by decide⟩ ∨ family=⟨5,by decide⟩ ∨ family=⟨6,by decide⟩ ∨ family=⟨7,by decide⟩ := by
    have bound := family.isLt
    simp only [Fin.ext_iff]
    omega
  rcases cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact FixedFamilyInitial554.family0 original c w legal rkInitial authInitial initial senderInitial receiverInitial
  · exact FixedFamilyInitial554.family1 original c w legal rkInitial authInitial initial senderInitial receiverInitial
  · exact FixedFamilyInitial554.family2 original c w legal rkInitial authInitial initial senderInitial receiverInitial
  · exact FixedFamilyInitial554.family3 original c w legal rkInitial authInitial initial senderInitial receiverInitial
  · exact FixedFamilyInitial554.family4 original c w legal rkInitial authInitial initial senderInitial receiverInitial
  · exact FixedFamilyInitial554.family5 original c w legal rkInitial authInitial initial senderInitial receiverInitial
  · exact FixedFamilyInitial554.family6 original c w legal rkInitial authInitial initial senderInitial receiverInitial
  · exact FixedFamilyInitial554.family7 original c w legal rkInitial authInitial initial senderInitial receiverInitial
set_option pp.all true in
#check @initial_rows
#print axioms initial_rows

def Rows (rho : Nat → F) : Prop := ∀ family : Fin 8,
  SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+start family+i)) 252

theorem all_rows (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    Rows (assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial) := by
  intro family offset before row found
  by_cases first : offset<2
  · exact initial_rows original c w legal rkInitial authInitial initial senderInitial receiverInitial family offset first row found
  · have member : (offset-2)/2+1∈(entries family).map (fun e => e.index) := by
      rw [schedule]
      exact List.mem_range'.mpr ⟨(offset-2)/2,by omega,by omega⟩
    obtain ⟨e,member,index⟩ := List.mem_map.mp member
    have checked := List.all_eq_true.mp (checked family) e member
    have matched := List.all_eq_true.mp (matched family) e member
    have rows := FixedFamilyRows552.rows original c w legal rkInitial authInitial initial senderInitial receiverInitial
      family (layout family) rfl rfl e checked matched
    have valid : FixedFamilyJoin543.Valid (layout family) e := of_decide_eq_true checked
    rcases valid with ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,position⟩
    apply rows ((offset-2)%2) (by omega) row
    change CapturedFullRelation58.rowAt (177954+e.operation.assertionStart+(offset-2)%2)=some row
    change e.operation.assertionStart=(start family+2)+2*(e.index-1) at position
    have same : 177954+e.operation.assertionStart+(offset-2)%2=177954+start family+offset := by omega
    rw [same]
    exact found
set_option pp.all true in
#check @all_rows
#print axioms all_rows

theorem legal_completed (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w) :
    ∃ rkInitial authInitial : Group.Point F, ∃ senderInitial : Fin 3 → Group.Point F,
    ∃ receiverInitial : Fin 3 → Group.Point F, ∃ initial : Fin 4 → Group.Point F,
      FixedFamilyConstruction553.Earlier original c w legal rkInitial authInitial initial senderInitial receiverInitial ∧
      Rows (assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial) := by
  obtain ⟨rkInitial,authInitial,senderInitial,receiverInitial,initial,earlier,_⟩ :=
    FixedFamilyConstruction553.legal_completed original c w legal
  exact ⟨rkInitial,authInitial,senderInitial,receiverInitial,initial,earlier,
    all_rows original c w legal rkInitial authInitial initial senderInitial receiverInitial⟩
set_option pp.all true in
#check @legal_completed
#print axioms legal_completed
end ShielddSecurity.FixedFamiliesConstruction556
