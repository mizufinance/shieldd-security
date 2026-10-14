import ShielddSecurity.PublishedPointSeed584
import ShielddSecurity.PayloadConstruction574
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.PublishedPointConstruction585
open ConcreteJubjubField01 TransferSem
open CompilerAssertionBlock51
open PublishedPointSeed584 (assignment)
attribute [local irreducible] assignment PayloadConstruction574.Earlier

theorem final_column (family : Fin 8) :
    FixedPublishedRows580.leftColumn family=FixedFamilyLayout545.pointStart family+250 := by
  have cases : family=⟨0,by decide⟩ ∨ family=⟨1,by decide⟩ ∨ family=⟨2,by decide⟩ ∨
      family=⟨3,by decide⟩ ∨ family=⟨4,by decide⟩ ∨ family=⟨5,by decide⟩ ∨
      family=⟨6,by decide⟩ ∨ family=⟨7,by decide⟩ := by
    have bound := family.isLt
    simp only [Fin.ext_iff]
    omega
  rcases cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

def Rows (rho : Nat → F) : Prop := ∀ family : Fin 8,
  SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+FixedPublishedRows580.position family+i)) 2

theorem all_rows (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    Rows (assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial) := by
  intro family
  apply (FixedPublishedRows580.rows_iff _ family).mpr
  rw [final_column]
  unfold assignment
  have published := PublishedPointSeed584.published_point original c w legal rkInitial authInitial initial
    senderInitial receiverInitial family
  unfold assignment at published
  exact (FixedFamilyPublished579.final_point (PublishedPointSeed584.seed original w) c w legal
    rkInitial authInitial initial senderInitial receiverInitial family).trans published.symm

def Earlier (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) : Prop :=
  PayloadConstruction574.Earlier (PublishedPointSeed584.seed original w) c w legal
    rkInitial authInitial initial senderInitial receiverInitial ∧
  PayloadConstruction574.Rows (assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial)

theorem legal_completed (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w) :
    ∃ rkInitial authInitial : Group.Point F, ∃ senderInitial : Fin 3 → Group.Point F,
    ∃ receiverInitial : Fin 3 → Group.Point F, ∃ initial : Fin 4 → Group.Point F,
      Earlier original c w legal rkInitial authInitial initial senderInitial receiverInitial ∧
      Rows (assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial) := by
  obtain ⟨rkInitial,authInitial,senderInitial,receiverInitial,initial,earlier,payloadRows⟩ :=
    PayloadConstruction574.legal_completed (PublishedPointSeed584.seed original w) c w legal
  exact ⟨rkInitial,authInitial,senderInitial,receiverInitial,initial,⟨earlier,by simpa only [assignment] using payloadRows⟩,
    all_rows original c w legal rkInitial authInitial initial senderInitial receiverInitial⟩

end ShielddSecurity.PublishedPointConstruction585

set_option pp.all true in
#check @ShielddSecurity.PublishedPointConstruction585.final_column
#print axioms ShielddSecurity.PublishedPointConstruction585.final_column

set_option pp.all true in
#check @ShielddSecurity.PublishedPointConstruction585.Rows
#print axioms ShielddSecurity.PublishedPointConstruction585.Rows

set_option pp.all true in
#check @ShielddSecurity.PublishedPointConstruction585.all_rows
#print axioms ShielddSecurity.PublishedPointConstruction585.all_rows

set_option pp.all true in
#check @ShielddSecurity.PublishedPointConstruction585.Earlier
#print axioms ShielddSecurity.PublishedPointConstruction585.Earlier

set_option pp.all true in
#check @ShielddSecurity.PublishedPointConstruction585.legal_completed
#print axioms ShielddSecurity.PublishedPointConstruction585.legal_completed
