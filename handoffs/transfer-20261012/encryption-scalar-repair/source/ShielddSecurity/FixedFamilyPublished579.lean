import ShielddSecurity.FixedFamilyFinal578
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.FixedFamilyPublished579
open ConcreteJubjubField01 TransferSem FixedFamilyLayout545
attribute [local irreducible] AuthorizationFixedDomain485.crypto

def published (w : TransferSem.Witness) (family : Fin 8) : TransferCore.Affine :=
  ([(w.outputs 0).recovery.epk,(w.outputs 1).recovery.epk,
   (w.encryption.ownership 0).r,(w.encryption.ownership 1).r,
   (w.encryption.tiers 0).epk,(w.encryption.tiers 1).epk,
   (w.encryption.tiers 2).epk,(w.encryption.tiers 3).epk]).getD family.val ⟨0,0⟩

theorem legal_point (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w) (family : Fin 8) :
    (AuthorizationFixedDomain485.crypto c).mul (scalar w family)
      (AuthorizationFixedDomain485.crypto c).generator=published w family := by
  obtain ⟨_,_,_,_,_,outputs,_,_,encryption,_⟩ := legal.2.1
  obtain ⟨_,_,_,_,_,_,tiers,ownership⟩ := encryption
  have cases : family=⟨0,by decide⟩ ∨ family=⟨1,by decide⟩ ∨ family=⟨2,by decide⟩ ∨
      family=⟨3,by decide⟩ ∨ family=⟨4,by decide⟩ ∨ family=⟨5,by decide⟩ ∨
      family=⟨6,by decide⟩ ∨ family=⟨7,by decide⟩ := by
    have bound := family.isLt
    simp only [Fin.ext_iff]
    omega
  rcases cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact (outputs 0).2.2.2.2.1.symm
  · exact (outputs 1).2.2.2.2.1.symm
  · exact (ownership 0).2.1.symm
  · exact (ownership 1).2.1.symm
  · exact (tiers 0).2.1.symm
  · exact (tiers 1).2.1.symm
  · exact (tiers 2).2.1.symm
  · exact (tiers 3).2.1.symm

theorem final_point (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) (family : Fin 8) :
    VariableWindowColumns449.columnPoint
      (PayloadBindings565.assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial)
      (pointStart family+250)=SubgroupSeedCompletion203.fieldPoint (published w family) := by
  rw [←legal_point c w legal family]
  exact FixedFamilyFinal578.semantic_point original c w legal rkInitial authInitial initial
    senderInitial receiverInitial family

end ShielddSecurity.FixedFamilyPublished579
set_option pp.all true in
#check @ShielddSecurity.FixedFamilyPublished579.published
#print axioms ShielddSecurity.FixedFamilyPublished579.published
set_option pp.all true in
#check @ShielddSecurity.FixedFamilyPublished579.legal_point
#print axioms ShielddSecurity.FixedFamilyPublished579.legal_point
set_option pp.all true in
#check @ShielddSecurity.FixedFamilyPublished579.final_point
#print axioms ShielddSecurity.FixedFamilyPublished579.final_point
