import ShielddSecurity.FixedFamilyPublished579
import ShielddSecurity.CapturedGeneratorSubgroup586
import ShielddSecurity.AuthorizationDhDomain471
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.PublishedPointNonzero587
open ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem FixedFamilyLayout545
open FixedFamilyPublished579 (published)
attribute [local irreducible] model

theorem legal_nonidentity (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w) (family : Fin 8) :
    TransferSem.nonidentity (published w family) := by
  obtain ⟨_,_,_,_,_,outputs,_,_,encryption,_⟩ := legal.2.1
  obtain ⟨_,_,_,_,_,_,tiers,ownership⟩ := encryption
  have cases : family=⟨0,by decide⟩ ∨ family=⟨1,by decide⟩ ∨ family=⟨2,by decide⟩ ∨
      family=⟨3,by decide⟩ ∨ family=⟨4,by decide⟩ ∨ family=⟨5,by decide⟩ ∨
      family=⟨6,by decide⟩ ∨ family=⟨7,by decide⟩ := by
    have bound := family.isLt
    simp only [Fin.ext_iff]
    omega
  rcases cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact (outputs 0).2.2.2.2.2.1
  · exact (outputs 1).2.2.2.2.2.1
  · exact (ownership 0).2.2.1
  · exact (ownership 1).2.2.1
  · exact (tiers 0).2.2.1
  · exact (tiers 1).2.2.1
  · exact (tiers 2).2.2.1
  · exact (tiers 3).2.2.1

theorem canonical (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w) (family : Fin 8) :
    TransferCore.CanonicalAffine (published w family) := by
  rw [←FixedFamilyPublished579.legal_point c w legal family]
  exact AuthorizationDhDomain471.encoded_canonical
    (GroupNativeMultiply.nativeMultiply (CapturedFirstSubgroup81.d:F)
      (SubgroupSeedCompletion203.fieldPoint (AuthorizationFixedDomain485.crypto c).generator)
      (encodeBits 255 (scalar w family)))

theorem member (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w) (family : Fin 8) :
    CapturedSubgroupModel199.Member model (SubgroupSeedCompletion203.fieldPoint (F:=F) (published w family)) := by
  rw [←FixedFamilyPublished579.legal_point c w legal family]
  have bound := SharedScalarCanonical396.all_bounds
    (ConcreteAuthorizationCrypto430.withOperations (AuthorizationFixedDomain485.withGenerator c))
    w legal (scalarFamily family)
  rw [AuthorizationFixedDomain485.multiply_coordinates c (scalar w family) (lt_trans bound (by decide))]
  exact CapturedGeneratorSubgroup586.multiple_member (scalar w family)

theorem x_nonzero (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w) (family : Fin 8) :
    ((published w family).x:F)≠0 :=
  SubgroupNonidentity350.member_x_nonzero model _ (member c w legal family)
    (UserPointDomain351.field_nonidentity _ (canonical c w legal family) (legal_nonidentity c w legal family))

end ShielddSecurity.PublishedPointNonzero587

set_option pp.all true in
#check @ShielddSecurity.PublishedPointNonzero587.legal_nonidentity
#print axioms ShielddSecurity.PublishedPointNonzero587.legal_nonidentity

set_option pp.all true in
#check @ShielddSecurity.PublishedPointNonzero587.canonical
#print axioms ShielddSecurity.PublishedPointNonzero587.canonical

set_option pp.all true in
#check @ShielddSecurity.PublishedPointNonzero587.member
#print axioms ShielddSecurity.PublishedPointNonzero587.member

set_option pp.all true in
#check @ShielddSecurity.PublishedPointNonzero587.x_nonzero
#print axioms ShielddSecurity.PublishedPointNonzero587.x_nonzero
