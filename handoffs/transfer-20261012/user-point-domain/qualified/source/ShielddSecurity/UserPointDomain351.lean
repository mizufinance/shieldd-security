import ShielddSecurity.SubgroupNonidentity350
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.UserPointDomain351
open ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem

def point (user : User) (slot : Fin 3) : TransferCore.Affine :=
  if slot.val=0 then user.address.diversified
  else if slot.val=1 then user.address.transmission
  else user.rnkDH

theorem legal_points (c : Crypto) (w : TransferSem.Witness) (user : User)
    (legal : UserSem (crypto c) w user) (slot : Fin 3) :
    ValidPoint (crypto c) (point user slot) ∧ nonidentity (point user slot) := by
  rcases slot with ⟨slot,bound⟩
  have cases : slot=0 ∨ slot=1 ∨ slot=2 := by omega
  rcases cases with rfl|rfl|rfl
  · exact ⟨legal.1,legal.2.1⟩
  · exact ⟨legal.2.2.1,legal.2.2.2.1⟩
  · exact ⟨legal.2.2.2.2.1,legal.2.2.2.2.2.1⟩

theorem member (c : Crypto) (w : TransferSem.Witness) (user : User)
    (legal : UserSem (crypto c) w user) (slot : Fin 3) :
    CapturedSubgroupModel199.Member model (SubgroupSeedCompletion203.fieldPoint (F:=F) (point user slot)) :=
  SubgroupSeedCompletion203.member_of_valid c representation model (point user slot)
    (legal_points c w user legal slot).1

theorem preimages (c : Crypto) (w : TransferSem.Witness) (user : User)
    (legal : UserSem (crypto c) w user) :
    ∃ initial : Fin 3 → Group.Point F,
      (∀ slot,Group.OnCurve (CapturedFirstSubgroup81.d:F) (initial slot)) ∧
      ∀ slot,CompilerSubgroupArithmetic79.eight (CapturedFirstSubgroup81.d:F) (initial slot)=
        SubgroupSeedCompletion203.fieldPoint (point user slot) := by
  classical
  have one (slot : Fin 3) := SubgroupPreimage202.member_preimage (CapturedFirstSubgroup81.d:F)
    ConcreteJubjubField01.imaginary
    (by rw [coefficient_eq]; exact ConcreteJubjubField01.coefficient_no_unit_square)
    ConcreteJubjubField01.imaginary_square model _ (member c w user legal slot)
  exact ⟨fun slot => Classical.choose (one slot),
    fun slot => (Classical.choose_spec (one slot)).1,
    fun slot => (Classical.choose_spec (one slot)).2⟩

theorem field_nonidentity (value : TransferCore.Affine) (canonical : ShielddSecurity.TransferCore.CanonicalAffine value)
    (nonzero : nonidentity value) : SubgroupSeedCompletion203.fieldPoint (F:=F) value≠Group.identityPoint := by
  intro equal
  have own : RegistryPointSemantic200.encode representation (SubgroupSeedCompletion203.fieldPoint (F:=F) value)=value := by
    change (⟨representation.value (value.x:F),representation.value (value.y:F)⟩ : TransferCore.Affine)=value
    rw [RegistryNaturalSeed298.represented_nat value.x canonical.1,
      RegistryNaturalSeed298.represented_nat value.y canonical.2]
  have decoded := congrArg (RegistryPointSemantic200.encode representation) equal
  rw [own] at decoded
  change value=⟨0,1⟩ at decoded
  exact nonzero decoded

theorem x_nonzero (c : Crypto) (w : TransferSem.Witness) (user : User)
    (legal : UserSem (crypto c) w user) (slot : Fin 3) :
    (SubgroupSeedCompletion203.fieldPoint (F:=F) (point user slot)).x≠0 := by
  have facts := legal_points c w user legal slot
  exact SubgroupNonidentity350.member_x_nonzero model _ (member c w user legal slot)
    (field_nonidentity _ facts.1.1 facts.2)

theorem inverse_equation (c : Crypto) (w : TransferSem.Witness) (user : User)
    (legal : UserSem (crypto c) w user) (slot : Fin 3) :
    ((point user slot).x:F)*((point user slot).x:F)⁻¹=1 :=
  mul_inv_cancel₀ (x_nonzero c w user legal slot)
end ShielddSecurity.UserPointDomain351

set_option pp.all true in
#check @ShielddSecurity.UserPointDomain351.point
#print axioms ShielddSecurity.UserPointDomain351.point

set_option pp.all true in
#check @ShielddSecurity.UserPointDomain351.legal_points
#print axioms ShielddSecurity.UserPointDomain351.legal_points

set_option pp.all true in
#check @ShielddSecurity.UserPointDomain351.member
#print axioms ShielddSecurity.UserPointDomain351.member

set_option pp.all true in
#check @ShielddSecurity.UserPointDomain351.preimages
#print axioms ShielddSecurity.UserPointDomain351.preimages

set_option pp.all true in
#check @ShielddSecurity.UserPointDomain351.field_nonidentity
#print axioms ShielddSecurity.UserPointDomain351.field_nonidentity

set_option pp.all true in
#check @ShielddSecurity.UserPointDomain351.x_nonzero
#print axioms ShielddSecurity.UserPointDomain351.x_nonzero

set_option pp.all true in
#check @ShielddSecurity.UserPointDomain351.inverse_equation
#print axioms ShielddSecurity.UserPointDomain351.inverse_equation
