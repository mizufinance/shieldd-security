import ShielddSecurity.AuthorizationNonidentityConstruction414
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.AuthorizationSharedDomain415
open ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem

def operand (c : Crypto) (w : TransferSem.Witness) (index : Fin 5) : F :=
  if h : index.val<3 then ((UserPointDomain351.point w.sender ⟨index.val,h⟩).x:F)
  else if index.val=3 then ((ring (crypto c) w).x:F)
  else (w.asset:F)

theorem ring_nonzero (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (crypto c) w) : ((ring (crypto c) w).x:F)≠0 := by
  have auth := legal.2.1.2.2.2.1
  cases flag : w.regulated with
  | false =>
    simp only [ring,flag,Bool.false_eq_true,if_false]
    change ((49822839976625491399435002605169580882773999909559575334089637637825427273330:Nat):F)≠0
    decide +kernel
  | true =>
    have valid := legal.2.1.1.2.1
    have nonzero := auth.2.2.2.1
    simp only [ring,flag,if_true] at nonzero ⊢
    exact SubgroupNonidentity350.member_x_nonzero model _
      (SubgroupSeedCompletion203.member_of_valid c representation model w.registry.ring valid)
      (UserPointDomain351.field_nonidentity _ valid.1 nonzero)

theorem asset_nonzero (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (crypto c) w) : (w.asset:F)≠0 := by
  have bound := legal.2.1.1.2.2.2.2.2.2.2.1
  have nonzero := legal.2.1.2.2.2.1.2.2.1
  intro equal
  have same : w.asset=0 := CapturedEpochHints62.cast_small_unique w.asset 0 bound (by decide) equal
  exact nonzero same

theorem operand_nonzero (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (crypto c) w) (index : Fin 5) : operand c w index≠0 := by
  unfold operand
  split
  · exact UserPointDomain351.x_nonzero c w w.sender legal.2.1.2.1 _
  · split
    · exact ring_nonzero c w legal
    · exact asset_nonzero c w legal

theorem inverse_equation (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (crypto c) w) (index : Fin 5) :
    operand c w index*(operand c w index)⁻¹=1 := mul_inv_cancel₀ (operand_nonzero c w legal index)

end ShielddSecurity.AuthorizationSharedDomain415

set_option pp.all true in
#check @ShielddSecurity.AuthorizationSharedDomain415.operand
#print axioms ShielddSecurity.AuthorizationSharedDomain415.operand

set_option pp.all true in
#check @ShielddSecurity.AuthorizationSharedDomain415.ring_nonzero
#print axioms ShielddSecurity.AuthorizationSharedDomain415.ring_nonzero

set_option pp.all true in
#check @ShielddSecurity.AuthorizationSharedDomain415.asset_nonzero
#print axioms ShielddSecurity.AuthorizationSharedDomain415.asset_nonzero

set_option pp.all true in
#check @ShielddSecurity.AuthorizationSharedDomain415.operand_nonzero
#print axioms ShielddSecurity.AuthorizationSharedDomain415.operand_nonzero

set_option pp.all true in
#check @ShielddSecurity.AuthorizationSharedDomain415.inverse_equation
#print axioms ShielddSecurity.AuthorizationSharedDomain415.inverse_equation
