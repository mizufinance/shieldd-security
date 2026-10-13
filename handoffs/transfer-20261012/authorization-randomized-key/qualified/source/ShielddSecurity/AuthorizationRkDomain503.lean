import ShielddSecurity.AuthorizationClampConstruction403
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.AuthorizationRkDomain503
open ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem

theorem valid_rk (c : Crypto) (w : TransferSem.Witness) (legal : TransferSem.TransferSem (crypto c) w) :
    ValidPoint (crypto c) w.auth.rk ∧ nonidentity w.auth.rk := by
  rcases legal.2.1.2.2.2.1 with ⟨_,_,_,_,_,_,_,_,_,valid,nonzero,_⟩
  exact ⟨valid,nonzero⟩

theorem member (c : Crypto) (w : TransferSem.Witness) (legal : TransferSem.TransferSem (crypto c) w) :
    CapturedSubgroupModel199.Member model (SubgroupSeedCompletion203.fieldPoint (F:=F) w.auth.rk) :=
  SubgroupSeedCompletion203.member_of_valid c representation model w.auth.rk (valid_rk c w legal).1

theorem preimage (c : Crypto) (w : TransferSem.Witness) (legal : TransferSem.TransferSem (crypto c) w) :
    ∃ initial : Group.Point F,Group.OnCurve (CapturedFirstSubgroup81.d:F) initial ∧
      CompilerSubgroupArithmetic79.eight (CapturedFirstSubgroup81.d:F) initial=
        SubgroupSeedCompletion203.fieldPoint w.auth.rk :=
  SubgroupPreimage202.member_preimage (CapturedFirstSubgroup81.d:F)
    ConcreteJubjubField01.imaginary
    (by rw [coefficient_eq]; exact ConcreteJubjubField01.coefficient_no_unit_square)
    ConcreteJubjubField01.imaginary_square model _ (member c w legal)

theorem x_nonzero (c : Crypto) (w : TransferSem.Witness) (legal : TransferSem.TransferSem (crypto c) w) :
    (w.auth.rk.x:F)≠0 :=
  SubgroupNonidentity350.member_x_nonzero model _ (member c w legal)
    (UserPointDomain351.field_nonidentity _ (valid_rk c w legal).1.1 (valid_rk c w legal).2)

theorem inverse_equation (c : Crypto) (w : TransferSem.Witness) (legal : TransferSem.TransferSem (crypto c) w) :
    (w.auth.rk.x:F)*(w.auth.rk.x:F)⁻¹=1 := mul_inv_cancel₀ (x_nonzero c w legal)

end ShielddSecurity.AuthorizationRkDomain503

set_option pp.all true in
#check @ShielddSecurity.AuthorizationRkDomain503.valid_rk
#print axioms ShielddSecurity.AuthorizationRkDomain503.valid_rk

set_option pp.all true in
#check @ShielddSecurity.AuthorizationRkDomain503.member
#print axioms ShielddSecurity.AuthorizationRkDomain503.member

set_option pp.all true in
#check @ShielddSecurity.AuthorizationRkDomain503.preimage
#print axioms ShielddSecurity.AuthorizationRkDomain503.preimage

set_option pp.all true in
#check @ShielddSecurity.AuthorizationRkDomain503.x_nonzero
#print axioms ShielddSecurity.AuthorizationRkDomain503.x_nonzero

set_option pp.all true in
#check @ShielddSecurity.AuthorizationRkDomain503.inverse_equation
#print axioms ShielddSecurity.AuthorizationRkDomain503.inverse_equation
