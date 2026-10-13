import ShielddSecurity.AuthorizationClampConstruction403
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.AuthorizationPointDomain404
open ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem

theorem valid_ak (c : Crypto) (w : TransferSem.Witness) (legal : TransferSem.TransferSem (crypto c) w) :
    ValidPoint (crypto c) w.auth.ak ∧ nonidentity w.auth.ak :=
  ⟨legal.2.1.2.2.2.1.1,legal.2.1.2.2.2.1.2.1⟩

theorem member (c : Crypto) (w : TransferSem.Witness) (legal : TransferSem.TransferSem (crypto c) w) :
    CapturedSubgroupModel199.Member model (SubgroupSeedCompletion203.fieldPoint (F:=F) w.auth.ak) :=
  SubgroupSeedCompletion203.member_of_valid c representation model w.auth.ak (valid_ak c w legal).1

theorem preimage (c : Crypto) (w : TransferSem.Witness) (legal : TransferSem.TransferSem (crypto c) w) :
    ∃ initial : Group.Point F,Group.OnCurve (CapturedFirstSubgroup81.d:F) initial ∧
      CompilerSubgroupArithmetic79.eight (CapturedFirstSubgroup81.d:F) initial=
        SubgroupSeedCompletion203.fieldPoint w.auth.ak :=
  SubgroupPreimage202.member_preimage (CapturedFirstSubgroup81.d:F)
    ConcreteJubjubField01.imaginary
    (by rw [coefficient_eq]; exact ConcreteJubjubField01.coefficient_no_unit_square)
    ConcreteJubjubField01.imaginary_square model _ (member c w legal)

theorem x_nonzero (c : Crypto) (w : TransferSem.Witness) (legal : TransferSem.TransferSem (crypto c) w) :
    (w.auth.ak.x:F)≠0 :=
  SubgroupNonidentity350.member_x_nonzero model _ (member c w legal)
    (UserPointDomain351.field_nonidentity _ (valid_ak c w legal).1.1 (valid_ak c w legal).2)

theorem inverse_equation (c : Crypto) (w : TransferSem.Witness) (legal : TransferSem.TransferSem (crypto c) w) :
    (w.auth.ak.x:F)*(w.auth.ak.x:F)⁻¹=1 := mul_inv_cancel₀ (x_nonzero c w legal)

end ShielddSecurity.AuthorizationPointDomain404

set_option pp.all true in
#check @ShielddSecurity.AuthorizationPointDomain404.valid_ak
#print axioms ShielddSecurity.AuthorizationPointDomain404.valid_ak

set_option pp.all true in
#check @ShielddSecurity.AuthorizationPointDomain404.member
#print axioms ShielddSecurity.AuthorizationPointDomain404.member

set_option pp.all true in
#check @ShielddSecurity.AuthorizationPointDomain404.preimage
#print axioms ShielddSecurity.AuthorizationPointDomain404.preimage

set_option pp.all true in
#check @ShielddSecurity.AuthorizationPointDomain404.x_nonzero
#print axioms ShielddSecurity.AuthorizationPointDomain404.x_nonzero

set_option pp.all true in
#check @ShielddSecurity.AuthorizationPointDomain404.inverse_equation
#print axioms ShielddSecurity.AuthorizationPointDomain404.inverse_equation
