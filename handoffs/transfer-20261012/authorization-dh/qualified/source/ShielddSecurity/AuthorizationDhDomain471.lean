import ShielddSecurity.AuthorizationFinalPoint467
import ShielddSecurity.AuthorizationDhNonzero475
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.AuthorizationDhDomain471
open ConcretePointTorsion01 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem
open AuthorizationTraceAssignment457
attribute [local irreducible] GroupNativeMultiply.nativeMultiply

def point (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (ConcreteAuthorizationCrypto430.crypto c) w) : Group.Point F :=
  model.coordinates (w.auth.ivk • bases c w legal 1)


set_option pp.all true in
#check @ShielddSecurity.AuthorizationDhDomain471.point
#print axioms ShielddSecurity.AuthorizationDhDomain471.point

theorem coordinates (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (ConcreteAuthorizationCrypto430.crypto c) w) :
    SubgroupSeedCompletion203.fieldPoint ((ConcreteAuthorizationCrypto430.crypto c).mul w.auth.ivk w.sender.rnkDH)=
      point c w legal :=
  AuthorizationGroupDomain445.multiplication c w legal ⟨2,by decide⟩


set_option pp.all true in
#check @ShielddSecurity.AuthorizationDhDomain471.coordinates
#print axioms ShielddSecurity.AuthorizationDhDomain471.coordinates

theorem member (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (ConcreteAuthorizationCrypto430.crypto c) w) :
    CapturedSubgroupModel199.Member model (point c w legal) := by
  have killed := (Classical.choose_spec (UserPointDomain351.member (ConcreteAuthorizationCrypto430.withOperations c)
    w w.sender legal.2.1.2.1 ⟨2,by decide⟩)).2
  change TransferCore.scalarOrder • bases c w legal 1=0 at killed
  refine ⟨w.auth.ivk • bases c w legal 1,rfl,?_⟩
  rw [←mul_nsmul,Nat.mul_comm,mul_nsmul,killed,nsmul_zero]


set_option pp.all true in
#check @ShielddSecurity.AuthorizationDhDomain471.member
#print axioms ShielddSecurity.AuthorizationDhDomain471.member

theorem encoded_canonical (value : Group.Point F) :
    TransferCore.CanonicalAffine (RegistryPointSemantic200.encode representation value) :=
  ⟨representation.bounded value.x,representation.bounded value.y⟩


set_option pp.all true in
#check @ShielddSecurity.AuthorizationDhDomain471.encoded_canonical
#print axioms ShielddSecurity.AuthorizationDhDomain471.encoded_canonical

theorem canonical (c : Crypto) (w : TransferSem.Witness) :
    TransferCore.CanonicalAffine ((ConcreteAuthorizationCrypto430.crypto c).mul w.auth.ivk w.sender.rnkDH) :=
  encoded_canonical (GroupNativeMultiply.nativeMultiply (CapturedFirstSubgroup81.d:F)
    (SubgroupSeedCompletion203.fieldPoint w.sender.rnkDH) (encodeBits 255 w.auth.ivk))


set_option pp.all true in
#check @ShielddSecurity.AuthorizationDhDomain471.canonical
#print axioms ShielddSecurity.AuthorizationDhDomain471.canonical

theorem nonidentity (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (ConcreteAuthorizationCrypto430.crypto c) w) :
    point c w legal≠Group.identityPoint := by
  rw [←coordinates c w legal]
  exact UserPointDomain351.field_nonidentity _ (canonical c w) legal.2.1.2.2.2.1.2.2.2.2.2.2.1


set_option pp.all true in
#check @ShielddSecurity.AuthorizationDhDomain471.nonidentity
#print axioms ShielddSecurity.AuthorizationDhDomain471.nonidentity


attribute [local irreducible] point model

theorem x_nonzero (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (ConcreteAuthorizationCrypto430.crypto c) w) :
    (point c w legal).x≠0 :=
  AuthorizationDhNonzero475.x_nonzero (point c w legal) (member c w legal) (nonidentity c w legal)


set_option pp.all true in
#check @ShielddSecurity.AuthorizationDhDomain471.x_nonzero
#print axioms ShielddSecurity.AuthorizationDhDomain471.x_nonzero


end ShielddSecurity.AuthorizationDhDomain471
