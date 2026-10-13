import ShielddSecurity.ConcreteAuthorizationCrypto430
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.AuthorizationGroupDomain445
open ConcretePointTorsion01 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem
open ConcreteAuthorizationCrypto430 (withOperations)

def represented (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (ConcreteAuthorizationCrypto430.crypto c) w) (slot : Fin 3) : curve.Point :=
  Classical.choose (UserPointDomain351.member (withOperations c) w w.sender legal.2.1.2.1 slot)

theorem coordinates (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (ConcreteAuthorizationCrypto430.crypto c) w) (slot : Fin 3) :
    model.coordinates (represented c w legal slot)=
      SubgroupSeedCompletion203.fieldPoint (UserPointDomain351.point w.sender slot) :=
  (Classical.choose_spec (UserPointDomain351.member (withOperations c) w w.sender legal.2.1.2.1 slot)).1

theorem encoding (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (ConcreteAuthorizationCrypto430.crypto c) w) (slot : Fin 3) :
    RegistryPointSemantic200.encode representation (model.coordinates (represented c w legal slot))=
      UserPointDomain351.point w.sender slot := by
  rw [coordinates]
  have canonical := (UserPointDomain351.legal_points (withOperations c) w w.sender legal.2.1.2.1 slot).1.1
  change (⟨representation.value ((UserPointDomain351.point w.sender slot).x:F),
      representation.value ((UserPointDomain351.point w.sender slot).y:F)⟩ : TransferCore.Affine)=_
  rw [RegistryNaturalSeed298.represented_nat _ canonical.1,RegistryNaturalSeed298.represented_nat _ canonical.2]

theorem multiplication (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (ConcreteAuthorizationCrypto430.crypto c) w) (slot : Fin 3) :
    SubgroupSeedCompletion203.fieldPoint ((ConcreteAuthorizationCrypto430.crypto c).mul w.auth.ivk
      (UserPointDomain351.point w.sender slot)) =
    model.coordinates (w.auth.ivk • represented c w legal slot) := by
  have small := (AuthScalarSeed366.legal_bounds (withOperations c) w legal).2.1
  have bound : w.auth.ivk<2^255 := lt_trans small (by decide)
  have result := ConcreteAuthorizationCrypto430.multiply_coordinates c (represented c w legal slot) w.auth.ivk bound
  rw [encoding] at result
  exact result

theorem transmission (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (ConcreteAuthorizationCrypto430.crypto c) w) :
    model.coordinates (w.auth.ivk • represented c w legal ⟨0,by decide⟩)=
      SubgroupSeedCompletion203.fieldPoint w.sender.address.transmission := by
  have result := multiplication c w legal ⟨0,by decide⟩
  change SubgroupSeedCompletion203.fieldPoint ((ConcreteAuthorizationCrypto430.crypto c).mul w.auth.ivk
    w.sender.address.diversified)=_ at result
  have authorization := legal.2.1.2.2.2.1
  rw [authorization.2.2.2.2.2.1] at result
  exact result.symm
end ShielddSecurity.AuthorizationGroupDomain445

set_option pp.all true in
#check @ShielddSecurity.AuthorizationGroupDomain445.represented
#print axioms ShielddSecurity.AuthorizationGroupDomain445.represented

set_option pp.all true in
#check @ShielddSecurity.AuthorizationGroupDomain445.coordinates
#print axioms ShielddSecurity.AuthorizationGroupDomain445.coordinates

set_option pp.all true in
#check @ShielddSecurity.AuthorizationGroupDomain445.encoding
#print axioms ShielddSecurity.AuthorizationGroupDomain445.encoding

set_option pp.all true in
#check @ShielddSecurity.AuthorizationGroupDomain445.multiplication
#print axioms ShielddSecurity.AuthorizationGroupDomain445.multiplication

set_option pp.all true in
#check @ShielddSecurity.AuthorizationGroupDomain445.transmission
#print axioms ShielddSecurity.AuthorizationGroupDomain445.transmission
