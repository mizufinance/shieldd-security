import ShielddSecurity.AuthorizationFixedDomain485
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CheckingGroupDomain595
open ConcretePointTorsion01 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem

def selected (c : Crypto) (w : TransferSem.Witness) : TransferCore.Affine := checkingKey (AuthorizationFixedDomain485.crypto c) w

theorem sink_canonical : TransferCore.CanonicalAffine CapturedRegistryPointDomain75.sink := by
  unfold TransferCore.CanonicalAffine TransferCore.fieldModulus CapturedRegistryPointDomain75.sink
  decide +kernel

theorem sink_onCurve : Group.OnCurve (CapturedFirstSubgroup81.d:F)
    (SubgroupSeedCompletion203.fieldPoint CapturedRegistryPointDomain75.sink) := by
  unfold Group.OnCurve
  decide +kernel

theorem canonical (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w) : TransferCore.CanonicalAffine (selected c w) := by
  have valid : ValidPoint (AuthorizationFixedDomain485.crypto c) w.registry.audit.checking := legal.2.1.1.2.2.2.1
  change TransferCore.CanonicalAffine (if w.regulated then w.registry.audit.checking else CapturedRegistryPointDomain75.sink)
  cases flag : w.regulated
  · exact sink_canonical
  · exact valid.1

theorem onCurve (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w) :
    Group.OnCurve (CapturedFirstSubgroup81.d:F) (SubgroupSeedCompletion203.fieldPoint (selected c w)) := by
  have valid : ValidPoint (AuthorizationFixedDomain485.crypto c) w.registry.audit.checking := legal.2.1.1.2.2.2.1
  have member := SubgroupSeedCompletion203.member_of_valid
    (ConcreteAuthorizationCrypto430.withOperations (AuthorizationFixedDomain485.withGenerator c))
    representation model w.registry.audit.checking valid
  obtain ⟨point,coordinates,_⟩ := member
  change Group.OnCurve (CapturedFirstSubgroup81.d:F)
    (SubgroupSeedCompletion203.fieldPoint (if w.regulated then w.registry.audit.checking else CapturedRegistryPointDomain75.sink))
  cases flag : w.regulated
  · exact sink_onCurve
  · change Group.OnCurve (CapturedFirstSubgroup81.d:F) (SubgroupSeedCompletion203.fieldPoint w.registry.audit.checking)
    rw [←coordinates]
    exact model.onCurve point

attribute [local irreducible] model

def represented (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w) : curve.Point :=
  Classical.choose (model.covers _ (onCurve c w legal))

theorem coordinates (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w) :
    model.coordinates (represented c w legal)=SubgroupSeedCompletion203.fieldPoint (selected c w) :=
  Classical.choose_spec (model.covers _ (onCurve c w legal))

theorem encoding (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w) :
    RegistryPointSemantic200.encode representation (model.coordinates (represented c w legal))=selected c w := by
  rw [coordinates]
  change (⟨representation.value ((selected c w).x:F),representation.value ((selected c w).y:F)⟩ : TransferCore.Affine)=_
  rw [RegistryNaturalSeed298.represented_nat _ (canonical c w legal).1,
    RegistryNaturalSeed298.represented_nat _ (canonical c w legal).2]

theorem multiplication (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w) (scalar : Nat) (bound : scalar<2^255) :
    SubgroupSeedCompletion203.fieldPoint ((AuthorizationFixedDomain485.crypto c).mul scalar (selected c w))=
      model.coordinates (scalar • represented c w legal) := by
  have result := ConcreteAuthorizationCrypto430.multiply_coordinates
    (AuthorizationFixedDomain485.withGenerator c) (represented c w legal) scalar bound
  rw [encoding] at result
  exact result
end ShielddSecurity.CheckingGroupDomain595

set_option pp.all true in
#check @ShielddSecurity.CheckingGroupDomain595.sink_canonical
#print axioms ShielddSecurity.CheckingGroupDomain595.sink_canonical

set_option pp.all true in
#check @ShielddSecurity.CheckingGroupDomain595.sink_onCurve
#print axioms ShielddSecurity.CheckingGroupDomain595.sink_onCurve

set_option pp.all true in
#check @ShielddSecurity.CheckingGroupDomain595.canonical
#print axioms ShielddSecurity.CheckingGroupDomain595.canonical

set_option pp.all true in
#check @ShielddSecurity.CheckingGroupDomain595.onCurve
#print axioms ShielddSecurity.CheckingGroupDomain595.onCurve

set_option pp.all true in
#check @ShielddSecurity.CheckingGroupDomain595.coordinates
#print axioms ShielddSecurity.CheckingGroupDomain595.coordinates

set_option pp.all true in
#check @ShielddSecurity.CheckingGroupDomain595.encoding
#print axioms ShielddSecurity.CheckingGroupDomain595.encoding

set_option pp.all true in
#check @ShielddSecurity.CheckingGroupDomain595.multiplication
#print axioms ShielddSecurity.CheckingGroupDomain595.multiplication
