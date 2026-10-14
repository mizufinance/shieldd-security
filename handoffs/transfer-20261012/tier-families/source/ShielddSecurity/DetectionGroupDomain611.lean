import ShielddSecurity.AuthorizationFixedDomain485
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.DetectionGroupDomain611
open ConcretePointTorsion01 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem

def defaultPoint : TransferCore.Affine := ⟨17832230285398775523840151435063191920633280288053987250961356462684628833490,52236742954115892447572473178524297982305297140137344394933767595493156073169⟩
def baseCrypto (c : Crypto) : Crypto := { c with unregulatedDetection := defaultPoint }
def crypto (c : Crypto) : Crypto := AuthorizationFixedDomain485.crypto (baseCrypto c)

def selected (c : Crypto) (w : TransferSem.Witness) : TransferCore.Affine := detectionKey (crypto c) w

theorem defaultPoint_canonical : TransferCore.CanonicalAffine defaultPoint := by
  unfold TransferCore.CanonicalAffine TransferCore.fieldModulus defaultPoint
  decide +kernel

theorem defaultPoint_onCurve : Group.OnCurve (CapturedFirstSubgroup81.d:F)
    (SubgroupSeedCompletion203.fieldPoint defaultPoint) := by
  unfold Group.OnCurve
  decide +kernel

theorem canonical (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (crypto c) w) : TransferCore.CanonicalAffine (selected c w) := by
  have valid : ValidPoint (crypto c) w.registry.detection := legal.2.1.1.1
  change TransferCore.CanonicalAffine (if w.regulated then w.registry.detection else defaultPoint)
  cases flag : w.regulated
  · exact defaultPoint_canonical
  · exact valid.1

theorem onCurve (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (crypto c) w) :
    Group.OnCurve (CapturedFirstSubgroup81.d:F) (SubgroupSeedCompletion203.fieldPoint (selected c w)) := by
  have valid : ValidPoint (crypto c) w.registry.detection := legal.2.1.1.1
  have member := SubgroupSeedCompletion203.member_of_valid
    (ConcreteAuthorizationCrypto430.withOperations (AuthorizationFixedDomain485.withGenerator (baseCrypto c)))
    representation model w.registry.detection valid
  obtain ⟨point,coordinates,_⟩ := member
  change Group.OnCurve (CapturedFirstSubgroup81.d:F)
    (SubgroupSeedCompletion203.fieldPoint (if w.regulated then w.registry.detection else defaultPoint))
  cases flag : w.regulated
  · exact defaultPoint_onCurve
  · change Group.OnCurve (CapturedFirstSubgroup81.d:F) (SubgroupSeedCompletion203.fieldPoint w.registry.detection)
    rw [←coordinates]
    exact model.onCurve point

attribute [local irreducible] model

def represented (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (crypto c) w) : curve.Point :=
  Classical.choose (model.covers _ (onCurve c w legal))

theorem coordinates (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (crypto c) w) :
    model.coordinates (represented c w legal)=SubgroupSeedCompletion203.fieldPoint (selected c w) :=
  Classical.choose_spec (model.covers _ (onCurve c w legal))

theorem encoding (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (crypto c) w) :
    RegistryPointSemantic200.encode representation (model.coordinates (represented c w legal))=selected c w := by
  rw [coordinates]
  change (⟨representation.value ((selected c w).x:F),representation.value ((selected c w).y:F)⟩ : TransferCore.Affine)=_
  rw [RegistryNaturalSeed298.represented_nat _ (canonical c w legal).1,
    RegistryNaturalSeed298.represented_nat _ (canonical c w legal).2]

theorem multiplication (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (crypto c) w) (scalar : Nat) (bound : scalar<2^255) :
    SubgroupSeedCompletion203.fieldPoint ((crypto c).mul scalar (selected c w))=
      model.coordinates (scalar • represented c w legal) := by
  have result := ConcreteAuthorizationCrypto430.multiply_coordinates
    (AuthorizationFixedDomain485.withGenerator (baseCrypto c)) (represented c w legal) scalar bound
  rw [encoding] at result
  exact result
end ShielddSecurity.DetectionGroupDomain611

set_option pp.all true in
#check @ShielddSecurity.DetectionGroupDomain611.defaultPoint_canonical
#print axioms ShielddSecurity.DetectionGroupDomain611.defaultPoint_canonical

set_option pp.all true in
#check @ShielddSecurity.DetectionGroupDomain611.defaultPoint_onCurve
#print axioms ShielddSecurity.DetectionGroupDomain611.defaultPoint_onCurve

set_option pp.all true in
#check @ShielddSecurity.DetectionGroupDomain611.canonical
#print axioms ShielddSecurity.DetectionGroupDomain611.canonical

set_option pp.all true in
#check @ShielddSecurity.DetectionGroupDomain611.onCurve
#print axioms ShielddSecurity.DetectionGroupDomain611.onCurve

set_option pp.all true in
#check @ShielddSecurity.DetectionGroupDomain611.coordinates
#print axioms ShielddSecurity.DetectionGroupDomain611.coordinates

set_option pp.all true in
#check @ShielddSecurity.DetectionGroupDomain611.encoding
#print axioms ShielddSecurity.DetectionGroupDomain611.encoding

set_option pp.all true in
#check @ShielddSecurity.DetectionGroupDomain611.multiplication
#print axioms ShielddSecurity.DetectionGroupDomain611.multiplication
