import ShielddSecurity.DetectionGroupDomain611
import ShielddSecurity.PayloadGroupDomain557
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.TierGroupDomain612
open ConcretePointTorsion01 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem
open DetectionGroupDomain611 (baseCrypto)
def useDetection (w : TransferSem.Witness) (family : Fin 5) : Bool :=
  decide (family.val=1) || flagged w
def selected (c : Crypto) (w : TransferSem.Witness) (family : Fin 5) : TransferCore.Affine :=
  if useDetection w family then DetectionGroupDomain611.selected c w
  else PayloadGroupDomain557.selected (baseCrypto c) w

theorem canonical (c : Crypto) (w : TransferSem.Witness) (family : Fin 5)
    (legal : TransferSem.TransferSem (DetectionGroupDomain611.crypto c) w) : TransferCore.CanonicalAffine (selected c w family) := by
  unfold selected
  split
  · exact DetectionGroupDomain611.canonical c w legal
  · exact PayloadGroupDomain557.canonical (baseCrypto c) w legal

theorem onCurve (c : Crypto) (w : TransferSem.Witness) (family : Fin 5)
    (legal : TransferSem.TransferSem (DetectionGroupDomain611.crypto c) w) :
    Group.OnCurve (CapturedFirstSubgroup81.d:F) (SubgroupSeedCompletion203.fieldPoint (selected c w family)) := by
  unfold selected
  split
  · exact DetectionGroupDomain611.onCurve c w legal
  · exact PayloadGroupDomain557.onCurve (baseCrypto c) w legal

attribute [local irreducible] model

def represented (c : Crypto) (w : TransferSem.Witness) (family : Fin 5)
    (legal : TransferSem.TransferSem (DetectionGroupDomain611.crypto c) w) : curve.Point :=
  Classical.choose (model.covers _ (onCurve c w family legal))

theorem coordinates (c : Crypto) (w : TransferSem.Witness) (family : Fin 5)
    (legal : TransferSem.TransferSem (DetectionGroupDomain611.crypto c) w) :
    model.coordinates (represented c w family legal)=SubgroupSeedCompletion203.fieldPoint (selected c w family) :=
  Classical.choose_spec (model.covers _ (onCurve c w family legal))

theorem encoding (c : Crypto) (w : TransferSem.Witness) (family : Fin 5)
    (legal : TransferSem.TransferSem (DetectionGroupDomain611.crypto c) w) :
    RegistryPointSemantic200.encode representation (model.coordinates (represented c w family legal))=selected c w family := by
  rw [coordinates]
  change (⟨representation.value ((selected c w family).x:F),representation.value ((selected c w family).y:F)⟩ : TransferCore.Affine)=_
  rw [RegistryNaturalSeed298.represented_nat _ (canonical c w family legal).1,
    RegistryNaturalSeed298.represented_nat _ (canonical c w family legal).2]

theorem multiplication (c : Crypto) (w : TransferSem.Witness) (family : Fin 5)
    (legal : TransferSem.TransferSem (DetectionGroupDomain611.crypto c) w) (scalar : Nat) (bound : scalar<2^255) :
    SubgroupSeedCompletion203.fieldPoint ((DetectionGroupDomain611.crypto c).mul scalar (selected c w family))=
      model.coordinates (scalar • represented c w family legal) := by
  have result := ConcreteAuthorizationCrypto430.multiply_coordinates
    (AuthorizationFixedDomain485.withGenerator (baseCrypto c)) (represented c w family legal) scalar bound
  rw [encoding] at result
  exact result
end ShielddSecurity.TierGroupDomain612

set_option pp.all true in
#check @ShielddSecurity.TierGroupDomain612.useDetection
#print axioms ShielddSecurity.TierGroupDomain612.useDetection

set_option pp.all true in
#check @ShielddSecurity.TierGroupDomain612.selected
#print axioms ShielddSecurity.TierGroupDomain612.selected

set_option pp.all true in
#check @ShielddSecurity.TierGroupDomain612.canonical
#print axioms ShielddSecurity.TierGroupDomain612.canonical

set_option pp.all true in
#check @ShielddSecurity.TierGroupDomain612.onCurve
#print axioms ShielddSecurity.TierGroupDomain612.onCurve

set_option pp.all true in
#check @ShielddSecurity.TierGroupDomain612.coordinates
#print axioms ShielddSecurity.TierGroupDomain612.coordinates

set_option pp.all true in
#check @ShielddSecurity.TierGroupDomain612.encoding
#print axioms ShielddSecurity.TierGroupDomain612.encoding

set_option pp.all true in
#check @ShielddSecurity.TierGroupDomain612.multiplication
#print axioms ShielddSecurity.TierGroupDomain612.multiplication
