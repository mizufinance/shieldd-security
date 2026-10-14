-- GENERATED from points.json. Do not hand edit.
import ShielddSecurity.DetectionGroupDomain611
import ShielddSecurity.ConcreteAuthorizationCrypto430
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.BalanceBlindingDomain670
open ConcretePointTorsion01 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem
noncomputable def base : Group.Point F := ⟨47042227020334719030310671629496501061777616454137182971856918820250544653111,49531484613049745751551498609154147537293487462303198979615882148044956461707⟩
theorem base_onCurve : Group.OnCurve (CapturedFirstSubgroup81.d:F) base := by
  unfold Group.OnCurve
  decide +kernel
noncomputable def represented : curve.Point := Classical.choose (model.covers base base_onCurve)
theorem coordinates : model.coordinates represented=base := Classical.choose_spec (model.covers base base_onCurve)
noncomputable def blinding : TransferCore.Affine := RegistryPointSemantic200.encode representation base
noncomputable def withBlinding (c : Crypto) : Crypto := {c with blindingGenerator:=blinding}
noncomputable def crypto (c : Crypto) : Crypto := DetectionGroupDomain611.crypto (withBlinding c)
theorem blinding_coordinates : SubgroupSeedCompletion203.fieldPoint blinding=base :=
  ConcreteAuthorizationCrypto430.decode_encode base
attribute [local irreducible] model
theorem multiply_coordinates (c : Crypto) (scalar : Nat) (bound : scalar<2^255) :
    SubgroupSeedCompletion203.fieldPoint ((crypto c).mul scalar (crypto c).blindingGenerator)=
      model.coordinates (scalar • represented) := by
  let chosen := AuthorizationFixedDomain485.withGenerator (DetectionGroupDomain611.baseCrypto (withBlinding c))
  change SubgroupSeedCompletion203.fieldPoint ((ConcreteAuthorizationCrypto430.crypto chosen).mul scalar blinding)=_
  have result := ConcreteAuthorizationCrypto430.multiply_coordinates chosen represented scalar bound
  rw [coordinates] at result
  exact result
end ShielddSecurity.BalanceBlindingDomain670

set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingDomain670.base
#print axioms ShielddSecurity.BalanceBlindingDomain670.base

set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingDomain670.base_onCurve
#print axioms ShielddSecurity.BalanceBlindingDomain670.base_onCurve

set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingDomain670.represented
#print axioms ShielddSecurity.BalanceBlindingDomain670.represented

set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingDomain670.coordinates
#print axioms ShielddSecurity.BalanceBlindingDomain670.coordinates

set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingDomain670.blinding
#print axioms ShielddSecurity.BalanceBlindingDomain670.blinding

set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingDomain670.withBlinding
#print axioms ShielddSecurity.BalanceBlindingDomain670.withBlinding

set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingDomain670.crypto
#print axioms ShielddSecurity.BalanceBlindingDomain670.crypto

set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingDomain670.blinding_coordinates
#print axioms ShielddSecurity.BalanceBlindingDomain670.blinding_coordinates

set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingDomain670.multiply_coordinates
#print axioms ShielddSecurity.BalanceBlindingDomain670.multiply_coordinates
