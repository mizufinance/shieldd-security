import ShielddSecurity.AuthorizationFixedSelectors481B000
import ShielddSecurity.ConcreteAuthorizationCrypto430
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.AuthorizationFixedDomain485
open ConcretePointTorsion01 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem

def first : FixedSelectorAdapter480.Entry × Group.Point F := AuthorizationFixedSelectors481B000.tables[0]
def base : Group.Point F := FixedSelectorAdapter480.base first.1

theorem base_onCurve : Group.OnCurve (CapturedFirstSubgroup81.d:F) base := by
  have geometry := of_decide_eq_true (List.all_eq_true.mp AuthorizationFixedSelectors481B000.geometry_checked
    first (List.getElem_mem (by decide)))
  exact geometry.1

def represented : curve.Point := Classical.choose (model.covers base base_onCurve)
theorem coordinates : model.coordinates represented=base := Classical.choose_spec (model.covers base base_onCurve)

def generator : TransferCore.Affine := RegistryPointSemantic200.encode representation base
def withGenerator (c : Crypto) : Crypto := {c with generator:=generator}
def crypto (c : Crypto) : Crypto := ConcreteAuthorizationCrypto430.crypto (withGenerator c)

theorem generator_coordinates : SubgroupSeedCompletion203.fieldPoint generator=base :=
  ConcreteAuthorizationCrypto430.decode_encode base

theorem multiply_coordinates (c : Crypto) (scalar : Nat) (bound : scalar<2^255) :
    SubgroupSeedCompletion203.fieldPoint ((crypto c).mul scalar (crypto c).generator)=
      model.coordinates (scalar • represented) := by
  have result := ConcreteAuthorizationCrypto430.multiply_coordinates (withGenerator c) represented scalar bound
  rw [coordinates] at result
  exact result
end ShielddSecurity.AuthorizationFixedDomain485

set_option pp.all true in
#check @ShielddSecurity.AuthorizationFixedDomain485.first
#print axioms ShielddSecurity.AuthorizationFixedDomain485.first

set_option pp.all true in
#check @ShielddSecurity.AuthorizationFixedDomain485.base
#print axioms ShielddSecurity.AuthorizationFixedDomain485.base

set_option pp.all true in
#check @ShielddSecurity.AuthorizationFixedDomain485.base_onCurve
#print axioms ShielddSecurity.AuthorizationFixedDomain485.base_onCurve

set_option pp.all true in
#check @ShielddSecurity.AuthorizationFixedDomain485.represented
#print axioms ShielddSecurity.AuthorizationFixedDomain485.represented

set_option pp.all true in
#check @ShielddSecurity.AuthorizationFixedDomain485.coordinates
#print axioms ShielddSecurity.AuthorizationFixedDomain485.coordinates

set_option pp.all true in
#check @ShielddSecurity.AuthorizationFixedDomain485.generator
#print axioms ShielddSecurity.AuthorizationFixedDomain485.generator

set_option pp.all true in
#check @ShielddSecurity.AuthorizationFixedDomain485.withGenerator
#print axioms ShielddSecurity.AuthorizationFixedDomain485.withGenerator

set_option pp.all true in
#check @ShielddSecurity.AuthorizationFixedDomain485.crypto
#print axioms ShielddSecurity.AuthorizationFixedDomain485.crypto

set_option pp.all true in
#check @ShielddSecurity.AuthorizationFixedDomain485.generator_coordinates
#print axioms ShielddSecurity.AuthorizationFixedDomain485.generator_coordinates

set_option pp.all true in
#check @ShielddSecurity.AuthorizationFixedDomain485.multiply_coordinates
#print axioms ShielddSecurity.AuthorizationFixedDomain485.multiply_coordinates
