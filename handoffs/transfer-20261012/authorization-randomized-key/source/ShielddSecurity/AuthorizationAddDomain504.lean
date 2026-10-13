import ShielddSecurity.AuthorizationFixedFinal500
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.AuthorizationAddDomain504
open ConcretePointTorsion01 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem

def left (w : TransferSem.Witness) : Group.Point F := SubgroupSeedCompletion203.fieldPoint w.auth.ak
def right (w : TransferSem.Witness) : Group.Point F := model.coordinates (w.auth.randomizer • AuthorizationFixedDomain485.represented)
def delta (w : TransferSem.Witness) : F := Group.delta (CapturedFirstSubgroup81.d:F) (left w) (right w)
def denominator (w : TransferSem.Witness) : F := (1+delta w)*(1-delta w)

theorem left_onCurve (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w) :
    Group.OnCurve (CapturedFirstSubgroup81.d:F) (left w) := by
  obtain ⟨point,coordinates,_⟩ := AuthorizationPointDomain404.member
    (ConcreteAuthorizationCrypto430.withOperations (AuthorizationFixedDomain485.withGenerator c)) w legal
  rw [left,←coordinates]
  exact model.onCurve point

theorem denominator_nonzero (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w) : denominator w≠0 := by
  have nonzero := Group.denominators_nonzero (CapturedFirstSubgroup81.d:F) imaginary
    (by rw [coefficient_eq];exact coefficient_no_unit_square) imaginary_square
    (left w) (right w) (left_onCurve c w legal) (model.onCurve _)
  exact mul_ne_zero nonzero.1 nonzero.2

theorem result (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w) :
    Group.affineAdd (CapturedFirstSubgroup81.d:F) (left w) (right w)=
      SubgroupSeedCompletion203.fieldPoint w.auth.rk := by
  have bound := (AuthScalarSeed366.legal_bounds
    (ConcreteAuthorizationCrypto430.withOperations (AuthorizationFixedDomain485.withGenerator c)) w legal).2.2
  have multiply := AuthorizationFixedDomain485.multiply_coordinates c w.auth.randomizer (lt_trans bound (by decide))
  rcases legal.2.1.2.2.2.1 with ⟨_,_,_,_,_,_,_,_,_,_,_,key⟩
  have fieldKey := congrArg (SubgroupSeedCompletion203.fieldPoint (F:=F)) key
  change SubgroupSeedCompletion203.fieldPoint w.auth.rk=
    SubgroupSeedCompletion203.fieldPoint (RegistryPointSemantic200.encode representation
      (Group.affineAdd (CapturedFirstSubgroup81.d:F) (left w)
        (SubgroupSeedCompletion203.fieldPoint ((AuthorizationFixedDomain485.crypto c).mul
          w.auth.randomizer (AuthorizationFixedDomain485.crypto c).generator)))) at fieldKey
  rw [ConcreteAuthorizationCrypto430.decode_encode,multiply] at fieldKey
  exact fieldKey.symm
end ShielddSecurity.AuthorizationAddDomain504

set_option pp.all true in
#check @ShielddSecurity.AuthorizationAddDomain504.left
#print axioms ShielddSecurity.AuthorizationAddDomain504.left

set_option pp.all true in
#check @ShielddSecurity.AuthorizationAddDomain504.right
#print axioms ShielddSecurity.AuthorizationAddDomain504.right

set_option pp.all true in
#check @ShielddSecurity.AuthorizationAddDomain504.delta
#print axioms ShielddSecurity.AuthorizationAddDomain504.delta

set_option pp.all true in
#check @ShielddSecurity.AuthorizationAddDomain504.denominator
#print axioms ShielddSecurity.AuthorizationAddDomain504.denominator

set_option pp.all true in
#check @ShielddSecurity.AuthorizationAddDomain504.left_onCurve
#print axioms ShielddSecurity.AuthorizationAddDomain504.left_onCurve

set_option pp.all true in
#check @ShielddSecurity.AuthorizationAddDomain504.denominator_nonzero
#print axioms ShielddSecurity.AuthorizationAddDomain504.denominator_nonzero

set_option pp.all true in
#check @ShielddSecurity.AuthorizationAddDomain504.result
#print axioms ShielddSecurity.AuthorizationAddDomain504.result
