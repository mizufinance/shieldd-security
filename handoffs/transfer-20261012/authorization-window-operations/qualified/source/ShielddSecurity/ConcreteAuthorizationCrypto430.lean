import ShielddSecurity.IvkInverseConstruction429
import ShielddSecurity.GroupNativeMultiply
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.ConcreteAuthorizationCrypto430
open ConcretePointTorsion01 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem

/-- The source-level group operations; machine arithmetic correspondence is separate. -/
def withOperations (c : Crypto) : Crypto :=
  {c with
    add := fun left right => RegistryPointSemantic200.encode representation
      (Group.affineAdd (CapturedFirstSubgroup81.d:F)
        (SubgroupSeedCompletion203.fieldPoint left) (SubgroupSeedCompletion203.fieldPoint right))
    mul := fun scalar point => RegistryPointSemantic200.encode representation
      (GroupNativeMultiply.nativeMultiply (CapturedFirstSubgroup81.d:F)
        (SubgroupSeedCompletion203.fieldPoint point) (encodeBits 255 scalar))}

def crypto (c : Crypto) : Crypto := ConcreteRegistrySharedEncoding294.crypto (withOperations c)

theorem decode_encode (point : Group.Point F) :
    SubgroupSeedCompletion203.fieldPoint (RegistryPointSemantic200.encode representation point)=point := by
  cases point
  simp only [SubgroupSeedCompletion203.fieldPoint,RegistryPointSemantic200.encode,representation,
    ZMod.natCast_zmod_val]

theorem multiply_coordinates (c : Crypto) (base : curve.Point) (scalar : Nat) (bound : scalar<2^255) :
    SubgroupSeedCompletion203.fieldPoint ((crypto c).mul scalar
      (RegistryPointSemantic200.encode representation (model.coordinates base)))=
      model.coordinates (scalar • base) := by
  change SubgroupSeedCompletion203.fieldPoint (RegistryPointSemantic200.encode representation
    (GroupNativeMultiply.nativeMultiply (CapturedFirstSubgroup81.d:F)
      (SubgroupSeedCompletion203.fieldPoint (RegistryPointSemantic200.encode representation (model.coordinates base)))
      (encodeBits 255 scalar)))=_
  rw [decode_encode,decode_encode]
  rw [GroupNativeMultiply.native_multiply_coordinates (CapturedFirstSubgroup81.d:F)
    ConcreteJubjubField01.imaginary model
    (by rw [ConcreteRegistrySharedEncoding294.coefficient_eq];exact ConcreteJubjubField01.coefficient_no_unit_square)
    ConcreteJubjubField01.imaginary_square (by decide) base (encodeBits 255 scalar),
    encodeBits_value 255 scalar bound]

theorem add_coordinates (c : Crypto) (left right : curve.Point) :
    SubgroupSeedCompletion203.fieldPoint ((crypto c).add
      (RegistryPointSemantic200.encode representation (model.coordinates left))
      (RegistryPointSemantic200.encode representation (model.coordinates right)))=
      model.coordinates (left+right) := by
  change SubgroupSeedCompletion203.fieldPoint (RegistryPointSemantic200.encode representation
    (Group.affineAdd (CapturedFirstSubgroup81.d:F)
      (SubgroupSeedCompletion203.fieldPoint (RegistryPointSemantic200.encode representation (model.coordinates left)))
      (SubgroupSeedCompletion203.fieldPoint (RegistryPointSemantic200.encode representation (model.coordinates right)))))=_
  rw [decode_encode,decode_encode,decode_encode,model.addition]
end ShielddSecurity.ConcreteAuthorizationCrypto430

set_option pp.all true in
#check @ShielddSecurity.ConcreteAuthorizationCrypto430.withOperations
#print axioms ShielddSecurity.ConcreteAuthorizationCrypto430.withOperations

set_option pp.all true in
#check @ShielddSecurity.ConcreteAuthorizationCrypto430.crypto
#print axioms ShielddSecurity.ConcreteAuthorizationCrypto430.crypto

set_option pp.all true in
#check @ShielddSecurity.ConcreteAuthorizationCrypto430.decode_encode
#print axioms ShielddSecurity.ConcreteAuthorizationCrypto430.decode_encode

set_option pp.all true in
#check @ShielddSecurity.ConcreteAuthorizationCrypto430.multiply_coordinates
#print axioms ShielddSecurity.ConcreteAuthorizationCrypto430.multiply_coordinates

set_option pp.all true in
#check @ShielddSecurity.ConcreteAuthorizationCrypto430.add_coordinates
#print axioms ShielddSecurity.ConcreteAuthorizationCrypto430.add_coordinates
