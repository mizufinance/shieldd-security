import ShielddSecurity.SDKByteIterator01
import ShielddSecurity.SDKCompressedDecoder01
import ShielddSecurity.SDKSpendAuthSubgroup01

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency true

namespace ShielddSecurity.SDKCodecJoin01
open ConcreteJubjubField01 ConcretePointTorsion01 ConcreteCofactorModel01

attribute [local irreducible] SDKJubjubMultiply01.multiply SDKJubjubMultiply01.encodedBits

/-- Source-level mathematical SDK loop, including reverse-byte, reverse-inner-bit
and skip-four traversal. The native Rust representation boundary stays explicit. -/
def sourceMultiply (point : SDKJubjubExtended01.Extended F) (bytes : List Nat) :
    SDKJubjubExtended01.Extended F :=
  (SDKByteIterator01.retained bytes).foldl (SDKJubjubMultiply01.step point) SDKJubjubMultiply01.identity

theorem source_canonical (point : SDKJubjubExtended01.Extended F) (value : Nat) :
    sourceMultiply point (SDKByteIterator01.canonicalBytes 32 value) =
      SDKJubjubMultiply01.multiply point (SDKJubjubMultiply01.encodedBits value) := by
  unfold sourceMultiply
  rw [SDKByteIterator01.retained_canonical]
  conv_rhs => unfold SDKJubjubMultiply01.multiply
  rw [SDKJubjubMultiply01.encoded_reader]

theorem source_canonical_coordinates (point : SDKJubjubExtended01.Extended F) (p : curve.Point)
    (represented : SDKJubjubExtended01.Represents point (model.coordinates p))
    (value : Nat) (width : value < 2 ^ 252) :
    SDKJubjubExtended01.normalize (sourceMultiply point (SDKByteIterator01.canonicalBytes 32 value)) =
      model.coordinates (value • p) := by
  rw [source_canonical]
  exact SDKJubjubMultiply01.canonical_multiply point p represented value width

theorem modulus_canonical : SDKByteIterator01.canonicalBytes 32 Scalar.order =
    SDKJubjubMultiply01.modulusBytes := by decide +kernel

theorem source_modulus_test_iff (point : SDKJubjubExtended01.Extended F) (p : curve.Point)
    (represented : SDKJubjubExtended01.Represents point (model.coordinates p)) :
    SDKJubjubExtended01.isIdentity (sourceMultiply point SDKJubjubMultiply01.modulusBytes) ↔
      Scalar.order • p = 0 := by
  rw [← modulus_canonical, source_canonical]
  exact SDKJubjubMultiply01.modulus_test_iff point p represented

theorem decoded_sdk_subgroup (point : curve.Point)
    (decoded : SDKCompressedDecoder01.Decoded (SDKSpendAuthCertificates01.sdkY : F) 1
      (model.coordinates point)) : Scalar.order • point = 0 := by
  have coordinates := SDKCompressedDecoder01.sdk_decoded_unique (model.coordinates point) decoded
  have equal : point = SDKSpendAuthSubgroup01.base :=
    model.injective (coordinates.trans SDKSpendAuthSubgroup01.base_coordinates.symm)
  rw [equal]
  exact SDKSpendAuthSubgroup01.base_subgroup

end ShielddSecurity.SDKCodecJoin01

set_option pp.all true in
#check @ShielddSecurity.SDKCodecJoin01.sourceMultiply
#print axioms ShielddSecurity.SDKCodecJoin01.sourceMultiply
set_option pp.all true in
#check @ShielddSecurity.SDKCodecJoin01.source_canonical
#print axioms ShielddSecurity.SDKCodecJoin01.source_canonical
set_option pp.all true in
#check @ShielddSecurity.SDKCodecJoin01.source_canonical_coordinates
#print axioms ShielddSecurity.SDKCodecJoin01.source_canonical_coordinates
set_option pp.all true in
#check @ShielddSecurity.SDKCodecJoin01.modulus_canonical
#print axioms ShielddSecurity.SDKCodecJoin01.modulus_canonical
set_option pp.all true in
#check @ShielddSecurity.SDKCodecJoin01.source_modulus_test_iff
#print axioms ShielddSecurity.SDKCodecJoin01.source_modulus_test_iff
set_option pp.all true in
#check @ShielddSecurity.SDKCodecJoin01.decoded_sdk_subgroup
#print axioms ShielddSecurity.SDKCodecJoin01.decoded_sdk_subgroup
