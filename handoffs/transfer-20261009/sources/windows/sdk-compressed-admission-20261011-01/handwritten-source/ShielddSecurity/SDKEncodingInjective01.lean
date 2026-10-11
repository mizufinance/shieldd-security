import ShielddSecurity.SDKCompressedDecoder01
import ShielddSecurity.SDKByteIterator01

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.SDKEncodingInjective01

open ConcreteJubjubField01

theorem point_ext (left right : Group.Point F)
    (sameX : left.x = right.x) (sameY : left.y = right.y) : left = right := by
  cases left
  cases right
  congr 1

theorem same_parity_neg (x : F) (same : (-x).val % 2 = x.val % 2) : x = 0 := by
  by_contra nonzero
  letI : NeZero x := ⟨nonzero⟩
  rw [ZMod.val_neg_of_ne_zero] at same
  have bound := ZMod.val_lt x
  have primeOdd : Scalar.modulus % 2 = 1 := by decide +kernel
  omega

/-- On the concrete full curve, y and canonical x parity determine a point.
The zero-root case is included; no nonidentity or subgroup premise is needed. -/
theorem curve_unique (left right : Group.Point F)
    (leftCurve : Group.OnCurve coefficient left) (rightCurve : Group.OnCurve coefficient right)
    (sameY : left.y = right.y) (sameSign : left.x.val % 2 = right.x.val % 2) :
    left = right := by
  have denominator := SDKCompressedDecoder01.denominator_nonzero coefficient imaginary
    right.y coefficient_no_unit_square imaginary_square
  rcases SDKCompressedDecoder01.same_y_roots coefficient left right leftCurve rightCurve
    sameY denominator with sameX | negativeX
  · exact point_ext left right sameX sameY
  · rw [negativeX] at sameSign
    have zero := same_parity_neg right.x sameSign
    have sameX : left.x = right.x := by simpa only [zero, neg_zero] using negativeX
    exact point_ext left right sameX sameY

theorem canonical_bytes_injective (left right : Nat)
    (leftBound : left < 2 ^ 256) (rightBound : right < 2 ^ 256)
    (same : SDKByteIterator01.canonicalBytes 32 left = SDKByteIterator01.canonicalBytes 32 right) :
    left = right := by
  have bits := congrArg SDKByteIterator01.ascending same
  rw [SDKByteIterator01.ascending_canonical, SDKByteIterator01.ascending_canonical,
    SDKByteIterator01.range_reader, SDKByteIterator01.range_reader] at bits
  change GroupScalarCodec.readBits 256 left = GroupScalarCodec.readBits 256 right at bits
  have values := congrArg binary bits
  rw [GroupScalarCodec.reader_value 256 left leftBound,
    GroupScalarCodec.reader_value 256 right rightBound] at values
  exact values

/-- Algebraic encoding integer: canonical y in the low 255 bits and x parity
in bit 255. Native to_bytes, field encoding and byte arrays remain a separate
Rust refinement boundary. -/
def encodedValue (point : Group.Point F) : Nat :=
  point.y.val + 2 ^ 255 * (point.x.val % 2)

theorem encoded_value_bound (point : Group.Point F) : encodedValue point < 2 ^ 256 := by
  have yBound := lt_trans (ZMod.val_lt point.y) GroupScalarCodec.circuit_field_width
  have signBound := Nat.mod_lt point.x.val (by decide : 0 < 2)
  dsimp only [encodedValue]
  norm_num only [Nat.reducePow] at yBound ⊢
  omega

theorem encoded_value_coordinates (left right : Group.Point F)
    (same : encodedValue left = encodedValue right) :
    left.y = right.y ∧ left.x.val % 2 = right.x.val % 2 := by
  have leftBound := lt_trans (ZMod.val_lt left.y) GroupScalarCodec.circuit_field_width
  have rightBound := lt_trans (ZMod.val_lt right.y) GroupScalarCodec.circuit_field_width
  dsimp only [encodedValue] at same
  norm_num only [Nat.reducePow] at same leftBound rightBound
  have sameY : left.y.val = right.y.val := by omega
  exact ⟨ZMod.val_injective Scalar.modulus sameY, by omega⟩

def encode (point : Group.Point F) : List Nat :=
  SDKByteIterator01.canonicalBytes 32 (encodedValue point)

theorem encoding_injective (left right : Group.Point F)
    (leftCurve : Group.OnCurve coefficient left) (rightCurve : Group.OnCurve coefficient right)
    (same : encode left = encode right) : left = right := by
  have value := canonical_bytes_injective (encodedValue left) (encodedValue right)
    (encoded_value_bound left) (encoded_value_bound right) same
  have coordinates := encoded_value_coordinates left right value
  exact curve_unique left right leftCurve rightCurve coordinates.1 coordinates.2

theorem decoded_unique (point output : Group.Point F)
    (curve : Group.OnCurve coefficient point)
    (decoded : SDKCompressedDecoder01.Decoded point.y (point.x.val % 2) output) :
    output = point :=
  curve_unique output point (SDKCompressedDecoder01.decoded_on_curve _ _ _ decoded)
    curve decoded.1 decoded.2.2

end ShielddSecurity.SDKEncodingInjective01


set_option pp.all true in
#check @ShielddSecurity.SDKEncodingInjective01.point_ext
#print axioms ShielddSecurity.SDKEncodingInjective01.point_ext
set_option pp.all true in
#check @ShielddSecurity.SDKEncodingInjective01.same_parity_neg
#print axioms ShielddSecurity.SDKEncodingInjective01.same_parity_neg
set_option pp.all true in
#check @ShielddSecurity.SDKEncodingInjective01.curve_unique
#print axioms ShielddSecurity.SDKEncodingInjective01.curve_unique
set_option pp.all true in
#check @ShielddSecurity.SDKEncodingInjective01.canonical_bytes_injective
#print axioms ShielddSecurity.SDKEncodingInjective01.canonical_bytes_injective
set_option pp.all true in
#check @ShielddSecurity.SDKEncodingInjective01.encodedValue
#print axioms ShielddSecurity.SDKEncodingInjective01.encodedValue
set_option pp.all true in
#check @ShielddSecurity.SDKEncodingInjective01.encoded_value_bound
#print axioms ShielddSecurity.SDKEncodingInjective01.encoded_value_bound
set_option pp.all true in
#check @ShielddSecurity.SDKEncodingInjective01.encoded_value_coordinates
#print axioms ShielddSecurity.SDKEncodingInjective01.encoded_value_coordinates
set_option pp.all true in
#check @ShielddSecurity.SDKEncodingInjective01.encode
#print axioms ShielddSecurity.SDKEncodingInjective01.encode
set_option pp.all true in
#check @ShielddSecurity.SDKEncodingInjective01.encoding_injective
#print axioms ShielddSecurity.SDKEncodingInjective01.encoding_injective
set_option pp.all true in
#check @ShielddSecurity.SDKEncodingInjective01.decoded_unique
#print axioms ShielddSecurity.SDKEncodingInjective01.decoded_unique
