import ShielddSecurity.ShielddNativeParameterRead

set_option maxHeartbeats 200000

namespace ShielddSecurity.ShielddNativeParameterCodec

open GroupByteCodec

variable {F : Type} [Field F] [CharP F Scalar.modulus]

/-- A canonical natural artifact entry and its field cast produce the same
actual32-byte BE buffer. This bridges the artifact loader to the independently
defined field-codec constant function, not just their eventual field values. -/
theorem big_endian_cast (codec : TransferReduction.CanonicalField F) (n : Nat)
    (canonical : n < Scalar.modulus) :
    (canonicalWrite codec).encode (n : F) = ShielddNativeParameterRead.bigEndian n := by
  funext index
  apply Fin.ext
  simp only [canonicalWrite,ShielddNativeParameterRead.bigEndian,
    TransferReduction.decode_canonical_cast codec n canonical]

/-- Exact equality of the native Scalar objects returned by the owned BE
reader, including the unreachable-on-canonical-input total default branch. -/
theorem circuit_load_cast {Raw Encoded : Type}
    (operations : ShielddNativeScalar.Operations (F := F) Raw)
    (reader : ShielddNativeScalar.ReadPrimitives Encoded Raw operations)
    (codec : TransferReduction.CanonicalField F) (n : Nat) (canonical : n < Scalar.modulus) :
    ShielddNativeIvkHash.circuitConstant operations reader codec (n : F) =
      ShielddNativeParameterRead.circuitParse operations reader n := by
  unfold ShielddNativeIvkHash.circuitConstant ShielddNativeParameterRead.circuitParse
  rw [big_endian_cast codec n canonical]

theorem little_endian_cast (codec : TransferReduction.CanonicalField F) (n : Nat)
    (canonical : n < Scalar.modulus) :
    ShielddNativeIvkHash.littleEndianWrite codec (n : F) =
      reverseBytes (ShielddNativeParameterRead.bigEndian n) := by
  funext index
  apply Fin.ext
  simp only [ShielddNativeIvkHash.littleEndianWrite,
    TransferReduction.decode_canonical_cast codec n canonical,
    ShielddNativeParameterRead.reversed_byte]

/-- The SDK reads identical LE arrays in both definitions, so the returned
Q objects are equal by deterministic parsing. No Fq-value injectivity or
chosen native constant equality is supplied as an additional contract. -/
theorem sdk_load_cast {Q : Type} (fq : GroupNativeSdk.FqBytes Q)
    (arithmetic : ShielddNativeIvkHash.FqArithmetic (F := F) Q fq)
    (codec : TransferReduction.CanonicalField F) (n : Nat) (canonical : n < Scalar.modulus) :
    ShielddNativeIvkHash.sdkConstant fq arithmetic codec (n : F) =
      ShielddNativeParameterRead.sdkParse fq arithmetic n := by
  unfold ShielddNativeIvkHash.sdkConstant ShielddNativeParameterRead.sdkParse
  rw [little_endian_cast codec n canonical]

set_option pp.all true in
#check @big_endian_cast
#print axioms big_endian_cast
set_option pp.all true in
#check @circuit_load_cast
#print axioms circuit_load_cast
set_option pp.all true in
#check @little_endian_cast
#print axioms little_endian_cast
set_option pp.all true in
#check @sdk_load_cast
#print axioms sdk_load_cast

end ShielddSecurity.ShielddNativeParameterCodec
