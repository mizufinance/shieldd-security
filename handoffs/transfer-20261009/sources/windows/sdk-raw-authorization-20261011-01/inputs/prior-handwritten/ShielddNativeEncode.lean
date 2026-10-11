import ShielddSecurity.ShielddNativeMultiply

set_option maxHeartbeats 300000

namespace ShielddSecurity.ShielddNativeEncode

variable {F Raw Encoded : Type} [Field F] [CharP F Scalar.modulus]

/-- Explicit global laws of the two upstream encoder primitives. The integer
returned by blst_scalar_from_fr is canonical and interprets the input raw
field state. blst_bendian_from_scalar writes that integer at every byte.
These laws mention neither a group point nor a desired multiplication output.
They do not assume the owned Scalar::as_slice/Write bodies are correct. -/
structure Primitives (operations : ShielddNativeScalar.Operations (F := F) Raw) where
  fromFr : Raw → Encoded
  integer : Encoded → Nat
  bigEndian : Encoded → GroupByteCodec.Bytes
  fromFrBounded : ∀ raw, integer (fromFr raw) < Scalar.modulus
  fromFrValue : ∀ raw, (integer (fromFr raw) : F) = operations.value raw
  bigEndianMeaning : ∀ encoded index,
    (bigEndian encoded index).val = GroupScalarCodec.bigEndianByte (integer encoded) index.val

/-- Scalar::as_slice calls from_fr then bendian; Write copies the resulting
32-byte array. Encoding is globally defined here from those primitive bodies. -/
def asSlice (operations : ShielddNativeScalar.Operations (F := F) Raw)
    (primitives : Primitives (Encoded := Encoded) operations)
    (scalar : ShielddNativeScalar.Wrapped Raw) : GroupByteCodec.Bytes :=
  primitives.bigEndian (primitives.fromFr scalar.raw)

def encode (operations : ShielddNativeScalar.Operations (F := F) Raw)
    (primitives : Primitives (Encoded := Encoded) operations)
    (scalar : ShielddNativeScalar.Wrapped Raw) : GroupByteCodec.Bytes :=
  asSlice operations primitives scalar

theorem byte_value (operations : ShielddNativeScalar.Operations (F := F) Raw)
    (primitives : Primitives (Encoded := Encoded) operations)
    (codec : TransferReduction.CanonicalField F)
    (scalar : ShielddNativeScalar.Wrapped Raw) (index : Fin 32) :
    (encode operations primitives scalar index).val =
      GroupScalarCodec.bigEndianByte (codec.decode (ShielddNativeScalar.value operations scalar)) index.val := by
  have same : primitives.integer (primitives.fromFr scalar.raw) =
      codec.decode (ShielddNativeScalar.value operations scalar) :=
    Scalar.canonical_representative_unique (ShielddNativeScalar.value operations scalar)
      _ _ (primitives.fromFrBounded scalar.raw) (codec.bounded _)
      (primitives.fromFrValue scalar.raw) (codec.roundtrip _)
  change (primitives.bigEndian (primitives.fromFr scalar.raw) index).val = _
  rw [primitives.bigEndianMeaning,same]

theorem encoded_reader (operations : ShielddNativeScalar.Operations (F := F) Raw)
    (primitives : Primitives (Encoded := Encoded) operations)
    (codec : TransferReduction.CanonicalField F)
    (scalar : ShielddNativeScalar.Wrapped Raw) :
    GroupByteCodec.reader (encode operations primitives scalar) =
      GroupScalarCodec.encodedBits (codec.decode (ShielddNativeScalar.value operations scalar)) := by
  have bytes : encode operations primitives scalar =
      (GroupByteCodec.canonicalWrite codec).encode (ShielddNativeScalar.value operations scalar) := by
    funext index
    apply Fin.ext
    exact byte_value operations primitives codec scalar index
  rw [bytes]
  exact GroupByteCodec.reader_join codec (GroupByteCodec.canonicalWrite codec) _

/-- Owned Point<Scalar>::multiply: exact255 byte-indexed bits, from(u64)
conversion, reversed native chunks, coefficient_d, final normalization. -/
def multiplyScalar (operations : ShielddNativeScalar.Operations (F := F) Raw)
    (primitives : Primitives (Encoded := Encoded) operations)
    (base : ShielddNativePoint.Point Raw) (scalar : ShielddNativeScalar.Wrapped Raw) :
    ShielddNativePoint.Point Raw :=
  ShielddNativeMultiply.multiply operations (ShielddNativeScalar.coefficientD operations) base
    (GroupByteCodec.reader (encode operations primitives scalar))

theorem multiply_scalar_coordinates {J : Type} [AddCommGroup J]
    (operations : ShielddNativeScalar.Operations (F := F) Raw)
    (primitives : Primitives (Encoded := Encoded) operations)
    (codec : TransferReduction.CanonicalField F)
    (imaginary : F)
    (model : Group.StandardCurveModel J (-(10240 : F) * (10241 : F)⁻¹))
    (nonSquare : Group.NoUnitSquare (-(10240 : F) * (10241 : F)⁻¹))
    (imaginarySquare : imaginary * imaginary = -1) (two : (2 : F) ≠ 0)
    (base : ShielddNativePoint.Point Raw) (point : J)
    (input : ShielddNativePoint.pointValue operations base = model.coordinates point)
    (scalar : ShielddNativeScalar.Wrapped Raw) :
    ShielddNativePoint.pointValue operations (multiplyScalar operations primitives base scalar) =
      model.coordinates (codec.decode (ShielddNativeScalar.value operations scalar) • point) := by
  unfold multiplyScalar
  rw [ShielddNativeMultiply.multiply_value,ShielddNativeScalar.coefficient_d_value,input,encoded_reader]
  rw [GroupScalarCodec.encoded_reader]
  exact GroupScalarCodec.native_field_coordinates _ imaginary model nonSquare imaginarySquare two
    point _ (codec.bounded _)

set_option pp.all true in
#check @byte_value
#print axioms byte_value
set_option pp.all true in
#check @encoded_reader
#print axioms encoded_reader
set_option pp.all true in
#check @multiply_scalar_coordinates
#print axioms multiply_scalar_coordinates

end ShielddSecurity.ShielddNativeEncode
