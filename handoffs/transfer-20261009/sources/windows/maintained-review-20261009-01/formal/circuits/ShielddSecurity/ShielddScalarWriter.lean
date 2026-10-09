import ShielddSecurity.ShielddNativeScalar

set_option maxHeartbeats 200000

namespace ShielddSecurity.ShielddScalarWriter

open GroupByteCodec ShielddNativeScalar

variable {F : Type} [Field F]

/-- Global contracts for the two unmodified BLST primitives called by the
owned Scalar::as_slice wrapper. The first returns the canonical integer for
every valid raw field state; the second writes all32 big-endian bytes. These
contracts do not assume the complete owned writer or a particular witness. -/
structure Primitives (Encoded Raw : Type) (codec : TransferReduction.CanonicalField F)
    (operations : Operations (F := F) Raw) where
  fromFr : Raw → Encoded
  integer : Encoded → Nat
  bigEndian : Encoded → Bytes
  fromFrMeaning : ∀ raw, integer (fromFr raw) = codec.decode (operations.value raw)
  bigEndianMeaning : ∀ encoded, integer encoded < Scalar.modulus → ∀ index,
    (bigEndian encoded index).val = GroupScalarCodec.bigEndianByte (integer encoded) index.val

/-- Exact owned call order: blst_scalar_from_fr followed by
blst_bendian_from_scalar. The latter overwrites every byte of the zero buffer. -/
def asSlice {Encoded Raw : Type} {codec : TransferReduction.CanonicalField F}
    {operations : Operations (F := F) Raw} (primitives : Primitives Encoded Raw codec operations)
    (scalar : Wrapped Raw) : Bytes := primitives.bigEndian (primitives.fromFr scalar.raw)

theorem as_slice_byte_value {Encoded Raw : Type} (codec : TransferReduction.CanonicalField F)
    (operations : Operations (F := F) Raw) (primitives : Primitives Encoded Raw codec operations)
    (scalar : Wrapped Raw) (index : Fin 32) :
    (asSlice primitives scalar index).val =
      GroupScalarCodec.bigEndianByte (codec.decode (value operations scalar)) index.val := by
  have bound : primitives.integer (primitives.fromFr scalar.raw) < Scalar.modulus := by
    rw [primitives.fromFrMeaning]
    exact codec.bounded _
  exact (primitives.bigEndianMeaning _ bound index).trans
    (congrArg (fun n => GroupScalarCodec.bigEndianByte n index.val)
      (primitives.fromFrMeaning scalar.raw))

/-- A representative is constructed through the already modeled canonical
AllowZero reader, including field zero. No raw representation section is
assumed. Only its field value is used; raw-state equality is unnecessary. -/
def represent {ReadEncoded Raw : Type} (codec : TransferReduction.CanonicalField F)
    (operations : Operations (F := F) Raw) (read : ReadPrimitives ReadEncoded Raw operations)
    (fieldValue : F) : Wrapped Raw :=
  ⟨read.fromScalar (read.fromBigEndian ((canonicalWrite codec).encode fieldValue))⟩

theorem represented_value {ReadEncoded Raw : Type} (codec : TransferReduction.CanonicalField F)
    (operations : Operations (F := F) Raw) (read : ReadPrimitives ReadEncoded Raw operations)
    (fieldValue : F) : value operations (represent codec operations read fieldValue) = fieldValue := by
  have represented := read_allow_zero_value operations read (codec.decode fieldValue)
    (codec.bounded fieldValue) ((canonicalWrite codec).encode fieldValue)
    ((canonicalWrite codec).byteValue fieldValue)
  exact represented.2.trans (codec.roundtrip fieldValue)

/-- Native bytes, indexed by their field meaning. Its canonical law follows
from the two primitive contracts and the constructed representative. -/
def writer {Encoded ReadEncoded Raw : Type} (codec : TransferReduction.CanonicalField F)
    (operations : Operations (F := F) Raw) (read : ReadPrimitives ReadEncoded Raw operations)
    (primitives : Primitives Encoded Raw codec operations) : BEWrite codec where
  encode fieldValue := asSlice primitives (represent codec operations read fieldValue)
  byteValue fieldValue index := by
    rw [as_slice_byte_value,represented_value]

theorem raw_write_agreement {Encoded ReadEncoded Raw : Type}
    (codec : TransferReduction.CanonicalField F) (operations : Operations (F := F) Raw)
    (read : ReadPrimitives ReadEncoded Raw operations)
    (primitives : Primitives Encoded Raw codec operations) (scalar : Wrapped Raw) :
    asSlice primitives scalar = (writer codec operations read primitives).encode (value operations scalar) := by
  funext index
  apply Fin.ext
  exact (as_slice_byte_value codec operations primitives scalar index).trans
    ((writer codec operations read primitives).byteValue (value operations scalar) index).symm

theorem raw_reader_join {Encoded ReadEncoded Raw : Type}
    (codec : TransferReduction.CanonicalField F) (operations : Operations (F := F) Raw)
    (read : ReadPrimitives ReadEncoded Raw operations)
    (primitives : Primitives Encoded Raw codec operations) (scalar : Wrapped Raw) :
    reader (asSlice primitives scalar) =
      GroupScalarCodec.encodedBits (codec.decode (value operations scalar)) := by
  rw [raw_write_agreement]
  exact reader_join codec (writer codec operations read primitives) _

/-- BufMut::put_slice copies the complete initialized32-byte slice to the
buffer. The copy primitive's standard functional contract is list append;
allocation, memory safety and zeroization are outside this value model. -/
def write {Encoded Raw : Type} {codec : TransferReduction.CanonicalField F}
    {operations : Operations (F := F) Raw} (primitives : Primitives Encoded Raw codec operations)
    (prefix : List Byte) (scalar : Wrapped Raw) : List Byte :=
  prefix ++ List.ofFn (asSlice primitives scalar)

theorem write_prefix {Encoded ReadEncoded Raw : Type}
    (codec : TransferReduction.CanonicalField F) (operations : Operations (F := F) Raw)
    (read : ReadPrimitives ReadEncoded Raw operations)
    (primitives : Primitives Encoded Raw codec operations) (prefix : List Byte) (scalar : Wrapped Raw) :
    write primitives prefix scalar = prefix ++
      List.ofFn ((writer codec operations read primitives).encode (value operations scalar)) := by
  unfold write
  rw [raw_write_agreement]

theorem readback {Encoded ReadEncoded Raw : Type}
    (codec : TransferReduction.CanonicalField F) (operations : Operations (F := F) Raw)
    (read : ReadPrimitives ReadEncoded Raw operations)
    (primitives : Primitives Encoded Raw codec operations) (scalar : Wrapped Raw) :
    (ShielddScalarReader.decoder (readerBackend operations read)).decode (asSlice primitives scalar) =
      some (value operations scalar) := by
  have decoded := ShielddScalarReader.decoder_canonical (readerBackend operations read)
    (codec.decode (value operations scalar)) (codec.bounded _)
    (asSlice primitives scalar) (as_slice_byte_value codec operations primitives scalar)
  exact decoded.trans (congrArg some (codec.roundtrip _))

set_option pp.all true in
#check @as_slice_byte_value
#print axioms as_slice_byte_value
set_option pp.all true in
#check @represented_value
#print axioms represented_value
set_option pp.all true in
#check @writer
#print axioms writer
set_option pp.all true in
#check @raw_write_agreement
#print axioms raw_write_agreement
set_option pp.all true in
#check @raw_reader_join
#print axioms raw_reader_join
set_option pp.all true in
#check @write_prefix
#print axioms write_prefix
set_option pp.all true in
#check @readback
#print axioms readback

end ShielddSecurity.ShielddScalarWriter
